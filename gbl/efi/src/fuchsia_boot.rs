// Copyright 2024, The Android Open Source Project
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::utils::efi_to_zbi_mem_range_type;
#[allow(unused_imports)]
use crate::{
    efi_blocks::{find_block_devices, EfiGblDisk},
    fastboot::fastboot,
    ops::Ops,
    utils::get_efi_mem_attr,
};
use efi::{EfiEntry, EfiMemoryAttributesTable, EfiMemoryMap};
use efi_types::{
    EfiMemoryAttributesTableHeader, EfiMemoryDescriptor, EFI_MEMORY_ATTRIBUTE_EMA_RUNTIME,
};
use liberror::Error;
use liberror::Error::BufferTooSmall;
use libgbl::{
    constants::PAGE_SIZE as PAGE_SIZE_USIZE,
    fuchsia_boot::{zircon_check_enter_fastboot, zircon_load_verify_abr, zircon_part_name},
    gbl_print, gbl_println,
    ops::ImageBuffer,
    partition::check_part_unique,
    GblOps,
    IntegrationError::UnificationError,
    Result,
};
use safemath::SafeNum;
use zbi::{zbi_format::zbi_mem_range_t, ZbiContainer, ZbiFlags, ZbiType};
use zerocopy::{Ref, SplitByteSliceMut};

const PAGE_SIZE: u64 = PAGE_SIZE_USIZE as u64;

/// Check if the disk GPT layout is a Fuchsia device layout.
pub fn is_fuchsia_gpt(disks: &[EfiGblDisk]) -> Result<()> {
    let partitions: &[&[&str]] = &[
        &["zircon_a", "zircon-a"],
        &["zircon_b", "zircon-b"],
        &["zircon_r", "zircon-r"],
        &["vbmeta_a"],
        &["vbmeta_b"],
        &["vbmeta_r"],
        &["misc", "durable_boot"],
    ];
    if !partitions
        .iter()
        .all(|&partition| partition.iter().any(|v| check_part_unique(&disks[..], *v).is_ok()))
    {
        return Err(Error::NotFound.into());
    }

    Ok(())
}

/// Loads and verifies Fuchsia according to A/B/R.
///
/// On success, returns the kernel and zbi_item buffer.
pub fn efi_fuchsia_load(ops: &mut Ops) -> Result<(ImageBuffer<'static>, ImageBuffer<'static>)> {
    gbl_println!(ops, "Try booting as Fuchsia/Zircon");
    // Checks whether to enter fastboot mode.
    if zircon_check_enter_fastboot(ops) {
        fastboot(ops, &mut [])?;
    }
    let (zbi_items_buffer, kernel_buffer, slot) = zircon_load_verify_abr(ops)?;
    gbl_println!(ops, "Booting from slot: {}", zircon_part_name(Some(slot)));
    Ok((kernel_buffer, zbi_items_buffer))
}

/// Exits boot services and boots loaded fuchsia images.
pub fn efi_fuchsia_boot(
    _efi_entry: EfiEntry,
    mut _kernel_buffer: ImageBuffer,
    mut _zbi_items: ImageBuffer,
) -> Result<()> {
    let _zbi_items = _zbi_items.used_mut();
    #[cfg(target_arch = "aarch64")]
    {
        // Uses the unused buffer for `exit_boot_services` to store output memory map.
        // The map is not used for now. We currently rely on UEFI firmware to pass memory map via
        // an raw zbi blob in device tree. Long term we want to support adding from EFI memory maps
        // if none is provided.
        let item_size = zbi::ZbiContainer::parse(&mut _zbi_items[..])?.container_size()?;
        let (_, remains) = _zbi_items.split_at_mut(item_size);
        let _ = efi::exit_boot_services(_efi_entry, remains).unwrap();
        // SAFETY: The kernel has passed libavb verification or device is unlocked, in which case we
        // assume the caller has addressed all safety and security concerns.
        unsafe { boot::aarch64::jump_zircon_el2_or_lower(_kernel_buffer.used_mut(), _zbi_items) };
    }

    #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
    {
        const BUFFER_SIZE: usize = 32 * 1024 / 2;
        let mut mem_map_buf = [0u8; BUFFER_SIZE];
        let mut zbi_items = zbi::ZbiContainer::parse(&mut _zbi_items[..])?;
        let efi_memory_attribute_table =
            get_efi_mem_attr(&_efi_entry).ok_or(Error::InvalidInput)?;

        // `exit_boot_service` returnes EFI memory map that is used to derive and append MEM_CONFIG
        // items.
        let efi_memory_map = efi::exit_boot_services(_efi_entry, &mut mem_map_buf).unwrap();

        add_memory_items(&efi_memory_map, &efi_memory_attribute_table, &mut zbi_items)?;

        // SAFETY: The kernel has passed libavb verification or device is unlocked, in which case we
        // assume the caller has addressed all safety and security concerns.
        unsafe { boot::x86::zbi_boot(_kernel_buffer.used_mut(), _zbi_items) };
    }

    #[cfg(target_arch = "riscv64")]
    {
        unimplemented!();
    }
}

// This function must not use allocation
#[allow(unused)]
fn add_memory_items<B>(
    efi_memory_map: &EfiMemoryMap,
    efi_memory_attribute_table: &EfiMemoryAttributesTable,
    zbi_items: &mut ZbiContainer<B>,
) -> Result<()>
where
    B: SplitByteSliceMut + PartialEq,
{
    generate_efi_memory_attributes_table_item(
        efi_memory_map,
        efi_memory_attribute_table,
        zbi_items,
    )?;

    generate_mem_config_item(efi_memory_map, zbi_items)?;

    Ok(())
}

fn generate_efi_memory_attributes_table_item<'b, B>(
    efi_memory_map: &EfiMemoryMap<'b>,
    efi_memory_attribute_table: &EfiMemoryAttributesTable,
    zbi_items: &mut ZbiContainer<B>,
) -> Result<()>
where
    B: SplitByteSliceMut + PartialEq,
{
    let payload = zbi_items.get_next_payload()?;
    let provided_payload_size = payload.len();
    let (mut header, mut tail) =
        Ref::<&mut [u8], EfiMemoryAttributesTableHeader>::new_from_prefix(payload)
            .ok_or(Error::BadBufferSize)?;

    for efi_memory_desc in efi_memory_map.into_iter() {
        if efi_memory_desc.attributes & EFI_MEMORY_ATTRIBUTE_EMA_RUNTIME == 0 {
            continue;
        }

        let mut base = efi_memory_desc.physical_start;
        let mut size: u64 = (SafeNum::from(efi_memory_desc.number_of_pages) * PAGE_SIZE)
            .try_into()
            .map_err(Error::from)?;

        // This EMAT entry is either a sub-region or a full copy of the memory map region, per
        // EFI 2.10 4.6.4: "Additionally, every memory region described by a Descriptor in
        // EFI_MEMORY_ATTRIBUTES_TABLE must be a sub-region of, or equal to, a descriptor in the
        // table produced by GetMemoryMap()."
        //
        // This means that we do not have to consider the case where the EMAT entry only overlaps
        // the end of the memory map entry.
        //
        // EMAT items are ordered by physical address, so once we go past |base| we can quit the
        // loop.
        for emat_item in efi_memory_attribute_table
            .into_iter()
            .skip_while(move |item| item.physical_start < base)
            .take_while(move |item| item.physical_start < base + size)
        {
            if emat_item.physical_start > base {
                // Create a region for [base ... emat_item->PhysicalStart), because that region is
                // not covered by the EMAT.
                let mut generated_item;
                (generated_item, tail) = Ref::<_, EfiMemoryDescriptor>::new_from_prefix(tail)
                    .ok_or(UnificationError(BufferTooSmall(Some(
                        size_of::<EfiMemoryDescriptor>(),
                    ))))?;

                generated_item.physical_start = base;
                generated_item.number_of_pages = (emat_item.physical_start - base) / PAGE_SIZE;
                generated_item.virtual_start = 0;
                generated_item.attributes = EFI_MEMORY_ATTRIBUTE_EMA_RUNTIME;
                generated_item.memory_type = emat_item.memory_type;

                // Adjust base and size forward.
                size -= emat_item.physical_start - base;
                base = emat_item.physical_start;
            } else {
                // emat_item.physical_start == base
                // Create a region for [base ... emat_item->NumberOfPages * PAGE_SIZE)
                let mut generated_item;
                (generated_item, tail) = Ref::<_, EfiMemoryDescriptor>::new_from_prefix(tail)
                    .ok_or(UnificationError(BufferTooSmall(Some(
                        size_of::<EfiMemoryDescriptor>(),
                    ))))?;
                *generated_item = *emat_item;

                // Adjust base and size forward.
                base += emat_item.number_of_pages * PAGE_SIZE;
                size -= emat_item.number_of_pages * PAGE_SIZE;
            }
        }

        if size != 0 {
            let mut generated_item;
            (generated_item, tail) = Ref::<_, EfiMemoryDescriptor>::new_from_prefix(tail)
                .ok_or(UnificationError(BufferTooSmall(Some(size_of::<EfiMemoryDescriptor>()))))?;

            generated_item.physical_start = base;
            generated_item.number_of_pages = size / PAGE_SIZE;
            generated_item.virtual_start = 0;
            generated_item.attributes = EFI_MEMORY_ATTRIBUTE_EMA_RUNTIME;
            generated_item.memory_type = efi_memory_desc.memory_type;
        }
    }

    let used_payload = provided_payload_size - tail.len();
    header.descriptor_size = size_of::<EfiMemoryDescriptor>().try_into().map_err(Error::from)?;
    header.number_of_entries =
        (used_payload / size_of::<EfiMemoryDescriptor>()).try_into().unwrap();
    header.reserved = 0;
    header.version = 1;

    zbi_items.create_entry(
        ZbiType::EfiMemoryAttributesTable,
        0,
        ZbiFlags::default(),
        used_payload,
    )?;

    Ok(())
}

fn generate_mem_config_item<'b, B>(
    efi_memory_map: &EfiMemoryMap<'b>,
    zbi_items: &mut ZbiContainer<B>,
) -> Result<()>
where
    B: SplitByteSliceMut + PartialEq,
{
    let mut tail = zbi_items.get_next_payload()?;
    let provided_payload_size = tail.len();

    for efi_desc in efi_memory_map.into_iter() {
        let mut zbi_mem_range: Ref<&mut [u8], zbi_mem_range_t>;
        (zbi_mem_range, tail) = Ref::new_from_prefix(tail)
            .ok_or(UnificationError(BufferTooSmall(Some(size_of::<zbi_mem_range_t>()))))?;
        zbi_mem_range.paddr = efi_desc.physical_start;
        zbi_mem_range.length = efi_desc.number_of_pages * PAGE_SIZE;
        zbi_mem_range.type_ = efi_to_zbi_mem_range_type(efi_desc.memory_type);
        zbi_mem_range.reserved = 0;
    }

    let used_payload = provided_payload_size - tail.len();
    zbi_items.create_entry(ZbiType::MemConfig, 0, ZbiFlags::default(), used_payload)?;

    Ok(())
}
