// Copyright 2023, The Android Open Source Project
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

use crate::{fastboot::efi_gbl_fastboot_entry, ops::Ops};
use efi::{efi_println, EfiEntry};
use libgbl::{
    android_boot::{android_main, BootBuffer},
    gbl_println, GblOps, Result,
};

/// Android bootloader main entry (before booting).
///
/// On success, returns a tuple of slices (ramdisk, fdt, kernel, remains).
pub fn efi_android_load<'a>(
    ops: &mut Ops,
    load: BootBuffer<'a>,
) -> Result<(&'a [u8], &'a [u8], &'a [u8], &'a mut [u8])> {
    let entry = ops.efi_entry;
    gbl_println!(ops, "Try booting as Android");
    Ok(android_main(ops, load, |fb| efi_gbl_fastboot_entry(entry, fb))?)
}

/// Boots loaded android images.
#[cfg_attr(feature = "efi_boot_stub", allow(unused_variables))]
pub fn efi_android_boot(
    entry: EfiEntry,
    kernel: &'static [u8],
    ramdisk: &'static [u8],
    fdt: &'static [u8],
    remains: &'static mut [u8],
) -> Result<!> {
    efi_println!(entry, "");
    efi_println!(
        entry,
        "Booting kernel @ {:#x}, ramdisk @ {:#x}, fdt @ {:#x}",
        kernel.as_ptr() as usize,
        ramdisk.as_ptr() as usize,
        fdt.as_ptr() as usize
    );

    #[cfg(all(target_arch = "aarch64", feature = "gbl_tracing"))]
    {
        // TODO(b/473552136): Temporary test for tracing functionality.
        unsafe extern "C" {
            safe fn get_peak_stack() -> usize;
        }
        efi_println!(entry, "max stack used: {} bytes", get_peak_stack());
    }

    #[cfg(all(target_arch = "aarch64", not(feature = "efi_boot_stub")))]
    {
        let _ = efi::exit_boot_services(entry, remains)?;
        // SAFETY: We currently target at Cuttlefish emulator where images are provided valid.
        unsafe { boot::aarch64::jump_linux_el2_or_lower(kernel, ramdisk, fdt) };
    }

    #[cfg(all(target_arch = "x86_64", not(feature = "efi_boot_stub")))]
    {
        use fdt::Fdt;
        use liberror::Error;
        use libgbl::android_boot::device_tree::PROP_BOOTARGS;
        use safemath::SafeNum;

        const EFI_PAGE_SIZE: u64 = efi_types::EFI_PAGE_SIZE as u64;

        let fdt = Fdt::new(&fdt[..])?;
        let systab_addr = entry.system_table().as_ptr() as usize;

        // Back the EFI memory map handed to Linux with firmware-reserved memory.
        //
        // `remains` is bootloader-owned reclaimable RAM. It appears in the map as EfiLoaderData
        // and is therefore reported to Linux as usable E820, so the kernel reuses it for early
        // allocations before efi_init() parses the map. The map is corrupted by the time it is
        // read, and the fault lands before any console is registered. Pages typed
        // EfiACPIReclaimMemory map to E820 ACPI, which neither the kernel nor its decompressor
        // allocates from, so the map survives until it is consumed. The Linux EFI stub uses
        // the same type. Allocate before the final
        // GetMemoryMap() so the map it returns already describes this buffer as reserved.
        // Query the required capacity instead of sizing from a possibly compacted map.
        // Allocating the buffer changes the map, so add one page of headroom.
        let _ = remains;

        let mmap_buffer = {
            const MMAP_HEADROOM_PAGES: u64 = 1;
            let bs = entry.system_table().boot_services();
            let required = SafeNum::from(bs.memory_map_size()?);
            let pages = (required + (EFI_PAGE_SIZE - 1)) / EFI_PAGE_SIZE + MMAP_HEADROOM_PAGES;
            let mmap_pages = usize::try_from(pages).map_err(Error::ArithmeticOverflow)?;
            let len = usize::try_from(pages * EFI_PAGE_SIZE).map_err(Error::ArithmeticOverflow)?;
            if isize::try_from(len).is_err() {
                return Err(Error::InvalidInput.into());
            }

            let ptr = bs.allocate_pages(
                efi_types::EFI_MEMORY_TYPE_ACPIRECLAIM_MEMORY,
                efi::AllocationAddress::Any,
                mmap_pages,
            )? as *mut u8;
            // A conforming AllocatePages() cannot return null on success, but nothing in the
            // type system says so and a null slice would be undefined behavior.
            if ptr.is_null() {
                return Err(Error::InvalidState.into());
            }
            // SAFETY:
            // * `allocate_pages` returned `mmap_pages` contiguous pages owned by this code.
            // * `len` is those pages in bytes, computed with checked arithmetic and checked
            //   above to fit in `isize`.
            // * `write_bytes` initializes every byte before the slice is created.
            // * Nothing else aliases the allocation until the kernel consumes the map.
            unsafe {
                core::ptr::write_bytes(ptr, 0, len);
                core::slice::from_raw_parts_mut(ptr, len)
            }
        };
        let efi_mmap = efi::exit_boot_services(entry, mmap_buffer)?;
        // SAFETY: We currently target at Cuttlefish emulator where images are provided valid.
        unsafe {
            boot::x86::boot_linux_bzimage(
                kernel,
                ramdisk,
                fdt.get_property("chosen", PROP_BOOTARGS).unwrap(),
                |e820_entries, efi_info| {
                    // "EL64" Signature tells the kernel it's a 64-bit EFI boot
                    efi_info.efi_loader_signature = 0x34364c45;
                    // Pass the physical address of the UEFI System Table
                    efi_info.efi_systab = (systab_addr & 0xFFFFFFFF).try_into().unwrap();
                    efi_info.efi_systab_hi = (systab_addr >> 32).try_into().unwrap();

                    // Get the memory map.
                    let mmap_ptr = efi_mmap.buffer().as_ptr() as usize;

                    // Pass the Memory Map pointers and metadata
                    efi_info.efi_memdesc_version =
                        efi_mmap.descriptor_version().try_into().unwrap();
                    efi_info.efi_memdesc_size = efi_mmap.descriptor_size().try_into().unwrap();
                    efi_info.efi_memmap_size = efi_mmap.buffer().len().try_into().unwrap();
                    efi_info.efi_memmap = (mmap_ptr & 0xFFFFFFFF).try_into().unwrap();
                    efi_info.efi_memmap_hi = (mmap_ptr >> 32).try_into().unwrap();

                    let mut idx = 0;
                    for mem in efi_mmap.into_iter() {
                        let cur_type = crate::utils::efi_to_e820_mem_type(mem.memory_type);
                        // Coalesce adjacent memory regions of similar type.
                        // We intentionally check only against the previous entry (`idx - 1`) based on
                        // the expectation that the EFI memory map is mostly sorted. This strikes a
                        // balance between time efficiency and compaction.
                        if idx != 0
                            && (e820_entries[idx - 1].type_ == cur_type)
                            && ((e820_entries[idx - 1].addr + e820_entries[idx - 1].size)
                                == mem.physical_start)
                        {
                            e820_entries[idx - 1].size += mem.number_of_pages * 4096;
                        } else {
                            if idx >= e820_entries.len() {
                                return Err(Error::MemoryMapCallbackError(-1));
                            }

                            e820_entries[idx] = boot::x86::e820entry {
                                addr: mem.physical_start,
                                size: mem.number_of_pages * EFI_PAGE_SIZE,
                                type_: cur_type,
                            };
                            idx += 1;
                        }
                    }

                    // Sort the memory map entries by address as required by linux boot protocol.
                    e820_entries[0..idx].sort_unstable_by_key(|e820_entry| e820_entry.addr);

                    Ok(idx.try_into().unwrap())
                },
                0x9_0000,
            )?;
        }
    }

    #[cfg(target_arch = "riscv64")]
    {
        let boot_hart_id = entry
            .system_table()
            .boot_services()
            .find_first_and_open::<efi::protocol::riscv::RiscvBootProtocol>()?
            .get_boot_hartid()?;
        efi_println!(entry, "riscv boot_hart_id: {}", boot_hart_id);
        let _ = efi::exit_boot_services(entry, remains)?;
        // SAFETY: We currently target at Cuttlefish emulator where images are provided valid.
        unsafe { boot::riscv64::jump_linux(kernel, boot_hart_id, fdt) };
    }

    #[cfg(feature = "efi_boot_stub")]
    {
        use libgbl::android_boot::device_tree::PROP_BOOTARGS;

        /// Maximum length of kernel command line in bytes, matching Linux `COMMAND_LINE_SIZE`.
        const COMMAND_LINE_SIZE: usize = 2048;

        efi_println!(entry, "Loading kernel PE/COFF image (EFI boot stub)");

        if !is_efi_boot_stub(kernel) {
            efi_println!(entry, "Unsupported PE/COFF format");
            return Err(liberror::Error::Unsupported.into());
        }

        let bs = entry.system_table().boot_services();

        // SAFETY: `kernel` points to valid PE/COFF kernel image bytes.
        let mut loaded_image = unsafe { bs.load_image(kernel)? };

        // Convert FDT bootargs to UTF-16 and install into LoadOptions.
        let options: arrayvec::ArrayVec<u16, COMMAND_LINE_SIZE> =
            if let Ok(bootargs) = fdt::Fdt::new(fdt)?.get_property("chosen", PROP_BOOTARGS) {
                bootargs
                    .iter()
                    .copied()
                    .take_while(|&b| b != 0)
                    .map(|b| b as u16)
                    .chain(core::iter::once(0))
                    .take(COMMAND_LINE_SIZE)
                    .collect()
            } else {
                arrayvec::ArrayVec::new()
            };

        if !options.is_empty() {
            // SAFETY: `options` is stack-allocated and the current stack frame outlives
            // `loaded_image.start()`.
            unsafe {
                loaded_image.protocol.set_load_options(
                    options.as_ptr() as *const _,
                    (options.len() * core::mem::size_of::<u16>()) as u32,
                );
            }
        }

        #[cfg(target_arch = "aarch64")]
        {
            // SAFETY: The boot app should either succeed by never returning, or fail by triggering
            // an infinite loop or system reset, so `fdt` with 'static lifetime is never
            // deallocated during EFI execution.
            unsafe {
                bs.install_configuration_table(&efi::EFI_DTB_TABLE_GUID, fdt.as_ptr() as *mut _)?;
            }

            // Install the fixed placement protocol to disable physical KASLR (does NOT disable
            // virtual KASLR which is controlled via kaslr-seed FDT node).
            // TODO: Do we really want this? Do we want the firmware to handle KASLR or rely on the
            // kernel to relocate itself?
            bs.install_null_protocol_interface(
                &mut loaded_image.image_handle,
                &efi::LINUX_EFI_LOADED_IMAGE_FIXED_GUID,
            )?;
        }

        #[cfg(target_arch = "x86_64")]
        {
            use efi::protocol::{
                device_path::InitrdDevicePathProtocol,
                load_file2::{InitrdLoadFile2Protocol, LoadFile2Protocol},
            };
            use spin::{Mutex, MutexGuard};

            let initrd_load_file2 = {
                static INITRD_LOAD_FILE2: Mutex<Option<InitrdLoadFile2Protocol>> = Mutex::new(None);
                let lf2 = MutexGuard::leak(INITRD_LOAD_FILE2.lock());
                *lf2 = Some(InitrdLoadFile2Protocol(ramdisk));
                lf2.as_mut().unwrap()
            };
            let initrd_device_path = {
                static INITRD_DEVICE_PATH: Mutex<InitrdDevicePathProtocol> =
                    Mutex::new(InitrdDevicePathProtocol);
                MutexGuard::leak(INITRD_DEVICE_PATH.lock())
            };

            let mut initrd_handle: efi_types::EfiHandle = core::ptr::null_mut();
            bs.install_protocol_from_rust::<LoadFile2Protocol, _>(
                Some(&mut initrd_handle),
                initrd_load_file2,
            )?;
            bs.install_protocol_from_rust::<InitrdDevicePathProtocol, _>(
                Some(&mut initrd_handle),
                initrd_device_path,
            )?;

            efi_println!(entry, "Installed initrd LoadFile2 protocol and handle");
        }

        efi_println!(entry, "Starting kernel EFI boot stub");
        let res = loaded_image.start();
        panic!("Failed to start kernel boot stub or kernel boot stub returned with error: {res:?}");
    }
}

/// Returns true if the kernel is compiled as a PE/COFF EFI binary (`CONFIG_EFI_STUB=y`).
#[cfg(feature = "efi_boot_stub")]
fn is_efi_boot_stub(kernel: &[u8]) -> bool {
    if kernel.len() < 0x40 || &kernel[0..2] != b"MZ" {
        return false;
    }
    let pe_offset = u32::from_le_bytes(kernel[0x3c..0x40].try_into().unwrap()) as usize;
    kernel.get(pe_offset..).unwrap_or_default().starts_with(b"PE\0\0")
}
