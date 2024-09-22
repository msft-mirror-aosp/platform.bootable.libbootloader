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

use crate::{efi_blocks::find_block_devices, ops::Ops};
use core::fmt::Write;
use efi::{efi_print, efi_println, EfiEntry};
use liberror::Error;
use libgbl::{
    fuchsia_boot::{zircon_load_verify_abr, zircon_part_name},
    Result,
};

/// Check if the disk GPT layout is a Fuchsia device layout.
pub fn is_fuchsia_gpt(efi_entry: &EfiEntry) -> Result<()> {
    let mut gpt_devices = find_block_devices(&efi_entry)?;
    let partitions: [&[&str]; 8] = [
        &["zircon_a"],
        &["zircon_b"],
        &["zircon_r"],
        &["vbmeta_a"],
        &["vbmeta_b"],
        &["vbmeta_r"],
        &["fvm"],
        &["misc", "durable_boot"],
    ];
    if !partitions
        .iter()
        .all(|&partition| partition.iter().any(|v| gpt_devices.find_partition(*v).is_ok()))
    {
        return Err(Error::NotFound.into());
    }

    Ok(())
}

/// Loads, verifies and boots Fuchsia according to A/B/R.
pub fn fuchsia_boot_demo(efi_entry: EfiEntry) -> Result<()> {
    efi_println!(efi_entry, "Try booting as Fuchsia/Zircon");

    // Allocates buffer for load.
    let mut load_buffer = vec![0u8; 128 * 1024 * 1024]; // 128MB
    let (_zbi_items, _kernel, slot) = {
        let mut blks = find_block_devices(&efi_entry)?;
        let partitions = &blks.as_gbl_parts()?;
        let mut ops = Ops { efi_entry: &efi_entry, partitions };
        zircon_load_verify_abr(&mut ops, &mut load_buffer)?
    };
    efi_println!(efi_entry, "Booting from slot: {}", zircon_part_name(Some(slot)));

    #[cfg(target_arch = "aarch64")]
    {
        // Uses the unused buffer for `exit_boot_services` to store output memory map.
        // The map is not used for now. We currently rely on UEFI firmware to pass memory map via
        // an raw zbi blob in device tree. Long term we want to support adding from EFI memory maps
        // if none is provided.
        let item_size = zbi::ZbiContainer::parse(&mut _zbi_items[..])?.container_size();
        let (_, remains) = _zbi_items.split_at_mut(item_size);
        let _ = efi::exit_boot_services(efi_entry, remains).unwrap();
        // SAFETY: The kernel has passed libavb verification or device is unlocked, in which case we
        // assume the caller has addressed all safety and security concerns.
        unsafe { boot::aarch64::jump_zircon_el2_or_lower(_kernel, _zbi_items) };
    }

    #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
    {
        let items_size = zbi::ZbiContainer::parse(&mut _zbi_items[..])?.container_size();
        let (_, remains) = _zbi_items.split_at_mut(items_size);
        // `exit_boot_service` returnes EFI memory map that is used to derive and append MEM_CONFIG
        // items.
        let _ = efi::exit_boot_services(efi_entry, remains).unwrap();
        // SAFETY: The kernel has passed libavb verification or device is unlocked, in which case we
        // assume the caller has addressed all safety and security concerns.
        unsafe { boot::x86::zbi_boot(_kernel, _zbi_items) };
    }

    #[cfg(target_arch = "riscv64")]
    {
        unimplemented!();
    }
}
