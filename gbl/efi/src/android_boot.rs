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

use crate::{
    fastboot::{with_fastboot_channels, VecPinFut},
    ops::Ops,
    utils::{get_platform_buffer_info, BufferInfo},
};
use alloc::{boxed::Box, vec::Vec};
use core::{fmt::Write, str::from_utf8};
use efi::{efi_print, efi_println, exit_boot_services, EfiEntry};
use efi_types::{GBL_IMAGE_TYPE_FASTBOOT, GBL_IMAGE_TYPE_OS_LOAD};
use gbl_async::poll;
use libgbl::{android_boot::android_main, gbl_print, gbl_println, GblOps, Result};

const SZ_MB: usize = 1024 * 1024;

/// Android bootloader main entry (before booting).
///
/// On success, returns a tuple of slices (ramdisk, fdt, kernel, remains).
pub fn efi_android_load(
    ops: &mut Ops,
) -> Result<(&'static mut [u8], &'static mut [u8], &'static mut [u8], &'static mut [u8])> {
    let entry = ops.efi_entry;
    // Prepares the OS load buffer.
    let img_type_os_load = from_utf8(GBL_IMAGE_TYPE_OS_LOAD).unwrap();
    let load_buffer = match get_platform_buffer_info(&entry, img_type_os_load, 256 * SZ_MB) {
        BufferInfo::Static(v) => v,
        BufferInfo::Alloc(sz) => {
            let alloc = vec![0u8; sz];
            gbl_println!(ops, "Allocated {:#x} bytes for OS load buffer.", alloc.len());
            alloc.leak()
        }
    };

    // Checks if we have a reserved buffer for fastboot
    let img_type_fastboot = from_utf8(GBL_IMAGE_TYPE_FASTBOOT).unwrap();
    let mut fastboot_buffer_info = None;

    gbl_println!(ops, "Try booting as Android");

    Ok(android_main(ops, load_buffer.as_mut(), |fb| {
        // Note: `get_or_insert_with` lazily evaluates closure (only when insert is necessary).
        let buffer = fastboot_buffer_info.get_or_insert_with(|| {
            get_platform_buffer_info(&entry, img_type_fastboot, 512 * SZ_MB)
        });
        let mut alloc;
        let buffer = match buffer {
            BufferInfo::Static(v) => &mut v[..],
            BufferInfo::Alloc(sz) => {
                alloc = vec![0u8; *sz];
                efi_println!(entry, "Allocated {:#x} bytes for fastboot buffer.", alloc.len());
                &mut alloc
            }
        };
        // TODO(b/383620444): Investigate letting GblOps return fastboot channels.
        with_fastboot_channels(&entry, |local, usb, tcp| {
            // We currently only consider 1 parallell flash + 1 parallel download.
            // This can be made configurable if necessary.
            const GBL_FB_N: usize = 2;
            let mut bufs = Vec::from_iter(buffer.chunks_exact_mut(buffer.len() / GBL_FB_N));
            let bufs = &(&mut bufs[..]).into();
            let mut fut = Box::pin(fb.run(bufs, VecPinFut::default(), local, usb, tcp));
            while poll(&mut fut).is_none() {}
        })
    })?)
}

/// Exits boot services and boots loaded android images.
pub fn efi_android_boot(
    entry: EfiEntry,
    kernel: &[u8],
    ramdisk: &[u8],
    fdt: &[u8],
    remains: &mut [u8],
) -> Result<()> {
    efi_println!(entry, "");
    efi_println!(
        entry,
        "Booting kernel @ {:#x}, ramdisk @ {:#x}, fdt @ {:#x}",
        kernel.as_ptr() as usize,
        ramdisk.as_ptr() as usize,
        fdt.as_ptr() as usize
    );
    efi_println!(entry, "");

    #[cfg(target_arch = "aarch64")]
    {
        let _ = exit_boot_services(entry, remains)?;
        // SAFETY: We currently targets at Cuttlefish emulator where images are provided valid.
        unsafe { boot::aarch64::jump_linux_el2_or_lower(kernel, ramdisk, fdt) };
    }

    #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
    {
        use fdt::Fdt;
        use liberror::Error;
        use libgbl::android_boot::BOOTARGS_PROP;

        let fdt = Fdt::new(&fdt[..])?;
        let efi_mmap = exit_boot_services(entry, remains)?;
        // SAFETY: We currently target at Cuttlefish emulator where images are provided valid.
        unsafe {
            boot::x86::boot_linux_bzimage(
                kernel,
                ramdisk,
                fdt.get_property("chosen", BOOTARGS_PROP).unwrap(),
                |e820_entries| {
                    // Convert EFI memory type to e820 memory type.
                    if efi_mmap.len() > e820_entries.len() {
                        return Err(Error::MemoryMapCallbackError(-1));
                    }
                    for (idx, mem) in efi_mmap.into_iter().enumerate() {
                        e820_entries[idx] = boot::x86::e820entry {
                            addr: mem.physical_start,
                            size: mem.number_of_pages * 4096,
                            type_: crate::utils::efi_to_e820_mem_type(mem.memory_type),
                        };
                    }
                    Ok(efi_mmap.len().try_into().unwrap())
                },
                0x9_0000,
            )?;
        }
        unreachable!();
    }

    #[cfg(target_arch = "riscv64")]
    {
        let boot_hart_id = entry
            .system_table()
            .boot_services()
            .find_first_and_open::<efi::protocol::riscv::RiscvBootProtocol>()?
            .get_boot_hartid()?;
        efi_println!(entry, "riscv boot_hart_id: {}", boot_hart_id);
        let _ = exit_boot_services(entry, remains)?;
        // SAFETY: We currently target at Cuttlefish emulator where images are provided valid.
        unsafe { boot::riscv64::jump_linux(kernel, boot_hart_id, fdt) };
    }
}
