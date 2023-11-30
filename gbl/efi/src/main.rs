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

// This EFI application implements a demo for booting Android from disk. It can be run from
// Cuttlefish by adding `--android_efi_loader=<path of this EFI binary>` to the command line.
//
// A number of simplifications are made (see `android_load::load_android_simple()`):
//
//   * No A/B slot switching is performed. It always boot from *_a slot.
//   * No AVB is performed. Thus boot mode is recovery only.
//   * No dynamic partitions.
//   * Only support V3/V4 image and Android 13+ (generic ramdisk from the "init_boot" partition)
//
// The missing pieces above are currently under development as part of the full end-to-end boot
// flow in libgbl, which will eventually replace this demo. The demo is currently used as an
// end-to-end test for libraries developed so far.

#![no_std]
#![no_main]

// For the `vec!` macro
#[macro_use]
extern crate alloc;
use core::fmt::Write;

use efi::defs::EfiSystemTable;
use efi::{exit_boot_services, initialize};

#[macro_use]
mod utils;
use utils::{loaded_image_path, Result};

#[cfg(target_arch = "riscv64")]
mod riscv64;

mod android_load;
use android_load::load_android_simple;

fn main(image_handle: *mut core::ffi::c_void, systab_ptr: *mut EfiSystemTable) -> Result<()> {
    // SAFETY: Called only once here upon EFI app entry.
    let entry = unsafe { initialize(image_handle, systab_ptr)? };

    efi_print!(entry, "\n\n****Rust EFI Application****\n\n");
    efi_print!(entry, "Image path: {}\n", loaded_image_path(&entry)?);

    // Allocate buffer for load.
    let mut load_buffer = vec![0u8; 128 * 1024 * 1024]; // 128MB

    let (kernel, ramdisk, fdt, remains) = load_android_simple(&entry, &mut load_buffer[..])?;

    efi_print!(
        &entry,
        "\nBooting kernel @ {:#x}, ramdisk @ {:#x}, fdt @ {:#x}\n\n",
        kernel.as_ptr() as usize,
        ramdisk.as_ptr() as usize,
        fdt.as_ptr() as usize
    );

    #[cfg(target_arch = "aarch64")]
    {
        let _ = exit_boot_services(entry, remains)?;
        // SAFETY: We currently targets at Cuttlefish emulator where images are provided valid.
        unsafe { boot::aarch64::jump_linux_el2_or_lower(kernel, fdt) };
    }

    #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
    {
        let fdt = fdt::Fdt::new(&fdt[..])?;
        let efi_mmap = exit_boot_services(entry, remains)?;
        // SAFETY: We currently targets at Cuttlefish emulator where images are provided valid.
        unsafe {
            boot::x86::boot_linux_bzimage(
                kernel,
                ramdisk,
                fdt.get_property(
                    "chosen",
                    core::ffi::CStr::from_bytes_with_nul(b"bootargs\0").unwrap(),
                )
                .unwrap(),
                |e820_entries| {
                    // Convert EFI memorty type to e820 memory type.
                    if efi_mmap.len() > e820_entries.len() {
                        return Err(boot::BootError::E820MemoryMapCallbackError(-1));
                    }
                    for (idx, mem) in efi_mmap.into_iter().enumerate() {
                        e820_entries[idx] = boot::x86::e820entry {
                            addr: mem.physical_start,
                            size: mem.number_of_pages * 4096,
                            type_: utils::efi_to_e820_mem_type(mem.memory_type),
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
            .find_first_and_open::<efi::RiscvBootProtocol>()?
            .get_boot_hartid()?;
        efi_print!(entry, "riscv boot_hart_id: {}\n", boot_hart_id);
        let _ = exit_boot_services(entry, remains)?;
        // SAFETY: We currently targets at Cuttlefish emulator where images are provided valid.
        unsafe { boot::riscv64::jump_linux(kernel, boot_hart_id, fdt) };
    }
}

#[no_mangle]
pub extern "C" fn efi_main(image_handle: *mut core::ffi::c_void, systab_ptr: *mut EfiSystemTable) {
    main(image_handle, systab_ptr).unwrap();
    loop {}
}
