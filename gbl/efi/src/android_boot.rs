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

use crate::{efi_blocks::find_block_devices, fastboot::fastboot, ops::Ops};
use efi::{exit_boot_services, EfiEntry};
use libgbl::{fastboot::LoadedImageInfo, gbl_print, gbl_println, GblOps, Os, Result};

// The following implements a demo for booting Android from disk. It can be run from
// Cuttlefish by adding `--android_efi_loader=<path of this EFI binary>` to the command line.
//
// A number of simplifications are made (see `android_load::load_android_simple()`):
//
//   * No A/B slot switching is performed. It always boot from *_a slot.
//   * No AVB is performed.
//   * No dynamic partitions.
//   * Only support V3/V4 image and Android 13+ (generic ramdisk from the "init_boot" partition)
//
// The missing pieces above are currently under development as part of the full end-to-end boot
// flow in libgbl, which will eventually replace this demo. The demo is currently used as an
// end-to-end test for libraries developed so far.
pub fn android_boot_demo(entry: EfiEntry) -> Result<()> {
    let blks = find_block_devices(&entry)?;
    let mut ops = Ops::new(&entry, &blks[..], Some(Os::Android));
    // Allocate buffer for load.
    let mut load_buffer = vec![0u8; 256 * 1024 * 1024]; // 256MB

    let fb_res = match ops.should_stop_in_fastboot() {
        Ok(true) => fastboot(&mut ops, &mut load_buffer)?,
        Err(e) => {
            gbl_println!(ops, "Warning: error while checking fastboot trigger ({:?})", e);
            gbl_println!(ops, "Ignoring error and continuing with normal boot");
            Default::default()
        }
        _ => Default::default(),
    };

    gbl_println!(ops, "Try booting as Android");

    let (ramdisk, fdt, kernel, remains) = match fb_res.loaded_image_info {
        Some(LoadedImageInfo::Android { .. }) => {
            fb_res.split_loaded_android(&mut load_buffer).unwrap()
        }
        _ => libgbl::android_boot::android_main(&mut ops, &mut load_buffer[..])?,
    };

    gbl_println!(ops, "");
    gbl_println!(
        ops,
        "Booting kernel @ {:#x}, ramdisk @ {:#x}, fdt @ {:#x}",
        kernel.as_ptr() as usize,
        ramdisk.as_ptr() as usize,
        fdt.as_ptr() as usize
    );
    gbl_println!(ops, "");

    #[cfg(target_arch = "aarch64")]
    {
        drop(blks); // Drop `blks` to release the borrow on `entry`.
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
        drop(blks); // Drop `blks` to release the borrow on `entry`.
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
        gbl_println!(ops, "riscv boot_hart_id: {}", boot_hart_id);
        drop(blks); // Drop `blks` to release the borrow on `entry`.
        let _ = exit_boot_services(entry, remains)?;
        // SAFETY: We currently target at Cuttlefish emulator where images are provided valid.
        unsafe { boot::riscv64::jump_linux(kernel, boot_hart_id, fdt) };
    }
}
