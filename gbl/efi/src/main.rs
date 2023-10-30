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

#![no_std]
#![no_main]

#[cfg(target_arch = "riscv64")]
mod riscv64;

use core::ffi::CStr;
use core::fmt::Write;
use core::str::from_utf8;
use gbl_storage::{required_scratch_size, BlockDevice, Gpt};

use efi::defs::EfiSystemTable;
use efi::{initialize, BlockIoProtocol, LoadedImageProtocol};
use fdt::Fdt;

// For the `vec!` macro
#[macro_use]
extern crate alloc;

#[macro_use]
mod utils;
use utils::{get_device_path, get_efi_fdt, EfiBlockDevice, Result};

fn main(image_handle: *mut core::ffi::c_void, systab_ptr: *mut EfiSystemTable) -> Result<()> {
    let entry = initialize(image_handle, systab_ptr);

    efi_print!(entry, "\n\n****Rust EFI Application****\n\n");

    let bs = entry.system_table().boot_services();
    let loaded_image = bs.open_protocol::<LoadedImageProtocol>(entry.image_handle())?;
    efi_print!(entry, "Image path: {}\n", get_device_path(&entry, loaded_image.device_handle()?)?);

    let mut gpt_buf = vec![0u8; Gpt::required_buffer_size(128)?];
    let mut gpt = Gpt::new_from_buffer(128, &mut gpt_buf[..])?;

    efi_print!(entry, "Scanning block devices...\n");
    let block_dev_handles = bs.locate_handle_buffer_by_protocol::<BlockIoProtocol>()?;
    for (i, handle) in block_dev_handles.handles().iter().enumerate() {
        efi_print!(entry, "-------------------\n");
        efi_print!(entry, "Block device #{}: {}\n", i, get_device_path(&entry, *handle)?);

        let mut blk_dev = EfiBlockDevice(bs.open_protocol::<BlockIoProtocol>(*handle)?);
        let mut scratch = vec![0u8; required_scratch_size(&mut blk_dev)?];
        efi_print!(
            entry,
            "block size: {}, blocks: {}, alignment: {}\n",
            blk_dev.block_size(),
            blk_dev.num_blocks(),
            blk_dev.alignment()
        );
        match blk_dev.sync_gpt(&mut gpt, &mut scratch) {
            Ok(()) => {
                efi_print!(entry, "GPT found!\n");
                for e in gpt.entries()? {
                    efi_print!(entry, "{}\n", e);
                }
            }
            Err(e) => {
                efi_print!(entry, "No GPT on device. {}\n", e);
            }
        }
    }

    // Check if we have a device tree.
    match get_efi_fdt(&entry) {
        Some((_, bytes)) => {
            let fdt = Fdt::new(bytes)?;
            efi_print!(entry, "Device tree found\n");
            let print_property = |node: &str, name: &CStr| -> Result<()> {
                efi_print!(
                    entry,
                    "{}:{} = {}\n",
                    node,
                    name.to_str().unwrap(),
                    from_utf8(fdt.get_property(node, name).unwrap_or("NA".as_bytes())).unwrap()
                );
                Ok(())
            };
            print_property("/", CStr::from_bytes_with_nul(b"compatible\0").unwrap())?;
            print_property("/chosen", CStr::from_bytes_with_nul(b"u-boot,version\0").unwrap())?;
            print_property("/chosen", CStr::from_bytes_with_nul(b"bootargs\0").unwrap())?;
        }
        _ => {}
    }
    Ok(())
}

#[no_mangle]
pub extern "C" fn efi_main(image_handle: *mut core::ffi::c_void, systab_ptr: *mut EfiSystemTable) {
    main(image_handle, systab_ptr).unwrap();
    loop {}
}

#[no_mangle]
pub extern "C" fn __chkstk() {}
