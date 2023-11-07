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

use alloc::vec::Vec;
use core::ffi::CStr;
use core::fmt::Write;
use core::str::from_utf8;
use gbl_storage::BlockDevice;

use efi::defs::EfiSystemTable;
use efi::{initialize, BlockIoProtocol, LoadedImageProtocol};
use fdt::Fdt;

// For the `vec!` macro
#[macro_use]
extern crate alloc;

#[macro_use]
mod utils;
use utils::{get_device_path, get_efi_fdt, EfiGptDevice, MultiGptDevices, Result};

fn main(image_handle: *mut core::ffi::c_void, systab_ptr: *mut EfiSystemTable) -> Result<()> {
    // SAFETY: Called only once here upon EFI app entry.
    let entry = unsafe { initialize(image_handle, systab_ptr)? };

    efi_print!(entry, "\n\n****Rust EFI Application****\n\n");

    let bs = entry.system_table().boot_services();
    let loaded_image = bs.open_protocol::<LoadedImageProtocol>(entry.image_handle())?;
    efi_print!(entry, "Image path: {}\n", get_device_path(&entry, loaded_image.device_handle()?)?);

    efi_print!(entry, "Scanning block devices...\n");
    let block_dev_handles = bs.locate_handle_buffer_by_protocol::<BlockIoProtocol>()?;
    let mut gpt_devices = Vec::<EfiGptDevice>::new();
    for (i, handle) in block_dev_handles.handles().iter().enumerate() {
        efi_print!(entry, "-------------------\n");
        efi_print!(entry, "Block device #{}: {}\n", i, get_device_path(&entry, *handle)?);
        let mut gpt_dev = EfiGptDevice::new(bs.open_protocol::<BlockIoProtocol>(*handle)?)?;
        efi_print!(
            entry,
            "block size: {}, blocks: {}, alignment: {}\n",
            gpt_dev.block_device().block_size(),
            gpt_dev.block_device().num_blocks(),
            gpt_dev.block_device().alignment()
        );
        match gpt_dev.sync_gpt() {
            Ok(()) => {
                efi_print!(entry, "GPT found!\n");
                for e in gpt_dev.gpt()?.entries()? {
                    efi_print!(entry, "{}\n", e);
                }
                gpt_devices.push(gpt_dev);
            }
            Err(err) => {
                efi_print!(entry, "No GPT on device. {:?}\n", err);
            }
        };
    }

    // Following is example code for testing library linkage. They'll be removed and replaced with
    // full GBL boot flow as development goes.

    let mut multi_gpt_dev = MultiGptDevices::new(gpt_devices);
    match multi_gpt_dev.partition_size("bootconfig") {
        Ok(sz) => {
            efi_print!(entry, "Has device-specific bootconfig: {} bytes\n", sz);
            let mut bootconfig = vec![0u8; sz];
            multi_gpt_dev.read_gpt_partition("bootconfig", 0, &mut bootconfig[..])?;
            efi_print!(
                entry,
                "{}\n",
                CStr::from_bytes_until_nul(&mut bootconfig[..]).unwrap().to_str().unwrap()
            );
        }
        _ => {}
    };

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
