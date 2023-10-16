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

use core::fmt::Write;
use gbl_storage::{required_scratch_size, BlockDevice, Gpt, StorageError};

use efi::defs::EfiSystemTable;
use efi::{
    initialize, BlockIoProtocol, DeviceHandle, DevicePathProtocol, DevicePathText,
    DevicePathToTextProtocol, EfiEntry, EfiError, LoadedImageProtocol, Protocol,
};

// For the `vec!` macro
#[macro_use]
extern crate alloc;

// Implement a block device on top of BlockIoProtocol
struct EfiBlockDevice<'a>(Protocol<'a, BlockIoProtocol>);

impl BlockDevice for EfiBlockDevice<'_> {
    fn block_size(&mut self) -> u64 {
        self.0.media().unwrap().block_size as u64
    }

    fn num_blocks(&mut self) -> u64 {
        (self.0.media().unwrap().last_block + 1) as u64
    }

    fn alignment(&mut self) -> u64 {
        core::cmp::max(1, self.0.media().unwrap().io_align as u64)
    }

    fn read_blocks(&mut self, blk_offset: u64, out: &mut [u8]) -> bool {
        self.0.read_blocks(blk_offset, out).is_ok()
    }

    fn write_blocks(&mut self, blk_offset: u64, data: &[u8]) -> bool {
        self.0.write_blocks(blk_offset, data).is_ok()
    }
}

/// A top level error type that consolidates errors from different libraries.
#[derive(Debug)]
enum GblEfiError {
    StorageError(gbl_storage::StorageError),
    EfiError(efi::EfiError),
}

impl From<StorageError> for GblEfiError {
    fn from(error: StorageError) -> GblEfiError {
        GblEfiError::StorageError(error)
    }
}

impl From<EfiError> for GblEfiError {
    fn from(error: EfiError) -> GblEfiError {
        GblEfiError::EfiError(error)
    }
}

/// Helper function to get the `DevicePathText` from a `DeviceHandle`.
fn get_device_path<'a>(
    entry: &'a EfiEntry,
    handle: DeviceHandle,
) -> Result<DevicePathText<'a>, GblEfiError> {
    let bs = entry.system_table().boot_services();
    let path = bs.open_protocol::<DevicePathProtocol>(handle)?;
    let path_to_text = bs.find_first_and_open::<DevicePathToTextProtocol>()?;
    Ok(path_to_text.convert_device_path_to_text(&path, false, false)?)
}

/// Helper macro for printing message via `EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL` in
/// `EFI_SYSTEM_TABLE.ConOut`.
#[macro_export]
macro_rules! efi_print {
    ( $efi_entry:expr, $( $x:expr ),* ) => {
        write!($efi_entry.system_table().con_out().unwrap(), $($x,)*).unwrap()
    };
}

fn main(
    image_handle: *mut core::ffi::c_void,
    systab_ptr: *mut EfiSystemTable,
) -> Result<(), GblEfiError> {
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
    Ok(())
}

#[no_mangle]
pub extern "C" fn efi_main(image_handle: *mut core::ffi::c_void, systab_ptr: *mut EfiSystemTable) {
    main(image_handle, systab_ptr).unwrap();
    loop {}
}
