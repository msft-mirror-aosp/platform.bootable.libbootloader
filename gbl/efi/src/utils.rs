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

use efi::defs::EfiGuid;
use efi::{
    BlockIoProtocol, DeviceHandle, DevicePathProtocol, DevicePathText, DevicePathToTextProtocol,
    EfiEntry, EfiError, Protocol,
};
use fdt::{FdtError, FdtHeader};
use gbl_storage::{BlockDevice, StorageError};

pub const EFI_DTB_TABLE_GUID: EfiGuid =
    EfiGuid::new(0xb1b621d5, 0xf19c, 0x41a5, [0x83, 0x0b, 0xd9, 0x15, 0x2c, 0x69, 0xaa, 0xe0]);

/// Helper macro for printing message via `EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL` in
/// `EFI_SYSTEM_TABLE.ConOut`.
#[macro_export]
macro_rules! efi_print {
    ( $efi_entry:expr, $( $x:expr ),* ) => {
        write!($efi_entry.system_table().con_out().unwrap(), $($x,)*).unwrap()
    };
}

/// GBL EFI application error type.
pub type Result<T> = core::result::Result<T, GblEfiError>;

/// A top level error type that consolidates errors from different libraries.
#[derive(Debug)]
pub enum GblEfiError {
    StorageError(gbl_storage::StorageError),
    EfiError(efi::EfiError),
    FdtError(fdt::FdtError),
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

impl From<FdtError> for GblEfiError {
    fn from(error: FdtError) -> GblEfiError {
        GblEfiError::FdtError(error)
    }
}

// Implement a block device on top of BlockIoProtocol
pub struct EfiBlockDevice<'a>(pub Protocol<'a, BlockIoProtocol>);

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

/// Helper function to get the `DevicePathText` from a `DeviceHandle`.
pub fn get_device_path<'a>(
    entry: &'a EfiEntry,
    handle: DeviceHandle,
) -> Result<DevicePathText<'a>> {
    let bs = entry.system_table().boot_services();
    let path = bs.open_protocol::<DevicePathProtocol>(handle)?;
    let path_to_text = bs.find_first_and_open::<DevicePathToTextProtocol>()?;
    Ok(path_to_text.convert_device_path_to_text(&path, false, false)?)
}

/// Find FDT from EFI configuration table.
pub fn get_efi_fdt<'a>(entry: &'a EfiEntry) -> Option<(&FdtHeader, &[u8])> {
    if let Some(config_tables) = entry.system_table().configuration_table() {
        for table in config_tables {
            if table.vendor_guid == EFI_DTB_TABLE_GUID {
                // SAFETY: Buffer provided by EFI configuration table.
                return unsafe { FdtHeader::from_raw(table.vendor_table as *const _).ok() };
            }
        }
    }
    None
}
