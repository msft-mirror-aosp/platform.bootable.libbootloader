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

use alloc::vec::Vec;
use efi::defs::EfiGuid;
use efi::{
    BlockIoProtocol, DeviceHandle, DevicePathProtocol, DevicePathText, DevicePathToTextProtocol,
    EfiEntry, EfiError, Protocol,
};
use fdt::{FdtError, FdtHeader};
use gbl_storage::{required_scratch_size, BlockDevice, Gpt, GptEntry, StorageError};

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

/// Error type for EFI application.
#[derive(Debug)]
pub enum EfiAppError {
    ArithmeticOverflow,
    NotFound,
}

/// A top level error type that consolidates errors from different libraries.
#[derive(Debug)]
pub enum GblEfiError {
    StorageError(gbl_storage::StorageError),
    EfiAppError(EfiAppError),
    EfiError(efi::EfiError),
    FdtError(fdt::FdtError),
}

impl From<StorageError> for GblEfiError {
    fn from(error: StorageError) -> GblEfiError {
        GblEfiError::StorageError(error)
    }
}

impl From<EfiAppError> for GblEfiError {
    fn from(error: EfiAppError) -> GblEfiError {
        GblEfiError::EfiAppError(error)
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

fn to_usize<T: TryInto<usize>>(val: T) -> Result<usize> {
    Ok(val.try_into().map_err(|_| EfiAppError::ArithmeticOverflow)?)
}

fn usize_mul<L: TryInto<usize>, R: TryInto<usize>>(lhs: L, rhs: R) -> Result<usize> {
    Ok(to_usize(lhs)?.checked_mul(to_usize(rhs)?).ok_or_else(|| EfiAppError::ArithmeticOverflow)?)
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

const MAX_GPT_ENTRIES: u64 = 128;

/// A helper wrapper for managing GPT buffer.
struct GptBuffer(Vec<u8>);

impl GptBuffer {
    pub fn new() -> Result<Self> {
        let mut gpt_buffer = vec![0u8; Gpt::required_buffer_size(MAX_GPT_ENTRIES)?];
        Gpt::new_from_buffer(MAX_GPT_ENTRIES, &mut gpt_buffer)?;
        Ok(Self(gpt_buffer))
    }

    pub fn gpt(&mut self) -> Result<Gpt> {
        Ok(Gpt::get_existing_from_buffer(&mut self.0[..])?)
    }
}

/// A GPT block device type.
/// It wraps `BlockDevice` APIs with internally maintained scratch and GPT buffers to simplify
/// usage
pub struct EfiGptDevice<'a> {
    blk_dev: EfiBlockDevice<'a>,
    scratch: Vec<u8>,
    gpt_buffer: GptBuffer,
}

impl<'a> EfiGptDevice<'a> {
    /// Initialize from a `BlockIoProtocol` EFI protocol
    pub fn new(protocol: Protocol<'a, BlockIoProtocol>) -> Result<Self> {
        let mut blk_dev = EfiBlockDevice(protocol);
        let scratch = vec![0u8; required_scratch_size(&mut blk_dev)?];
        let gpt_buffer = GptBuffer::new()?;
        Ok(Self { blk_dev, scratch, gpt_buffer })
    }

    /// Returns the raw `BlockDevice` trait.
    pub fn block_device<'b>(&'b mut self) -> &'b mut EfiBlockDevice<'a> {
        &mut self.blk_dev
    }

    /// Wrapper of BlockDevice::sync_gpt()
    pub fn sync_gpt(&mut self) -> Result<()> {
        self.blk_dev.sync_gpt(&mut self.gpt_buffer.gpt()?, &mut self.scratch[..])?;
        Ok(())
    }

    /// Returns the GPT.
    pub fn gpt<'b>(&'b mut self) -> Result<Gpt<'b>> {
        self.gpt_buffer.gpt()
    }

    /// Wrapper of BlockDevice::read_gpt_partition()
    pub fn read_gpt_partition(
        &mut self,
        part_name: &str,
        offset: u64,
        out: &mut [u8],
    ) -> Result<()> {
        Ok(self.blk_dev.read_gpt_partition(
            &self.gpt_buffer.gpt()?,
            part_name,
            offset,
            out,
            &mut self.scratch[..],
        )?)
    }
}

/// A helper type that searches and reads/writes from multiple GPT devices.
/// Platforms like cuttlefish may have additional block devices for storing device specific data
/// such as bootconfig.
pub struct MultiGptDevices<'a> {
    gpt_devices: Vec<EfiGptDevice<'a>>,
}

impl<'a> MultiGptDevices<'a> {
    pub fn new(gpt_devices: Vec<EfiGptDevice<'a>>) -> Self {
        Self { gpt_devices }
    }

    /// Find a partition on the first match.
    fn find_partition(&mut self, part: &str) -> Result<(usize, GptEntry)> {
        for (idx, device) in &mut self.gpt_devices[..].iter_mut().enumerate() {
            match device.gpt()?.find_partition(part)? {
                Some(p) => {
                    return Ok((idx, *p));
                }
                _ => {}
            }
        }
        Err(EfiAppError::NotFound.into())
    }

    /// Return the size of the target partition on the first match.
    pub fn partition_size(&mut self, part: &str) -> Result<usize> {
        let (idx, part) = self.find_partition(part)?;
        Ok(usize_mul(part.blocks()?, self.gpt_devices[idx].block_device().block_size())?)
    }

    /// Traverse all gpt devices and read the given partition on the first match.
    pub fn read_gpt_partition(
        &mut self,
        part_name: &str,
        offset: u64,
        out: &mut [u8],
    ) -> Result<()> {
        let (idx, _) = self.find_partition(part_name)?;
        Ok(self.gpt_devices[idx].read_gpt_partition(part_name, offset, out)?)
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
