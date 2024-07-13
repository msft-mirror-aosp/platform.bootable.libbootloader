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

use crate::error::Result;
use alloc::vec::Vec;
use core::{cmp::max, fmt::Write};
use efi::{
    defs::EfiBlockIoMedia,
    efi_print, efi_println,
    protocol::{block_io::BlockIoProtocol, block_io2::BlockIo2Protocol, Protocol},
    EfiEntry,
};
use gbl_async::block_on;
use gbl_storage::{
    check_part_unique, read_unique_gpt_partition, AsAsyncGptDeviceIter, AsyncBlockDevice,
    AsyncGptDevice, BlockInfo, BlockIoAsync, BlockIoError, GptCache, Partition,
};
use safemath::SafeNum;

/// `EfiBlockDeviceIo` wraps a EFI `BlockIoProtocol` or `BlockIo2Protocol` and implements the
/// `BlockIoAsync` interface.
pub enum EfiBlockDeviceIo<'a> {
    Sync(Protocol<'a, BlockIoProtocol>),
    Async(Protocol<'a, BlockIo2Protocol>),
}

impl<'a> EfiBlockDeviceIo<'a> {
    fn media(&self) -> EfiBlockIoMedia {
        match self {
            EfiBlockDeviceIo::Sync(v) => v.media(),
            EfiBlockDeviceIo::Async(v) => v.media(),
        }
        .unwrap()
    }

    fn info(&mut self) -> BlockInfo {
        let media = self.media();
        BlockInfo {
            block_size: media.block_size as u64,
            num_blocks: (media.last_block + 1) as u64,
            alignment: max(1, media.io_align as u64),
        }
    }
}

impl BlockIoAsync for EfiBlockDeviceIo<'_> {
    fn info(&mut self) -> BlockInfo {
        (*self).info()
    }

    async fn read_blocks(
        &mut self,
        blk_offset: u64,
        out: &mut [u8],
    ) -> core::result::Result<(), BlockIoError> {
        match self {
            EfiBlockDeviceIo::Sync(v) => v.read_blocks(blk_offset, out),
            EfiBlockDeviceIo::Async(v) => v.read_blocks_ex(blk_offset, out).await,
        }
        .map_err(|_| BlockIoError::Others(Some("EFI block read error")))
    }

    async fn write_blocks(
        &mut self,
        blk_offset: u64,
        data: &mut [u8],
    ) -> core::result::Result<(), BlockIoError> {
        match self {
            EfiBlockDeviceIo::Sync(v) => v.write_blocks(blk_offset, data),
            EfiBlockDeviceIo::Async(v) => v.write_blocks_ex(blk_offset, data).await,
        }
        .map_err(|_| BlockIoError::Others(Some("EFI block write error")))
    }
}

/// Type alias for `AsyncBlockDevice` that uses `&mut EfiBlockDeviceIo` as IO.
pub type EfiAsyncBlockDevice<'a, 'b> = AsyncBlockDevice<'b, &'b mut EfiBlockDeviceIo<'a>>;
/// Type alias for `AsyncGptDevice` that uses `&mut EfiBlockDeviceIo` as IO.
pub type EfiAsyncGptDevice<'a, 'b> = AsyncGptDevice<'b, &'b mut EfiBlockDeviceIo<'a>>;

/// `EfiBlockDevice` represents a block device in the EFI context.
pub struct EfiBlockDevice<'a> {
    io: EfiBlockDeviceIo<'a>,
    buffer: Vec<u8>,
}

const MAX_GPT_ENTRIES: u64 = 128;

impl<'a> EfiBlockDevice<'a> {
    /// Creates a new instance.
    ///
    /// The API allocates scratch and GPT buffer from heap.
    pub fn new(mut io: EfiBlockDeviceIo<'a>) -> Result<Self> {
        let scratch_size = SafeNum::from(EfiAsyncBlockDevice::required_scratch_size(&mut io)?);
        let gpt_buffer_size = SafeNum::from(GptCache::required_buffer_size(MAX_GPT_ENTRIES)?);
        let buffer = vec![0u8; (scratch_size + gpt_buffer_size).try_into()?];
        Ok(Self { io, buffer })
    }

    /// A helper that creates and returns an instance of `EfiAsyncBlockDevice` and the GPT buffer.
    fn as_blk_and_gpt_buffer(&mut self) -> (EfiAsyncBlockDevice<'a, '_>, &mut [u8]) {
        let scratch_size = EfiAsyncBlockDevice::required_scratch_size(&mut self.io).unwrap();
        let (scratch, gpt) = self.buffer.as_mut_slice().split_at_mut(scratch_size);
        let blk = AsyncBlockDevice::new(&mut self.io, scratch).unwrap();
        (blk, gpt)
    }

    /// Syncs GPT.
    pub fn sync_gpt(&mut self) -> Result<()> {
        let (mut blk, gpt) = self.as_blk_and_gpt_buffer();
        let mut gpt = GptCache::from_uninit(MAX_GPT_ENTRIES, gpt).unwrap();
        Ok(block_on(blk.sync_gpt(&mut gpt))?)
    }

    /// Creates an instance of `EfiAsyncGptDevice`.
    pub fn as_gpt_dev(&mut self) -> EfiAsyncGptDevice<'a, '_> {
        let (blk, gpt) = self.as_blk_and_gpt_buffer();
        let gpt = GptCache::from_existing(gpt).unwrap();
        EfiAsyncGptDevice::new(blk, gpt)
    }
}

/// `EfiMultiBlockDevices` wraps a vector of `EfiBlockDevice`.
pub struct EfiMultiBlockDevices<'a>(Vec<EfiBlockDevice<'a>>);

impl<'a> AsAsyncGptDeviceIter for EfiMultiBlockDevices<'a> {
    type BlockIo<'b> = &'b mut EfiBlockDeviceIo<'a> where Self:'b;

    fn iter(&mut self) -> impl IntoIterator<Item = AsyncGptDevice<'_, Self::BlockIo<'_>>> {
        self.0.iter_mut().map(|v| v.as_gpt_dev())
    }
}

impl<'a> EfiMultiBlockDevices<'a> {
    /// Checks uniqueness of and reads from a GPT partition
    pub async fn read_gpt_partition(&mut self, part: &str, off: u64, out: &mut [u8]) -> Result<()> {
        Ok(read_unique_gpt_partition(self, part, off, out).await?)
    }

    /// Checks uniqueness of and reads from a GPT partition synchronously.
    pub fn read_gpt_partition_sync(&mut self, part: &str, off: u64, out: &mut [u8]) -> Result<()> {
        block_on(self.read_gpt_partition(part, off, out))
    }

    /// Creates a vector of `EfiAsyncGptDevice`.
    pub fn as_gpt_devs(&mut self) -> Vec<EfiAsyncGptDevice<'a, '_>> {
        self.0.iter_mut().map(|v| v.as_gpt_dev()).collect::<Vec<_>>()
    }

    /// Finds a partition.
    pub fn find_partition(&mut self, part: &str) -> Result<Partition> {
        Ok(check_part_unique(self, part)?.1)
    }
}

/// Finds and returns all EFI devices supporting either EFI_BLOCK_IO or EFI_BLOCK_IO2 protocol.
pub fn find_block_devices(efi_entry: &EfiEntry) -> Result<EfiMultiBlockDevices> {
    let bs = efi_entry.system_table().boot_services();
    let block_dev_handles = bs.locate_handle_buffer_by_protocol::<BlockIoProtocol>()?;
    let mut block_devices = Vec::<EfiBlockDevice>::new();
    for (idx, handle) in block_dev_handles.handles().iter().enumerate() {
        // Prioritizes `BlockIo2Protocol`.
        let blk_io = match bs.open_protocol::<BlockIo2Protocol>(*handle) {
            Ok(v) => EfiBlockDeviceIo::Async(v),
            _ => EfiBlockDeviceIo::Sync(bs.open_protocol::<BlockIoProtocol>(*handle)?),
        };
        if blk_io.media().logical_partition {
            continue;
        }
        let mut blk = EfiBlockDevice::new(blk_io)?;
        match blk.sync_gpt() {
            Ok(()) => {
                efi_println!(efi_entry, "Block #{}: GPT detected", idx);
            }
            Err(e) => {
                efi_println!(efi_entry, "Block #{}: Failed to find GPT. {:?}", idx, e);
            }
        };
        block_devices.push(blk);
    }
    Ok(EfiMultiBlockDevices(block_devices))
}
