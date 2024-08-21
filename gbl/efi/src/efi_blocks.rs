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

use alloc::vec::Vec;
use core::{cmp::max, fmt::Write};
use efi::{
    efi_print, efi_println,
    protocol::{block_io::BlockIoProtocol, block_io2::BlockIo2Protocol, Protocol},
    EfiEntry,
};
use efi_types::EfiBlockIoMedia;
use gbl_async::block_on;
use gbl_storage::{AsyncBlockDevice, AsyncGptDevice, BlockInfo, BlockIoAsync, GptCache};
use liberror::Error;
use libgbl::partition::{
    check_part_unique, read_unique_partition, Partition, PartitionBlockDevice,
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

    async fn read_blocks(&mut self, blk_offset: u64, out: &mut [u8]) -> Result<(), Error> {
        match self {
            EfiBlockDeviceIo::Sync(v) => v.read_blocks(blk_offset, out),
            EfiBlockDeviceIo::Async(v) => v.read_blocks_ex(blk_offset, out).await,
        }
        .or(Err(Error::BlockIoError))
    }

    async fn write_blocks(&mut self, blk_offset: u64, data: &mut [u8]) -> Result<(), Error> {
        match self {
            EfiBlockDeviceIo::Sync(v) => v.write_blocks(blk_offset, data),
            EfiBlockDeviceIo::Async(v) => v.write_blocks_ex(blk_offset, data).await,
        }
        .or(Err(Error::BlockIoError))
    }
}

/// Type alias for `AsyncBlockDevice` that uses `&mut EfiBlockDeviceIo` as IO.
pub type EfiAsyncBlockDevice<'a, 'b> = AsyncBlockDevice<'b, &'b mut EfiBlockDeviceIo<'a>>;
/// Type alias for `AsyncGptDevice` that uses `&mut EfiBlockDeviceIo` as IO.
pub type EfiAsyncGptDevice<'a, 'b> = AsyncGptDevice<'b, &'b mut EfiBlockDeviceIo<'a>>;

const MAX_GPT_ENTRIES: u64 = 128;

/// `PartitionInfoBuffer` manages the buffer for raw partition name or GPT partition table.
enum PartitionInfoBuffer {
    Gpt(Vec<u8>),
    // TODO(b/357688291): Add raw partition entry once supported.
}

/// `EfiBlockDevice` manages EFI block IO, scratch and partition table buffers.
pub struct EfiBlockDevice<'a> {
    io: EfiBlockDeviceIo<'a>,
    scratch: Vec<u8>,
    partition: PartitionInfoBuffer,
}

impl<'a> EfiBlockDevice<'a> {
    /// Creates a new instance as GPT partition device.
    ///
    /// The API allocates scratch and GPT buffer from heap.
    pub fn new_gpt(mut io: EfiBlockDeviceIo<'a>) -> Result<Self, Error> {
        let scratch_size = SafeNum::from(EfiAsyncBlockDevice::required_scratch_size(&mut io)?);
        let mut gpt_buf = vec![0u8; GptCache::required_buffer_size(MAX_GPT_ENTRIES)?];
        // Initializes GPT buffer.
        let _ = GptCache::from_uninit(MAX_GPT_ENTRIES, &mut gpt_buf)?;
        Ok(Self {
            io,
            scratch: vec![0u8; scratch_size.try_into()?],
            partition: PartitionInfoBuffer::Gpt(gpt_buf),
        })
    }

    /// Creates an instance of GBL partition block device.
    pub fn as_gbl_part(
        &mut self,
    ) -> Result<PartitionBlockDevice<&mut EfiBlockDeviceIo<'a>>, Error> {
        let blk = AsyncBlockDevice::new(&mut self.io, &mut self.scratch)?;
        Ok(match &mut self.partition {
            PartitionInfoBuffer::Gpt(buf) => {
                PartitionBlockDevice::new_gpt(blk, GptCache::from_existing(buf).unwrap())
            }
        })
    }

    /// Creates an instance of `EfiAsyncGptDevice`.
    // TODO(b/357688291): Remove once we switch to `PartitionBlockDevice` and `GblOps`.
    pub fn as_gpt_dev(&mut self) -> Result<EfiAsyncGptDevice<'a, '_>, Error> {
        let PartitionInfoBuffer::Gpt(ref mut buf) = &mut self.partition;
        let blk = AsyncBlockDevice::new(&mut self.io, &mut self.scratch)?;
        let gpt = GptCache::from_existing(buf).unwrap();
        Ok(EfiAsyncGptDevice::new(blk, gpt))
    }
}

/// `EfiMultiBlockDevices` wraps a vector of `EfiBlockDevice`.
pub struct EfiMultiBlockDevices<'a>(pub Vec<EfiBlockDevice<'a>>);

impl<'a> EfiMultiBlockDevices<'a> {
    /// Creates a vector of `PartitionBlockDevice`
    pub fn as_gbl_parts(
        &mut self,
    ) -> Result<Vec<PartitionBlockDevice<&mut EfiBlockDeviceIo<'a>>>, Error> {
        let mut res = vec![];
        for ele in &mut self.0 {
            res.push(ele.as_gbl_part()?)
        }
        Ok(res)
    }

    /// Checks uniqueness of and reads from a GPT partition
    // TODO(b/357688291): Remove once we switch to GblOps for read/writing partitions.
    pub async fn read_gpt_partition(
        &mut self,
        part: &str,
        off: u64,
        out: &mut [u8],
    ) -> Result<(), Error> {
        // This is not very efficient because `as_gbl_parts()` allocates temporaray memory for array
        // of `PartitionBlockDevice`. Ideally, we want to create the array once and re-use it. This
        // will be done once we switch to GblOps for reading/writing partition.
        read_unique_partition(&self.as_gbl_parts()?, part, off, out).await
    }

    /// Checks uniqueness of and reads from a GPT partition synchronously.
    // TODO(b/357688291): Remove once we switch to GblOps for read/writing partitions.
    pub fn read_gpt_partition_sync(
        &mut self,
        part: &str,
        off: u64,
        out: &mut [u8],
    ) -> Result<(), Error> {
        block_on(self.read_gpt_partition(part, off, out))
    }

    /// Finds a partition.
    // TODO(b/357688291): Remove once we switch to GblOps for finding partitions.
    pub fn find_partition(&mut self, part: &str) -> Result<Partition, Error> {
        Ok(check_part_unique(&self.as_gbl_parts()?, part)?.1)
    }
}

/// Finds and returns all EFI devices supporting either EFI_BLOCK_IO or EFI_BLOCK_IO2 protocol.
pub fn find_block_devices(efi_entry: &EfiEntry) -> Result<EfiMultiBlockDevices, Error> {
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
        // TODO(b/357688291): Support raw partition based on device path info.
        let mut blk = EfiBlockDevice::new_gpt(blk_io)?;
        match block_on(blk.as_gbl_part()?.sync_gpt()) {
            Ok(true) => {
                efi_println!(efi_entry, "Block #{}: GPT detected", idx);
            }
            Err(e) => {
                efi_println!(efi_entry, "Block #{}: Failed to find GPT. {:?}", idx, e);
            }
            _ => {}
        };
        block_devices.push(blk);
    }
    Ok(EfiMultiBlockDevices(block_devices))
}
