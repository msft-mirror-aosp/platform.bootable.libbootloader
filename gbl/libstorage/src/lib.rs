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

//! APIs for reading/writing with non-block-aligned ranges and unaligned buffer.
//!
//! Most block devices require reading/writing in the unit of block and that the input/output
//! buffer satisfies certain alignment (i.e. DMA). This library provides APIs that build on top
//! of them and relax these constraints. The library supports reading/writing raw block content
//! as well as parsing/reading/writing GPT partitions.
//!
//! # Examples
//!
//! ```rust
//! use gbl_storage::{
//!     AsBlockDevice, BlockIoSync, BlockDevice, required_scratch_size, BlockInfo, BlockIoError,
//! };
//!
//! /// Mocks a block device using a buffer.
//! pub struct RamBlockIo {
//!     storage: std::vec::Vec<u8>,
//! }
//!
//! impl BlockIoSync for RamBlockIo {
//!     fn info(&mut self) -> BlockInfo {
//!         BlockInfo {
//!             block_size: 512,
//!             num_blocks: self.storage.len() as u64 / 512,
//!             alignment: 64,
//!         }
//!     }
//!
//!     fn read_blocks(&mut self, blk_offset: u64, out: &mut [u8]) -> Result<(), BlockIoError> {
//!         let start = blk_offset * self.info().block_size;
//!         let end = start + out.len() as u64;
//!         out.clone_from_slice(&self.storage[start as usize..end as usize]);
//!         Ok(())
//!     }
//!
//!     fn write_blocks(&mut self, blk_offset: u64, data: &mut [u8]) -> Result<(), BlockIoError> {
//!         let start = blk_offset * self.info().block_size;
//!         let end = start + data.len() as u64;
//!         self.storage[start as usize..end as usize].clone_from_slice(&data);
//!         Ok(())
//!     }
//! }
//!
//! const MAX_GPT_ENTRIES: u64 = 128;
//!
//! let mut ram_block_io = RamBlockIo { storage: vec![0u8; 64 * 1024] };
//! // Prepare a scratch buffer, size calculated with `required_scratch_size()`.
//! let mut scratch =
//!     vec![0u8; required_scratch_size(ram_block_io.info(), MAX_GPT_ENTRIES).unwrap()];
//! // Create a `BlockDevice`
//! let mut ram_block_dev =
//!     BlockDevice::new(&mut ram_block_io, &mut scratch[..], MAX_GPT_ENTRIES);
//!
//! // Read/write with arbitrary range and buffer without worrying about alignment.
//! let mut out = vec![0u8; 1234];
//! ram_block_dev.read(4321, &mut out[..]).unwrap();
//! let mut data = vec![0u8; 5678];
//! // Mutable input. More efficient
//! ram_block_dev.write(8765, data.as_mut_slice()).unwrap();
//!
//! // Sync GPT
//! let _ = ram_block_dev.sync_gpt();
//! // Access GPT entries
//! let _ = ram_block_dev.find_partition("some-partition");
//! // Read/Write GPT partitions with arbitrary offset, size, buffer
//! let _ = ram_block_dev.read_gpt_partition("partition", 4321, &mut out[..]);
//! let _ = ram_block_dev.write_gpt_partition("partition", 8765, data.as_mut_slice());
//!
//! // Alterantively, you can also define a custom type that internally owns and binds the
//! // implementation of `BlockIoSync` and scratch buffer together, and then implement the
//! // `AsBlockDevice` trait. This gives a cleaner management of resources.
//! pub struct OwnedBlockDevice {
//!     io: RamBlockIo,
//!     scratch: std::vec::Vec<u8>,
//! }
//!
//! impl AsBlockDevice for OwnedBlockDevice {
//!     fn with(&mut self, f: &mut dyn FnMut(&mut dyn BlockIoSync, &mut [u8], u64)) {
//!         f(&mut self.io, &mut self.scratch[..], MAX_GPT_ENTRIES)
//!     }
//! }
//!
//! // `owned_block_dev` has the same APIs as `BlockDevice`.
//! let mut owned_block_dev = OwnedBlockDevice { io: ram_block_io, scratch: scratch };
//! ```

#![cfg_attr(not(test), no_std)]
#![allow(async_fn_in_trait)]

use gbl_async::block_on;

// Selective export of submodule types.
mod gpt;
use gpt::check_gpt_rw_params;
use gpt::Gpt;
pub use gpt::{GptEntry, GptHeader, GPT_MAGIC, GPT_NAME_LEN_U16};

use safemath::SafeNum;

mod multi_blocks;
pub use multi_blocks::AsMultiBlockDevices;

mod algorithm;
pub use algorithm::{read_async, write_async, AsyncAsSync, SyncAsAsync};

/// The type of Result used in this library.
pub type Result<T> = core::result::Result<T, StorageError>;

/// Error code for this library.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum StorageError {
    ArithmeticOverflow(safemath::Error),
    BlockDeviceNotFound,
    BlockIoError(BlockIoError),
    BlockIoNotProvided,
    FailedGettingBlockDevices(Option<&'static str>),
    IoAborted,
    InvalidInput,
    NoValidGpt,
    NotExist,
    NotReady,
    OutOfRange,
    PartitionNotUnique,
    ScratchTooSmall,
}

impl From<safemath::Error> for StorageError {
    fn from(err: safemath::Error) -> Self {
        Self::ArithmeticOverflow(err)
    }
}

impl From<core::num::TryFromIntError> for StorageError {
    fn from(_: core::num::TryFromIntError) -> Self {
        Self::OutOfRange
    }
}

impl From<BlockIoError> for StorageError {
    fn from(val: BlockIoError) -> Self {
        Self::BlockIoError(val)
    }
}

impl core::fmt::Display for StorageError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// `BlockInfo` contains information for a block device.
pub struct BlockInfo {
    /// Native block size of the block device.
    pub block_size: u64,
    /// Total number of blocks of the block device.
    pub num_blocks: u64,
    /// The alignment requirement for IO buffers. For example, many block device drivers use DMA
    /// for data transfer, which typically requires that the buffer address for DMA be aligned to
    /// 16/32/64 bytes etc. If the block device has no alignment requirement, it can return 1.
    pub alignment: u64,
}

impl BlockInfo {
    /// Computes the total size in bytes of the block device.
    pub fn total_size(&self) -> Result<u64> {
        Ok((SafeNum::from(self.block_size) * self.num_blocks).try_into()?)
    }
}

/// `BlockIoError` represents the error code for returned by implementation of `BlockIoSync` and
/// `BlockIoAsync` interfaces.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BlockIoError {
    Others(Option<&'static str>),
}

/// `BlockIoAsync` provides interfaces for asynchronous read and write.
pub trait BlockIoAsync {
    /// Returns the `BlockInfo` for this block device.
    fn info(&mut self) -> BlockInfo;

    /// Read blocks of data from the block device
    ///
    /// # Args
    ///
    /// * `blk_offset`: Offset in number of blocks.
    ///
    /// * `out`: Buffer to store the read data. Callers of this method ensure that it is
    ///   aligned according to alignment() and `out.len()` is multiples of `block_size()`.
    ///
    /// # Returns
    ///
    /// Returns true if exactly out.len() number of bytes are read. Otherwise false.
    async fn read_blocks(
        &mut self,
        blk_offset: u64,
        out: &mut [u8],
    ) -> core::result::Result<(), BlockIoError>;

    /// Write blocks of data to the block device
    ///
    /// # Args
    ///
    /// * `blk_offset`: Offset in number of blocks.
    ///
    /// * `data`: Data to write. Callers of this method ensure that it is aligned according to
    ///   `alignment()` and `data.len()` is multiples of `block_size()`.
    ///
    /// # Returns
    ///
    /// Returns true if exactly data.len() number of bytes are written. Otherwise false.
    async fn write_blocks(
        &mut self,
        blk_offset: u64,
        data: &mut [u8],
    ) -> core::result::Result<(), BlockIoError>;
}

/// `BlockIoSync` provide interfaces for synchronous read and write.
pub trait BlockIoSync {
    /// Gets the `BlockInfo` for this block device
    fn info(&mut self) -> BlockInfo;

    /// Read blocks of data from the block device
    ///
    /// # Args
    ///
    /// * `blk_offset`: Offset in number of blocks.
    ///
    /// * `out`: Buffer to store the read data. Callers of this method ensure that it is
    ///   aligned according to alignment() and `out.len()` is multiples of `block_size()`.
    ///
    /// # Returns
    ///
    /// Returns true if exactly out.len() number of bytes are read. Otherwise false.
    fn read_blocks(
        &mut self,
        blk_offset: u64,
        out: &mut [u8],
    ) -> core::result::Result<(), BlockIoError>;

    /// Write blocks of data to the block device
    ///
    /// # Args
    ///
    /// * `blk_offset`: Offset in number of blocks.
    ///
    /// * `data`: Data to write. Callers of this method ensure that it is aligned according to
    ///   `alignment()` and `data.len()` is multiples of `block_size()`.
    ///
    /// # Returns
    ///
    /// Returns true if exactly data.len() number of bytes are written. Otherwise false.
    fn write_blocks(
        &mut self,
        blk_offset: u64,
        data: &mut [u8],
    ) -> core::result::Result<(), BlockIoError>;
}

impl BlockIoSync for &mut dyn BlockIoSync {
    fn info(&mut self) -> BlockInfo {
        (*self).info()
    }

    fn read_blocks(
        &mut self,
        blk_offset: u64,
        out: &mut [u8],
    ) -> core::result::Result<(), BlockIoError> {
        (*self).read_blocks(blk_offset, out)
    }

    fn write_blocks(
        &mut self,
        blk_offset: u64,
        data: &mut [u8],
    ) -> core::result::Result<(), BlockIoError> {
        (*self).write_blocks(blk_offset, data)
    }
}

/// `Partition` contains information about a GPT partition.
#[derive(Debug, Copy, Clone)]
pub struct Partition {
    entry: GptEntry,
    block_size: u64,
}

impl Partition {
    /// Creates a new instance.
    fn new(entry: GptEntry, block_size: u64) -> Self {
        Self { entry, block_size }
    }

    /// Returns the partition size in bytes.
    pub fn size(&self) -> Result<u64> {
        (SafeNum::from(self.entry.blocks()?) * self.block_size)
            .try_into()
            .map_err(|e: safemath::Error| e.into())
    }

    /// Returns the block size of this partition.
    pub fn block_size(&self) -> u64 {
        self.block_size
    }

    /// Returns the partition entry structure in the GPT header.
    pub fn gpt_entry(&self) -> &GptEntry {
        &self.entry
    }
}

/// `PartitionIterator` is returned by `AsBlockDevice::partition_iter()` and can be used to
/// iterate all GPT partition entries.
pub struct PartitionIterator<'a> {
    dev: &'a mut dyn AsBlockDevice,
    idx: usize,
}

impl Iterator for PartitionIterator<'_> {
    type Item = Partition;

    fn next(&mut self) -> Option<Self::Item> {
        let res = with_partitioned_scratch(
            self.dev,
            |io, _, gpt_buffer, _| -> Result<Option<Partition>> {
                Ok(Gpt::from_existing(gpt_buffer)?
                    .entries()?
                    .get(self.idx)
                    .map(|v| Partition::new(*v, io.info().block_size)))
            },
        )
        .ok()?
        .ok()??;
        self.idx += 1;
        Some(res)
    }
}

/// `AsBlockDevice` provides APIs for synchronous read/write of raw block storage or GPT
/// partitions.
///
/// Users that need to perform asynchronous non-blocking read/write should use
/// `read_async`, `write_async` APIs instead.
pub trait AsBlockDevice {
    /// Runs the provided closure `f` with the following parameters:
    ///
    ///   1. An implementation of block IO `&mut dyn BlockIoSync`.
    ///   2. A scratch buffer `&mut [u8]`.
    ///   3. A `u64` specifying the maximum allowed number of GPT entries.
    ///
    /// * The scratch buffer is internally used for two purposes: 1. to handle read/write with
    ///   offset, size that are not multiples of block size or input/output buffer that are not
    ///   aligned, and 2. to load and sync GPT headers.
    ///
    /// * The necessary size for the scratch buffer depends on `BlockInfo::alignment`,
    ///   `BlockInfo::block_size` and maximum allowed GPT entries. It can be computed using the
    ///   helper API `required_scratch_size()`. If maximum allowed GPT entries is 0, GPT is
    ///   considered unavailable and no buffer will be reserved for GPT headers. If additionally,
    ///   `BlockIoSync` has no alignment requirement, i.e. both alignment and block size are 1, the
    ///   total required scratch size is 0.
    ///
    /// * GPT headers will be cached in the scratch buffer after calling `Self::sync_gpt()` and
    ///   returning success. Subsequent call of `Self:read_gpt_partiton()`,
    ///   `Self::write_gpt_partition()`, and `Self::write_gpt_partition()`
    ///   will look up partition entries from the cached GPT header.
    ///   Thus callers should make sure to always return the same scratch buffer and avoid
    ///   modifying its content.
    ///
    /// * A smaller value of maximum allowed GPT entries gives smaller required scratch buffer
    ///   size. However if the `entries_count` field in the GPT header is greater than this value,
    ///   GPT parsing will fail. Note that most tools and OS fix the `entries_count` value to the
    ///   max value 128 regardless of the actual number of partition entries used. Thus unless you
    ///   have full control of GPT generation in your entire system where you can always ensure a
    ///   smaller bound on it, it is recommended to always return 128.
    fn with(&mut self, f: &mut dyn FnMut(&mut dyn BlockIoSync, &mut [u8], u64));

    /// Returns the `BlockInfo` of the provided Block IO.
    fn info(&mut self) -> BlockInfo {
        let mut res = None;
        self.with(&mut |io, _, _| res = Some(io.info()));
        res.unwrap()
    }

    /// Read data from the block device.
    ///
    /// # Args
    ///
    /// * `offset`: Offset in number of bytes.
    ///
    /// * `out`: Buffer to store the read data.
    ///
    /// * Returns success when exactly `out.len()` number of bytes are read.
    fn read(&mut self, offset: u64, out: &mut [u8]) -> Result<()> {
        with_partitioned_scratch(self, |io, alignment, _, _| {
            block_on(read_async(&mut SyncAsAsync::new(io), offset, out, alignment))
        })?
    }

    /// Write data to the device.
    ///
    /// # Args
    ///
    /// * `offset`: Offset in number of bytes.
    ///
    /// * `data`: Data to write.
    ///
    /// * The API enables an optimization which temporarily changes `data` layout internally and
    ///   reduces the number of calls to `Self::write_blocks()` down to O(1) regardless of input's
    ///   alignment. This is the recommended usage.
    ///
    /// * Returns success when exactly `data.len()` number of bytes are written.
    fn write(&mut self, offset: u64, data: &mut [u8]) -> Result<()> {
        with_partitioned_scratch(self, |io, alignment_scratch, _, _| {
            block_on(write_async(&mut SyncAsAsync::new(io), offset, data, alignment_scratch))
        })?
    }

    /// Parse and sync GPT from a block device.
    ///
    /// The API validates and restores primary/secondary GPT header.
    ///
    /// # Returns
    ///
    /// Returns success if GPT is loaded/restored successfully.
    fn sync_gpt(&mut self) -> Result<()> {
        with_partitioned_scratch(self, |io, alignment_scratch, gpt_buffer, max_entries| {
            block_on(gpt::gpt_sync(
                &mut SyncAsAsync::new(io),
                &mut Gpt::new_from_buffer(max_entries, gpt_buffer)?,
                alignment_scratch,
            ))
        })?
    }

    /// Returns an iterator to GPT partition entries.
    fn partition_iter(&mut self) -> PartitionIterator
    where
        Self: Sized,
    {
        PartitionIterator { dev: self, idx: 0 }
    }

    /// Returns the `Partition` for a partition.
    ///
    /// # Args
    ///
    /// * `part`: Name of the partition.
    fn find_partition(&mut self, part: &str) -> Result<Partition> {
        with_partitioned_scratch(self, |io, _, gpt_buffer, _| {
            Ok(Partition::new(
                *Gpt::from_existing(gpt_buffer)?.find_partition(part)?,
                io.info().block_size,
            ))
        })?
    }

    /// Read a GPT partition on a block device
    ///
    /// # Args
    ///
    /// * `part_name`: Name of the partition.
    ///
    /// * `offset`: Offset in number of bytes into the partition.
    ///
    /// * `out`: Buffer to store the read data.
    ///
    /// # Returns
    ///
    /// Returns success when exactly `out.len()` of bytes are read successfully.
    fn read_gpt_partition(&mut self, part_name: &str, offset: u64, out: &mut [u8]) -> Result<()> {
        let offset = with_partitioned_scratch(self, |_, _, gpt_buffer, _| {
            check_gpt_rw_params(gpt_buffer, part_name, offset, out.len())
        })??;
        self.read(offset, out)
    }

    /// Write a GPT partition on a block device.
    /// Optimization for mutable buffers.
    /// See `AsBlockDevice::write` for details on alignment requirements
    /// for optimized performance.
    ///
    /// # Args
    ///
    /// * `part_name`: Name of the partition.
    ///
    /// * `offset`: Offset in number of bytes into the partition.
    ///
    /// * `data`: Data to write. See `data` passed to `BlockIoSync::write()` for details.
    ///
    /// # Returns
    ///
    /// Returns success when exactly `data.len()` of bytes are written successfully.
    fn write_gpt_partition(&mut self, part_name: &str, offset: u64, data: &mut [u8]) -> Result<()> {
        let offset = with_partitioned_scratch(self, |_, _, gpt_buffer, _| {
            check_gpt_rw_params(gpt_buffer, part_name, offset, data.len())
        })??;
        self.write(offset, data)
    }
}

impl<T: ?Sized + AsBlockDevice> AsBlockDevice for &mut T {
    fn with(&mut self, f: &mut dyn FnMut(&mut dyn BlockIoSync, &mut [u8], u64)) {
        (*self).with(f)
    }
}

/// `BlockDevice` borrows a `BlockIoSync`, scratch buffer and implements `AsBlockDevice`.
pub struct BlockDevice<'a, 'b> {
    io: &'a mut dyn BlockIoSync,
    scratch: &'b mut [u8],
    max_gpt_entries: u64,
}

impl<'a, 'b> BlockDevice<'a, 'b> {
    pub fn new(io: &'a mut dyn BlockIoSync, scratch: &'b mut [u8], max_gpt_entries: u64) -> Self {
        Self { io, scratch, max_gpt_entries }
    }
}

impl AsBlockDevice for BlockDevice<'_, '_> {
    fn with(&mut self, f: &mut dyn FnMut(&mut dyn BlockIoSync, &mut [u8], u64)) {
        f(self.io, self.scratch, self.max_gpt_entries)
    }
}

/// Calculates the required scratch buffer size given a `BlockInfo` and maximum GPT entries.
pub fn required_scratch_size(info: BlockInfo, max_gpt_entries: u64) -> Result<usize> {
    let alignment_size: SafeNum = alignment_scratch_size(info)?.into();
    let gpt_buffer_size = match max_gpt_entries {
        0 => 0,
        v => Gpt::required_buffer_size(v)?,
    };
    (alignment_size + gpt_buffer_size).try_into().map_err(|e: safemath::Error| e.into())
}

/// A helper that wraps `AsBlockDevice::with` and additionally partitions the scratch buffer into
/// alignment scratch and GPT buffers.
fn with_partitioned_scratch<F, R>(dev: &mut (impl AsBlockDevice + ?Sized), mut f: F) -> Result<R>
where
    F: FnMut(&mut dyn BlockIoSync, &mut [u8], &mut [u8], u64) -> R,
{
    let mut res: Result<R> = Err(StorageError::BlockIoNotProvided);
    dev.with(&mut |io, scratch, max_entries| {
        res = (|| {
            if scratch.len() < required_scratch_size(io.info(), max_entries)? {
                return Err(StorageError::ScratchTooSmall);
            }
            let (alignment, gpt) = scratch.split_at_mut(alignment_scratch_size(io.info())?);
            Ok(f(io, alignment, gpt, max_entries))
        })();
    });
    res
}

/// Check if `value` is aligned to (multiples of) `alignment`
/// It can fail if the remainider calculation fails overflow check.
pub fn is_aligned(value: SafeNum, alignment: SafeNum) -> Result<bool> {
    Ok(u64::try_from(value % alignment)? == 0)
}

/// Check if `buffer` address is aligned to `alignment`
/// It can fail if the remainider calculation fails overflow check.
pub fn is_buffer_aligned(buffer: &[u8], alignment: u64) -> Result<bool> {
    is_aligned((buffer.as_ptr() as usize).into(), alignment.into())
}

/// Check read/write range and calculate offset in number of blocks.
fn check_range(info: BlockInfo, offset: u64, buffer: &[u8]) -> Result<SafeNum> {
    let offset: SafeNum = offset.into();
    let block_size: SafeNum = info.block_size.into();
    debug_assert!(is_aligned(offset, block_size)?, "{:?}, {:?}", offset, block_size);
    debug_assert!(is_aligned(buffer.len().into(), block_size)?);
    debug_assert!(is_buffer_aligned(buffer, info.alignment)?);
    let blk_offset = offset / block_size;
    let blk_count = SafeNum::from(buffer.len()) / block_size;
    match u64::try_from(blk_offset + blk_count)? <= info.num_blocks {
        true => Ok(blk_offset),
        false => Err(StorageError::OutOfRange),
    }
}

/// Calculates the necessary scratch buffer size for handling block and buffer misalignment.
pub fn alignment_scratch_size(info: BlockInfo) -> Result<usize> {
    let block_alignment = match info.block_size {
        1 => 0,
        v => v,
    };
    ((SafeNum::from(info.alignment) - 1) * 2 + block_alignment)
        .try_into()
        .map_err(|e: safemath::Error| e.into())
}

/// Gets a subslice of the given slice with aligned address according to `alignment`
fn aligned_subslice(buffer: &mut [u8], alignment: u64) -> Result<&mut [u8]> {
    let addr = SafeNum::from(buffer.as_ptr() as usize);
    Ok(&mut buffer[(addr.round_up(alignment) - addr).try_into()?..])
}

#[cfg(test)]
mod test {
    use core::mem::size_of;
    use gbl_storage_testlib::{
        required_scratch_size, AsBlockDevice, TestBlockDevice, TestBlockDeviceBuilder,
    };
    use safemath::SafeNum;

    #[derive(Debug)]
    struct TestCase {
        rw_offset: u64,
        rw_size: u64,
        misalignment: u64,
        alignment: u64,
        block_size: u64,
        storage_size: u64,
    }

    impl TestCase {
        fn new(
            rw_offset: u64,
            rw_size: u64,
            misalignment: u64,
            alignment: u64,
            block_size: u64,
            storage_size: u64,
        ) -> Self {
            Self { rw_offset, rw_size, misalignment, alignment, block_size, storage_size }
        }
    }

    // Helper object for allocating aligned buffer.
    struct AlignedBuffer {
        buffer: Vec<u8>,
        alignment: u64,
        size: u64,
    }

    impl AlignedBuffer {
        pub fn new(alignment: u64, size: u64) -> Self {
            let aligned_size = (SafeNum::from(size) + alignment).try_into().unwrap();
            let buffer = vec![0u8; aligned_size];
            Self { buffer, alignment, size }
        }

        pub fn get(&mut self) -> &mut [u8] {
            let addr = SafeNum::from(self.buffer.as_ptr() as usize);
            let aligned_start = addr.round_up(self.alignment) - addr;
            &mut self.buffer
                [aligned_start.try_into().unwrap()..(aligned_start + self.size).try_into().unwrap()]
        }
    }

    /// Upper bound on the number of `read_blocks_async()/write_blocks_async()` calls by
    /// `AsBlockDevice::read()` and `AsBlockDevice::write()`.
    ///
    /// * `fn read_aligned_all()`: At most 1 call to `read_blocks_async()`.
    /// * `fn read_aligned_offset_and_buffer()`: At most 2 calls to `read_aligned_all()`.
    /// * `fn read_aligned_buffer()`: At most 1 call to `read_aligned_offset_and_buffer()` plus 1
    ///   call to `read_blocks_async()`.
    /// * `fn read_async()`: At most 2 calls to `read_aligned_buffer()`.
    ///
    /// Analysis is similar for `fn write_async()`.
    const READ_WRITE_BLOCKS_UPPER_BOUND: usize = 6;

    fn read_test_helper(case: &TestCase) {
        let data = (0..case.storage_size).map(|v| v as u8).collect::<Vec<_>>();
        let mut blk = TestBlockDeviceBuilder::new()
            .set_alignment(case.alignment)
            .set_block_size(case.block_size)
            .set_data(&data)
            .build();
        // Make an aligned buffer. A misaligned version is created by taking a sub slice that
        // starts at an unaligned offset. Because of this we need to allocate
        // `case.misalignment` more to accommodate it.
        let mut aligned_buf = AlignedBuffer::new(case.alignment, case.rw_size + case.misalignment);
        let misalignment = SafeNum::from(case.misalignment);
        let out = &mut aligned_buf.get()
            [misalignment.try_into().unwrap()..(misalignment + case.rw_size).try_into().unwrap()];
        blk.read(case.rw_offset, out).unwrap();
        let rw_offset = SafeNum::from(case.rw_offset);
        assert_eq!(
            out.to_vec(),
            blk.io.storage
                [rw_offset.try_into().unwrap()..(rw_offset + case.rw_size).try_into().unwrap()]
                .to_vec(),
            "Failed. Test case {:?}",
            case,
        );

        assert!(blk.io.num_reads <= READ_WRITE_BLOCKS_UPPER_BOUND);
    }

    fn write_test_helper(case: &TestCase, write_func: fn(&mut TestBlockDevice, u64, &mut [u8])) {
        let data = (0..case.storage_size).map(|v| v as u8).collect::<Vec<_>>();
        let mut blk = TestBlockDeviceBuilder::new()
            .set_alignment(case.alignment)
            .set_block_size(case.block_size)
            .set_data(&data)
            .build();
        // Write a reverse version of the current data.
        let rw_offset = SafeNum::from(case.rw_offset);
        let mut expected = blk.io.storage
            [rw_offset.try_into().unwrap()..(rw_offset + case.rw_size).try_into().unwrap()]
            .to_vec();
        expected.reverse();
        // Make an aligned buffer. A misaligned version is created by taking a sub slice that
        // starts at an unaligned offset. Because of this we need to allocate
        // `case.misalignment` more to accommodate it.
        let misalignment = SafeNum::from(case.misalignment);
        let mut aligned_buf = AlignedBuffer::new(case.alignment, case.rw_size + case.misalignment);
        let data = &mut aligned_buf.get()
            [misalignment.try_into().unwrap()..(misalignment + case.rw_size).try_into().unwrap()];
        data.clone_from_slice(&expected);
        write_func(&mut blk, case.rw_offset, data);
        let rw_offset = SafeNum::from(case.rw_offset);
        assert_eq!(
            expected,
            blk.io.storage
                [rw_offset.try_into().unwrap()..(rw_offset + case.rw_size).try_into().unwrap()]
                .to_vec(),
            "Failed. Test case {:?}",
            case,
        );
        // Check that input is not modified.
        assert_eq!(expected, data, "Input is modified. Test case {:?}", case,);
    }

    macro_rules! read_write_test {
        ($name:ident, $x0:expr, $x1:expr, $x2:expr, $x3:expr, $x4:expr, $x5:expr) => {
            mod $name {
                use super::*;

                #[test]
                fn read_test() {
                    read_test_helper(&TestCase::new($x0, $x1, $x2, $x3, $x4, $x5));
                }

                #[test]
                fn read_scaled_test() {
                    // Scaled all parameters by double and test again.
                    let (x0, x1, x2, x3, x4, x5) =
                        (2 * $x0, 2 * $x1, 2 * $x2, 2 * $x3, 2 * $x4, 2 * $x5);
                    read_test_helper(&TestCase::new(x0, x1, x2, x3, x4, x5));
                }

                // Input bytes slice is a mutable reference
                #[test]
                fn write_mut_test() {
                    let func = |blk: &mut TestBlockDevice, offset: u64, data: &mut [u8]| {
                        blk.write(offset, data).unwrap();
                        assert!(blk.io.num_reads <= READ_WRITE_BLOCKS_UPPER_BOUND);
                        assert!(blk.io.num_writes <= READ_WRITE_BLOCKS_UPPER_BOUND);
                    };
                    write_test_helper(&TestCase::new($x0, $x1, $x2, $x3, $x4, $x5), func);
                }

                #[test]
                fn write_mut_scaled_test() {
                    // Scaled all parameters by double and test again.
                    let (x0, x1, x2, x3, x4, x5) =
                        (2 * $x0, 2 * $x1, 2 * $x2, 2 * $x3, 2 * $x4, 2 * $x5);
                    let func = |blk: &mut TestBlockDevice, offset: u64, data: &mut [u8]| {
                        blk.write(offset, data).unwrap();
                        assert!(blk.io.num_reads <= READ_WRITE_BLOCKS_UPPER_BOUND);
                        assert!(blk.io.num_writes <= READ_WRITE_BLOCKS_UPPER_BOUND);
                    };
                    write_test_helper(&TestCase::new(x0, x1, x2, x3, x4, x5), func);
                }
            }
        };
    }

    const BLOCK_SIZE: u64 = 512;
    const ALIGNMENT: u64 = 64;
    const STORAGE: u64 = BLOCK_SIZE * 32;

    // Test cases for different scenarios of read/write windows w.r.t buffer/block alignmnet
    // boundary.
    // offset
    //   |~~~~~~~~~~~~~size~~~~~~~~~~~~|
    //   |---------|---------|---------|
    read_write_test! {aligned_all, 0, STORAGE, 0, ALIGNMENT, BLOCK_SIZE, STORAGE
    }

    // offset
    //   |~~~~~~~~~size~~~~~~~~~|
    //   |---------|---------|---------|
    read_write_test! {
        aligned_offset_uanligned_size, 0, STORAGE - 1, 0, ALIGNMENT, BLOCK_SIZE, STORAGE
    }
    // offset
    //   |~~size~~|
    //   |---------|---------|---------|
    read_write_test! {
        aligned_offset_intra_block, 0, BLOCK_SIZE - 1, 0, ALIGNMENT, BLOCK_SIZE, STORAGE
    }
    //     offset
    //       |~~~~~~~~~~~size~~~~~~~~~~|
    //   |---------|---------|---------|
    read_write_test! {
        unaligned_offset_aligned_end, 1, STORAGE - 1, 0, ALIGNMENT, BLOCK_SIZE, STORAGE
    }
    //     offset
    //       |~~~~~~~~~size~~~~~~~~|
    //   |---------|---------|---------|
    read_write_test! {unaligned_offset_len, 1, STORAGE - 2, 0, ALIGNMENT, BLOCK_SIZE, STORAGE
    }
    //     offset
    //       |~~~size~~~|
    //   |---------|---------|---------|
    read_write_test! {
        unaligned_offset_len_partial_cross_block, 1, BLOCK_SIZE, 0, ALIGNMENT, BLOCK_SIZE, STORAGE
    }
    //   offset
    //     |~size~|
    //   |---------|---------|---------|
    read_write_test! {
        ualigned_offset_len_partial_intra_block,
        1,
        BLOCK_SIZE - 2,
        0,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE
    }

    // Same sets of test cases but with an additional block added to `rw_offset`
    read_write_test! {
        aligned_all_extra_offset,
        BLOCK_SIZE,
        STORAGE,
        0,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE + BLOCK_SIZE
    }
    read_write_test! {
        aligned_offset_uanligned_size_extra_offset,
        BLOCK_SIZE,
        STORAGE - 1,
        0,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE + BLOCK_SIZE
    }
    read_write_test! {
        aligned_offset_intra_block_extra_offset,
        BLOCK_SIZE,
        BLOCK_SIZE - 1,
        0,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE + BLOCK_SIZE
    }
    read_write_test! {
        unaligned_offset_aligned_end_extra_offset,
        BLOCK_SIZE + 1,
        STORAGE - 1,
        0,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE + BLOCK_SIZE
    }
    read_write_test! {
        unaligned_offset_len_extra_offset,
        BLOCK_SIZE + 1,
        STORAGE - 2,
        0,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE + BLOCK_SIZE
    }
    read_write_test! {
        unaligned_offset_len_partial_cross_block_extra_offset,
        BLOCK_SIZE + 1,
        BLOCK_SIZE,
        0,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE + BLOCK_SIZE
    }
    read_write_test! {
        ualigned_offset_len_partial_intra_block_extra_offset,
        BLOCK_SIZE + 1,
        BLOCK_SIZE - 2,
        0,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE + BLOCK_SIZE
    }

    // Same sets of test cases but with unaligned output buffer {'misALIGNMENT` != 0}
    read_write_test! {
        aligned_all_unaligned_buffer,
        0,
        STORAGE,
        1,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE
    }
    read_write_test! {
        aligned_offset_uanligned_size_unaligned_buffer,
        0,
        STORAGE - 1,
        1,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE
    }
    read_write_test! {
        aligned_offset_intra_block_unaligned_buffer,
        0,
        BLOCK_SIZE - 1,
        1,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE
    }
    read_write_test! {
        unaligned_offset_aligned_end_unaligned_buffer,
        1,
        STORAGE - 1,
        1,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE
    }
    read_write_test! {
        unaligned_offset_len_unaligned_buffer,
        1,
        STORAGE - 2,
        1,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE
    }
    read_write_test! {
        unaligned_offset_len_partial_cross_block_unaligned_buffer,
        1,
        BLOCK_SIZE,
        1,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE
    }
    read_write_test! {
        ualigned_offset_len_partial_intra_block_unaligned_buffer,
        1,
        BLOCK_SIZE - 2,
        1,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE
    }

    // Special cases where `rw_offset` is not block aligned but buffer aligned. This can
    // trigger some internal optimization code path.
    read_write_test! {
        buffer_aligned_offset_and_len,
        ALIGNMENT,
        STORAGE - ALIGNMENT,
        0,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE
    }
    read_write_test! {
        buffer_aligned_offset,
        ALIGNMENT,
        STORAGE - ALIGNMENT - 1,
        0,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE
    }
    read_write_test! {
        buffer_aligned_offset_aligned_end,
        ALIGNMENT,
        BLOCK_SIZE,
        0,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE
    }
    read_write_test! {
        buffer_aligned_offset_intra_block,
        ALIGNMENT,
        BLOCK_SIZE - ALIGNMENT - 1,
        0,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE
    }

    #[test]
    fn test_no_alignment_require_zero_size_scratch() {
        let mut blk = TestBlockDeviceBuilder::new()
            .set_alignment(1)
            .set_block_size(1)
            .set_max_gpt_entries(0)
            .set_size(1)
            .build();
        assert_eq!(required_scratch_size(blk.info(), 0).unwrap(), 0);
    }

    #[test]
    fn test_scratch_too_small() {
        let storage_size = (TestBlockDeviceBuilder::DEFAULT_BLOCK_SIZE * 3) as usize;
        let scratch_size =
            TestBlockDeviceBuilder::new().set_size(storage_size).build().scratch.len() - 1;
        let mut blk = TestBlockDeviceBuilder::new()
            .set_size(storage_size)
            .set_scratch_size(scratch_size)
            .build();
        let block_size = TestBlockDeviceBuilder::DEFAULT_BLOCK_SIZE;
        assert!(blk.read(0, &mut vec![0u8; block_size.try_into().unwrap()]).is_err());
    }

    #[test]
    fn test_read_overflow() {
        let mut blk = TestBlockDeviceBuilder::new()
            .set_alignment(1)
            .set_block_size(1)
            .set_max_gpt_entries(0)
            .set_size(512)
            .build();
        assert!(blk.read(512, &mut vec![0u8; 1]).is_err());
        assert!(blk.read(0, &mut vec![0u8; 513]).is_err());
    }

    #[test]
    fn test_read_arithmetic_overflow() {
        let mut blk = TestBlockDeviceBuilder::new()
            .set_alignment(1)
            .set_block_size(1)
            .set_max_gpt_entries(0)
            .set_size(512)
            .build();
        assert!(blk.read(u64::MAX, &mut vec![0u8; 1]).is_err());
    }

    #[test]
    fn test_write_overflow() {
        let mut blk = TestBlockDeviceBuilder::new()
            .set_alignment(1)
            .set_block_size(1)
            .set_max_gpt_entries(0)
            .set_size(512)
            .build();
        assert!(blk.write(512, vec![0u8; 1].as_mut_slice()).is_err());
        assert!(blk.write(0, vec![0u8; 513].as_mut_slice()).is_err());
    }

    #[test]
    fn test_write_arithmetic_overflow() {
        let mut blk = TestBlockDeviceBuilder::new()
            .set_alignment(1)
            .set_block_size(1)
            .set_max_gpt_entries(0)
            .set_size(512)
            .build();
        assert!(blk.write(u64::MAX, vec![0u8; 1].as_mut_slice()).is_err());
    }

    #[test]
    fn test_u64_not_narrower_than_usize() {
        // If this ever fails we need to adjust all code for >64 bit pointers and size.
        assert!(size_of::<u64>() >= size_of::<*const u8>());
        assert!(size_of::<u64>() >= size_of::<usize>());
    }
}
