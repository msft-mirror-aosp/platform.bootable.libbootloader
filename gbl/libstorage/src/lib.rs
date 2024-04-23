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
//!     AsBlockDevice, BlockIo, BlockDevice, required_scratch_size,
//! };
//!
//! /// Mocks a block device using a buffer.
//! pub struct RamBlockIo {
//!     storage: std::vec::Vec<u8>,
//! }
//!
//! impl BlockIo for RamBlockIo {
//!     fn block_size(&mut self) -> u64 {
//!         512
//!     }
//!
//!     fn num_blocks(&mut self) -> u64 {
//!         self.storage.len() as u64 / self.block_size()
//!     }
//!
//!     fn alignment(&mut self) -> u64 {
//!         64
//!     }
//!
//!     fn read_blocks(&mut self, blk_offset: u64, out: &mut [u8]) -> bool {
//!         let start = blk_offset * self.block_size();
//!         let end = start + out.len() as u64;
//!         out.clone_from_slice(&self.storage[start as usize..end as usize]);
//!         true
//!     }
//!
//!     fn write_blocks(&mut self, blk_offset: u64, data: &[u8]) -> bool {
//!         let start = blk_offset * self.block_size();
//!         let end = start + data.len() as u64;
//!         self.storage[start as usize..end as usize].clone_from_slice(&data);
//!         true
//!     }
//! }
//!
//! const MAX_GPT_ENTRIES: u64 = 128;
//!
//! let mut ram_block_io = RamBlockIo { storage: vec![0u8; 64 * 1024] };
//! // Prepare a scratch buffer, size calculated with `required_scratch_size()`.
//! let mut scratch =
//!     vec![0u8; required_scratch_size(&mut ram_block_io, MAX_GPT_ENTRIES).unwrap()];
//! // Create a `BlockDevice`
//! let mut ram_block_dev =
//!     BlockDevice::new(&mut ram_block_io, &mut scratch[..], MAX_GPT_ENTRIES);
//!
//! // Read/write with arbitrary range and buffer without worrying about alignment.
//! let mut out = vec![0u8; 1234];
//! ram_block_dev.read(4321, &mut out[..]).unwrap();
//! let mut data = vec![0u8; 5678];
//! // Mutable input. More efficient
//! ram_block_dev.write_mut(8765, data.as_mut_slice()).unwrap();
//! // Immutable input. Works too but not as efficient.
//! ram_block_dev.write(8765, &data).unwrap();
//!
//! // Sync GPT
//! let _ = ram_block_dev.sync_gpt();
//! // Access GPT entries
//! let _ = ram_block_dev.find_partition("some-partition");
//! // Read/Write GPT partitions with arbitrary offset, size, buffer
//! let _ = ram_block_dev.read_gpt_partition("partition", 4321, &mut out[..]);
//! let _ = ram_block_dev.write_gpt_partition_mut("partition", 8765, data.as_mut_slice());
//!
//! // Alterantively, you can also define a custom type that internally owns and binds the
//! // implementation of `BlockIo` and scratch buffer together, and then implement the
//! // `AsBlockDevice` trait. This gives a cleaner management of resources.
//! pub struct OwnedBlockDevice {
//!     io: RamBlockIo,
//!     scratch: std::vec::Vec<u8>,
//! }
//!
//! impl AsBlockDevice for OwnedBlockDevice {
//!     fn with(&mut self, f: &mut dyn FnMut(&mut dyn BlockIo, &mut [u8], u64)) {
//!         f(&mut self.io, &mut self.scratch[..], MAX_GPT_ENTRIES)
//!     }
//! }
//!
//! // `owned_block_dev` has the same APIs as `BlockDevice`.
//! let mut owned_block_dev = OwnedBlockDevice { io: ram_block_io, scratch: scratch };
//! ```

#![cfg_attr(not(test), no_std)]

use core::cmp::min;

// Selective export of submodule types.
mod gpt;
use gpt::Gpt;
pub use gpt::{GptEntry, GPT_NAME_LEN_U16};

use safemath::SafeNum;

mod multi_blocks;
pub use multi_blocks::AsMultiBlockDevices;

/// The type of Result used in this library.
pub type Result<T> = core::result::Result<T, StorageError>;

/// Error code for this library.
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum StorageError {
    ArithmeticOverflow(safemath::Error),
    BlockDeviceNotFound,
    BlockIoError,
    BlockIoNotProvided,
    FailedGettingBlockDevices(Option<&'static str>),
    InvalidInput,
    NoValidGpt,
    NotExist,
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

impl core::fmt::Display for StorageError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            StorageError::ArithmeticOverflow(e) => write!(f, "Arithmetic overflow {:?}", e),
            StorageError::BlockDeviceNotFound => write!(f, "Block device not found"),
            StorageError::BlockIoError => write!(f, "Block IO error"),
            StorageError::BlockIoNotProvided => write!(f, "Block IO is not provided"),
            StorageError::FailedGettingBlockDevices(v) => {
                write!(f, "Failed to iterate all block devices {:?}", v)
            }
            StorageError::InvalidInput => write!(f, "Invalid input"),
            StorageError::NoValidGpt => write!(f, "GPT not found"),
            StorageError::NotExist => write!(f, "The specified partition could not be found"),
            StorageError::OutOfRange => write!(f, "Out of range"),
            StorageError::PartitionNotUnique => {
                write!(f, "Partition is found on multiple block devices")
            }
            StorageError::ScratchTooSmall => write!(f, "Not enough scratch buffer"),
        }
    }
}

/// `BlockIo` contains methods for reading/writing blocks of data to a block device with aligned
/// input/output buffers.
pub trait BlockIo {
    /// Returns the block size of the block device.
    fn block_size(&mut self) -> u64;

    /// Returns the total number of blocks of the block device.
    fn num_blocks(&mut self) -> u64;

    /// Returns the alignment requirement for buffers passed to the `write_blocks()` and
    /// `read_blocks()` methods. For example, many block device drivers use DMA for data transfer,
    /// which typically requires that the buffer address for DMA be aligned to 16/32/64 bytes etc.
    /// If the block device has no alignment requirement, it can return 1.
    fn alignment(&mut self) -> u64;

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
    fn read_blocks(&mut self, blk_offset: u64, out: &mut [u8]) -> bool;

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
    fn write_blocks(&mut self, blk_offset: u64, data: &[u8]) -> bool;
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

/// `PartitionIterator` is returned by `AsBlockDevice::partition_iter()` and can be used to iterate
/// all GPT partition entries.
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
                    .map(|v| Partition::new(*v, io.block_size())))
            },
        )
        .ok()?
        .ok()??;
        self.idx += 1;
        Some(res)
    }
}

/// `AsBlockDevice` provides APIs for reading raw block content and GPT partitions with
/// arbirary offset, size and input/output buffer.
pub trait AsBlockDevice {
    /// Runs the provided closure `f` with the following parameters:
    ///
    ///   1. An implementation of block IO `&mut dyn BlockIo`.
    ///   2. A scratch buffer `&mut [u8]`.
    ///   3. A `u64` specifying the maximum allowed number of GPT entries.
    ///
    /// * The scratch buffer is internally used for two purposes: 1. to handle read/write with
    ///   offset, size that are not multiples of block size or input/output buffer that are not
    ///   aligned, and 2. to load and sync GPT headers.
    ///
    /// * The necessary size for the scratch buffer depends on `BlockIo:alignment()`,
    ///   `BlockIo:block_size()` and maximum allowed GPT entries. It can be computed using the
    ///   helper API `required_scratch_size()`. If maximum allowed GPT entries is 0, GPT is
    ///   considered unavailable and no buffer will be reserved for GPT headers. If additionally,
    ///   `BlockIo` has no alignment requirement, i.e. both alignment and block size are 1, the
    ///   total required scratch size is 0.
    ///
    /// * GPT headers will be cached in the scratch buffer after calling `Self::sync_gpt()` and
    ///   returning success. Subsequent call of `Self:read_gpt_partiton()`,
    ///   `Self::write_gpt_partition()`, and `Self::write_gpt_partition_mut()`
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
    fn with(&mut self, f: &mut dyn FnMut(&mut dyn BlockIo, &mut [u8], u64));

    /// Returns the block size of the underlying `BlockIo`
    fn block_size(&mut self) -> Result<u64> {
        with_partitioned_scratch(self, |io, _, _, _| io.block_size())
    }

    /// Returns the number of blocks of the underlying `BlockIo`
    fn num_blocks(&mut self) -> Result<u64> {
        with_partitioned_scratch(self, |io, _, _, _| io.num_blocks())
    }

    /// Returns the total size in number of bytes.
    fn total_size(&mut self) -> Result<u64> {
        Ok((SafeNum::from(self.block_size()?) * self.num_blocks()?).try_into()?)
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
        with_partitioned_scratch(self, |io, alignment, _, _| read(io, offset, out, alignment))?
    }

    /// Write data to the device.
    ///
    /// # Args
    ///
    /// * `offset`: Offset in number of bytes.
    ///
    /// * `data`: Data to write.
    ///
    /// * If offset`/`data.len()` is not aligned to `Self::block_size()`
    ///   or data.as_ptr() is not aligned to `Self::alignment()`, the API may
    ///   reduce to a block by block read-modify-write in the worst case, which can be inefficient.
    ///
    /// * Returns success when exactly `data.len()` number of bytes are written.
    fn write(&mut self, offset: u64, data: &[u8]) -> Result<()> {
        with_partitioned_scratch(self, |io, alignment_scratch, _, _| {
            write_bytes(io, offset, data, alignment_scratch)
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
    fn write_mut(&mut self, offset: u64, data: &mut [u8]) -> Result<()> {
        with_partitioned_scratch(self, |io, alignment_scratch, _, _| {
            write_bytes_mut(io, offset, data, alignment_scratch)
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
            gpt::gpt_sync(
                io,
                &mut Gpt::new_from_buffer(max_entries, gpt_buffer)?,
                alignment_scratch,
            )
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
                io.block_size(),
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
        with_partitioned_scratch(self, |io, alignment_scratch, gpt_buffer, _| {
            gpt::read_gpt_partition(
                io,
                &mut Gpt::from_existing(gpt_buffer)?,
                part_name,
                offset,
                out,
                alignment_scratch,
            )
        })?
    }

    /// Write a GPT partition on a block device
    ///
    /// # Args
    ///
    /// * `part_name`: Name of the partition.
    ///
    /// * `offset`: Offset in number of bytes into the partition.
    ///
    /// * `data`: Data to write. See `data` passed to `BlockIo::write()` for details.
    ///
    /// # Returns
    ///
    /// Returns success when exactly `data.len()` of bytes are written successfully.
    fn write_gpt_partition(&mut self, part_name: &str, offset: u64, data: &[u8]) -> Result<()> {
        with_partitioned_scratch(self, |io, alignment_scratch, gpt_buffer, _| {
            gpt::write_gpt_partition(
                io,
                &mut Gpt::from_existing(gpt_buffer)?,
                part_name,
                offset,
                data,
                alignment_scratch,
            )
        })?
    }

    /// Write a GPT partition on a block device.
    /// Optimization for mutable buffers.
    /// See `AsBlockDevice::write_mut` for details on alignment requirements
    /// for optimized performance.
    ///
    /// # Args
    ///
    /// * `part_name`: Name of the partition.
    ///
    /// * `offset`: Offset in number of bytes into the partition.
    ///
    /// * `data`: Data to write. See `data` passed to `BlockIo::write()` for details.
    ///
    /// # Returns
    ///
    /// Returns success when exactly `data.len()` of bytes are written successfully.
    fn write_gpt_partition_mut(
        &mut self,
        part_name: &str,
        offset: u64,
        data: &mut [u8],
    ) -> Result<()> {
        with_partitioned_scratch(self, |io, alignment_scratch, gpt_buffer, _| {
            gpt::write_gpt_partition_mut(
                io,
                &mut Gpt::from_existing(gpt_buffer)?,
                part_name,
                offset,
                data.into(),
                alignment_scratch,
            )
        })?
    }
}

impl<T: ?Sized + AsBlockDevice> AsBlockDevice for &mut T {
    fn with(&mut self, f: &mut dyn FnMut(&mut dyn BlockIo, &mut [u8], u64)) {
        (*self).with(f)
    }
}

/// `BlockDevice` borrows a `BlockIo`, scratch buffer and implements `AsBlockDevice`.
pub struct BlockDevice<'a, 'b> {
    io: &'a mut dyn BlockIo,
    scratch: &'b mut [u8],
    max_gpt_entries: u64,
}

impl<'a, 'b> BlockDevice<'a, 'b> {
    pub fn new(io: &'a mut dyn BlockIo, scratch: &'b mut [u8], max_gpt_entries: u64) -> Self {
        Self { io, scratch, max_gpt_entries }
    }
}

impl AsBlockDevice for BlockDevice<'_, '_> {
    fn with(&mut self, f: &mut dyn FnMut(&mut dyn BlockIo, &mut [u8], u64)) {
        f(self.io, self.scratch, self.max_gpt_entries)
    }
}

/// Calculates the required scratch buffer size for a `BlockIo` and number of maximum GPT entries.
pub fn required_scratch_size(
    io: &mut (impl BlockIo + ?Sized),
    max_gpt_entries: u64,
) -> Result<usize> {
    let alignment_size: SafeNum = alignment_scratch_size(io)?.into();
    let gpt_buffer_size = match max_gpt_entries {
        0 => 0,
        v => Gpt::required_buffer_size(v)?,
    };
    (alignment_size + gpt_buffer_size).try_into().map_err(|e: safemath::Error| e.into())
}

/// A helper that wraps `AsBlockDevice::with` and additionally partitions the scratch buffer into
/// alignment scratch and GPT buffers.
pub(crate) fn with_partitioned_scratch<F, R>(
    dev: &mut (impl AsBlockDevice + ?Sized),
    mut f: F,
) -> Result<R>
where
    F: FnMut(&mut dyn BlockIo, &mut [u8], &mut [u8], u64) -> R,
{
    let mut res: Result<R> = Err(StorageError::BlockIoNotProvided);
    dev.with(&mut |io, scratch, max_entries| {
        res = (|| {
            if scratch.len() < required_scratch_size(io, max_entries)? {
                return Err(StorageError::ScratchTooSmall);
            }
            let (alignment, gpt) = scratch.split_at_mut(alignment_scratch_size(io)?);
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
fn check_range(
    blk_io: &mut (impl BlockIo + ?Sized),
    offset: u64,
    buffer: &[u8],
) -> Result<SafeNum> {
    let offset: SafeNum = offset.into();
    let block_size: SafeNum = blk_io.block_size().into();
    debug_assert!(is_aligned(offset, block_size)?);
    debug_assert!(is_aligned(buffer.len().into(), block_size)?);
    debug_assert!(is_buffer_aligned(buffer, blk_io.alignment().into())?);
    let blk_offset = offset / block_size;
    let blk_count = SafeNum::from(buffer.len()) / block_size;
    match u64::try_from(blk_offset + blk_count)? <= blk_io.num_blocks() {
        true => Ok(blk_offset),
        false => Err(StorageError::OutOfRange),
    }
}

/// Read with block-aligned offset, length and aligned buffer
fn read_aligned_all(
    blk_io: &mut (impl BlockIo + ?Sized),
    offset: u64,
    out: &mut [u8],
) -> Result<()> {
    let blk_offset = check_range(blk_io, offset, out).map(u64::try_from)??;
    if blk_io.read_blocks(blk_offset, out) {
        return Ok(());
    }
    Err(StorageError::BlockIoError)
}

/// Read with block-aligned offset and aligned buffer. Size don't need to be block aligned.
///   |~~~~~~~~~read~~~~~~~~~|
///   |---------|---------|---------|
fn read_aligned_offset_and_buffer(
    blk_io: &mut (impl BlockIo + ?Sized),
    offset: u64,
    out: &mut [u8],
    scratch: &mut [u8],
) -> Result<()> {
    let block_size = SafeNum::from(blk_io.block_size());
    debug_assert!(is_aligned(offset.into(), block_size)?);
    debug_assert!(is_buffer_aligned(out, blk_io.alignment())?);

    let aligned_read: usize = SafeNum::from(out.len()).round_down(block_size).try_into()?;

    if aligned_read > 0 {
        read_aligned_all(blk_io, offset, &mut out[..aligned_read])?;
    }
    let unaligned = &mut out[aligned_read..];
    if unaligned.is_empty() {
        return Ok(());
    }
    // Read unalinged part.
    let block_scratch = &mut scratch[..block_size.try_into()?];
    let aligned_offset = SafeNum::from(offset) + aligned_read;
    read_aligned_all(blk_io, aligned_offset.try_into()?, block_scratch)?;
    unaligned.clone_from_slice(&block_scratch[..unaligned.len()]);
    Ok(())
}

/// Read with aligned buffer. Offset and size don't need to be block aligned.
/// Case 1:
///            |~~~~~~read~~~~~~~|
///        |------------|------------|
/// Case 2:
///          |~~~read~~~|
///        |---------------|--------------|
fn read_aligned_buffer(
    blk_io: &mut (impl BlockIo + ?Sized),
    offset: u64,
    out: &mut [u8],
    scratch: &mut [u8],
) -> Result<()> {
    debug_assert!(is_buffer_aligned(out, blk_io.alignment())?);

    if is_aligned(offset.into(), blk_io.block_size().into())? {
        return read_aligned_offset_and_buffer(blk_io, offset, out, scratch);
    }
    let offset = SafeNum::from(offset);
    let aligned_start: u64 =
        min(offset.round_up(blk_io.block_size()).try_into()?, (offset + out.len()).try_into()?);

    let aligned_relative_offset: usize = (SafeNum::from(aligned_start) - offset).try_into()?;
    if aligned_relative_offset < out.len() {
        if is_buffer_aligned(&out[aligned_relative_offset..], blk_io.alignment())? {
            // If new output address is aligned, read directly.
            read_aligned_offset_and_buffer(
                blk_io,
                aligned_start,
                &mut out[aligned_relative_offset..],
                scratch,
            )?;
        } else {
            // Otherwise read into `out` (assumed aligned) and memmove to the correct
            // position
            let read_len: usize =
                (SafeNum::from(out.len()) - aligned_relative_offset).try_into()?;
            read_aligned_offset_and_buffer(blk_io, aligned_start, &mut out[..read_len], scratch)?;
            out.copy_within(..read_len, aligned_relative_offset);
        }
    }

    // Now read the unaligned part
    let block_scratch = &mut scratch[..SafeNum::from(blk_io.block_size()).try_into()?];
    let round_down_offset = offset.round_down(blk_io.block_size());
    read_aligned_all(blk_io, round_down_offset.try_into()?, block_scratch)?;
    let offset_relative = offset - round_down_offset;
    let unaligned = &mut out[..aligned_relative_offset];
    unaligned.clone_from_slice(
        &block_scratch
            [offset_relative.try_into()?..(offset_relative + unaligned.len()).try_into()?],
    );
    Ok(())
}

/// Calculates the necessary scratch buffer size for handling block and buffer misalignment.
pub fn alignment_scratch_size(blk_io: &mut (impl BlockIo + ?Sized)) -> Result<usize> {
    let block_alignment = match blk_io.block_size() {
        1 => 0,
        v => v,
    };
    ((SafeNum::from(blk_io.alignment()) - 1) * 2 + block_alignment)
        .try_into()
        .map_err(|e: safemath::Error| e.into())
}

/// Gets a subslice of the given slice with aligned address according to `alignment`
fn aligned_subslice(buffer: &mut [u8], alignment: u64) -> Result<&mut [u8]> {
    let addr = SafeNum::from(buffer.as_ptr() as usize);
    Ok(&mut buffer[(addr.round_up(alignment) - addr).try_into()?..])
}

// Partition a scratch into two aligned parts: [u8; alignment()-1] and [u8; block_size())]
// for handling block and buffer misalignment respecitvely.
fn split_scratch<'a>(
    blk_io: &mut (impl BlockIo + ?Sized),
    scratch: &'a mut [u8],
) -> Result<(&'a mut [u8], &'a mut [u8])> {
    let (buffer_alignment, block_alignment) = aligned_subslice(scratch, blk_io.alignment())?
        .split_at_mut((SafeNum::from(blk_io.alignment()) - 1).try_into()?);
    let block_alignment = aligned_subslice(block_alignment, blk_io.alignment())?;
    let block_alignment_scratch_size = match blk_io.block_size() {
        1 => SafeNum::ZERO,
        v => v.into(),
    };
    Ok((buffer_alignment, &mut block_alignment[..block_alignment_scratch_size.try_into()?]))
}

/// Read with no alignment requirement.
fn read(
    blk_io: &mut (impl BlockIo + ?Sized),
    offset: u64,
    out: &mut [u8],
    scratch: &mut [u8],
) -> Result<()> {
    let (buffer_alignment_scratch, block_alignment_scratch) = split_scratch(blk_io, scratch)?;

    if is_buffer_aligned(out, blk_io.alignment())? {
        return read_aligned_buffer(blk_io, offset, out, block_alignment_scratch);
    }

    // Buffer misalignment:
    // Case 1:
    //     |~~~~~~~~~~~~buffer~~~~~~~~~~~~|
    //   |----------------------|---------------------|
    //      blk_io.alignment()
    //
    // Case 2:
    //    |~~~~~~buffer~~~~~|
    //  |----------------------|---------------------|
    //     blk_io.alignment()

    let out_addr_value = SafeNum::from(out.as_ptr() as usize);
    let unaligned_read: usize =
        min((out_addr_value.round_up(blk_io.alignment()) - out_addr_value).try_into()?, out.len());

    // Read unaligned part
    let unaligned_out = &mut buffer_alignment_scratch[..unaligned_read];
    read_aligned_buffer(blk_io, offset, unaligned_out, block_alignment_scratch)?;
    out[..unaligned_read].clone_from_slice(unaligned_out);

    if unaligned_read == out.len() {
        return Ok(());
    }
    // Read aligned part
    read_aligned_buffer(
        blk_io,
        (SafeNum::from(offset) + unaligned_read).try_into()?,
        &mut out[unaligned_read..],
        block_alignment_scratch,
    )
}

fn write_aligned_all(blk_io: &mut (impl BlockIo + ?Sized), offset: u64, data: &[u8]) -> Result<()> {
    let blk_offset = check_range(blk_io, offset, data)?;
    if blk_io.write_blocks(blk_offset.try_into()?, data) {
        return Ok(());
    }
    Err(StorageError::BlockIoError)
}

/// Write with block-aligned offset and aligned buffer. `data.len()` can be unaligned.
///   |~~~~~~~~~size~~~~~~~~~|
///   |---------|---------|---------|
fn write_aligned_offset_and_buffer(
    blk_io: &mut (impl BlockIo + ?Sized),
    offset: u64,
    data: &[u8],
    scratch: &mut [u8],
) -> Result<()> {
    debug_assert!(is_aligned(offset.into(), blk_io.block_size().into())?);
    debug_assert!(is_buffer_aligned(data, blk_io.alignment())?);

    let aligned_write: usize =
        SafeNum::from(data.len()).round_down(blk_io.block_size()).try_into()?;
    if aligned_write > 0 {
        write_aligned_all(blk_io, offset, &data[..aligned_write])?;
    }
    let unaligned = &data[aligned_write..];
    if unaligned.len() == 0 {
        return Ok(());
    }

    // Perform read-modify-write for the unaligned part
    let unaligned_start: u64 = (SafeNum::from(offset) + aligned_write).try_into()?;
    let block_scratch = &mut scratch[..SafeNum::from(blk_io.block_size()).try_into()?];
    read_aligned_all(blk_io, unaligned_start, block_scratch)?;
    block_scratch[..unaligned.len()].clone_from_slice(unaligned);
    write_aligned_all(blk_io, unaligned_start, block_scratch)
}

/// Write data to the device with immutable input bytes slice. However, if `offset`/`data.len()`
/// is not aligned to `blk_io.block_size()` or data.as_ptr() is not aligned to
/// `blk_io.alignment()`, the API may reduce to a block by block read-modify-write in the worst
/// case.
fn write_bytes(
    blk_io: &mut (impl BlockIo + ?Sized),
    offset: u64,
    data: &[u8],
    scratch: &mut [u8],
) -> Result<()> {
    let (_, block_scratch) = split_scratch(blk_io, scratch)?;
    let block_size = SafeNum::from(blk_io.block_size());
    let mut data_offset = SafeNum::ZERO;
    let mut offset = SafeNum::from(offset);
    while usize::try_from(data_offset)? < data.len() {
        if is_aligned(offset, block_size)?
            && is_buffer_aligned(&data[data_offset.try_into()?..], blk_io.alignment())?
        {
            return write_aligned_offset_and_buffer(
                blk_io,
                offset.try_into()?,
                &data[data_offset.try_into()?..],
                block_scratch,
            );
        }

        let block_offset = offset.round_down(block_size);
        let copy_offset = offset - block_offset;
        let copy_size =
            min(data[data_offset.try_into()?..].len(), (block_size - copy_offset).try_into()?);
        if copy_size < block_size.try_into()? {
            // Partial block copy. Perform read-modify-write
            read_aligned_all(blk_io, block_offset.try_into()?, block_scratch)?;
        }
        block_scratch[copy_offset.try_into()?..(copy_offset + copy_size).try_into()?]
            .clone_from_slice(
                &data[data_offset.try_into()?..(data_offset + copy_size).try_into()?],
            );
        write_aligned_all(blk_io, block_offset.try_into()?, block_scratch)?;
        data_offset += copy_size;
        offset += copy_size;
    }

    Ok(())
}

/// Swap the position of sub segment [0..pos] and [pos..]
fn swap_slice(slice: &mut [u8], pos: usize) {
    let (left, right) = slice.split_at_mut(pos);
    left.reverse();
    right.reverse();
    slice.reverse();
}

/// Write with aligned buffer. Offset and size don't need to be block aligned.
/// Case 1:
///            |~~~~~~write~~~~~~~|
///        |------------|------------|
/// Case 2:
///          |~~~write~~~|
///        |---------------|--------------|
fn write_aligned_buffer(
    blk_io: &mut (impl BlockIo + ?Sized),
    offset: u64,
    data: &mut [u8],
    scratch: &mut [u8],
) -> Result<()> {
    debug_assert!(is_buffer_aligned(data, blk_io.alignment())?);

    let offset = SafeNum::from(offset);
    if is_aligned(offset, blk_io.block_size().into())? {
        return write_aligned_offset_and_buffer(blk_io, offset.try_into()?, data, scratch);
    }

    let aligned_start: u64 =
        min(offset.round_up(blk_io.block_size()).try_into()?, (offset + data.len()).try_into()?);
    let aligned_relative_offset: usize = (SafeNum::from(aligned_start) - offset).try_into()?;
    if aligned_relative_offset < data.len() {
        if is_buffer_aligned(&data[aligned_relative_offset..], blk_io.alignment())? {
            // If new address is aligned, write directly.
            write_aligned_offset_and_buffer(
                blk_io,
                aligned_start,
                &data[aligned_relative_offset..],
                scratch,
            )?;
        } else {
            let write_len: usize =
                (SafeNum::from(data.len()) - aligned_relative_offset).try_into()?;
            // Swap the offset-aligned part to the beginning of the buffer (assumed aligned)
            swap_slice(data, aligned_relative_offset);
            let res =
                write_aligned_offset_and_buffer(blk_io, aligned_start, &data[..write_len], scratch);
            // Swap the two parts back before checking the result.
            swap_slice(data, write_len);
            res?;
        }
    }

    // perform read-modify-write for the unaligned part.
    let block_scratch = &mut scratch[..SafeNum::from(blk_io.block_size()).try_into()?];
    let round_down_offset: u64 = offset.round_down(blk_io.block_size()).try_into()?;
    read_aligned_all(blk_io, round_down_offset, block_scratch)?;
    let offset_relative = offset - round_down_offset;
    block_scratch
        [offset_relative.try_into()?..(offset_relative + aligned_relative_offset).try_into()?]
        .clone_from_slice(&data[..aligned_relative_offset]);
    write_aligned_all(blk_io, round_down_offset, block_scratch)
}

/// Same as write_bytes(). Expcet that the API takes a mutable input bytes slice instead.
/// It does internal optimization that temporarily modifies `data` layout to minimize number of
/// calls to `blk_io.read_blocks()`/`blk_io.write_blocks()` (down to O(1)).
fn write_bytes_mut(
    blk_io: &mut (impl BlockIo + ?Sized),
    offset: u64,
    data: &mut [u8],
    scratch: &mut [u8],
) -> Result<()> {
    let (buffer_alignment_scratch, block_alignment_scratch) = split_scratch(blk_io, scratch)?;
    if is_buffer_aligned(data, blk_io.alignment())? {
        return write_aligned_buffer(blk_io, offset, data, block_alignment_scratch);
    }

    // Buffer misalignment:
    // Case 1:
    //     |~~~~~~~~~~~~buffer~~~~~~~~~~~~|
    //   |----------------------|---------------------|
    //      blk_io.alignment()
    //
    // Case 2:
    //    |~~~~~~buffer~~~~~|
    //  |----------------------|---------------------|
    //     blk_io.alignment()

    // Write unaligned part
    let data_addr_value = SafeNum::from(data.as_ptr() as usize);
    let unaligned_write: usize = min(
        (data_addr_value.round_up(blk_io.alignment()) - data_addr_value).try_into()?,
        data.len(),
    );
    let mut unaligned_data = &mut buffer_alignment_scratch[..unaligned_write];
    unaligned_data.clone_from_slice(&data[..unaligned_write]);
    write_aligned_buffer(blk_io, offset, &mut unaligned_data, block_alignment_scratch)?;
    if unaligned_write == data.len() {
        return Ok(());
    }

    // Write aligned part
    write_aligned_buffer(
        blk_io,
        (SafeNum::from(offset) + unaligned_write).try_into()?,
        &mut data[unaligned_write..],
        block_alignment_scratch,
    )
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

    /// Upper bound on the number of `BlockIo::read_blocks()/write_blocks()` calls by
    /// `AsBlockDevice::read()` and `AsBlockDevice::write()` with mutable input buffer.
    ///
    /// * `fn read_aligned_all()`: At most 1 call to `BlockIo::read_blocks()`.
    /// * `fn read_aligned_offset_and_buffer()`: At most 2 calls to `read_aligned_all()`.
    /// * `fn read_aligned_buffer()`: At most 1 call to `read_aligned_offset_and_buffer()` plus 1
    ///   call to `BlockIo::read_blocks()`.
    /// * `fn read()`: At most 2 calls to `read_aligned_buffer()`.
    ///
    /// Analysis is similar for `fn write()`.
    const READ_WRITE_BLOCKS_UPPER_BOUND: usize = 6;

    fn read_test_helper(case: &TestCase) {
        let mut blk = TestBlockDeviceBuilder::new()
            .set_alignment(case.alignment)
            .set_block_size(case.block_size)
            .set_size(case.storage_size as usize)
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
        let mut blk = TestBlockDeviceBuilder::new()
            .set_alignment(case.alignment)
            .set_block_size(case.block_size)
            .set_size(case.storage_size as usize)
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

                // Input bytes slice is an immutable reference
                #[test]
                fn write_test() {
                    let func = |blk: &mut TestBlockDevice, offset: u64, data: &mut [u8]| {
                        blk.write(offset, data).unwrap();
                    };
                    write_test_helper(&TestCase::new($x0, $x1, $x2, $x3, $x4, $x5), func);
                }

                #[test]
                fn write_scaled_test() {
                    // Scaled all parameters by double and test again.
                    let func = |blk: &mut TestBlockDevice, offset: u64, data: &mut [u8]| {
                        blk.write(offset, data).unwrap();
                    };
                    let (x0, x1, x2, x3, x4, x5) =
                        (2 * $x0, 2 * $x1, 2 * $x2, 2 * $x3, 2 * $x4, 2 * $x5);
                    write_test_helper(&TestCase::new(x0, x1, x2, x3, x4, x5), func);
                }

                // Input bytes slice is a mutable reference
                #[test]
                fn write_mut_test() {
                    let func = |blk: &mut TestBlockDevice, offset: u64, data: &mut [u8]| {
                        blk.write_mut(offset, data).unwrap();
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
                        blk.write_mut(offset, data).unwrap();
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
        assert_eq!(required_scratch_size(&mut blk.io, 0).unwrap(), 0);
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
        assert!(blk.write_mut(512, vec![0u8; 1].as_mut_slice()).is_err());
        assert!(blk.write_mut(0, vec![0u8; 513].as_mut_slice()).is_err());

        assert!(blk.write(512, &vec![0u8; 1]).is_err());
        assert!(blk.write(0, &vec![0u8; 513]).is_err());
    }

    #[test]
    fn test_write_arithmetic_overflow() {
        let mut blk = TestBlockDeviceBuilder::new()
            .set_alignment(1)
            .set_block_size(1)
            .set_max_gpt_entries(0)
            .set_size(512)
            .build();
        assert!(blk.write_mut(u64::MAX, vec![0u8; 1].as_mut_slice()).is_err());
        assert!(blk.write(u64::MAX, &vec![0u8; 1]).is_err());
    }

    #[test]
    fn test_u64_not_narrower_than_usize() {
        // If this ever fails we need to adjust all code for >64 bit pointers and size.
        assert!(size_of::<u64>() >= size_of::<*const u8>());
        assert!(size_of::<u64>() >= size_of::<usize>());
    }
}
