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

//! The library provides APIs for reading/writing with block devices with arbitrary alignment,
//! ranges and parsing and manipulation GPT.

#![cfg_attr(not(test), no_std)]
#![allow(async_fn_in_trait)]

extern crate alloc;
use arrayvec::ArrayVec;
use bytes::buf::UninitSlice;
use core::{
    cmp::min,
    iter,
    ops::{Bound, Deref, DerefMut, Index, IndexMut, RangeBounds},
};
use gbl_async::{block_on, yield_now};
use liberror::{Error, Result};
use libutils::{
    aligned_subslice,
    buffer_pool::{BufferPool, PoolRef},
    shared::Shared,
};
use safemath::SafeNum;

// Selective export of submodule types.
mod gpt;
pub use gpt::{
    gpt_buffer_size, new_gpt_max, new_gpt_n, Gpt, GptBuilder, GptEntry, GptGuid, GptHeader,
    GptLoadBufferN, GptMax, GptN, GptSyncResult, Partition, PartitionIterator, GPT_GUID_LEN,
    GPT_MAGIC, GPT_MAX_NUM_ENTRIES, GPT_MIN_NUM_ENTRIES, GPT_NAME_LEN_U16,
};

mod algorithm;
use algorithm::{erase_async, read_async, write_async};

pub mod ram_block;
pub use ram_block::RamBlockIo;

/// Provides checked indexing for a type which only has `[]`-style indexing.
///
/// This allows us to handle errors on index overflow rather than panicking.
pub trait CheckedGet<T>: Index<T> + IndexMut<T>
where
    T: RangeBounds<usize>,
{
    /// Returns the buffer length.
    fn len(&self) -> usize;

    /// Returns the slice or [Error].
    fn get(&self, index: T) -> Result<&Self::Output> {
        self.check_index(&index)?;
        Ok(&self[index])
    }

    /// Returns the slice or [Error].
    fn get_mut(&mut self, index: T) -> Result<&mut Self::Output> {
        self.check_index(&index)?;
        Ok(&mut self[index])
    }

    /// Returns [Error] if the index is out-of-bounds.
    fn check_index(&self, index: &T) -> Result<()> {
        let required_index = match index.end_bound() {
            Bound::Included(x) => *x,            // [_..=x]
            Bound::Excluded(0) => return Ok(()), // [_..0]
            Bound::Excluded(x) => x - 1,         // [_..x]
            Bound::Unbounded => {
                // When the end bound is unbounded (e.g. [x..]), we need to
                // check the start bound for validity instead.
                //
                // The expected behavior here is that starting just past the end
                // of the object is fine - it produces the empty list - but
                // going past that is an error.
                match index.start_bound() {
                    Bound::Included(0) => return Ok(()), // [0..]
                    Bound::Included(x) => x - 1,         // [x..]
                    Bound::Excluded(x) => *x,            // Non-standard
                    Bound::Unbounded => return Ok(()),   // [..]
                }
            }
        };

        if self.len() > required_index {
            return Ok(());
        }
        Err(Error::BufferTooSmall(Some(required_index + 1)))
    }
}

impl<T> CheckedGet<T> for UninitSlice
where
    UninitSlice: Index<T> + IndexMut<T>,
    T: RangeBounds<usize>,
{
    fn len(&self) -> usize {
        self.len()
    }
}

/// `BlockInfo` contains information for a block device.
#[derive(Copy, Clone, Debug)]
pub struct BlockInfo {
    /// Native block size of the block device.
    pub block_size: u64,
    /// The size of an erase block in number of blocks.
    pub erase_blocks_num: u64,
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

    /// Returns the erase block size in bytes.
    pub fn erase_block_size(&self) -> Result<u64> {
        Ok((SafeNum::from(self.erase_blocks_num) * self.block_size).try_into()?)
    }
}

/// `BlockIo` provides interfaces for reading and writing block storage medium.
///
/// Note for implementors: if an operation is valid,
/// i.e. the block offset and buffer meet the preconditions of the call,
/// but the implementation cannot service the request immediately,
/// the implementation SHOULD return `Err(OutOfResources)`.
///
/// This allows callers to reattempt the operation with the expectation that required
/// resources will eventually become available, e.g. space in a request queue.
///
/// It is possible for the same BlockIo to be used concurrently for multiple requests.
/// It is the responsibility of the implementation to be safe for concurrency.
/// This is normally easy to achieve due to the borrow checker, but care must be taken
/// if an implementation crosses an FFI boundary.
///
/// SAFETY:
/// * `read_blocks` method must guarantee `out` to be fully initialized on success.
///   Otherwise error must be returned.
///   This is necessary because callers are guaranteed that the [UninitSlice] buffer
///   has been fully initialized on success and can safely be converted to a `&[u8]`
///   and read normally.
pub unsafe trait BlockIo {
    /// Returns the `BlockInfo` for this block device.
    fn info(&self) -> BlockInfo;

    /// Read blocks of data from the block device
    ///
    /// # Args
    ///
    /// * `blk_offset`: Offset in number of blocks.
    ///
    /// * `out`: Buffer to store the read data. Callers of this method ensure that it is
    ///   aligned according to alignment() and `out.len()` is multiples of `block_size()`.
    ///
    /// ## `out` buffer type
    ///
    /// The `out` type is a bit odd in that `UninitSlice` doesn't borrow but instead consumes
    /// a reference and transforms it into its own reference. One consequence of this is that if
    /// the caller only has a reference and needs to retain it to use it again, it needs to be
    /// "reborrowed" at the call site:
    ///
    /// ```
    /// # use gbl_storage::BlockIo;
    ///
    /// fn read_twice<'a>(io: &mut impl BlockIo, out: &mut [u8]) {
    ///     // `&mut *` re-borrows so that a temporary copy of the reference is consumed, not
    ///     // the reference itself.
    ///     io.read_blocks(0, &mut *out);
    ///
    ///     // If we hadn't re-borrowed earlier, this would be a use-after-move error.
    ///     io.read_blocks(0, out);
    /// }
    /// ```
    ///
    /// It is possible to avoid this, but the function gets significantly more complicated:
    ///
    /// ```
    /// # use bytes::buf::UninitSlice;
    ///
    /// // 1. The type now requires this "where" clause:
    /// fn foo<'a, T>(buffer: &'a mut T)
    /// where
    ///     T: ?Sized,
    ///     &'a mut UninitSlice: From<&'a mut T>
    /// {
    ///     // 2. Calling `.into()` no longer deduces types automatically - this does not compile:
    ///     // let len = buffer.into().len();
    ///
    ///     // We have to do this instead to convert:
    ///     let len = <&mut UninitSlice>::from(buffer).len();
    /// }
    /// ```
    ///
    /// Currently we have about the same number of functions that use this parameter as we do call
    /// sites that need to re-borrow, so for now we keep the simpler the one-line reborrow.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if exactly out.len() number of bytes are read. In this case only, if the
    /// backing buffer for `out` is [MaybeUninit], then it's safe to convert it to a `&[u8]` and
    /// read the now-initialized data.
    async fn read_blocks<'a>(
        &self,
        blk_offset: u64,
        out: impl Into<&'a mut UninitSlice>,
    ) -> Result<()>;

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
    /// Returns Ok(()) if exactly data.len() number of bytes are written. Otherwise errors.
    async fn write_blocks(&self, blk_offset: u64, data: &mut [u8]) -> Result<()>;

    /// Erases blocks of data on the device.
    ///
    /// # Args
    ///
    /// * `blk_offset`: Offset in number of erase blocks.
    ///
    /// * `num_blks`: number of erase blocks to erase.
    ///
    /// # Returns
    ///
    /// Returns Ok(()) if erase is successful. Error otherwise.
    async fn erase_blocks(&self, blk_offset: u64, num_blks: u64) -> Result<()>;

    /// Same as `Self::read_blocks()` but IO is blocking.
    ///
    /// The default implementation simply calls and blocks `Self::read_blocks` until completion.
    /// In some cases however, non-blocking IO may have non-trivial overhead and platform may prefer
    /// to have separate and optimized implementation for blocking IO use case. This can be provided
    /// by overriding this API.
    fn read_blocks_sync<'a>(
        &self,
        blk_offset: u64,
        out: impl Into<&'a mut UninitSlice>,
    ) -> Result<()> {
        block_on(self.read_blocks(blk_offset, out))
    }

    /// Same as `Self::write_blocks` but IO is blocking
    fn write_blocks_sync(&self, blk_offset: u64, data: &mut [u8]) -> Result<()> {
        block_on(self.write_blocks(blk_offset, data))
    }

    /// Same as `Self::erase_blocks` but IO is blocking
    fn erase_blocks_sync(&self, blk_offset: u64, num_blks: u64) -> Result<()> {
        block_on(self.erase_blocks(blk_offset, num_blks))
    }

    /// Flushes any cached write data to the physical storage device.
    ///
    /// The default implementation is a no-op that returns `Ok(())`.
    async fn flush(&self) -> Result<()> {
        Ok(())
    }

    /// Same as `Self::flush()` but is blocking.
    fn flush_sync(&self) -> Result<()> {
        block_on(self.flush())
    }
}

/// `BlockIoSync` wraps another BlockIo implementation and only uses its blocking IO interface
/// `BlockIo::read_block_sync()` and `BlockIo::write_block_sync()` for implementing its own
/// `BlockIo`.
pub struct BlockIoSync<T>(T);

// SAFETY:
// The implementation simply forwards from another implementation of `BlockIO` which is assumed
// safely implemented.
unsafe impl<T: BlockIo> BlockIo for BlockIoSync<T> {
    fn info(&self) -> BlockInfo {
        self.0.info()
    }

    async fn read_blocks<'a>(
        &self,
        blk_offset: u64,
        out: impl Into<&'a mut UninitSlice>,
    ) -> Result<()> {
        self.0.read_blocks_sync(blk_offset, out)
    }

    async fn write_blocks(&self, blk_offset: u64, data: &mut [u8]) -> Result<()> {
        self.0.write_blocks_sync(blk_offset, data)
    }

    async fn erase_blocks(&self, blk_offset: u64, num_blks: u64) -> Result<()> {
        self.erase_blocks_sync(blk_offset, num_blks)
    }

    async fn flush(&self) -> Result<()> {
        self.0.flush_sync()
    }

    fn flush_sync(&self) -> Result<()> {
        self.0.flush_sync()
    }
}

// SAFETY:
// `read_blocks` method has same guarantees as `BlockIo` implementation of referenced type T.
// Which guarantees `out` to be fully initialized on success.
unsafe impl<T: Deref> BlockIo for T
where
    T::Target: BlockIo,
{
    fn info(&self) -> BlockInfo {
        self.deref().info()
    }

    async fn read_blocks<'a>(
        &self,
        blk_offset: u64,
        out: impl Into<&'a mut UninitSlice>,
    ) -> Result<()> {
        self.deref().read_blocks(blk_offset, out).await
    }

    async fn write_blocks(&self, blk_offset: u64, data: &mut [u8]) -> Result<()> {
        self.deref().write_blocks(blk_offset, data).await
    }

    async fn erase_blocks(&self, blk_offset: u64, num_blks: u64) -> Result<()> {
        self.deref().erase_blocks(blk_offset, num_blks).await
    }

    fn read_blocks_sync<'a>(
        &self,
        blk_offset: u64,
        out: impl Into<&'a mut UninitSlice>,
    ) -> Result<()> {
        self.deref().read_blocks_sync(blk_offset, out)
    }

    fn write_blocks_sync(&self, blk_offset: u64, data: &mut [u8]) -> Result<()> {
        self.deref().write_blocks_sync(blk_offset, data)
    }

    fn erase_blocks_sync(&self, blk_offset: u64, num_blks: u64) -> Result<()> {
        self.deref().erase_blocks_sync(blk_offset, num_blks)
    }

    async fn flush(&self) -> Result<()> {
        self.deref().flush().await
    }

    fn flush_sync(&self) -> Result<()> {
        self.deref().flush_sync()
    }
}

/// An implementation of `BlockIo` of where all required methods are `unimplemented!()`
pub struct BlockIoNull {}

// SAFETY:
// `read_blocks` never succeeds since it is not implemented and will panic.
unsafe impl BlockIo for BlockIoNull {
    fn info(&self) -> BlockInfo {
        unimplemented!();
    }

    async fn read_blocks<'a>(&self, _: u64, _: impl Into<&'a mut UninitSlice>) -> Result<()> {
        unimplemented!();
    }

    async fn write_blocks(&self, _: u64, _: &mut [u8]) -> Result<()> {
        unimplemented!();
    }

    async fn erase_blocks(&self, _: u64, _: u64) -> Result<()> {
        unimplemented!();
    }
}

/// Check if `value` is aligned to (multiples of) `alignment`
/// It can fail if the remainider calculation fails overflow check.
fn is_aligned(value: impl Into<SafeNum>, alignment: impl Into<SafeNum>) -> Result<bool> {
    Ok(u64::try_from(value.into() % alignment.into())? == 0)
}

/// Check if `buffer` address is aligned to `alignment`
/// It can fail if the remainider calculation fails overflow check.
///
/// `buffer` needs to be `mut&` here because there's no way with [UninitSlice]
/// to get the underlying pointer from a const, but this function will not
/// modify `buffer`. This is OK for us because we always have mutable buffers.
fn is_buffer_aligned<'a>(buffer: impl Into<&'a mut UninitSlice>, alignment: u64) -> Result<bool> {
    is_aligned(buffer.into().as_mut_ptr() as usize, alignment)
}

/// Check read/write range and calculate offset in number of blocks.
fn check_range<'a>(
    info: BlockInfo,
    offset: u64,
    buffer: impl Into<&'a mut UninitSlice>,
) -> Result<SafeNum> {
    let offset: SafeNum = offset.into();
    let block_size: SafeNum = info.block_size.into();
    let buffer = buffer.into();
    debug_assert!(is_aligned(offset, block_size)?, "{:?}, {:?}", offset, block_size);
    debug_assert!(is_aligned(buffer.len(), block_size)?);
    debug_assert!(is_buffer_aligned(&mut *buffer, info.alignment)?);
    let blk_offset = offset / block_size;
    let blk_count = SafeNum::from(buffer.len()) / block_size;
    let end: u64 = (blk_offset + blk_count).try_into()?;
    match end <= info.num_blocks {
        true => Ok(blk_offset),
        false => Err(Error::BadIndex(end as usize)),
    }
}

/// Computes the required scratch size for initializing an [AsyncBlockDevice].
pub fn scratch_size(io: &impl BlockIo) -> Result<usize> {
    let info = io.info();
    let block_alignment = match info.block_size {
        1 => 0,
        v => v,
    };
    Ok(((SafeNum::from(info.alignment) - 1) * 2 + block_alignment).try_into()?)
}

/// `Disk` contains a BlockIO and scratch buffer pool and provides APIs for
/// reading/writing with arbitrary ranges and alignment.
pub struct Disk<T, P> {
    io: T,
    pool: Shared<P>,
}

impl<T: BlockIo, const N: usize, B: FromIterator<u8> + DerefMut<Target = [u8]>>
    Disk<T, ArrayVec<Option<B>, N>>
{
    /// Same as `Self::new()` but allocates the necessary scratch buffers.
    pub fn new_alloc_scratch(io: T) -> Result<Self> {
        let scratch_size = scratch_size(&io)?;
        let pool = ArrayVec::from_iter(
            (0..N).map(|_| Some(B::from_iter(iter::repeat(0).take(scratch_size)))),
        );
        Self::new(io, pool)
    }
}

macro_rules! try_until_resources_available {
    ($check:expr) => {
        loop {
            let res = $check.await;
            if res == Err(Error::OutOfResources) {
                yield_now().await;
            } else {
                return res;
            }
        }
    };
}

impl<T: BlockIo, P: BufferPool> Disk<T, P> {
    /// Creates a new instance with the given IO and scratch buffer pool.
    ///
    /// * The scratch buffer pool is internally used for handling partial block
    ///   read/write and unaligned input/output user buffers.
    ///
    /// * The necessary size for the scratch buffers depends on `BlockInfo::alignment`,
    ///   `BlockInfo::block_size`. It can be computed using the helper API `scratch_size()`. If the
    ///   block device has no alignment requirement, i.e. both alignment and block size are 1, the
    ///   total required scratch size is 0.
    pub fn new(io: T, pool: P) -> Result<Self> {
        let scratch_size = scratch_size(&io)?;
        if !pool.check_buffer_sizes(scratch_size) {
            Err(Error::BufferTooSmall(Some(scratch_size)))
        } else {
            Ok(Self { io, pool: pool.into() })
        }
    }

    /// Gets the [BlockInfo]
    pub fn block_info(&self) -> BlockInfo {
        self.io.info()
    }

    /// Gets the underlying BlockIo implementation.
    pub fn io(&self) -> &T {
        &self.io
    }

    /// Gets the underlying BlockIo implementation mutably.
    pub fn io_mut(&mut self) -> &mut T {
        &mut self.io
    }

    /// Reads data from the block device.
    ///
    /// # Args
    ///
    /// * `offset`: Offset in number of bytes.
    /// * `out`: Buffer to store the read data.
    /// * Returns success when exactly `out.len()` number of bytes are read.
    pub async fn read<'a>(&self, offset: u64, out: impl Into<&'a mut UninitSlice>) -> Result<()> {
        let mut scratch = self.pool.allocate_async().await;
        let out = out.into();
        try_until_resources_available!(read_async(&self.io, offset, &mut *out, &mut scratch))
    }

    /// Writes data to the device.
    ///
    /// # Args
    ///
    /// * `offset`: Offset in number of bytes.
    /// * `data`: Data to write.
    ///
    /// # Returns
    ///
    /// * Returns success when exactly `data.len()` number of bytes are written.
    pub async fn write(&self, offset: u64, data: &mut [u8]) -> Result<()> {
        let mut scratch = self.pool.allocate_async().await;
        try_until_resources_available!(write_async(&self.io, offset, data, &mut scratch))
    }

    /// Fills a disk range with the given byte value
    ///
    /// # Args
    ///
    /// * `offset`: Offset in number of bytes.
    /// * `size`: Number of bytes to fill.
    /// * `val`: Fill value.
    /// * `scratch`: A scratch buffer that will be used for writing `val` in batches.
    ///
    /// # Returns
    ///
    /// * Returns Err(Error::InvalidInput) if size of `scratch` is 0.
    pub async fn fill(
        &self,
        mut offset: u64,
        size: u64,
        val: u8,
        scratch: &mut [u8],
    ) -> Result<()> {
        if scratch.is_empty() {
            return Err(Error::InvalidInput);
        }
        let blk_sz = usize::try_from(self.block_info().block_size)?;
        // Optimizes by trying to get an aligned and multi-block-size buffer.
        let buf = match aligned_subslice(scratch, self.block_info().alignment) {
            Ok(v) => match v.len() / blk_sz {
                b if b > 0 => &mut v[..b * blk_sz],
                _ => v,
            },
            _ => scratch,
        };
        let sz = min(size, buf.len().try_into()?);
        buf[..usize::try_from(sz).unwrap()].fill(val);
        let end: u64 = (SafeNum::from(offset) + size).try_into()?;
        while offset < end {
            let to_write = min(sz, end - offset);
            self.write(offset, &mut buf[..usize::try_from(to_write).unwrap()]).await?;
            offset += to_write;
        }
        Ok(())
    }

    /// Performs IO-specific erase.
    ///
    /// # Args
    ///
    /// * `offset`: Offset in number of bytes.
    /// * `size`: Number of bytes erase.
    /// * `erase_scratch`: A scratch buffer that will be used for partial block erase
    ///   when offset and size are not multiples of block size.
    ///   The buffer must be at least the erase block size.
    ///
    ///  # Returns
    ///
    /// * Return Err(Error::BufferTooSmall(_)) if `scratch` is less than block size.
    pub async fn erase(&self, offset: u64, size: u64, erase_scratch: &mut [u8]) -> Result<()> {
        let mut scratch = self.pool.allocate_async().await;
        try_until_resources_available!(erase_async(
            &self.io,
            offset,
            size,
            erase_scratch,
            &mut scratch
        ))
    }

    /// Loads and syncs GPT from a block device.
    ///
    /// The API validates and optionally restores primary/secondary GPT header.
    ///
    /// # Returns
    ///
    /// * Returns Ok(sync_result) if disk IO is successful, where `sync_result` contains the GPT
    ///   verification and restoration result.
    /// * Returns Err() if disk IO encounters errors.
    pub async fn sync_gpt(
        &self,
        gpt: &mut Gpt<impl DerefMut<Target = [u8]>>,
        repair: bool,
    ) -> Result<GptSyncResult> {
        gpt.load_and_sync(self, repair).await
    }

    /// Updates GPT to the block device and sync primary and secondary GPT.
    ///
    /// # Args
    ///
    /// * `mbr_primary`: A buffer containing the MBR block, primary GPT header and entries.
    /// * `resize`: If set to true, the method updates the last partition to cover the rest of the
    ///    storage.
    /// * `gpt`: The GPT to update.
    ///
    /// # Returns
    ///
    /// * Return `Ok(())` if new GPT is valid and device is updated and synced successfully.
    pub async fn update_gpt(
        &self,
        mbr_primary: &mut [u8],
        resize: bool,
        gpt: &mut Gpt<impl DerefMut<Target = [u8]>>,
    ) -> Result<()> {
        gpt::update_gpt(self, mbr_primary, resize, gpt).await
    }

    /// Erases GPT if the disk has one.
    ///
    /// The method will first perform a GPT sync and makes sure that all valid entries are wiped.
    ///
    /// # Args
    ///
    /// * `gpt`: An instance of GPT.
    pub async fn erase_gpt(&self, gpt: &mut Gpt<impl DerefMut<Target = [u8]>>) -> Result<()> {
        gpt::erase_gpt(self, gpt).await
    }

    /// Writes a GPT partition on a block device.
    ///
    ///
    /// # Args
    ///
    /// * `gpt`: A `GptCache` initialized with `Self::sync_gpt()`.
    /// * `part_name`: Name of the partition.
    /// * `offset`: Offset in number of bytes into the partition.
    /// * `data`: Data to write. See `data` passed to `BlockIoSync::write()` for details.
    ///
    /// # Returns
    ///
    /// Returns success when exactly `data.len()` of bytes are written successfully.
    pub async fn write_gpt_partition(
        &self,
        gpt: &mut Gpt<impl DerefMut<Target = [u8]>>,
        part_name: &str,
        offset: u64,
        data: &mut [u8],
    ) -> Result<()> {
        let offset = gpt.check_range(part_name, offset, data.len())?;
        self.write(offset, data).await
    }

    /// Creates a view of self as a purely synchronous disk.
    pub fn as_sync(&self) -> Disk<BlockIoSync<&T>, PoolRef<'_, P>> {
        Disk::new(BlockIoSync(&self.io), PoolRef::new(self.pool.borrow_mut())).unwrap()
    }

    /// Flushes modified data to the physical block device.
    pub async fn flush(&self) -> Result<()> {
        self.io.flush().await
    }

    /// Flushes modified data to the physical block device synchronously.
    pub fn flush_sync(&self) -> Result<()> {
        self.io.flush_sync()
    }
}

impl<T, B: FromIterator<u8> + DerefMut<Target = [u8]>, const N: usize>
    Disk<RamBlockIo<T>, ArrayVec<Option<B>, N>>
where
    T: DerefMut<Target = [u8]>,
{
    /// Creates a new ram disk instance with allocated scratch buffer pool.
    pub fn new_ram_alloc(block_size: u64, alignment: u64, storage: T) -> Result<Self> {
        let ram_blk = RamBlockIo::new(block_size, alignment, storage);
        Self::new_alloc_scratch(ram_blk)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use alloc::boxed::Box;
    use core::ops::Deref;
    use gbl_async::{block_on, join, poll};
    use libtestutils::AlignedBuffer;
    use libutils::constants::KiB;

    use std::slice::SliceIndex;

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

    // Type alias of the [Disk] type used by unittests.
    pub(crate) type TestDisk = Disk<RamBlockIo<Vec<u8>>, ArrayVec<Option<Box<[u8]>>, 2>>;

    /// Helper to test the [CheckedGet] trait on [UninitSlice].
    ///
    /// # Arguments
    ///
    /// * `index`: a slice index that should work on an 8-element [UninitSlice]
    ///            and [u8]
    fn test_checked_get<T>(index: T)
    where
        // These traits are a little hairy, but it's basically just saying that
        // the index should be able to slice both `UninitSlice` and `&[u8]`, and
        // produce the same type as output.
        UninitSlice: Index<T, Output = UninitSlice> + IndexMut<T>,
        T: RangeBounds<usize> + SliceIndex<[u8], Output = [u8]> + Clone,
    {
        // Backing data starts as zeroes.
        let mut data = [0u8; 8];
        let slice = UninitSlice::new(&mut data);

        // Set up different expected data that we will copy in and then verify.
        let expected: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
        let expected = &expected[index.clone()];

        // Non-mutable `UninitSlice` is kind of useless, all you can do is slice
        // it and check the length, so that's all we can test for.
        assert_eq!(slice.get(index.clone()).unwrap().len(), expected.len());

        // Mutable slice is more interesting, but the only safe operation is to
        // copy a &[u8] slice. So our test uses this to modify the underlying
        // bytes, and then verify that they were in fact modified as expected.
        slice.get_mut(index.clone()).unwrap().copy_from_slice(expected);
        assert_eq!(&data[index], expected);
    }

    #[test]
    fn checked_get_exclusive_bounds() {
        test_checked_get(0..8);
        test_checked_get(0..1);
        test_checked_get(7..8);
        test_checked_get(8..8);
    }

    #[test]
    fn checked_get_inclusive_bounds() {
        test_checked_get(0..=7);
        test_checked_get(0..=1);
        test_checked_get(6..=7);
        test_checked_get(7..=7);
    }

    #[test]
    fn checked_get_unbound() {
        test_checked_get(0..);
        test_checked_get(7..);
        test_checked_get(8..);
        test_checked_get(..1);
        test_checked_get(..7);
        test_checked_get(..);
    }

    #[test]
    fn checked_get_out_of_bounds() {
        let mut data = [0u8; 8];
        let slice = UninitSlice::new(&mut data);

        assert_eq!(slice.get(8..10).unwrap_err(), Error::BufferTooSmall(Some(10)));
        assert_eq!(slice.get(9..).unwrap_err(), Error::BufferTooSmall(Some(9)));
        assert_eq!(slice.get(..15).unwrap_err(), Error::BufferTooSmall(Some(15)));
    }

    fn read_test_helper(case: &TestCase) {
        let data = (0..case.storage_size).map(|v| v as u8).collect::<Vec<_>>();
        let disk = TestDisk::new_ram_alloc(case.block_size, case.alignment, data).unwrap();
        // Make an aligned buffer. A misaligned version is created by taking a sub slice that
        // starts at an unaligned offset. Because of this we need to allocate
        // `case.misalignment` more to accommodate it.
        let mut aligned_buf: AlignedBuffer<u8> = AlignedBuffer::new(
            (case.rw_size + case.misalignment).try_into().unwrap(),
            case.alignment.try_into().unwrap(),
        );
        let misalignment = usize::try_from(case.misalignment).unwrap();
        let rw_sz = usize::try_from(case.rw_size).unwrap();
        let out = &mut aligned_buf[misalignment..][..rw_sz];
        block_on(disk.read(case.rw_offset, &mut *out)).unwrap();
        let rw_off = usize::try_from(case.rw_offset).unwrap();
        assert_eq!(out, &disk.io().storage()[rw_off..][..rw_sz], "Failed. Test case {:?}", case);
        assert!(disk.io().num_reads() <= READ_WRITE_BLOCKS_UPPER_BOUND);
    }

    fn write_test_helper(
        case: &TestCase,
        mut write_func: impl FnMut(&mut TestDisk, u64, &mut [u8]),
    ) {
        let data = (0..case.storage_size).map(|v| v as u8).collect::<Vec<_>>();
        // Write a reverse version of the current data.
        let rw_off = usize::try_from(case.rw_offset).unwrap();
        let rw_sz = usize::try_from(case.rw_size).unwrap();
        let mut expected = data[rw_off..][..rw_sz].to_vec();
        expected.reverse();
        let mut disk = TestDisk::new_ram_alloc(case.block_size, case.alignment, data).unwrap();
        // Make an aligned buffer. A misaligned version is created by taking a sub slice that
        // starts at an unaligned offset. Because of this we need to allocate
        // `case.misalignment` more to accommodate it.
        let mut aligned_buf = AlignedBuffer::new(
            (case.rw_size + case.misalignment).try_into().unwrap(),
            case.alignment.try_into().unwrap(),
        );
        let misalignment = usize::try_from(case.misalignment).unwrap();
        let data = &mut aligned_buf[misalignment..][..rw_sz];
        data.clone_from_slice(&expected);
        write_func(&mut disk, case.rw_offset, data);
        let written = &disk.io().storage()[rw_off..][..rw_sz];
        assert_eq!(expected, written, "Failed. Test case {:?}", case);
        // Check that input is not modified.
        assert_eq!(expected, data, "Input is modified. Test case {:?}", case,);
    }

    fn erase_test_helper(case: &TestCase) {
        let data = (0..case.storage_size).map(|v| v as u8).collect::<Vec<_>>();
        let disk = TestDisk::new_ram_alloc(case.block_size, case.alignment, data.clone()).unwrap();
        let mut erase_scratch =
            vec![0u8; disk.io().info().erase_block_size().unwrap().try_into().unwrap()];
        let rw_off = usize::try_from(case.rw_offset).unwrap();
        let rw_sz = usize::try_from(case.rw_size).unwrap();
        let orig = disk.io().storage()[rw_off..][..rw_sz].to_vec();
        block_on(disk.erase(case.rw_offset, case.rw_size, &mut erase_scratch[..])).unwrap();
        // New scope to simplify lifetime for dev.io().storage()
        {
            let erased = &mut disk.io().storage_mut()[rw_off..][..rw_sz];
            erased.iter_mut().for_each(|v| *v = !*v);
            assert_eq!(erased.to_vec(), orig, "Erase test failed. Test case {:?}", case);
        }
        // The rest of the sotrage should be unchanged.
        assert_eq!(data, disk.io().storage().deref());
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
                    write_test_helper(
                        &TestCase::new($x0, $x1, $x2, $x3, $x4, $x5),
                        |blk, offset, data| {
                            block_on(blk.write(offset, data)).unwrap();
                            assert!(blk.io().num_reads() <= READ_WRITE_BLOCKS_UPPER_BOUND);
                            assert!(blk.io().num_writes() <= READ_WRITE_BLOCKS_UPPER_BOUND);
                        },
                    );
                }

                #[test]
                fn write_mut_scaled_test() {
                    // Scaled all parameters by double and test again.
                    let (x0, x1, x2, x3, x4, x5) =
                        (2 * $x0, 2 * $x1, 2 * $x2, 2 * $x3, 2 * $x4, 2 * $x5);
                    write_test_helper(
                        &TestCase::new(x0, x1, x2, x3, x4, x5),
                        |blk, offset, data| {
                            block_on(blk.write(offset, data)).unwrap();
                            assert!(blk.io().num_reads() <= READ_WRITE_BLOCKS_UPPER_BOUND);
                            assert!(blk.io().num_writes() <= READ_WRITE_BLOCKS_UPPER_BOUND);
                        },
                    );
                }

                #[test]
                fn erase_test() {
                    // For test, an erase block is 2 native blocks, thus scale all parameters by
                    // double, except block size.
                    let (x0, x1, x2, x3, x4, x5) =
                        (2 * $x0, 2 * $x1, 2 * $x2, 2 * $x3, 2 * $x4, 2 * $x5);
                    erase_test_helper(&TestCase::new(x0, x1, x2, x3, x4, x5));
                }

                #[test]
                fn erase_scaled_test() {
                    // Scaled all parameters by double and test again.
                    let (x0, x1, x2, x3, x4, x5) =
                        (4 * $x0, 4 * $x1, 4 * $x2, 4 * $x3, 2 * $x4, 4 * $x5);
                    erase_test_helper(&TestCase::new(x0, x1, x2, x3, x4, x5));
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
        STORAGE * 2
    }
    read_write_test! {
        aligned_offset_uanligned_size_extra_offset,
        BLOCK_SIZE,
        STORAGE - 1,
        0,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE * 2
    }
    read_write_test! {
        aligned_offset_intra_block_extra_offset,
        BLOCK_SIZE,
        BLOCK_SIZE - 1,
        0,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE * 2
    }
    read_write_test! {
        unaligned_offset_aligned_end_extra_offset,
        BLOCK_SIZE + 1,
        STORAGE - 1,
        0,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE * 2
    }
    read_write_test! {
        unaligned_offset_len_extra_offset,
        BLOCK_SIZE + 1,
        STORAGE - 2,
        0,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE * 2
    }
    read_write_test! {
        unaligned_offset_len_partial_cross_block_extra_offset,
        BLOCK_SIZE + 1,
        BLOCK_SIZE,
        0,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE * 2
    }
    read_write_test! {
        ualigned_offset_len_partial_intra_block_extra_offset,
        BLOCK_SIZE + 1,
        BLOCK_SIZE - 2,
        0,
        ALIGNMENT,
        BLOCK_SIZE,
        STORAGE * 2
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
        let io = RamBlockIo::new(1, 1, vec![]);
        assert_eq!(scratch_size(&io).unwrap(), 0);
    }

    #[test]
    fn test_scratch_too_small() {
        let io = RamBlockIo::new(512, 512, vec![]);
        let scratch_size = scratch_size(&io).unwrap() - 1;
        let pool = ArrayVec::from_iter(
            (0..2).map(|_| Some(Box::from_iter(iter::repeat(0).take(scratch_size)))),
        );
        assert!(TestDisk::new(io, pool).is_err());
    }

    #[test]
    fn test_read_overflow() {
        let disk = TestDisk::new_ram_alloc(512, 512, vec![0u8; 512]).unwrap();
        assert!(block_on(disk.read(512, &mut vec![0u8; 1][..])).is_err());
        assert!(block_on(disk.read(0, &mut vec![0u8; 513][..])).is_err());
    }

    #[test]
    fn test_read_arithmetic_overflow() {
        let disk = TestDisk::new_ram_alloc(512, 512, vec![0u8; 512]).unwrap();
        assert!(block_on(disk.read(u64::MAX, &mut vec![0u8; 1][..])).is_err());
    }

    #[test]
    fn test_write_overflow() {
        let disk = TestDisk::new_ram_alloc(512, 512, vec![0u8; 512]).unwrap();
        assert!(block_on(disk.write(512, &mut vec![0u8; 1])).is_err());
        assert!(block_on(disk.write(0, &mut vec![0u8; 513])).is_err());
    }

    #[test]
    fn test_write_arithmetic_overflow() {
        let disk = TestDisk::new_ram_alloc(512, 512, vec![0u8; 512]).unwrap();
        assert!(block_on(disk.write(u64::MAX, &mut vec![0u8; 1])).is_err());
    }

    #[test]
    fn test_ram_block_io_concurrent_write() {
        let disk = TestDisk::new_ram_alloc(512, 32, vec![0u8; KiB!(64)]).unwrap();
        let mut write_1_buf = vec![1u8; KiB!(2)];
        let mut write_2_buf = vec![2u8; KiB!(2)];

        let mut read_buf = vec![0u8; KiB!(2)];

        // Perfectly aligned writes
        block_on(async {
            let write_1_fut = disk.write(0, write_1_buf.as_mut_slice());
            let write_2_fut = disk.write(KiB!(4), write_2_buf.as_mut_slice());
            let (res_1, res_2) = join(write_1_fut, write_2_fut).await;
            assert!(res_1.is_ok());
            assert!(res_2.is_ok());

            disk.read(0, read_buf.as_mut_slice()).await.unwrap();
            assert_eq!(read_buf, write_1_buf);

            disk.read(KiB!(4), read_buf.as_mut_slice()).await.unwrap();
            assert_eq!(read_buf, write_2_buf);
        });

        // Write is unaligned on blocks
        block_on(async {
            let write_1_fut = disk.write(KiB!(6) + 128, write_1_buf.as_mut_slice());
            let write_2_fut = disk.write(KiB!(8) + 128, write_2_buf.as_mut_slice());
            let (res_1, res_2) = join(write_1_fut, write_2_fut).await;
            assert!(res_1.is_ok());
            assert!(res_2.is_ok());

            disk.read(KiB!(6) + 128, read_buf.as_mut_slice()).await.unwrap();
            assert_eq!(read_buf, write_1_buf);

            disk.read(KiB!(8) + 128, read_buf.as_mut_slice()).await.unwrap();
            assert_eq!(read_buf, write_2_buf);
        });
    }

    #[test]
    fn test_ram_block_io_queue_exhaustion() {
        let disk = TestDisk::new_ram_alloc(512, 32, vec![0u8; KiB!(64)]).unwrap();

        let mut orig = vec![0u8; KiB!(2)];
        let mut buf = vec![0u8; KiB!(2)];
        block_on(async {
            disk.read(0, orig.as_mut_slice()).await.unwrap();

            // Simulate a full queue.
            *disk.io().error.borrow_mut() = Some(Error::OutOfResources);
            let mut future = Box::pin(disk.read(0, buf.as_mut_slice()));

            // The first read on the block device should fail with OutOfResources,
            // but the Disk should hide this as being not ready.
            assert_eq!(poll(&mut future), None);
            *disk.io().error.borrow_mut() = None;

            // Now the I/O should complete.
            assert!(future.await.is_ok());
            assert_eq!(buf, orig);

            // Same check for write.
            *disk.io().error.borrow_mut() = Some(Error::OutOfResources);

            buf.iter_mut().for_each(|v| *v = !*v);
            let orig = buf.clone();
            let mut future = Box::pin(disk.write(0, buf.as_mut_slice()));
            assert_eq!(poll(&mut future), None);
            *disk.io().error.borrow_mut() = None;
            assert!(future.await.is_ok());

            disk.read(0, buf.as_mut_slice()).await.unwrap();
            assert_eq!(buf, orig);

            // Same check for erase.
            *disk.io().error.borrow_mut() = Some(Error::OutOfResources);
            let mut erase_scratch =
                vec![0u8; disk.block_info().erase_block_size().unwrap().try_into().unwrap()];
            let mut future = Box::pin(disk.erase(
                0,
                buf.len().try_into().unwrap(),
                erase_scratch.as_mut_slice(),
            ));
            assert_eq!(poll(&mut future), None);
            *disk.io().error.borrow_mut() = None;
            assert!(future.await.is_ok());
            disk.read(0, buf.as_mut_slice()).await.unwrap();
            assert_eq!(buf, vec![0u8; buf.len()]);
        });
    }
}
