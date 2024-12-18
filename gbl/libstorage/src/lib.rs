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

use core::{
    cell::RefMut,
    cmp::{max, min},
    mem::{size_of_val, MaybeUninit},
    ops::DerefMut,
    slice::SliceIndex,
};
use liberror::{Error, Result};
use libutils::aligned_subslice;
use safemath::SafeNum;

// Selective export of submodule types.
mod gpt;
pub use gpt::{
    gpt_buffer_size, new_gpt_max, new_gpt_n, Gpt, GptBuilder, GptEntry, GptHeader, GptLoadBufferN,
    GptMax, GptN, GptSyncResult, Partition, PartitionIterator, GPT_GUID_LEN, GPT_MAGIC,
    GPT_NAME_LEN_U16,
};

mod algorithm;
pub use algorithm::{read_async, write_async};

pub mod ram_block;
pub use ram_block::RamBlockIo;

/// `BlockInfo` contains information for a block device.
#[derive(Clone, Copy, Debug)]
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

/// `BlockIo` provides interfaces for reading and writing block storage medium.
///
/// SAFETY:
/// `read_blocks` method must guarantee `out` to be fully initialized on success. Otherwise error
/// must be returned.
/// This is necessary because unsafe code that uses BlockIo assumes `out` to be fully initialized to
/// work with it as with `&mut [u8]`.
pub unsafe trait BlockIo {
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
        out: &mut (impl SliceMaybeUninit + ?Sized),
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
    /// Returns true if exactly data.len() number of bytes are written. Otherwise false.
    async fn write_blocks(&mut self, blk_offset: u64, data: &mut [u8]) -> Result<()>;
}

// SAFETY:
// `read_blocks` method has same guaranties as `BlockIo` implementation of referenced type T.
// Which guaranties `out` to be fully initialized on success.
unsafe impl<T: DerefMut> BlockIo for T
where
    T::Target: BlockIo,
{
    fn info(&mut self) -> BlockInfo {
        self.deref_mut().info()
    }

    async fn read_blocks(
        &mut self,
        blk_offset: u64,
        out: &mut (impl SliceMaybeUninit + ?Sized),
    ) -> Result<()> {
        self.deref_mut().read_blocks(blk_offset, out).await
    }

    async fn write_blocks(&mut self, blk_offset: u64, data: &mut [u8]) -> Result<()> {
        self.deref_mut().write_blocks(blk_offset, data).await
    }
}

/// An implementation of `BlockIo` of where all required methods are `unimplemented!()`
pub struct BlockIoNull {}

// SAFETY:
// `read_blocks` never succeeds since it is not implemented and will panic.
unsafe impl BlockIo for BlockIoNull {
    fn info(&mut self) -> BlockInfo {
        unimplemented!();
    }

    async fn read_blocks(
        &mut self,
        _: u64,
        _: &mut (impl SliceMaybeUninit + ?Sized),
    ) -> Result<()> {
        unimplemented!();
    }

    async fn write_blocks(&mut self, _: u64, _: &mut [u8]) -> Result<()> {
        unimplemented!();
    }
}

/// Check if `value` is aligned to (multiples of) `alignment`
/// It can fail if the remainider calculation fails overflow check.
pub fn is_aligned(value: impl Into<SafeNum>, alignment: impl Into<SafeNum>) -> Result<bool> {
    Ok(u64::try_from(value.into() % alignment.into())? == 0)
}

/// Check if `buffer` address is aligned to `alignment`
/// It can fail if the remainider calculation fails overflow check.
pub fn is_buffer_aligned<T>(buffer: &[T], alignment: u64) -> Result<bool> {
    is_aligned(buffer.as_ptr() as usize, alignment)
}

/// Check read/write range and calculate offset in number of blocks.
fn check_range<T>(info: BlockInfo, offset: u64, buffer: &[T]) -> Result<SafeNum> {
    let offset: SafeNum = offset.into();
    let block_size: SafeNum = info.block_size.into();
    debug_assert!(is_aligned(offset, block_size)?, "{:?}, {:?}", offset, block_size);
    debug_assert!(is_aligned(size_of_val(buffer), block_size)?);
    debug_assert!(is_buffer_aligned(buffer, info.alignment)?);
    let blk_offset = offset / block_size;
    let blk_count = SafeNum::from(size_of_val(buffer)) / block_size;
    let end: u64 = (blk_offset + blk_count).try_into()?;
    match end <= info.num_blocks {
        true => Ok(blk_offset),
        false => Err(Error::BadIndex(end as usize)),
    }
}

/// Computes the required scratch size for initializing a [AsyncBlockDevice].
pub fn scratch_size(io: &mut impl BlockIo) -> Result<usize> {
    let info = io.info();
    let block_alignment = match info.block_size {
        1 => 0,
        v => v,
    };
    Ok(((SafeNum::from(info.alignment) - 1) * 2 + block_alignment).try_into()?)
}

/// `Disk` contains a BlockIO and scratch buffer and provides APIs for reading/writing with
/// arbitrary ranges and alignment.
pub struct Disk<T, S> {
    io: T,
    scratch: S,
}

impl<T: BlockIo, S: DerefMut<Target = [u8]>> Disk<T, S> {
    /// Creates a new instance with the given IO and scratch buffer.
    ///
    /// * The scratch buffer is internally used for handling partial block read/write and unaligned
    ///   input/output user buffers.
    ///
    /// * The necessary size for the scratch buffer depends on `BlockInfo::alignment`,
    ///   `BlockInfo::block_size`. It can be computed using the helper API `scratch_size()`. If the
    ///   block device has no alignment requirement, i.e. both alignment and block size are 1, the
    ///   total required scratch size is 0.
    pub fn new(mut io: T, scratch: S) -> Result<Self> {
        let sz = scratch_size(&mut io)?;
        match scratch.len() < sz {
            true => Err(Error::BufferTooSmall(Some(sz))),
            _ => Ok(Self { io, scratch }),
        }
    }

    /// Same as `Self::new()` but allocates the necessary scratch buffer.
    ///
    /// T must implement Extend<u8> and Default. It should typically be a vector like type.
    ///
    /// Allocation is done by extending T one element at a time. In most cases, we don't expect
    /// block size or alignment to be large values and this is only done once. thus this should be
    /// low cost. However if that is not the case, it is recommended to use `Self::new()` with
    /// pre-allocated scratch buffer.
    pub fn new_alloc_scratch(mut io: T) -> Result<Self>
    where
        S: Extend<u8> + Default,
    {
        let mut scratch = S::default();
        // Extends the scratch buffer to the required size.
        // Can call `extend_reserve()` first once it becomes stable.
        (0..max(scratch.len(), scratch_size(&mut io)?) - scratch.len())
            .for_each(|_| scratch.extend([0u8]));
        Self::new(io, scratch)
    }

    /// Creates a `Disk<&mut T, &mut [u8]>` instance that borrows the internal fields.
    pub fn as_borrowed(&mut self) -> Disk<&mut T, &mut [u8]> {
        Disk::new(&mut self.io, &mut self.scratch[..]).unwrap()
    }

    /// Gets the [BlockInfo]
    pub fn block_info(&mut self) -> BlockInfo {
        self.io.info()
    }

    /// Gets the underlying BlockIo implementation.
    pub fn io(&mut self) -> &mut T {
        &mut self.io
    }

    /// Reads data from the block device.
    ///
    /// # Args
    ///
    /// * `offset`: Offset in number of bytes.
    /// * `out`: Buffer to store the read data.
    /// * Returns success when exactly `out.len()` number of bytes are read.
    pub async fn read(
        &mut self,
        offset: u64,
        out: &mut (impl SliceMaybeUninit + ?Sized),
    ) -> Result<()> {
        read_async(&mut self.io, offset, out, &mut self.scratch).await
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
    pub async fn write(&mut self, offset: u64, data: &mut [u8]) -> Result<()> {
        write_async(&mut self.io, offset, data, &mut self.scratch).await
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
        &mut self,
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

    /// Loads and syncs GPT from a block device.
    ///
    /// The API validates and restores primary/secondary GPT header.
    ///
    /// # Returns
    ///
    /// * Returns Ok(sync_result) if disk IO is successful, where `sync_result` contains the GPT
    ///   verification and restoration result.
    /// * Returns Err() if disk IO encounters errors.
    pub async fn sync_gpt(
        &mut self,
        gpt: &mut Gpt<impl DerefMut<Target = [u8]>>,
    ) -> Result<GptSyncResult> {
        gpt.load_and_sync(self).await
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
        &mut self,
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
    pub async fn erase_gpt(&mut self, gpt: &mut Gpt<impl DerefMut<Target = [u8]>>) -> Result<()> {
        gpt::erase_gpt(self, gpt).await
    }

    /// Reads a GPT partition on a block device
    ///
    /// # Args
    ///
    /// * `gpt`: A `GptCache` initialized with `Self::sync_gpt()`.
    /// * `part_name`: Name of the partition.
    /// * `offset`: Offset in number of bytes into the partition.
    /// * `out`: Buffer to store the read data.
    ///
    /// # Returns
    ///
    /// Returns success when exactly `out.len()` of bytes are read successfully.
    pub async fn read_gpt_partition(
        &mut self,
        gpt: &mut Gpt<impl DerefMut<Target = [u8]>>,
        part_name: &str,
        offset: u64,
        out: &mut (impl SliceMaybeUninit + ?Sized),
    ) -> Result<()> {
        let offset = gpt.check_range(part_name, offset, out.len())?;
        self.read(offset, out).await
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
        &mut self,
        gpt: &mut Gpt<impl DerefMut<Target = [u8]>>,
        part_name: &str,
        offset: u64,
        data: &mut [u8],
    ) -> Result<()> {
        let offset = gpt.check_range(part_name, offset, data.len())?;
        self.write(offset, data).await
    }
}

impl<'a, T: BlockIo> Disk<RefMut<'a, T>, RefMut<'a, [u8]>> {
    /// Converts a `RefMut<Disk<T, S>>` to `Disk<RefMut<T>, RefMut<[u8]>>`. The scratch buffer
    /// generic type is eliminated in the return.
    pub fn from_ref_mut(val: RefMut<'a, Disk<T, impl DerefMut<Target = [u8]>>>) -> Self {
        let (io, scratch) = RefMut::map_split(val, |v| (&mut v.io, &mut v.scratch[..]));
        Disk::new(io, scratch).unwrap()
    }
}

impl<T, S> Disk<RamBlockIo<T>, S>
where
    T: DerefMut<Target = [u8]>,
    S: DerefMut<Target = [u8]> + Extend<u8> + Default,
{
    /// Creates a new ram disk instance with allocated scratch buffer.
    pub fn new_ram_alloc(block_size: u64, alignment: u64, storage: T) -> Result<Self> {
        let ram_blk = RamBlockIo::new(block_size, alignment, storage);
        Self::new_alloc_scratch(ram_blk)
    }
}

/// Helper trait to implement common logic working with MaybeUninit slices.
/// Implemented for [u8] and [MaybeUninit<u8>].
///
/// Read functions treats buffer as not initialized using this trait.
// AsRef,AsMut implementation added here. Since it is not possible to implement trait from other
// crate for trait in this trait. It is possible to implement other trait for `dyn` object of local
// trait. But it introduces other issues with lifetime and casting boilerplate.
//
// Alternatively we considered using wrapper type, which works but requires `into()` call either on
// function call. Or inside functions if they accept `impl Into<Wrapper>`.
// Using traits seems to be cleaner and potentially more effective.
pub trait SliceMaybeUninit {
    /// Get `&[MaybeUninit<u8>]` representation
    fn as_ref(&self) -> &[MaybeUninit<u8>];

    // AsMut implementation
    /// Get `&mut [MaybeUninit<u8>]` representation
    fn as_mut(&mut self) -> &mut [MaybeUninit<u8>];

    /// Get slice length
    fn len(&self) -> usize {
        self.as_ref().len()
    }

    /// Returns reference to element or subslice, or Error if index is out of bounds
    fn get<I>(&mut self, index: I) -> Result<&<I>::Output>
    where
        I: SliceIndex<[MaybeUninit<u8>]>,
    {
        self.as_ref().get(index).ok_or(Error::BufferTooSmall(None))
    }

    /// Returns mutable reference to element or subslice, or Error if index is out of bounds
    fn get_mut<I>(&mut self, index: I) -> Result<&mut <I>::Output>
    where
        I: SliceIndex<[MaybeUninit<u8>]>,
    {
        self.as_mut().get_mut(index).ok_or(Error::BufferTooSmall(None))
    }

    /// Clone from slice
    fn clone_from_slice(&mut self, src: &[u8]) {
        self.as_mut().clone_from_slice(as_uninit(src))
    }
}

impl SliceMaybeUninit for [u8] {
    fn as_ref(&self) -> &[MaybeUninit<u8>] {
        as_uninit(self)
    }
    fn as_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        as_uninit_mut(self)
    }
}

impl SliceMaybeUninit for [MaybeUninit<u8>] {
    fn as_ref(&self) -> &[MaybeUninit<u8>] {
        self
    }
    fn as_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self
    }
}

/// Present initialized `&mut [u8]` buffer as `&mut [MaybeUninit<u8>]`
pub fn as_uninit_mut(buf: &mut [u8]) -> &mut [MaybeUninit<u8>] {
    // SAFETY:
    // MaybeUninit<u8> has same size and alignment as u8.
    // `data` is valid pointer to initialised u8 slice of size `buf.len()`
    unsafe { core::slice::from_raw_parts_mut(buf.as_mut_ptr() as *mut MaybeUninit<u8>, buf.len()) }
}

/// Present initialized `&mut [u8]` buffer as `&mut [MaybeUninit<u8>]`
pub fn as_uninit(buf: &[u8]) -> &[MaybeUninit<u8>] {
    // SAFETY:
    // MaybeUninit<u8> has same size and alignment as u8.
    // `data` is valid pointer to initialised u8 slice of size `buf.len()`
    unsafe { core::slice::from_raw_parts(buf.as_ptr() as *const MaybeUninit<u8>, buf.len()) }
}

#[cfg(test)]
mod test {
    use super::*;
    use gbl_async::block_on;
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

    // Type alias of the [Disk] type used by unittests.
    pub(crate) type TestDisk = Disk<RamBlockIo<Vec<u8>>, Vec<u8>>;

    fn read_test_helper(case: &TestCase) {
        let data = (0..case.storage_size).map(|v| v as u8).collect::<Vec<_>>();
        let mut disk = TestDisk::new_ram_alloc(case.alignment, case.block_size, data).unwrap();
        // Make an aligned buffer. A misaligned version is created by taking a sub slice that
        // starts at an unaligned offset. Because of this we need to allocate
        // `case.misalignment` more to accommodate it.
        let mut aligned_buf = AlignedBuffer::new(case.alignment, case.rw_size + case.misalignment);
        let misalignment = usize::try_from(case.misalignment).unwrap();
        let rw_sz = usize::try_from(case.rw_size).unwrap();
        let out = &mut aligned_buf.get()[misalignment..][..rw_sz];
        block_on(disk.read(case.rw_offset, out)).unwrap();
        let rw_off = usize::try_from(case.rw_offset).unwrap();
        assert_eq!(out, &disk.io().storage()[rw_off..][..rw_sz], "Failed. Test case {:?}", case);
        assert!(disk.io().num_reads <= READ_WRITE_BLOCKS_UPPER_BOUND);
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
        let mut disk = TestDisk::new_ram_alloc(case.alignment, case.block_size, data).unwrap();
        // Make an aligned buffer. A misaligned version is created by taking a sub slice that
        // starts at an unaligned offset. Because of this we need to allocate
        // `case.misalignment` more to accommodate it.
        let mut aligned_buf = AlignedBuffer::new(case.alignment, case.rw_size + case.misalignment);
        let misalignment = usize::try_from(case.misalignment).unwrap();
        let data = &mut aligned_buf.get()[misalignment..][..rw_sz];
        data.clone_from_slice(&expected);
        write_func(&mut disk, case.rw_offset, data);
        let written = &disk.io().storage()[rw_off..][..rw_sz];
        assert_eq!(expected, written, "Failed. Test case {:?}", case);
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
                    write_test_helper(
                        &TestCase::new($x0, $x1, $x2, $x3, $x4, $x5),
                        |blk, offset, data| {
                            block_on(blk.write(offset, data)).unwrap();
                            assert!(blk.io().num_reads <= READ_WRITE_BLOCKS_UPPER_BOUND);
                            assert!(blk.io().num_writes <= READ_WRITE_BLOCKS_UPPER_BOUND);
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
                            assert!(blk.io().num_reads <= READ_WRITE_BLOCKS_UPPER_BOUND);
                            assert!(blk.io().num_writes <= READ_WRITE_BLOCKS_UPPER_BOUND);
                        },
                    );
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
        let mut io = RamBlockIo::new(1, 1, vec![]);
        assert_eq!(scratch_size(&mut io).unwrap(), 0);
    }

    #[test]
    fn test_scratch_too_small() {
        let mut io = RamBlockIo::new(512, 512, vec![]);
        let scratch = vec![0u8; scratch_size(&mut io).unwrap() - 1];
        assert!(TestDisk::new(io, scratch).is_err());
    }

    #[test]
    fn test_read_overflow() {
        let mut disk = TestDisk::new_ram_alloc(512, 512, vec![0u8; 512]).unwrap();
        assert!(block_on(disk.read(512, &mut vec![0u8; 1][..])).is_err());
        assert!(block_on(disk.read(0, &mut vec![0u8; 513][..])).is_err());
    }

    #[test]
    fn test_read_arithmetic_overflow() {
        let mut disk = TestDisk::new_ram_alloc(512, 512, vec![0u8; 512]).unwrap();
        assert!(block_on(disk.read(u64::MAX, &mut vec![0u8; 1][..])).is_err());
    }

    #[test]
    fn test_write_overflow() {
        let mut disk = TestDisk::new_ram_alloc(512, 512, vec![0u8; 512]).unwrap();
        assert!(block_on(disk.write(512, &mut vec![0u8; 1])).is_err());
        assert!(block_on(disk.write(0, &mut vec![0u8; 513])).is_err());
    }

    #[test]
    fn test_write_arithmetic_overflow() {
        let mut disk = TestDisk::new_ram_alloc(512, 512, vec![0u8; 512]).unwrap();
        assert!(block_on(disk.write(u64::MAX, &mut vec![0u8; 1])).is_err());
    }
}
