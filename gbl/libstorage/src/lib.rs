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
//! of them and relax these constraints.
//!
//! A block device is represented by a type that implements the `BlockDevice` trait. The trait
//! provides information on block size, total size, alignment requirement and read/write methods.
//! The library offers two APIs `BlockDevice::read()` and `BlockDevice::write()` for
//! reading/writing with the trait without any alignment requirement on inputs.
//!
//! The trait also provides APIs `BlockDevice::sync_gpt()`, `BlockDevice::read_gpt_partition()` and
//! `BlockDevice::write_gpt_partition()` for loading/repairing, reading and writing GPT partitions.
//!
//! # Examples
//!
//! ```rust
//! use gbl_storage::{BlockDevice, required_scratch_size};
//!
//! pub struct RamBlockDevice {
//!     storage: std::vec::Vec<u8>,
//! }
//!
//! impl BlockDevice for RamBlockDevice {
//!     fn block_size(&mut self) -> u64 { 512 }
//!
//!     fn num_blocks(&mut self) -> u64 { self.storage.len() as u64 / self.block_size() }
//!
//!     fn alignment(&mut self) -> u64 { 64 }
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
//! let mut ram_block_dev = RamBlockDevice {storage: vec![0u8; 32 * 1024]};
//!
//! // Prepare a scratch buffer, size calculated with `required_scratch_size()`.
//! let mut scratch = vec![0u8; required_scratch_size(&mut ram_block_dev).unwrap()];
//!
//! // Read/write with arbitrary range and buffer without worrying about alignment.
//! let mut out = vec![0u8;1234];
//! ram_block_dev.read(4321, &mut out[..], &mut scratch).unwrap();
//! let mut data = vec![0u8;5678];
//! // Mutable input. More efficient
//! ram_block_dev.write(8765, &mut data[..], &mut scratch).unwrap();
//! // Immutable input. Works too but not as efficient.
//! ram_block_dev.write(8765, &data[..], &mut scratch).unwrap();
//! ```

#![cfg_attr(not(test), no_std)]

use core::cmp::min;

// Selective export of submodule types.
mod gpt;
pub use gpt::Gpt;
pub use gpt::GptEntry;

/// The type of Result used in this library.
pub type Result<T> = core::result::Result<T, StorageError>;

/// Error code for this library.
#[derive(Debug, Copy, Clone)]
pub enum StorageError {
    ArithmeticOverflow,
    OutOfRange,
    ScratchTooSmall,
    BlockDeviceError,
    InvalidInput,
    NoValidGpt,
    NotExist,
    U64toUSizeOverflow,
}

impl Into<&'static str> for StorageError {
    fn into(self) -> &'static str {
        match self {
            StorageError::ArithmeticOverflow => "Arithmetic overflow",
            StorageError::OutOfRange => "Out of range",
            StorageError::ScratchTooSmall => "Not enough scratch buffer",
            StorageError::BlockDeviceError => "Block device error",
            StorageError::InvalidInput => "Invalid input",
            StorageError::NoValidGpt => "GPT not found",
            StorageError::NotExist => "Not exists",
            StorageError::U64toUSizeOverflow => "u64 to usize fails",
        }
    }
}

impl core::fmt::Display for StorageError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", Into::<&'static str>::into(*self))
    }
}

/// A trait for reading/writing a block device
pub trait BlockDevice {
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

    // TODO(298485845): Investigate adding rust doc test for the public document.

    /// Read data from the block device.
    ///
    /// # Args
    ///
    /// * `offset`: Offset in number of bytes.
    ///
    /// * `out`: Buffer to store the read data.
    ///
    /// * `scratch`: A buffer for the API to handle misalignment and non-block-aligned read range.
    ///   Its size must be at least `required_scratch_size(blk_dev)`.
    ///
    /// * Returns success when exactly `out.len()` number of bytes are read.
    fn read(&mut self, offset: u64, out: &mut [u8], scratch: &mut [u8]) -> Result<()> {
        read(self, offset, out, scratch)
    }

    /// Write data to the device.
    ///
    /// # Args
    ///
    /// * `offset`: Offset in number of bytes.
    ///
    /// * `data`: Data to write. It can be `&[u8]`, `&mut [u8]` or other types that implement the
    ///   `WriteBuffer` trait.
    ///
    /// * If `data` is an immutable bytes slice `&[u8]` or doesn't support `Bytes::as_mut_slice()`,
    ///   when offset`/`data.len()` is not aligned to `blk_dev.block_size()` or data.as_ptr() is
    ///   not aligned to `blk_dev.alignment()`, the API may reduce to a block by block
    ///   read-modify-write in the worst case, which can be inefficient.
    ///
    /// * If `data` is a mutable bytes slice `&mut [u8]`, or support `Bytes::as_mut_slice()`. The
    ///   API enables optimization which temporarily changes `data` layout internally and reduces
    ///   the number of calls to `blk_dev.write_blocks()` down to O(1) regardless of inputs
    ///   alignment. This is the recommended usage.
    ///
    /// * `scratch`: A buffer for the API to handle buffer and write range misalignment. Its size
    ///   must be at least `required_scratch_size(blk_dev)`.
    ///
    /// * Returns success when exactly `data.len()` number of bytes are written.
    fn write<B>(&mut self, offset: u64, data: B, scratch: &mut [u8]) -> Result<()>
    where
        B: WriteBuffer,
    {
        write(self, offset, data, scratch)
    }

    /// Parse and sync GPT from a block device.
    ///
    /// # Args
    ///
    /// * The API validates and restores primary/secondary GPT header.
    ///
    /// * `blk_dev`: The block device to read GPT.
    ///
    /// * `scratch`: A buffer for the API to handle buffer and write range misalignment. Its size
    ///   must be at least `required_scratch_size(blk_dev)`.
    ///
    /// # Returns
    ///
    /// Returns success if GPT is loaded/restored successfully.
    fn sync_gpt(&mut self, gpt: &mut Gpt, scratch: &mut [u8]) -> Result<()> {
        gpt::gpt_sync(self, gpt, scratch)
    }

    /// Read a GPT partition on a block device
    ///
    /// # Args
    ///
    /// * `gpt`: An instance of Gpt. If the GPT comes from the same block device, this should be
    ///   obtained from calling sync_gpt() of this BlockDevice.
    ///
    /// * `part_name`: Name of the partition.
    ///
    /// * `offset`: Offset in number of bytes into the partition.
    ///
    /// * `out`: Buffer to store the read data.
    ///
    /// * `scratch`: A scratch buffer for reading/writing `blk_dev`. Must have a size at least
    ///   `required_scratch_size(blk_dev)`. See `BlockDevice::read()/write()` for more details.
    ///
    /// # Returns
    ///
    /// Returns success when exactly `out.len()` of bytes are read successfully.
    fn read_gpt_partition(
        &mut self,
        gpt: &Gpt,
        part_name: &str,
        offset: u64,
        out: &mut [u8],
        scratch: &mut [u8],
    ) -> Result<()> {
        gpt::read_gpt_partition(self, gpt, part_name, offset, out, scratch)
    }

    /// Write a GPT partition on a block device
    ///
    /// # Args
    ///
    /// * `gpt`: An instance of Gpt. If the GPT comes from the same block device, this should be
    ///   obtained from calling sync_gpt() of this BlockDevice.
    ///
    /// * `part_name`: Name of the partition.
    ///
    /// * `offset`: Offset in number of bytes into the partition.
    ///
    /// * `data`: Data to write. See `data` passed to `BlockDevice::write()` for details.
    ///
    /// * `scratch`: A scratch buffer for reading/writing `blk_dev`. Must have a size at least
    ///   `required_scratch_size(blk_dev)`. See `BlockDevice::read()/write()` for more details.
    ///
    /// # Returns
    ///
    /// Returns success when exactly `data.len()` of bytes are written successfully.
    fn write_gpt_partition<B>(
        &mut self,
        gpt: &Gpt,
        part_name: &str,
        offset: u64,
        data: B,
        scratch: &mut [u8],
    ) -> Result<()>
    where
        B: WriteBuffer,
    {
        gpt::write_gpt_partition(self, gpt, part_name, offset, data, scratch)
    }
}

/// Add two u64 integers and check overflow
fn add(lhs: u64, rhs: u64) -> Result<u64> {
    lhs.checked_add(rhs).ok_or_else(|| StorageError::ArithmeticOverflow)
}

/// Substract two u64 integers and check overflow
fn sub(lhs: u64, rhs: u64) -> Result<u64> {
    lhs.checked_sub(rhs).ok_or_else(|| StorageError::ArithmeticOverflow)
}

/// Calculate remainders and check overflow
fn rem(lhs: u64, rhs: u64) -> Result<u64> {
    lhs.checked_rem(rhs).ok_or_else(|| StorageError::ArithmeticOverflow)
}

/// Multiply two numbers and check overflow
fn mul(lhs: u64, rhs: u64) -> Result<u64> {
    lhs.checked_mul(rhs).ok_or_else(|| StorageError::ArithmeticOverflow)
}

/// Divide two numbers and check overflow
fn div(lhs: u64, rhs: u64) -> Result<u64> {
    lhs.checked_div(rhs).ok_or_else(|| StorageError::ArithmeticOverflow)
}

/// Check if `value` is aligned to (multiples of) `alignment`
/// It can fail if the remainider calculation fails overflow check.
fn is_aligned(value: u64, alignment: u64) -> Result<bool> {
    Ok(rem(value, alignment)? == 0)
}

/// Check if `buffer` address is aligned to `alignment`
/// It can fail if the remainider calculation fails overflow check.
fn is_buffer_aligned(buffer: &[u8], alignment: u64) -> Result<bool> {
    is_aligned(buffer.as_ptr() as u64, alignment)
}

/// Round down `size` according to `alignment`.
/// It can fail if any arithmetic operation fails overflow check
fn round_down(size: u64, alignment: u64) -> Result<u64> {
    sub(size, rem(size, alignment)?)
}

/// Round up `size` according to `alignment`.
/// It can fail if any arithmetic operation fails overflow check
fn round_up(size: u64, alignment: u64) -> Result<u64> {
    // equivalent to round_down(size + alignment - 1, alignment)
    round_down(add(size, sub(alignment, 1)?)?, alignment)
}

/// Check and convert u64 into usize
fn to_usize(val: u64) -> Result<usize> {
    val.try_into().map_err(|_| StorageError::U64toUSizeOverflow)
}

/// Check read/write range and calculate offset in number of blocks.
fn check_range(
    blk_dev: &mut (impl BlockDevice + ?Sized),
    offset: u64,
    buffer: &[u8],
) -> Result<u64> {
    // The following should be invariants if implementation is correct.
    debug_assert!(is_aligned(offset, blk_dev.block_size())?);
    debug_assert!(is_aligned(buffer.len() as u64, blk_dev.block_size())?);
    debug_assert!(is_buffer_aligned(buffer, blk_dev.alignment())?);
    let blk_offset = offset / blk_dev.block_size();
    let blk_count = buffer.len() as u64 / blk_dev.block_size();
    match add(blk_offset, blk_count)? <= blk_dev.num_blocks() {
        true => Ok(blk_offset),
        false => Err(StorageError::OutOfRange),
    }
}

/// Read with block-aligned offset, length and aligned buffer
fn read_aligned_all(
    blk_dev: &mut (impl BlockDevice + ?Sized),
    offset: u64,
    out: &mut [u8],
) -> Result<()> {
    let blk_offset = check_range(blk_dev, offset, out)?;
    if blk_dev.read_blocks(blk_offset, out) {
        return Ok(());
    }
    Err(StorageError::BlockDeviceError)
}

/// Read with block-aligned offset and aligned buffer. Size don't need to be block aligned.
///   |~~~~~~~~~read~~~~~~~~~|
///   |---------|---------|---------|
fn read_aligned_offset_and_buffer(
    blk_dev: &mut (impl BlockDevice + ?Sized),
    offset: u64,
    out: &mut [u8],
    scratch: &mut [u8],
) -> Result<()> {
    debug_assert!(is_aligned(offset, blk_dev.block_size())?);
    debug_assert!(is_buffer_aligned(out, blk_dev.alignment())?);

    let aligned_read = round_down(out.len() as u64, blk_dev.block_size())?;
    if aligned_read > 0 {
        read_aligned_all(blk_dev, offset, &mut out[..to_usize(aligned_read)?])?;
    }
    let unaligned = &mut out[to_usize(aligned_read)?..];
    if unaligned.len() == 0 {
        return Ok(());
    }
    // Read unalinged part.
    let block_scratch = &mut scratch[..to_usize(blk_dev.block_size())?];
    read_aligned_all(blk_dev, add(offset, aligned_read)?, block_scratch)?;
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
    blk_dev: &mut (impl BlockDevice + ?Sized),
    offset: u64,
    out: &mut [u8],
    scratch: &mut [u8],
) -> Result<()> {
    debug_assert!(is_buffer_aligned(out, blk_dev.alignment())?);

    if is_aligned(offset, blk_dev.block_size())? {
        return read_aligned_offset_and_buffer(blk_dev, offset, out, scratch);
    }

    let aligned_start =
        min(round_up(offset, blk_dev.block_size())?, add(offset, out.len() as u64)?);
    let aligned_relative_offset = sub(aligned_start, offset)?;
    if aligned_relative_offset < out.len() as u64 {
        if is_buffer_aligned(&out[to_usize(aligned_relative_offset)?..], blk_dev.alignment())? {
            // If new output address is aligned, read directly.
            read_aligned_offset_and_buffer(
                blk_dev,
                aligned_start,
                &mut out[to_usize(aligned_relative_offset)?..],
                scratch,
            )?;
        } else {
            // Otherwise read into `out` (assumed aligned) and memmove to the correct
            // position
            let read_len = sub(out.len() as u64, aligned_relative_offset)?;
            read_aligned_offset_and_buffer(
                blk_dev,
                aligned_start,
                &mut out[..to_usize(read_len)?],
                scratch,
            )?;
            out.copy_within(..to_usize(read_len)?, to_usize(aligned_relative_offset)?);
        }
    }

    // Now read the unaligned part
    let block_scratch = &mut scratch[..to_usize(blk_dev.block_size())?];
    let round_down_offset = round_down(offset, blk_dev.block_size())?;
    read_aligned_all(blk_dev, round_down_offset, block_scratch)?;
    let offset_relative = sub(offset, round_down_offset)?;
    let unaligned = &mut out[..to_usize(aligned_relative_offset)?];
    unaligned.clone_from_slice(
        &block_scratch
            [to_usize(offset_relative)?..to_usize(add(offset_relative, unaligned.len() as u64)?)?],
    );
    Ok(())
}

/// Returns the necessary size of `scratch` to pass to `read()` for the given
/// `blk_dev`
pub fn required_scratch_size(blk_dev: &mut (impl BlockDevice + ?Sized)) -> Result<usize> {
    // block_size() + 2 * alignment()
    // This guarantees that we can craft out two aligned scratch buffers:
    // [u8; blk_dev.alignment()] and [u8; blk_dev.block_size())] respectively. They are
    // needed for handing buffer and read/write range misalignment.
    to_usize(add(mul(2, blk_dev.alignment())?, blk_dev.block_size())?)
}

// Partition a scratch into two aligned parts: [u8; alignment()] and [u8; block_size())]
// for handling block and buffer misalignment respecitvely.
fn split_scratch<'a>(
    blk_dev: &mut (impl BlockDevice + ?Sized),
    scratch: &'a mut [u8],
) -> Result<(&'a mut [u8], &'a mut [u8])> {
    if scratch.len() < required_scratch_size(blk_dev)? {
        return Err(StorageError::ScratchTooSmall);
    }
    let addr_value = scratch.as_ptr() as u64;
    let aligned_start = sub(round_up(addr_value, blk_dev.alignment())?, addr_value)?;
    Ok(scratch[to_usize(aligned_start)?..].split_at_mut(to_usize(blk_dev.alignment())?))
}

/// Read with no alignment requirement.
fn read(
    blk_dev: &mut (impl BlockDevice + ?Sized),
    offset: u64,
    out: &mut [u8],
    scratch: &mut [u8],
) -> Result<()> {
    let (buffer_alignment_scratch, block_alignment_scratch) = split_scratch(blk_dev, scratch)?;

    if is_buffer_aligned(out, blk_dev.alignment())? {
        return read_aligned_buffer(blk_dev, offset, out, block_alignment_scratch);
    }

    // Buffer misalignment:
    // Case 1:
    //     |~~~~~~~~~~~~buffer~~~~~~~~~~~~|
    //   |----------------------|---------------------|
    //      blk_dev.alignment()
    //
    // Case 2:
    //    |~~~~~~buffer~~~~~|
    //  |----------------------|---------------------|
    //     blk_dev.alignment()

    let out_addr_value = out.as_ptr() as u64;
    let unaligned_read =
        min(sub(round_up(out_addr_value, blk_dev.alignment())?, out_addr_value)?, out.len() as u64);
    // Read unaligned part
    let unaligned_out = &mut buffer_alignment_scratch[..to_usize(unaligned_read)?];
    read_aligned_buffer(blk_dev, offset, unaligned_out, block_alignment_scratch)?;
    out[..to_usize(unaligned_read)?].clone_from_slice(unaligned_out);

    if unaligned_read == out.len() as u64 {
        return Ok(());
    }
    // Read aligned part
    read_aligned_buffer(
        blk_dev,
        add(offset, unaligned_read)?,
        &mut out[to_usize(unaligned_read)?..],
        block_alignment_scratch,
    )
}

fn write_aligned_all(
    blk_dev: &mut (impl BlockDevice + ?Sized),
    offset: u64,
    data: &[u8],
) -> Result<()> {
    let blk_offset = check_range(blk_dev, offset, data)?;
    if blk_dev.write_blocks(blk_offset, data) {
        return Ok(());
    }
    Err(StorageError::BlockDeviceError)
}

/// Write with block-aligned offset and aligned buffer. `data.len()` can be unaligned.
///   |~~~~~~~~~size~~~~~~~~~|
///   |---------|---------|---------|
fn write_aligned_offset_and_buffer(
    blk_dev: &mut (impl BlockDevice + ?Sized),
    offset: u64,
    data: &[u8],
    scratch: &mut [u8],
) -> Result<()> {
    debug_assert!(is_aligned(offset, blk_dev.block_size())?);
    debug_assert!(is_buffer_aligned(data, blk_dev.alignment())?);

    let aligned_write = round_down(data.len() as u64, blk_dev.block_size())?;
    if aligned_write > 0 {
        write_aligned_all(blk_dev, offset, &data[..to_usize(aligned_write)?])?;
    }
    let unaligned = &data[to_usize(aligned_write)?..];
    if unaligned.len() == 0 {
        return Ok(());
    }

    // Perform read-modify-write for the unaligned part
    let unaligned_start = add(offset, aligned_write)?;
    let block_scratch = &mut scratch[..to_usize(blk_dev.block_size())?];
    read_aligned_all(blk_dev, unaligned_start, block_scratch)?;
    block_scratch[..unaligned.len()].clone_from_slice(unaligned);
    write_aligned_all(blk_dev, unaligned_start, block_scratch)
}

/// Write data to the device with immutable input bytes slice. However, if `offset`/`data.len()`
/// is not aligned to `blk_dev.block_size()` or data.as_ptr() is not aligned to
/// `blk_dev.alignment()`, the API may reduce to a block by block read-modify-write in the worst
/// case.
fn write_bytes(
    blk_dev: &mut (impl BlockDevice + ?Sized),
    mut offset: u64,
    data: &[u8],
    scratch: &mut [u8],
) -> Result<()> {
    let (_, scratch) = split_scratch(blk_dev, scratch)?;
    let block_size = blk_dev.block_size();
    let block_scratch = &mut scratch[..to_usize(block_size)?];
    let mut data_offset = 0;
    while data_offset < data.len() as u64 {
        if is_aligned(offset, blk_dev.block_size())?
            && is_buffer_aligned(&data[to_usize(data_offset)?..], blk_dev.alignment())?
        {
            return write_aligned_offset_and_buffer(
                blk_dev,
                offset,
                &data[to_usize(data_offset)?..],
                scratch,
            );
        }

        let block_offset = round_down(offset, block_size)?;
        let copy_offset = offset - block_offset;
        let copy_size = min(data[to_usize(data_offset)?..].len() as u64, block_size - copy_offset);
        if copy_size < block_size {
            // Partial block copy. Perform read-modify-write
            read_aligned_all(blk_dev, block_offset, block_scratch)?;
        }
        block_scratch[to_usize(copy_offset)?..to_usize(copy_offset + copy_size)?]
            .clone_from_slice(&data[to_usize(data_offset)?..to_usize(data_offset + copy_size)?]);
        write_aligned_all(blk_dev, block_offset, block_scratch)?;
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
    blk_dev: &mut (impl BlockDevice + ?Sized),
    offset: u64,
    data: &mut [u8],
    scratch: &mut [u8],
) -> Result<()> {
    debug_assert!(is_buffer_aligned(data, blk_dev.alignment())?);

    if is_aligned(offset, blk_dev.block_size())? {
        return write_aligned_offset_and_buffer(blk_dev, offset, data, scratch);
    }

    let aligned_start =
        min(round_up(offset, blk_dev.block_size())?, add(offset, data.len() as u64)?);
    let aligned_relative_offset = sub(aligned_start, offset)?;
    if aligned_relative_offset < data.len() as u64 {
        if is_buffer_aligned(&data[to_usize(aligned_relative_offset)?..], blk_dev.alignment())? {
            // If new address is aligned, write directly.
            write_aligned_offset_and_buffer(
                blk_dev,
                aligned_start,
                &data[to_usize(aligned_relative_offset)?..],
                scratch,
            )?;
        } else {
            let write_len = sub(data.len() as u64, aligned_relative_offset)?;
            // Swap the offset-aligned part to the beginning of the buffer (assumed aligned)
            swap_slice(data, to_usize(aligned_relative_offset)?);
            let res = write_aligned_offset_and_buffer(
                blk_dev,
                aligned_start,
                &data[..to_usize(write_len)?],
                scratch,
            );
            // Swap the two parts back before checking the result.
            swap_slice(data, to_usize(write_len)?);
            res?;
        }
    }

    // perform read-modify-write for the unaligned part.
    let block_scratch = &mut scratch[..to_usize(blk_dev.block_size())?];
    let round_down_offset = round_down(offset, blk_dev.block_size())?;
    read_aligned_all(blk_dev, round_down_offset, block_scratch)?;
    let offset_relative = sub(offset, round_down_offset)?;
    block_scratch[to_usize(offset_relative)?..to_usize(offset_relative + aligned_relative_offset)?]
        .clone_from_slice(&data[..to_usize(aligned_relative_offset)?]);
    write_aligned_all(blk_dev, round_down_offset, block_scratch)
}

/// Same as write_bytes(). Expcet that the API takes a mutable input bytes slice instead.
/// It does internal optimization that temporarily modifies `data` layout to minimize number of
/// calls to `blk_dev.read_blocks()`/`blk_dev.write_blocks()` (down to O(1)).
fn write_bytes_mut(
    blk_dev: &mut (impl BlockDevice + ?Sized),
    offset: u64,
    data: &mut [u8],
    scratch: &mut [u8],
) -> Result<()> {
    let (buffer_alignment_scratch, block_alignment_scratch) = split_scratch(blk_dev, scratch)?;
    if is_buffer_aligned(data, blk_dev.alignment())? {
        return write_aligned_buffer(blk_dev, offset, data, block_alignment_scratch);
    }

    // Buffer misalignment:
    // Case 1:
    //     |~~~~~~~~~~~~buffer~~~~~~~~~~~~|
    //   |----------------------|---------------------|
    //      blk_dev.alignment()
    //
    // Case 2:
    //    |~~~~~~buffer~~~~~|
    //  |----------------------|---------------------|
    //     blk_dev.alignment()

    // Write unaligned part
    let data_addr_value = data.as_ptr() as u64;
    let unaligned_write = min(
        sub(round_up(data_addr_value, blk_dev.alignment())?, data_addr_value)?,
        data.len() as u64,
    );
    let mut unaligned_data = &mut buffer_alignment_scratch[..to_usize(unaligned_write)?];
    unaligned_data.clone_from_slice(&data[..to_usize(unaligned_write)?]);
    write_aligned_buffer(blk_dev, offset, &mut unaligned_data, block_alignment_scratch)?;
    if unaligned_write == data.len() as u64 {
        return Ok(());
    }

    // Write aligned part
    write_aligned_buffer(
        blk_dev,
        add(offset, unaligned_write)?,
        &mut data[to_usize(unaligned_write)?..],
        block_alignment_scratch,
    )
}

/// Top level write API that accept mutable/immutable bytes slice
fn write<B>(
    blk_dev: &mut (impl BlockDevice + ?Sized),
    offset: u64,
    mut data: B,
    scratch: &mut [u8],
) -> Result<()>
where
    B: WriteBuffer,
{
    if let Some(slice) = data.as_mut_slice() {
        return write_bytes_mut(blk_dev, offset, slice, scratch);
    } else if let Some(slice) = data.as_slice() {
        return write_bytes(blk_dev, offset, slice, scratch);
    }

    Err(StorageError::InvalidInput)
}

/// The trait is for abstracting the representation of bytes data. The `write()` API will
/// choose different algorithm based on the return result of the methods. The library provides
/// native implementation for `&[u8]` and `&mut [u8]`. It's technically possilbe for users to
/// implement other types such as `Vec<u8>` etc.
pub trait WriteBuffer {
    /// Return a mutable bytes slice for the data. If the data cannot be mutable, returns None.
    fn as_mut_slice(&mut self) -> Option<&mut [u8]>;

    /// Return a bytes slice for the data. Return None if not supported.
    fn as_slice(&mut self) -> Option<&[u8]>;

    // Provided methods

    /// Return the length of the data.
    fn data_len(&mut self) -> Result<usize> {
        self.as_slice()
            .map(|v| v.len())
            .or(self.as_mut_slice().map(|v| v.len()))
            .ok_or(StorageError::InvalidInput)
    }
}

impl WriteBuffer for &[u8] {
    fn as_mut_slice(&mut self) -> Option<&mut [u8]> {
        None
    }

    fn as_slice(&mut self) -> Option<&[u8]> {
        Some(*self)
    }
}

impl WriteBuffer for &mut [u8] {
    fn as_mut_slice(&mut self) -> Option<&mut [u8]> {
        Some(*self)
    }

    fn as_slice(&mut self) -> Option<&[u8]> {
        None
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use core::mem::size_of;
    use Vec;

    pub struct TestBlockDevice {
        pub block_size: u64,
        pub alignment: u64,
        pub storage: Vec<u8>,
    }

    impl TestBlockDevice {
        pub fn new(alignment: u64, block_size: u64, storage_size: u64) -> Self {
            // Initialize default storage content.
            let storage: Vec<u8> = (0..storage_size).map(|x| x as u8).collect();
            return Self::new_with_data(alignment, block_size, &storage);
        }

        pub fn new_with_data(alignment: u64, block_size: u64, data: &[u8]) -> Self {
            Self { block_size: block_size, alignment: alignment, storage: Vec::from(data) }
        }
    }

    impl BlockDevice for TestBlockDevice {
        fn block_size(&mut self) -> u64 {
            self.block_size
        }

        fn num_blocks(&mut self) -> u64 {
            self.storage.len() as u64 / self.block_size()
        }

        fn alignment(&mut self) -> u64 {
            self.alignment
        }

        fn read_blocks(&mut self, blk_offset: u64, out: &mut [u8]) -> bool {
            assert!(is_buffer_aligned(out, self.alignment()).unwrap());
            assert!(is_aligned(out.len() as u64, self.block_size()).unwrap());
            let start = blk_offset * self.block_size();
            let end = start + out.len() as u64;
            out.clone_from_slice(&self.storage[to_usize(start).unwrap()..to_usize(end).unwrap()]);
            true
        }

        fn write_blocks(&mut self, blk_offset: u64, data: &[u8]) -> bool {
            assert!(is_buffer_aligned(data, self.alignment()).unwrap());
            assert!(is_aligned(data.len() as u64, self.block_size()).unwrap());
            let start = blk_offset * self.block_size();
            let end = start + data.len() as u64;
            self.storage[to_usize(start).unwrap()..to_usize(end).unwrap()].clone_from_slice(&data);
            true
        }
    }

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
            let buffer = vec![0u8; to_usize(size + alignment).unwrap()];
            Self { buffer, alignment, size }
        }

        pub fn get(&mut self) -> &mut [u8] {
            let addr = self.buffer.as_ptr() as u64;
            let aligned_start = round_up(addr, self.alignment).unwrap() - addr;
            &mut self.buffer
                [to_usize(aligned_start).unwrap()..to_usize(aligned_start + self.size).unwrap()]
        }
    }

    fn read_test_helper(case: &TestCase) {
        let mut blk_dev = TestBlockDevice::new(case.alignment, case.block_size, case.storage_size);
        // Make an aligned buffer. A misaligned version is created by taking a sub slice that
        // starts at an unaligned offset. Because of this we need to allocate
        // `case.misalignment` more to accommodate it.
        let mut aligned_buf = AlignedBuffer::new(case.alignment, case.rw_size + case.misalignment);
        let out = &mut aligned_buf.get()[to_usize(case.misalignment).unwrap()
            ..to_usize(case.misalignment + case.rw_size).unwrap()];
        let scratch = &mut vec![0u8; required_scratch_size(&mut blk_dev).unwrap()];
        blk_dev.read(case.rw_offset, out, scratch).unwrap();
        assert_eq!(
            out.to_vec(),
            blk_dev.storage[to_usize(case.rw_offset).unwrap()
                ..to_usize(case.rw_offset + case.rw_size).unwrap()]
                .to_vec(),
            "Failed. Test case {:?}",
            case,
        );
    }

    fn write_test_helper(
        case: &TestCase,
        write_func: fn(&mut TestBlockDevice, u64, &mut [u8]) -> Result<()>,
    ) {
        let mut blk_dev = TestBlockDevice::new(case.alignment, case.block_size, case.storage_size);
        // Write a reverse version of the current data.
        let mut expected = blk_dev.storage
            [to_usize(case.rw_offset).unwrap()..to_usize(case.rw_offset + case.rw_size).unwrap()]
            .to_vec();
        expected.reverse();
        // Make an aligned buffer. A misaligned version is created by taking a sub slice that
        // starts at an unaligned offset. Because of this we need to allocate
        // `case.misalignment` more to accommodate it.
        let mut aligned_buf = AlignedBuffer::new(case.alignment, case.rw_size + case.misalignment);
        let data = &mut aligned_buf.get()[to_usize(case.misalignment).unwrap()
            ..to_usize(case.misalignment + case.rw_size).unwrap()];
        data.clone_from_slice(&expected);
        write_func(&mut blk_dev, case.rw_offset, data).unwrap();
        assert_eq!(
            expected,
            blk_dev.storage[to_usize(case.rw_offset).unwrap()
                ..to_usize(case.rw_offset + case.rw_size).unwrap()]
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
                    let func = |blk_dev: &mut TestBlockDevice, offset: u64, data: &mut [u8]| {
                        let scratch = &mut vec![0u8; required_scratch_size(blk_dev).unwrap()];
                        blk_dev.write(offset, data as &[u8], scratch)
                    };
                    write_test_helper(&TestCase::new($x0, $x1, $x2, $x3, $x4, $x5), func);
                }

                #[test]
                fn write_scaled_test() {
                    // Scaled all parameters by double and test again.
                    let func = |blk_dev: &mut TestBlockDevice, offset: u64, data: &mut [u8]| {
                        let scratch = &mut vec![0u8; required_scratch_size(blk_dev).unwrap()];
                        blk_dev.write(offset, data as &[u8], scratch)
                    };
                    let (x0, x1, x2, x3, x4, x5) =
                        (2 * $x0, 2 * $x1, 2 * $x2, 2 * $x3, 2 * $x4, 2 * $x5);
                    write_test_helper(&TestCase::new(x0, x1, x2, x3, x4, x5), func);
                }

                // Input bytes slice is a mutable reference
                #[test]
                fn write_mut_test() {
                    let func = |blk_dev: &mut TestBlockDevice, offset: u64, data: &mut [u8]| {
                        let scratch = &mut vec![0u8; required_scratch_size(blk_dev).unwrap()];
                        blk_dev.write(offset, data, scratch)
                    };
                    write_test_helper(&TestCase::new($x0, $x1, $x2, $x3, $x4, $x5), func);
                }

                #[test]
                fn write_mut_scaled_test() {
                    // Scaled all parameters by double and test again.
                    let (x0, x1, x2, x3, x4, x5) =
                        (2 * $x0, 2 * $x1, 2 * $x2, 2 * $x3, 2 * $x4, 2 * $x5);
                    let func = |blk_dev: &mut TestBlockDevice, offset: u64, data: &mut [u8]| {
                        let scratch = &mut vec![0u8; required_scratch_size(blk_dev).unwrap()];
                        blk_dev.write(offset, data, scratch)
                    };
                    write_test_helper(&TestCase::new(x0, x1, x2, x3, x4, x5), func);
                }
            }
        };
    }

    const BLOCK_SIZE: u64 = 512;
    const ALIGNMENT: u64 = 64;
    const STORAGE: u64 = BLOCK_SIZE * 3;

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
    fn test_scratch_too_small() {
        let block_size: u64 = 512;
        let alignment: u64 = 64;
        let mut blk_dev = TestBlockDevice::new(alignment, block_size, block_size * 3);
        let mut scratch = vec![0u8; to_usize(block_size + 2 * alignment - 1).unwrap()];
        assert!(blk_dev
            .read(0, &mut vec![0u8; to_usize(block_size).unwrap()], &mut scratch)
            .is_err());
    }

    #[test]
    fn test_read_overflow() {
        let mut blk_dev = TestBlockDevice::new(1, 1, 512);
        let scratch = &mut vec![0u8; required_scratch_size(&mut blk_dev).unwrap()];
        assert!(blk_dev.read(512, &mut vec![0u8; 1], scratch).is_err());
        assert!(blk_dev.read(0, &mut vec![0u8; 513], scratch).is_err());
    }

    #[test]
    fn test_read_arithmetic_overflow() {
        let mut blk_dev = TestBlockDevice::new(1, 1, 512);
        let scratch = &mut vec![0u8; required_scratch_size(&mut blk_dev).unwrap()];
        assert!(blk_dev.read(u64::MAX, &mut vec![0u8; 1], scratch).is_err());
    }

    #[test]
    fn test_write_overflow() {
        let mut blk_dev = TestBlockDevice::new(1, 1, 512);
        let scratch = &mut vec![0u8; required_scratch_size(&mut blk_dev).unwrap()];
        assert!(blk_dev.write(512, vec![0u8; 1].as_mut_slice(), scratch).is_err());
        assert!(blk_dev.write(0, vec![0u8; 513].as_mut_slice(), scratch).is_err());

        assert!(blk_dev.write(512, vec![0u8; 1].as_slice(), scratch).is_err());
        assert!(blk_dev.write(0, vec![0u8; 513].as_slice(), scratch).is_err());
    }

    #[test]
    fn test_write_arithmetic_overflow() {
        let mut blk_dev = TestBlockDevice::new(1, 1, 512);
        let scratch = &mut vec![0u8; required_scratch_size(&mut blk_dev).unwrap()];
        assert!(blk_dev.write(u64::MAX, vec![0u8; 1].as_mut_slice(), scratch).is_err());
        assert!(blk_dev.write(u64::MAX, vec![0u8; 1].as_slice(), scratch).is_err());
    }

    #[test]
    fn test_u64_not_narrower_than_usize() {
        // If this ever fails we need to adjust all code for >64 bit pointers and size.
        assert!(size_of::<u64>() >= size_of::<*const u8>());
        assert!(size_of::<u64>() >= size_of::<usize>());
    }
}
