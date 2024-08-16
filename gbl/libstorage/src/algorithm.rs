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

use crate::{
    aligned_subslice, check_range, is_aligned, is_buffer_aligned, BlockInfo, BlockIoAsync,
    BlockIoSync,
};
use core::cmp::min;
use gbl_async::block_on;
use liberror::Result;
use safemath::SafeNum;

/// Reads from a range at block boundary to an aligned buffer.
async fn read_aligned_all(io: &mut impl BlockIoAsync, offset: u64, out: &mut [u8]) -> Result<()> {
    let blk_offset = check_range(io.info(), offset, out)?.try_into()?;
    Ok(io.read_blocks(blk_offset, out).await?)
}

/// Read with block-aligned offset and aligned buffer. Size don't need to be block aligned.
///   |~~~~~~~~~read~~~~~~~~~|
///   |---------|---------|---------|
async fn read_aligned_offset_and_buffer(
    io: &mut impl BlockIoAsync,
    offset: u64,
    out: &mut [u8],
    scratch: &mut [u8],
) -> Result<()> {
    let block_size = SafeNum::from(io.info().block_size);
    debug_assert!(is_aligned(offset.into(), block_size)?);
    debug_assert!(is_buffer_aligned(out, io.info().alignment)?);

    let aligned_read: usize = SafeNum::from(out.len()).round_down(block_size).try_into()?;

    if aligned_read > 0 {
        read_aligned_all(io, offset, &mut out[..aligned_read]).await?;
    }
    let unaligned = &mut out[aligned_read..];
    if unaligned.is_empty() {
        return Ok(());
    }
    // Read unalinged part.
    let block_scratch = &mut scratch[..block_size.try_into()?];
    let aligned_offset = SafeNum::from(offset) + aligned_read;
    read_aligned_all(io, aligned_offset.try_into()?, block_scratch).await?;
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
async fn read_aligned_buffer(
    io: &mut impl BlockIoAsync,
    offset: u64,
    out: &mut [u8],
    scratch: &mut [u8],
) -> Result<()> {
    debug_assert!(is_buffer_aligned(out, io.info().alignment)?);

    if is_aligned(offset.into(), io.info().block_size.into())? {
        return read_aligned_offset_and_buffer(io, offset, out, scratch).await;
    }
    let offset = SafeNum::from(offset);
    let aligned_start: u64 =
        min(offset.round_up(io.info().block_size).try_into()?, (offset + out.len()).try_into()?);

    let aligned_relative_offset: usize = (SafeNum::from(aligned_start) - offset).try_into()?;
    if aligned_relative_offset < out.len() {
        if is_buffer_aligned(&out[aligned_relative_offset..], io.info().alignment)? {
            // If new output address is aligned, read directly.
            read_aligned_offset_and_buffer(
                io,
                aligned_start,
                &mut out[aligned_relative_offset..],
                scratch,
            )
            .await?;
        } else {
            // Otherwise read into `out` (assumed aligned) and memmove to the correct
            // position
            let read_len: usize =
                (SafeNum::from(out.len()) - aligned_relative_offset).try_into()?;
            read_aligned_offset_and_buffer(io, aligned_start, &mut out[..read_len], scratch)
                .await?;
            out.copy_within(..read_len, aligned_relative_offset);
        }
    }

    // Now read the unaligned part
    let block_scratch = &mut scratch[..SafeNum::from(io.info().block_size).try_into()?];
    let round_down_offset = offset.round_down(io.info().block_size);
    read_aligned_all(io, round_down_offset.try_into()?, block_scratch).await?;
    let offset_relative = offset - round_down_offset;
    let unaligned = &mut out[..aligned_relative_offset];
    unaligned.clone_from_slice(
        &block_scratch
            [offset_relative.try_into()?..(offset_relative + unaligned.len()).try_into()?],
    );
    Ok(())
}

// Partition a scratch into two aligned parts: [u8; alignment()-1] and [u8; block_size())]
// for handling block and buffer misalignment respecitvely.
fn split_scratch<'a>(
    info: BlockInfo,
    scratch: &'a mut [u8],
) -> Result<(&'a mut [u8], &'a mut [u8])> {
    let (buffer_alignment, block_alignment) = aligned_subslice(scratch, info.alignment)?
        .split_at_mut((SafeNum::from(info.alignment) - 1).try_into()?);
    let block_alignment = aligned_subslice(block_alignment, info.alignment)?;
    let block_alignment_scratch_size = match info.block_size {
        1 => SafeNum::ZERO,
        v => v.into(),
    };
    Ok((buffer_alignment, &mut block_alignment[..block_alignment_scratch_size.try_into()?]))
}

/// Read with no alignment requirement.
pub async fn read_async(
    io: &mut impl BlockIoAsync,
    offset: u64,
    out: &mut [u8],
    scratch: &mut [u8],
) -> Result<()> {
    let (buffer_alignment_scratch, block_alignment_scratch) = split_scratch(io.info(), scratch)?;

    if is_buffer_aligned(out, io.info().alignment)? {
        return read_aligned_buffer(io, offset, out, block_alignment_scratch).await;
    }

    // Buffer misalignment:
    // Case 1:
    //     |~~~~~~~~~~~~buffer~~~~~~~~~~~~|
    //   |----------------------|---------------------|
    //      io.info().alignment
    //
    // Case 2:
    //    |~~~~~~buffer~~~~~|
    //  |----------------------|---------------------|
    //     io.info().alignment

    let out_addr_value = SafeNum::from(out.as_ptr() as usize);
    let unaligned_read: usize =
        min((out_addr_value.round_up(io.info().alignment) - out_addr_value).try_into()?, out.len());

    // Read unaligned part
    let unaligned_out = &mut buffer_alignment_scratch[..unaligned_read];
    read_aligned_buffer(io, offset, unaligned_out, block_alignment_scratch).await?;
    out[..unaligned_read].clone_from_slice(unaligned_out);

    if unaligned_read == out.len() {
        return Ok(());
    }
    // Read aligned part
    read_aligned_buffer(
        io,
        (SafeNum::from(offset) + unaligned_read).try_into()?,
        &mut out[unaligned_read..],
        block_alignment_scratch,
    )
    .await
}

/// Write bytes from aligned buffer to a block boundary range.
async fn write_aligned_all(io: &mut impl BlockIoAsync, offset: u64, data: &mut [u8]) -> Result<()> {
    let blk_offset = check_range(io.info(), offset, data)?.try_into()?;
    Ok(io.write_blocks(blk_offset, data).await?)
}

/// Write with block-aligned offset and aligned buffer. `data.len()` can be unaligned.
///   |~~~~~~~~~size~~~~~~~~~|
///   |---------|---------|---------|
async fn write_aligned_offset_and_buffer(
    io: &mut impl BlockIoAsync,
    offset: u64,
    data: &mut [u8],
    scratch: &mut [u8],
) -> Result<()> {
    debug_assert!(is_aligned(offset.into(), io.info().block_size.into())?);
    debug_assert!(is_buffer_aligned(data, io.info().alignment)?);

    let aligned_write: usize =
        SafeNum::from(data.len()).round_down(io.info().block_size).try_into()?;
    if aligned_write > 0 {
        write_aligned_all(io, offset, &mut data[..aligned_write]).await?;
    }
    let unaligned = &data[aligned_write..];
    if unaligned.len() == 0 {
        return Ok(());
    }

    // Perform read-modify-write for the unaligned part
    let unaligned_start: u64 = (SafeNum::from(offset) + aligned_write).try_into()?;
    let block_scratch = &mut scratch[..SafeNum::from(io.info().block_size).try_into()?];
    read_aligned_all(io, unaligned_start, block_scratch).await?;
    block_scratch[..unaligned.len()].clone_from_slice(unaligned);
    write_aligned_all(io, unaligned_start, block_scratch).await
}

// Rotates buffer to the left.
fn rotate_left(slice: &mut [u8], sz: usize, scratch: &mut [u8]) {
    scratch[..sz].clone_from_slice(&slice[..sz]);
    slice.copy_within(sz.., 0);
    let off = slice.len().checked_sub(sz).unwrap();
    slice[off..].clone_from_slice(&scratch[..sz]);
}

// Rotates buffer to the right.
fn rotate_right(slice: &mut [u8], sz: usize, scratch: &mut [u8]) {
    let off = slice.len().checked_sub(sz).unwrap();
    scratch[..sz].clone_from_slice(&slice[off..]);
    slice.copy_within(..off, sz);
    slice[..sz].clone_from_slice(&scratch[..sz]);
}

/// Write with aligned buffer. Offset and size don't need to be block aligned.
/// Case 1:
///            |~~~~~~write~~~~~~~|
///        |------------|------------|
/// Case 2:
///          |~~~write~~~|
///        |---------------|--------------|
async fn write_aligned_buffer(
    io: &mut impl BlockIoAsync,
    offset: u64,
    data: &mut [u8],
    scratch: &mut [u8],
) -> Result<()> {
    debug_assert!(is_buffer_aligned(data, io.info().alignment)?);

    let offset = SafeNum::from(offset);
    if is_aligned(offset, io.info().block_size.into())? {
        return write_aligned_offset_and_buffer(io, offset.try_into()?, data, scratch).await;
    }

    let aligned_start: u64 =
        min(offset.round_up(io.info().block_size).try_into()?, (offset + data.len()).try_into()?);
    let aligned_relative_offset: usize = (SafeNum::from(aligned_start) - offset).try_into()?;
    if aligned_relative_offset < data.len() {
        if is_buffer_aligned(&data[aligned_relative_offset..], io.info().alignment)? {
            // If new address is aligned, write directly.
            write_aligned_offset_and_buffer(
                io,
                aligned_start,
                &mut data[aligned_relative_offset..],
                scratch,
            )
            .await?;
        } else {
            let write_len: usize =
                (SafeNum::from(data.len()) - aligned_relative_offset).try_into()?;
            // Swap the offset-aligned part to the beginning of the buffer (assumed aligned)
            rotate_left(data, aligned_relative_offset, scratch);
            let res =
                write_aligned_offset_and_buffer(io, aligned_start, &mut data[..write_len], scratch)
                    .await;
            // Swap the two parts back before checking the result.
            rotate_right(data, aligned_relative_offset, scratch);
            res?;
        }
    }

    // perform read-modify-write for the unaligned part.
    let block_scratch = &mut scratch[..SafeNum::from(io.info().block_size).try_into()?];
    let round_down_offset: u64 = offset.round_down(io.info().block_size).try_into()?;
    read_aligned_all(io, round_down_offset, block_scratch).await?;
    let offset_relative = offset - round_down_offset;
    block_scratch
        [offset_relative.try_into()?..(offset_relative + aligned_relative_offset).try_into()?]
        .clone_from_slice(&data[..aligned_relative_offset]);
    write_aligned_all(io, round_down_offset, block_scratch).await
}

/// Writes bytes to the block device.
/// It does internal optimization that temporarily modifies `data` layout to minimize number of
/// calls to `io.read_blocks()`/`io.write_blocks()` (down to O(1)).
pub async fn write_async(
    io: &mut impl BlockIoAsync,
    offset: u64,
    data: &mut [u8],
    scratch: &mut [u8],
) -> Result<()> {
    let (buffer_alignment_scratch, block_alignment_scratch) = split_scratch(io.info(), scratch)?;
    if is_buffer_aligned(data, io.info().alignment)? {
        return write_aligned_buffer(io, offset, data, block_alignment_scratch).await;
    }

    // Buffer misalignment:
    // Case 1:
    //     |~~~~~~~~~~~~buffer~~~~~~~~~~~~|
    //   |----------------------|---------------------|
    //      io.alignment()
    //
    // Case 2:
    //    |~~~~~~buffer~~~~~|
    //  |----------------------|---------------------|
    //     io.alignment()

    // Write unaligned part
    let data_addr_value = SafeNum::from(data.as_ptr() as usize);
    let unaligned_write: usize = min(
        (data_addr_value.round_up(io.info().alignment) - data_addr_value).try_into()?,
        data.len(),
    );
    let mut unaligned_data = &mut buffer_alignment_scratch[..unaligned_write];
    unaligned_data.clone_from_slice(&data[..unaligned_write]);
    write_aligned_buffer(io, offset, &mut unaligned_data, block_alignment_scratch).await?;
    if unaligned_write == data.len() {
        return Ok(());
    }

    // Write aligned part
    write_aligned_buffer(
        io,
        (SafeNum::from(offset) + unaligned_write).try_into()?,
        &mut data[unaligned_write..],
        block_alignment_scratch,
    )
    .await
}

/// `AsyncAsSync` wraps a `BlockIoAsync` trait object and implement `BlockIoSync` interfaces. It
/// simply blocks until IO completes.
pub struct AsyncAsSync<T: BlockIoAsync>(T);

impl<T: BlockIoAsync> AsyncAsSync<T> {
    /// Creates a new instance
    pub fn new(io: T) -> Self {
        Self(io)
    }

    /// Returns the `BlockIoAsync`.
    pub fn io(&mut self) -> &mut T {
        &mut self.0
    }
}

impl<T: BlockIoAsync> BlockIoSync for AsyncAsSync<T> {
    fn info(&mut self) -> BlockInfo {
        self.0.info()
    }

    fn read_blocks(&mut self, blk_offset: u64, out: &mut [u8]) -> Result<()> {
        block_on(self.0.read_blocks(blk_offset, out))
    }

    fn write_blocks(&mut self, blk_offset: u64, data: &mut [u8]) -> Result<()> {
        block_on(self.0.write_blocks(blk_offset, data))
    }
}

/// `SyncAsAsync` wraps a `BlockIoSync` and implements `BlockIoAsync` interfaces with blocking
/// operation under the hood.
pub struct SyncAsAsync<T: BlockIoSync>(T);

impl<T: BlockIoSync> SyncAsAsync<T> {
    /// Creates a new instance
    pub fn new(io: T) -> Self {
        Self(io)
    }

    /// Returns the `BlockIoSync`.
    pub fn io(&mut self) -> &mut T {
        &mut self.0
    }
}

// SAFETY:
// * Implementation of `read_blocks()` and `write_blocks()` are blocking. It will not keep retaining
//   the buffer after the function returns.
// * `Self::check_status(buf)` does not dereference input pointer.
impl<T: BlockIoSync> BlockIoAsync for SyncAsAsync<T> {
    fn info(&mut self) -> BlockInfo {
        self.0.info()
    }

    async fn read_blocks(&mut self, blk_offset: u64, out: &mut [u8]) -> Result<()> {
        self.0.read_blocks(blk_offset, out)
    }

    async fn write_blocks(&mut self, blk_offset: u64, data: &mut [u8]) -> Result<()> {
        self.0.write_blocks(blk_offset, data)
    }
}
