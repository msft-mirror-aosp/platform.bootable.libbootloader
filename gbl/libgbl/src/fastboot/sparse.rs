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

use core::{
    cmp::{max, min},
    mem::size_of,
};
use liberror::Error;
use static_assertions::const_assert;
use zerocopy::{FromBytes, Immutable, IntoBytes, Ref};

// TODO(b/331854173): Switch to use bindgen for the following type definitions once
// system/core/libsparse is added to repo checkout.

const HEADER_MAGIC: u32 = 0xED26FF3A;
const CHUNK_TYPE_RAW: u16 = 0xCAC1;
const CHUNK_TYPE_FILL: u16 = 0xCAC2;
const CHUNK_TYPE_DONT_CARE: u16 = 0xCAC3;
const CHUNK_TYPE_CRC32: u16 = 0xCAC4;

const SPARSE_HEADER_MAJOR_VER: u16 = 1;
const SPARSE_HEADER_MINOR_VER: u16 = 0;

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, Immutable, IntoBytes, FromBytes)]
pub struct SparseHeader {
    pub magic: u32,
    pub major_version: u16,
    pub minor_version: u16,
    pub file_hdr_sz: u16,
    pub chunk_hdr_sz: u16,
    pub blk_sz: u32,
    pub total_blks: u32,
    pub total_chunks: u32,
    pub image_checksum: u32,
}

impl SparseHeader {
    /// Returns the total size in bytes for the data after unsparsified.
    pub fn data_size(&self) -> u64 {
        (self.total_blks as u64) * (self.blk_sz as u64)
    }
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, IntoBytes, FromBytes)]
pub struct ChunkHeader {
    pub chunk_type: u16,
    pub reserved1: u16,
    pub chunk_sz: u32,
    pub total_sz: u32,
}

const ERR_ARITHMETIC_OVERFLOW: &str = "Arithmetic Overflow";
const ERR_IMAGE_SIZE: &str = "Bad image. Invalid image size";

/// Checks if a sparse image is valid and returns the sparse header.
pub fn is_sparse_image(sparse_img: &[u8]) -> Result<SparseHeader, Error> {
    let sparse_header: SparseHeader = copy_from(sparse_img)?;
    if sparse_header.magic != HEADER_MAGIC {
        return Err("Sparse magic mismatch".into());
    } else if sparse_header.major_version != SPARSE_HEADER_MAJOR_VER {
        return Err("Sparse major version mismatch".into());
    } else if sparse_header.minor_version != SPARSE_HEADER_MINOR_VER {
        return Err("Sparse minor version mismatch".into());
    }
    Ok(sparse_header)
}

/// `FillInfo` is derived from a sparse chunk and contains information whether to fill a value or
/// skip for a number of blocks.
///
/// Context and uses:
///
/// When writing fill chunks from a sparse image, it is usually better to write a larger buffer
/// with the filled value instead of a single u32 at a time. However, separately maintaining a fill
/// buffer can be inconvenient for the caller. Therefore, we use a strategy that re-uses the input
/// buffer for fill buffer.
///
/// The idea is to write the sparse image in two passes. In the first pass, we only write non-fill
/// chunks. For each sparse chunk, we create a `FillInfo` and append it from the beginning of the
/// input buffer. For fill chunks, `FillInfo::fill_blocks` and
/// `FillInfo::fill_value_or_skip_blocks` are set to the chunk size and fill value. For others,
/// `FillInfo::fill_blocks` will be set to 0 and `FillInfo::fill_value_or_skip_blocks` will be set
/// to the chunk size instead to represent number of blocks to skip. The second pass writes the
/// fill chunk according to `FillInfo`.
///
/// Because a sparse chunk is at least 12 bytes, whereas `FillInfo` is 8 bytes, at the end of the
/// first pass, we are guaranteed to have at least 1/3 of the input buffer free to use as fill
/// buffer.
#[repr(C, packed)]
#[derive(Debug, Default, Copy, Clone, Immutable, IntoBytes, FromBytes)]
struct FillInfo {
    // Number of blocks to fill.
    pub fill_blocks: u32,
    // If `fill_blocks` is None, this field represents the number of blocks to skip.
    // Otherwise, it represents the fill value.
    pub fill_value_or_skip_blocks: u32,
}

impl FillInfo {
    /// Creates an instance that represents filling a number of blocks.
    fn new_fill(blocks: u32, value: u32) -> Self {
        assert_ne!(blocks, 0);
        Self { fill_blocks: blocks, fill_value_or_skip_blocks: value }
    }

    /// Creates an instance that represents skipping a number of blocks.
    fn new_skip(blocks: u32) -> Self {
        Self { fill_blocks: 0, fill_value_or_skip_blocks: blocks }
    }

    // Returns (blocks, None) for the skip case or (blocks, Some(value)) for the fill case.
    fn get_blocks_and_value(&self) -> (u32, Option<u32>) {
        match self.fill_blocks {
            0 => (self.fill_value_or_skip_blocks, None),
            v => (v, Some(self.fill_value_or_skip_blocks)),
        }
    }
}

const_assert!(size_of::<FillInfo>() < size_of::<ChunkHeader>());

/// `SparseRawWriter` defines an interface for writing to raw storage used by `write_sparse_image`.
pub(crate) trait SparseRawWriter {
    /// Writes bytes from `data` to the destination storage at offset `off`
    async fn write(&mut self, off: u64, data: &mut [u8]) -> Result<(), Error>;
}

/// Write a sparse image in `sparse_img`.
///
/// # Args
//
/// * `sparse_img`: The input buffer containing the sparse image. The API modifes input buffer for
///   internal optimization.
/// * `writer`: An implementation of `SparseRawWriter`.
///
/// # Returns
///
/// Returns the total number of bytes written, including don't care chunks.
pub async fn write_sparse_image(
    sparse_img: &mut [u8],
    writer: &mut impl SparseRawWriter,
) -> Result<u64, Error> {
    let sparse_header: SparseHeader = is_sparse_image(sparse_img)?;
    let mut curr: usize = size_of::<SparseHeader>();
    let mut write_offset = 0u64;

    // First pass. Writes non-fill chunk and constructs `FillInfo`.
    let mut fill_off = 0usize;
    for _ in 0..sparse_header.total_chunks {
        let header: ChunkHeader = copy_from(&mut sparse_img[curr..])?;
        let payload = &mut sparse_img[curr + size_of::<ChunkHeader>()..];
        let payload_sz = u64_mul(header.chunk_sz, sparse_header.blk_sz)?;
        let mut fill = FillInfo::new_skip(header.chunk_sz);
        match header.chunk_type {
            CHUNK_TYPE_RAW => {
                writer.write(write_offset, get_mut(payload, 0, to_usize(payload_sz)?)?).await?;
            }
            CHUNK_TYPE_FILL if header.chunk_sz != 0 => {
                let fill_val = u32::from_le_bytes(get_mut(payload, 0, 4)?.try_into().unwrap());
                fill = FillInfo::new_fill(header.chunk_sz, fill_val);
            }
            CHUNK_TYPE_DONT_CARE | CHUNK_TYPE_CRC32 => {}
            _ => return Err("Invalid Chunk Type".into()),
        };
        write_offset = u64_add(write_offset, payload_sz)?;
        sparse_img[fill_off..][..size_of::<FillInfo>()].clone_from_slice(fill.as_bytes());
        fill_off = usize_add(fill_off, size_of::<FillInfo>())?;
        curr = usize_add(curr, header.total_sz)?;
    }
    let total = write_offset;

    // Second pass. Writes fill chunks.
    // Use all reamining buffer as fill buffer.
    let (fill_infos, fill_buffer) = sparse_img.split_at_mut(fill_off);
    let mut fill_buffer = FillBuffer { curr_val: None, curr_size: 0, buffer: fill_buffer };
    let fill_infos = Ref::<_, [FillInfo]>::new_slice(fill_infos).unwrap().into_slice();
    write_offset = 0;
    for ele in fill_infos {
        match ele.get_blocks_and_value() {
            (blks, None) => {
                write_offset = u64_add(write_offset, u64_mul(blks, sparse_header.blk_sz)?)?;
            }
            (blks, Some(v)) => {
                let sz = u64_mul(blks, sparse_header.blk_sz)?;
                let buffer = fill_buffer.get(v, sz)?;
                let buffer_len = to_u64(buffer.len())?;
                let end = u64_add(write_offset, sz)?;
                while write_offset < end {
                    let to_write = min(buffer_len, end - write_offset);
                    writer.write(write_offset, &mut buffer[..to_usize(to_write).unwrap()]).await?;
                    write_offset += to_write;
                }
            }
        }
    }
    Ok(total)
}

/// `FillUnit` is a packed C struct wrapping a u32. It is mainly used for filling a buffer of
/// arbitrary alignment with a u32 value.
#[repr(C, packed)]
#[derive(Debug, Default, Copy, Clone, Immutable, IntoBytes, FromBytes)]
struct FillUnit(u32);

/// `FillBuffer` manages a buffer and provides API for making a fill buffer with the given value.
struct FillBuffer<'a> {
    curr_val: Option<u32>,
    curr_size: usize,
    buffer: &'a mut [u8],
}

impl FillBuffer<'_> {
    /// Get a buffer up to `size` number of bytes filled with `val`.
    fn get(&mut self, val: u32, size: u64) -> Result<&mut [u8], Error> {
        let aligned_len = self.buffer.len() - (self.buffer.len() % size_of::<u32>());
        let size: usize = min(to_u64(aligned_len)?, size).try_into().unwrap();
        if Some(val) != self.curr_val {
            self.curr_size = 0;
            self.curr_val = Some(val);
        }
        let gap = max(self.curr_size, size) - self.curr_size;
        let to_fill = &mut self.buffer[self.curr_size..][..gap];
        Ref::<_, [FillUnit]>::new_slice(to_fill).unwrap().into_mut_slice().fill(FillUnit(val));
        self.curr_size += gap;
        Ok(&mut self.buffer[..size])
    }
}

/// A helper to check and get a mutable sub slice.
fn get_mut<L: TryInto<usize>, R: TryInto<usize>>(
    bytes: &mut [u8],
    start: L,
    end: R,
) -> Result<&mut [u8], Error> {
    bytes.get_mut(to_usize(start)?..to_usize(end)?).ok_or(ERR_IMAGE_SIZE.into())
}

/// A helper to check and get a sub slice.
fn get<L: TryInto<usize>, R: TryInto<usize>>(
    bytes: &[u8],
    start: L,
    end: R,
) -> Result<&[u8], Error> {
    bytes.get(to_usize(start)?..to_usize(end)?).ok_or(ERR_IMAGE_SIZE.into())
}

/// A helper to return a copy of a zerocopy object from bytes.
fn copy_from<T: IntoBytes + FromBytes + Default>(bytes: &[u8]) -> Result<T, Error> {
    let mut res: T = Default::default();
    res.as_bytes_mut().clone_from_slice(get(bytes, 0, size_of::<T>())?);
    Ok(res)
}

// Investigate switching the following to use SafeNum. A naive replacement results in too many
// `try_into()?` callsites which looks chaotics. Some proper wrapper might still be needed.

/// Checks and converts an integer into usize.
fn to_usize<T: TryInto<usize>>(val: T) -> Result<usize, Error> {
    Ok(val.try_into().map_err(|_| ERR_ARITHMETIC_OVERFLOW)?)
}

/// Adds two usize convertible numbers and checks overflow.
fn usize_add<L: TryInto<usize>, R: TryInto<usize>>(lhs: L, rhs: R) -> Result<usize, Error> {
    Ok(to_usize(lhs)?.checked_add(to_usize(rhs)?).ok_or(ERR_ARITHMETIC_OVERFLOW)?)
}

/// Checks and converts an integer into u64
fn to_u64<T: TryInto<u64>>(val: T) -> Result<u64, Error> {
    Ok(val.try_into().map_err(|_| ERR_ARITHMETIC_OVERFLOW)?)
}

/// Adds two u64 convertible numbers and checks overflow.
fn u64_add<L: TryInto<u64>, R: TryInto<u64>>(lhs: L, rhs: R) -> Result<u64, Error> {
    Ok(to_u64(lhs)?.checked_add(to_u64(rhs)?).ok_or(ERR_ARITHMETIC_OVERFLOW)?)
}

/// Multiplies two u64 convertible numbers and checks overflow.
fn u64_mul<L: TryInto<u64>, R: TryInto<u64>>(lhs: L, rhs: R) -> Result<u64, Error> {
    Ok(to_u64(lhs)?.checked_mul(to_u64(rhs)?).ok_or(ERR_ARITHMETIC_OVERFLOW)?)
}

#[cfg(test)]
mod test {
    use super::*;
    use gbl_async::block_on;

    impl SparseRawWriter for Vec<u8> {
        async fn write(&mut self, off: u64, data: &mut [u8]) -> Result<(), Error> {
            self[off.try_into().unwrap()..][..data.len()].clone_from_slice(data);
            Ok(())
        }
    }

    #[test]
    fn test_sparse_write() {
        let raw = include_bytes!("../../testdata/sparse_test_raw.bin");
        let sparse = include_bytes!("../../testdata/sparse_test.bin");
        // Gives a larger output buffer.
        let mut out = vec![0u8; 2 * raw.len()];
        assert_eq!(
            block_on(write_sparse_image(&mut sparse.to_vec()[..], &mut out)).unwrap(),
            raw.len().try_into().unwrap()
        );
        assert_eq!(out[..raw.len()].to_vec(), raw);
    }

    #[test]
    fn test_sparse_write_non_default_block_size() {
        let raw = include_bytes!("../../testdata/sparse_test_raw.bin");
        let sparse = include_bytes!("../../testdata/sparse_test_blk1024.bin");
        // Gives a larger output buffer.
        let mut out = vec![0u8; 2 * raw.len()];
        assert_eq!(
            block_on(write_sparse_image(&mut sparse.to_vec()[..], &mut out)).unwrap(),
            raw.len().try_into().unwrap()
        );
        assert_eq!(out[..raw.len()].to_vec(), raw);
    }

    /// A helper to copy a zerocopy object into a buffer
    fn copy_to<T: Immutable + IntoBytes + FromBytes>(val: &T, bytes: &mut [u8]) {
        bytes[..size_of::<T>()].clone_from_slice(val.as_bytes());
    }

    #[test]
    fn test_sparse_invalid_magic() {
        let mut sparse = include_bytes!("../../testdata/sparse_test.bin").to_vec();
        let mut sparse_header: SparseHeader = copy_from(&sparse[..]).unwrap();
        sparse_header.magic = 0;
        copy_to(&sparse_header, &mut sparse[..]);
        assert!(block_on(write_sparse_image(&mut sparse[..], &mut vec![])).is_err());
    }

    #[test]
    fn test_sparse_invalid_major_version() {
        let mut sparse = include_bytes!("../../testdata/sparse_test.bin").to_vec();
        let mut sparse_header: SparseHeader = copy_from(&sparse[..]).unwrap();
        sparse_header.major_version = SPARSE_HEADER_MAJOR_VER + 1;
        copy_to(&sparse_header, &mut sparse[..]);
        assert!(block_on(write_sparse_image(&mut sparse[..], &mut vec![])).is_err());
    }

    #[test]
    fn test_sparse_invalid_minor_version() {
        let mut sparse = include_bytes!("../../testdata/sparse_test.bin").to_vec();
        let mut sparse_header: SparseHeader = copy_from(&sparse[..]).unwrap();
        sparse_header.minor_version = SPARSE_HEADER_MINOR_VER + 1;
        copy_to(&sparse_header, &mut sparse[..]);
        assert!(block_on(write_sparse_image(&mut sparse[..], &mut vec![])).is_err());
    }
}
