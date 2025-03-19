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

//! Image decompression support.

// gzip [DeflateDecoder] requires heap allocation.
extern crate alloc;

use crate::{gbl_print, gbl_println, GblOps};
use liberror::{Error, Result};
use lz4_flex::decompress_into;
use zune_inflate::DeflateDecoder;

const LZ4_NEXT_BLOCK_FAILED_ERROR_MESSAGE: &str =
    "Failed to handle next block of lz4-compressed kernel";

/// Returns if the data is a gzip compressed data.
fn is_gzip_compressed(data: &[u8]) -> bool {
    data.starts_with(b"\x1f\x8b")
}

/// Returns if the data is a lz4 compressed data.
fn is_lz4_compressed(data: &[u8]) -> bool {
    data.starts_with(b"\x02\x21\x4c\x18")
}

/// To iterate over compressed blocks within lz4 structure.
struct LZ4BlocksIterator<'a> {
    data: &'a [u8],
}

impl<'a> LZ4BlocksIterator<'a> {
    /// Creates a new iterator from lz4 payload.
    fn new(data: &'a [u8]) -> Self {
        LZ4BlocksIterator { data }
    }
}

impl<'a> Iterator for LZ4BlocksIterator<'a> {
    type Item = Result<&'a [u8]>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.data.is_empty() {
            return None;
        }

        let Some((block_size, data)) = self.data.split_at_checked(4) else {
            return Some(Err(Error::Other(Some(LZ4_NEXT_BLOCK_FAILED_ERROR_MESSAGE))));
        };
        self.data = data;

        let block_size = u32::from_le_bytes(block_size.try_into().unwrap()).try_into().unwrap();
        // Hit end marker
        if block_size == 0 {
            return None;
        }

        let Some((block_content, data)) = self.data.split_at_checked(block_size) else {
            return Some(Err(Error::Other(Some(LZ4_NEXT_BLOCK_FAILED_ERROR_MESSAGE))));
        };
        self.data = data;

        Some(Ok(block_content))
    }
}

/// Decompresses lz4 `content` into `out`.
fn decompress_lz4(content: &[u8], out: &mut [u8]) -> Result<usize> {
    let blocks = LZ4BlocksIterator::new(content);
    let mut out_pos = 0;

    for block in blocks {
        match block {
            Ok(block) => {
                out_pos += decompress_into(&block, &mut out[out_pos..])
                    .map_err(|_| Error::Other(Some("Failed to decompress lz4 block")))?;
            }
            Err(e) => {
                return Err(e);
            }
        }
    }

    Ok(out_pos)
}

/// Decompresses gzip `content` into `out`.
///
/// Dynamic allocation is used insize `decoder.decode_gzip()`.
fn decompress_gzip(content: &[u8], out: &mut [u8]) -> Result<usize> {
    let mut decoder = DeflateDecoder::new(content);

    let decompressed_data =
        decoder.decode_gzip().map_err(|_| Error::Other(Some("Failed to decompress gzip data")))?;

    let decompressed_len = decompressed_data.len();
    out.get_mut(..decompressed_len)
        .ok_or(Error::BufferTooSmall(Some(decompressed_len)))?
        .clone_from_slice(&decompressed_data);

    Ok(decompressed_len)
}

/// Decompresses `kernel` into `out`.
///
/// Supported formats: gzip, lz4, and plain (uncompressed).
/// If the provided `kernel` is not compressed, it will be copied into `out`
/// without decompression.
///
/// Returns the size of the decompressed data copied into `out`.
pub fn decompress_kernel<'a, 'b>(
    ops: &mut impl GblOps<'a, 'b>,
    kernel: &[u8],
    out: &mut [u8],
) -> Result<usize> {
    if is_gzip_compressed(kernel) {
        gbl_println!(ops, "kernel is gzip compressed");
        let decompressed = decompress_gzip(kernel, out)?;
        gbl_println!(ops, "kernel decompressed size: {decompressed}");
        Ok(decompressed)
    } else if is_lz4_compressed(kernel) {
        gbl_println!(ops, "kernel is lz4 compressed");
        let without_magic = &kernel[4..];
        let decompressed = decompress_lz4(without_magic, out)?;
        gbl_println!(ops, "kernel decompressed size: {decompressed}");
        Ok(decompressed)
    } else {
        // Uncompressed case. Just copy into out.
        out.get_mut(..kernel.len())
            .ok_or(Error::BufferTooSmall(Some(kernel.len())))?
            .clone_from_slice(kernel);
        Ok(kernel.len())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ops::test::FakeGblOps;

    // Asserts byte slice equality with clear error on first mismatch.
    // Avoids full data dump from default assert, which can be very verbose.
    fn assert_bytes_eq(actual: &[u8], expected: &[u8]) {
        assert_eq!(actual.len(), expected.len());

        for (i, (l, r)) in expected.iter().zip(actual.iter()).enumerate() {
            assert_eq!(l, r, "Unmatched byte at index {i}")
        }
    }

    fn test_decompress_kernel(input: &[u8], expected_output: &[u8]) {
        let mut output_buffer = vec![0u8; input.len() * 10];

        let decompressed_len =
            decompress_kernel(&mut FakeGblOps::default(), input, &mut output_buffer).unwrap();

        assert_bytes_eq(&output_buffer[..decompressed_len], expected_output);
    }

    #[test]
    fn decompress_kernel_gzip() {
        let compressed_gzip = include_bytes!("../testdata/android/gki_boot_gz_kernel").to_vec();
        let expected_result =
            include_bytes!("../testdata/android/gki_boot_gz_kernel_uncompressed").to_vec();

        test_decompress_kernel(&compressed_gzip, &expected_result);
    }

    #[test]
    fn decompress_kernel_lz4() {
        let compressed_gzip = include_bytes!("../testdata/android/gki_boot_lz4_kernel").to_vec();
        let expected_result =
            include_bytes!("../testdata/android/gki_boot_lz4_kernel_uncompressed").to_vec();

        test_decompress_kernel(&compressed_gzip, &expected_result);
    }

    #[test]
    fn decompress_kernel_raw() {
        let kernel = include_bytes!("../testdata/android/kernel_a.img").to_vec();
        let expected_kernel = kernel.clone();

        test_decompress_kernel(&kernel, &expected_kernel);
    }
}
