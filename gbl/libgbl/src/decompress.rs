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

// gzip [DeflateDecoder] requires heap allocation. LZ4 decompression currently uses the heap but
// could potentially be adjusted to use preallocated buffers if necessary.
extern crate alloc;

use crate::{gbl_print, gbl_println, GblOps};
use liberror::Error;
use lz4_flex::decompress_into;
use zune_inflate::DeflateDecoder;

/// Returns if the data is a gzip compressed data.
pub fn is_gzip_compressed(data: &[u8]) -> bool {
    data.starts_with(b"\x1f\x8b")
}

/// Returns if the data is a lz4 compressed data.
pub fn is_lz4_compressed(data: &[u8]) -> bool {
    data.starts_with(b"\x02\x21\x4c\x18")
}

/// Returns if the data is either lz4 or gzip compressed.
pub fn is_compressed(data: &[u8]) -> bool {
    is_lz4_compressed(data) || is_gzip_compressed(data)
}

/// Decompresses the given kernel if necessary
///
/// The possibly-compressed kernel starts in `buffer`. If it's compressed, it will be decompressed
/// using heap memory and then copied back into the end of `buffer`.
///
/// # Returns
/// The offset of the decompressed kernel in `buffer`. If the kernel was not compressed. this
/// function is a no-op and will return `kernel_start` unchanged.
pub fn decompress_kernel<'a, 'b>(
    ops: &mut impl GblOps<'a, 'b>,
    buffer: &mut [u8],
    kernel_start: usize,
) -> Result<usize, Error> {
    if is_gzip_compressed(&buffer[kernel_start..]) {
        gbl_println!(ops, "kernel is gzip compressed");
        let mut decoder = DeflateDecoder::new(&buffer[kernel_start..]);
        let decompressed_data = match decoder.decode_gzip() {
            Ok(decompressed_data) => decompressed_data,
            _ => {
                return Err(Error::InvalidInput.into());
            }
        };
        gbl_println!(ops, "kernel decompressed size {}", decompressed_data.len());
        let kernel_start = buffer.len() - decompressed_data.len();
        // Move decompressed data to slice.
        buffer[kernel_start..].clone_from_slice(&decompressed_data);
        Ok(kernel_start)
    } else if is_lz4_compressed(&buffer[kernel_start..]) {
        gbl_println!(ops, "kernel is lz4 compressed");
        let kernel_tail_buffer = &buffer[kernel_start..];
        let mut contents = &kernel_tail_buffer[4..];
        let mut decompressed_kernel = alloc::vec::Vec::new();
        loop {
            if contents.len() < 4 {
                if contents.len() != 0 {
                    gbl_println!(ops, "Error: some leftover data in the content");
                }
                break;
            }
            let block_size: usize =
                u32::from_le_bytes(contents[0..4].try_into().unwrap()).try_into().unwrap();
            let block;
            (block, contents) = contents.split_at(block_size + 4);
            let block = &block[4..];
            // extend decompressed kernel buffer by 8MB
            let decompressed_kernel_len = decompressed_kernel.len();
            decompressed_kernel.resize(decompressed_kernel_len + 8 * 1024 * 1024, 0);
            // decompress the block
            let decompressed_data_size =
                decompress_into(&block, &mut decompressed_kernel[decompressed_kernel_len..])
                    .unwrap();
            // reduce the size of decompressed kernel buffer
            decompressed_kernel.resize(decompressed_kernel_len + decompressed_data_size, 0);
        }
        gbl_println!(ops, "kernel decompressed size {}", decompressed_kernel.len());
        let kernel_start = buffer.len() - decompressed_kernel.len();
        // Move decompressed data to slice
        buffer[kernel_start..].clone_from_slice(&decompressed_kernel);
        Ok(kernel_start)
    } else {
        gbl_println!(ops, "kernel is not compressed");
        Ok(kernel_start)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ops::test::FakeGblOps;

    #[test]
    fn decompress_kernel_gzip() {
        let original_data = "Test TTTTTTTTT 123";
        let compressed_data = [
            0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0x0b, 0x49, 0x2d, 0x2e,
            0x51, 0x08, 0x81, 0x01, 0x05, 0x43, 0x23, 0x63, 0x00, 0xbb, 0xed, 0x15, 0xe2, 0x12,
            0x00, 0x00, 0x00,
        ];

        // Create a buffer with the compressed data at the end.
        let mut buffer = vec![0u8; 8 * 1024];
        let compressed_offset = buffer.len() - compressed_data.len();
        buffer[compressed_offset..].clone_from_slice(&compressed_data[..]);

        let offset =
            decompress_kernel(&mut FakeGblOps::default(), &mut buffer[..], compressed_offset)
                .unwrap();
        assert_eq!(&buffer[offset..], original_data.as_bytes());
    }

    #[test]
    fn decompress_kernel_lz4() {
        let original_data = "Test TTTTTTTTT 123";
        let compressed_data = [
            0x02, 0x21, 0x4c, 0x18, 0x0f, 0x00, 0x00, 0x00, 0x63, 0x54, 0x65, 0x73, 0x74, 0x20,
            0x54, 0x01, 0x00, 0x50, 0x54, 0x20, 0x31, 0x32, 0x33,
        ];

        // Create a buffer with the compressed data at the end.
        let mut buffer = vec![0u8; 8 * 1024];
        let compressed_offset = buffer.len() - compressed_data.len();
        buffer[compressed_offset..].clone_from_slice(&compressed_data[..]);

        let offset =
            decompress_kernel(&mut FakeGblOps::default(), &mut buffer[..], compressed_offset)
                .unwrap();
        assert_eq!(&buffer[offset..], original_data.as_bytes());
    }
}
