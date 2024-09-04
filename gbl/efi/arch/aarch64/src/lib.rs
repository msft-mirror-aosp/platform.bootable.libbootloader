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

//! ARM-specific library for GBL EFI application.
#![cfg_attr(not(test), no_std)]

// Decompression is done on the heap
extern crate alloc;

use core::fmt::Write;
use efi::{efi_print, efi_println, EfiEntry};
use liberror::{Error, Result};
use zune_inflate::DeflateDecoder;

/// Decompresses the given kernel if necessary
///
/// The possibly-compressed kernel starts in `buffer`. If it's compressed, it will be decompressed
/// using heap memory and then copied back into the end of `buffer`.
///
/// # Returns
/// The offset of the decompressed kernel in `buffer`. If the kernel was not compressed. this
/// function is a no-op and will return `kernel_start` unchanged.
pub fn decompress_kernel(
    efi_entry: &EfiEntry,
    buffer: &mut [u8],
    kernel_start: usize,
) -> Result<usize> {
    if buffer[kernel_start..kernel_start + 2] == [0x1f, 0x8b] {
        efi_println!(efi_entry, "kernel is gzip compressed");
        let mut decoder = DeflateDecoder::new(&buffer[kernel_start..]);
        let decompressed_data = match decoder.decode_gzip() {
            Ok(decompressed_data) => decompressed_data,
            _ => {
                return Err(Error::InvalidInput.into());
            }
        };
        efi_println!(efi_entry, "kernel decompressed size {}", decompressed_data.len());
        let kernel_start = buffer.len() - decompressed_data.len();
        // Move decompressed data to slice.
        buffer[kernel_start..].clone_from_slice(&decompressed_data);
        Ok(kernel_start)
    } else {
        Ok(kernel_start)
    }
}
