// Copyright (C) 2024 The Android Open Source Project
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

//! Low-level utilities shared across multiple GBL libraries.

#![cfg_attr(not(test), no_std)]

use core::{cmp::min, str::from_utf8};
use liberror::{Error, Result};
use safemath::SafeNum;

/// Returns the largest aligned subslice.
///
/// This function drops as many bytes as needed from the front of the given slice to ensure the
/// result is properly-aligned. It does not truncate bytes from the end, so the resulting size may
/// not be a multiple of `alignment`.
///
/// If the next `alignment` boundary would be directly following the last byte, this returns the
/// 0-length slice at that alignment rather than an error, to match standard slicing behavior.
///
/// # Arguments
/// * `bytes`: the byte slice to align
/// * `alignment`: the desired starting alignment
///
/// # Returns
/// * The subslice on success
/// * [Error::ArithmeticOverflow] if `bytes` overflows when finding the next `alignment`
/// * [Error::BufferTooSmall] if `bytes` is not large enough to reach the next `alignment`. The
///   error will contain the size that would have been needed to reach `alignment`.
pub fn aligned_subslice<T>(bytes: &mut [u8], alignment: T) -> Result<&mut [u8]>
where
    T: Copy + Into<SafeNum>,
{
    let addr = bytes.as_ptr() as usize;
    let aligned_offset = (SafeNum::from(addr).round_up(alignment) - addr).try_into()?;
    Ok(bytes.get_mut(aligned_offset..).ok_or(Error::BufferTooSmall(Some(aligned_offset)))?)
}

/// A helper for getting the offset of the first byte with and aligned address.
///
/// # Arguments
/// * `bytes`: the byte slice
/// * `alignment`: the desired starting alignment.
///
/// # Returns
///
/// * Returns Ok(offset) on success, Err() on integer overflow.
pub fn aligned_offset<T>(buffer: &[u8], alignment: T) -> Result<usize>
where
    T: Copy + Into<SafeNum>,
{
    let addr = SafeNum::from(buffer.as_ptr() as usize);
    (addr.round_up(alignment) - addr).try_into().map_err(From::from)
}

/// A helper data structure for writing formatted string to fixed size bytes array.
#[derive(Debug)]
pub struct FormattedBytes<T>(T, usize);

impl<T: AsMut<[u8]> + AsRef<[u8]>> FormattedBytes<T> {
    /// Create an instance.
    pub fn new(buf: T) -> Self {
        Self(buf, 0)
    }

    /// Get the size of content.
    pub fn size(&self) -> usize {
        self.1
    }

    /// Appends the given `bytes` to the contents.
    ///
    /// If `bytes` exceeds the remaining buffer space, any excess bytes are discarded.
    ///
    /// Returns the resulting contents.
    pub fn append(&mut self, bytes: &[u8]) -> &mut [u8] {
        let buf = &mut self.0.as_mut()[self.1..];
        // Only write as much as the size of the bytes buffer. Additional write is silently
        // ignored.
        let to_write = min(buf.len(), bytes.len());
        buf[..to_write].clone_from_slice(&bytes[..to_write]);
        self.1 += to_write;
        &mut self.0.as_mut()[..self.1]
    }

    /// Converts to string.
    pub fn to_str(&self) -> &str {
        from_utf8(&self.0.as_ref()[..self.1]).unwrap_or("")
    }
}

impl<T: AsMut<[u8]> + AsRef<[u8]>> core::fmt::Write for FormattedBytes<T> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.append(s.as_bytes());
        Ok(())
    }
}

/// A convenient macro that behaves similar to snprintf in C.
///
/// Panics if the written string is not UTF-8.
#[macro_export]
macro_rules! snprintf {
    ( $arr:expr, $( $x:expr ),* ) => {
        {
            let mut bytes = $crate::FormattedBytes::new(&mut $arr[..]);
            core::fmt::Write::write_fmt(&mut bytes, core::format_args!($($x,)*)).unwrap();
            let size = bytes.size();
            core::str::from_utf8(&$arr[..size]).unwrap()
        }
    };
}

#[cfg(test)]
mod test {
    use super::*;

    // A byte array that's always at least 8-byte aligned for testing.
    #[repr(align(8))]
    struct AlignedBytes<const N: usize>([u8; N]);

    #[test]
    fn aligned_subslice_already_aligned() {
        let mut bytes = AlignedBytes([0u8; 16]);
        let bytes = &mut bytes.0;

        // AlignedBytes is `align(8)`, so must be 1/2/4/8-aligned.
        assert_eq!(aligned_subslice(bytes, 1).unwrap().as_ptr_range(), bytes.as_ptr_range());
        assert_eq!(aligned_subslice(bytes, 2).unwrap().as_ptr_range(), bytes.as_ptr_range());
        assert_eq!(aligned_subslice(bytes, 4).unwrap().as_ptr_range(), bytes.as_ptr_range());
        assert_eq!(aligned_subslice(bytes, 8).unwrap().as_ptr_range(), bytes.as_ptr_range());
    }

    #[test]
    fn aligned_subslice_unaligned() {
        let mut bytes = AlignedBytes([0u8; 16]);
        let bytes = &mut bytes.0;

        // AlignedBytes is 8-aligned, so offsetting by <8 should snap to the next 8-alignment.
        assert_eq!(
            aligned_subslice(&mut bytes[1..], 8).unwrap().as_ptr_range(),
            bytes[8..].as_ptr_range()
        );
        assert_eq!(
            aligned_subslice(&mut bytes[4..], 8).unwrap().as_ptr_range(),
            bytes[8..].as_ptr_range()
        );
        assert_eq!(
            aligned_subslice(&mut bytes[7..], 8).unwrap().as_ptr_range(),
            bytes[8..].as_ptr_range()
        );
    }

    #[test]
    fn aligned_subslice_empty_slice() {
        let mut bytes = AlignedBytes([0u8; 16]);
        let bytes = &mut bytes.0;

        // If the next alignment is just past the input, return the empty slice.
        assert_eq!(
            aligned_subslice(&mut bytes[9..], 8).unwrap().as_ptr_range(),
            bytes[16..].as_ptr_range()
        );
    }

    #[test]
    fn aligned_subslice_buffer_overflow() {
        let mut bytes = AlignedBytes([0u8; 7]); // 7 bytes; can't reach the next 8-alignment.
        let bytes = &mut bytes.0;

        assert_eq!(aligned_subslice(&mut bytes[1..], 8), Err(Error::BufferTooSmall(Some(7))));
        assert_eq!(aligned_subslice(&mut bytes[6..], 8), Err(Error::BufferTooSmall(Some(2))));
    }

    #[test]
    fn aligned_subslice_alignment_overflow() {
        let mut bytes = AlignedBytes([0u8; 16]);
        let bytes = &mut bytes.0;

        assert!(matches!(aligned_subslice(bytes, SafeNum::MAX), Err(Error::ArithmeticOverflow(_))));
    }

    #[test]
    fn test_formatted_bytes() {
        let mut bytes = [0u8; 4];
        assert_eq!(snprintf!(bytes, "abcde"), "abcd");
        assert_eq!(&bytes, b"abcd");
    }
}
