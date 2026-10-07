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

use core::{arch::asm, cmp::min, str::from_utf8};
use liberror::{Error, Result};
use safemath::SafeNum;

/// A generic, shared buffer pool.
pub mod buffer_pool;

/// Shared object guarded by a RefCell
pub mod shared;

/// Generic constants and associated helper functions and macros.
pub mod constants;

/// RAII guard for zeroizing memory on drop.
pub mod zeroize_guard;
pub use zeroize_guard::ZeroizeGuard;

#[cfg(target_arch = "aarch64")]
pub mod aarch64;

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
pub struct FormattedBytes<T> {
    buffer: T,
    len: usize,
}

impl<T: AsMut<[u8]> + AsRef<[u8]>> FormattedBytes<T> {
    /// Create an instance.
    pub fn new(buf: T) -> Self {
        Self { buffer: buf, len: 0 }
    }

    /// Get the size of content.
    pub fn size(&self) -> usize {
        self.len
    }

    /// Appends the given `bytes` to the contents.
    ///
    /// If `bytes` exceeds the remaining buffer space, any excess bytes are discarded.
    ///
    /// Returns the resulting contents.
    pub fn append(&mut self, bytes: &[u8]) -> &mut [u8] {
        let buf = &mut self.buffer.as_mut()[self.len..];
        // Only write as much as the size of the bytes buffer. Additional write is silently
        // ignored.
        let to_write = min(buf.len(), bytes.len());
        buf[..to_write].clone_from_slice(&bytes[..to_write]);
        self.len += to_write;
        &mut self.buffer.as_mut()[..self.len]
    }

    /// Gets the buffer
    pub fn buffer(&mut self) -> &mut [u8] {
        self.buffer.as_mut()
    }

    /// Parses self as a string or returns the empty string on error.
    pub fn as_str(&self) -> &str {
        from_utf8(&self.buffer.as_ref()[..self.len]).unwrap_or("")
    }
}

impl<T: AsRef<[u8]>> AsRef<[u8]> for FormattedBytes<T> {
    fn as_ref(&self) -> &[u8] {
        &self.buffer.as_ref()[..self.len]
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

/// Creates a byte buffer initialized with the given contents and a nul-terminator.
///
/// # Panics
///
/// Panics if the given buffer size can't contain the contents.
pub const fn cstr_buffer<const N: usize>(contents: &str) -> [u8; N] {
    let contents = contents.as_bytes();

    // Must be enough space for `contents` and a nul-terminator.
    assert!(contents.len() < N);

    let mut buffer = [0; N];
    let mut i = 0;
    while i < contents.len() {
        buffer[i] = contents[i];
        i += 1;
    }
    buffer
}

/// Returns the stack pointer register
pub fn get_sp() -> usize {
    let sp: usize;
    // SAFETY: The asm! macro is used to read the stack pointer register. This is safe because the
    // stack pointer register is always a valid register to read from.
    unsafe {
        #[cfg(target_arch = "aarch64")]
        asm!("mov {}, sp", out(reg) sp);
        #[cfg(target_arch = "riscv64")]
        asm!("mv {}, sp", out(reg) sp);
        #[cfg(target_arch = "x86_64")]
        asm!("mov {}, rsp", out(reg) sp);
    }
    sp
}

/// Returns the frame pointer register
#[inline(always)]
pub fn get_frame_ptr() -> usize {
    let fp: usize;
    // SAFETY: The asm! macro is used to read the frame pointer register. This is safe because the
    // frame pointer register is always a valid register to read from.
    unsafe {
        #[cfg(target_arch = "aarch64")]
        asm!("mov {}, fp", out(reg) fp);
        #[cfg(target_arch = "riscv64")]
        asm!("mv {}, fp", out(reg) fp);
        #[cfg(target_arch = "x86_64")]
        asm!("mov {}, rbp", out(reg) fp);
    }
    fp
}

/// Helper function for stripping namespaces from a typename.
pub fn base_type_name<T>() -> &'static str {
    let type_name = core::any::type_name::<T>();
    type_name.rsplit_once("::").unwrap_or(("", type_name)).1
}

/// Helper function to split the basename from a method expression
pub fn method_basename(method_str: &str) -> &str {
    method_str.rsplit(".").next().unwrap_or(method_str)
}

/// Simple macro to emulate C's __func__ macro.
/// Includes full module path.
#[macro_export]
macro_rules! func_name {
    () => {{
        fn thunk() {}
        let mut full_path = core::any::type_name_of_val(&thunk);
        let suffixes = [stringify!(thunk), "{{closure}}::", "::"];
        for s in suffixes {
            full_path = full_path.strip_suffix(s).unwrap_or(full_path);
        }
        full_path
    }};
}

/// A helper to check and fetch the next non-empty argument.
///
/// # Args
///
/// args: A string iterator.
pub fn next_arg<'a, T: Iterator<Item = &'a str>>(args: &mut T) -> Option<&'a str> {
    args.next().filter(|v| *v != "")
}

/// Helper trait for parsing integers from hex strings.
pub trait FromHexStr: Sized {
    /// Try to parse self from a possibly '0x' prefixed hex string.
    fn try_from_hex_str(s: &str) -> Result<Self>;

    /// Try to parse self from the next string element in an iterator.
    fn try_parse_next<'a, T: Iterator<Item = &'a str>>(args: &mut T) -> Result<Self> {
        Self::try_from_hex_str(next_arg(args).ok_or(Error::InvalidInput)?)
    }

    /// Parse an optional string.
    fn parse_optional(arg: Option<&str>) -> Result<Option<Self>> {
        arg.map(Self::try_from_hex_str).transpose()
    }
}

macro_rules! parsable_int(
    ($int_type:tt) => {
        impl FromHexStr for $int_type {
            fn try_from_hex_str(s: &str) -> Result<Self> {
                $int_type::from_str_radix(s.strip_prefix("0x")
                                          .or_else(|| s.strip_prefix("0X"))
                                          .unwrap_or(s), 16)
                    .map_err(Error::from)
            }
        }
    };
);

parsable_int!(u32);
parsable_int!(u64);
parsable_int!(usize);

/// Get timestamp from architecture specific timer.
#[cfg(target_arch = "aarch64")]
pub fn arch_timestamp() -> Result<core::time::Duration> {
    let (cnt, freq): (u64, u64);
    // SAFETY: Generic timer is always available on AArch64 and safe to read.
    unsafe {
        asm!(
            "isb",
            "mrs {cnt}, cntpct_el0",
            "mrs {freq}, cntfrq_el0",
            cnt = out(reg) cnt,
            freq = out(reg) freq,
        );
    }
    let (cnt, freq): (u128, u128) = (cnt as _, freq as _);
    let nanos = cnt * 1000 * 1000 * 1000 / freq;
    Ok(core::time::Duration::from_nanos(nanos as u64))
}

/// Get timestamp from architecture specific timer.
#[cfg(not(target_arch = "aarch64"))]
pub fn arch_timestamp() -> Result<core::time::Duration> {
    // Implement for other architectures if needed. For riscv64, we can use `rdtime`. For x86_64,
    // we can use `rdtsc`.
    Err(Error::Unsupported)
}

#[cfg(test)]
mod test {
    use super::*;
    use libtestutils::AlignedBuffer;

    #[test]
    fn aligned_subslice_already_aligned() {
        let mut bytes = AlignedBuffer::new(16, 8);

        // bytes is `align(8)`, so must be 1/2/4/8-aligned.
        assert_eq!(aligned_subslice(&mut bytes, 1).unwrap().as_ptr_range(), bytes.as_ptr_range());
        assert_eq!(aligned_subslice(&mut bytes, 2).unwrap().as_ptr_range(), bytes.as_ptr_range());
        assert_eq!(aligned_subslice(&mut bytes, 4).unwrap().as_ptr_range(), bytes.as_ptr_range());
        assert_eq!(aligned_subslice(&mut bytes, 8).unwrap().as_ptr_range(), bytes.as_ptr_range());
    }

    #[test]
    fn aligned_subslice_unaligned() {
        let mut bytes = AlignedBuffer::new(16, 8);

        // bytes is 8-aligned, so offsetting by <8 should snap to the next 8-alignment.
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
        let mut bytes = AlignedBuffer::new(16, 8);

        // If the next alignment is just past the input, return the empty slice.
        assert_eq!(
            aligned_subslice(&mut bytes[9..], 8).unwrap().as_ptr_range(),
            bytes[16..].as_ptr_range()
        );
    }

    #[test]
    fn aligned_subslice_buffer_overflow() {
        let mut bytes = AlignedBuffer::new(7, 8); // 7 bytes; can't reach the next 8-alignment.

        assert_eq!(aligned_subslice(&mut bytes[1..], 8), Err(Error::BufferTooSmall(Some(7))));
        assert_eq!(aligned_subslice(&mut bytes[6..], 8), Err(Error::BufferTooSmall(Some(2))));
    }

    #[test]
    fn aligned_subslice_alignment_overflow() {
        let mut bytes = AlignedBuffer::new(16, 8);

        assert!(matches!(
            aligned_subslice(&mut bytes, SafeNum::MAX),
            Err(Error::ArithmeticOverflow(_))
        ));
    }

    #[test]
    fn test_formatted_bytes() {
        let mut bytes = [0u8; 4];
        assert_eq!(snprintf!(bytes, "abcde"), "abcd");
        assert_eq!(&bytes, b"abcd");
    }

    #[test]
    fn cstr_buffer_success() {
        let buffer = cstr_buffer::<4>("foo");
        assert_eq!(&buffer, b"foo\0");
    }

    #[test]
    fn cstr_buffer_extra_space_success() {
        let buffer = cstr_buffer::<6>("foo");
        assert_eq!(&buffer, b"foo\0\0\0");
    }

    #[test]
    #[should_panic]
    fn cstr_buffer_overflow_panics() {
        let _ = cstr_buffer::<2>("foo");
    }

    #[test]
    #[should_panic]
    fn cstr_buffer_overflow_terminator_panics() {
        let _ = cstr_buffer::<3>("foo");
    }
}
