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

//! Low-level utilities without external dependencies.

#![cfg_attr(not(test), no_std)]

use core::{arch::asm, cmp::min, str::from_utf8};

/// Generic constants and associated helper functions and macros.
pub mod constants;

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
    fn try_from_hex_str(s: &str) -> Result<Self, &'static str>;

    /// Try to parse self from the next string element in an iterator.
    fn try_parse_next<'a, T: Iterator<Item = &'a str>>(args: &mut T) -> Result<Self, &'static str> {
        Self::try_from_hex_str(next_arg(args).ok_or("Missing argument")?)
    }

    /// Parse an optional string.
    fn parse_optional(arg: Option<&str>) -> Result<Option<Self>, &'static str> {
        arg.map(Self::try_from_hex_str).transpose()
    }
}

macro_rules! parsable_int(
    ($int_type:tt) => {
        impl FromHexStr for $int_type {
            fn try_from_hex_str(s: &str) -> Result<Self, &'static str> {
                $int_type::from_str_radix(s.strip_prefix("0x")
                                          .or_else(|| s.strip_prefix("0X"))
                                          .unwrap_or(s), 16)
                    .map_err(|_| "Invalid hex string")
            }
        }
    };
);

parsable_int!(u32);
parsable_int!(u64);
parsable_int!(usize);

#[cfg(test)]
mod test {
    use super::*;

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
