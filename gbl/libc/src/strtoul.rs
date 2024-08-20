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

//! This library provides implementation for strtoul libc functions family.
//! https://en.cppreference.com/w/cpp/string/byte/strtoul

use core::ffi::{c_char, c_int, c_ulong, CStr};
use safemath::SafeNum;

/// unsigned long int strtoul(const char *s, char **endptr, int base);
///
/// # Safety
///
/// * `s` must be valid pointer to null terminated C string
/// * `endptr` must be a valid pointer that is available for writing or null
#[no_mangle]
pub unsafe extern "C" fn strtoul(
    s: *const c_char,
    endptr: *mut *const c_char,
    base: c_int,
) -> c_ulong {
    assert!(!s.is_null());
    assert!(base == 0 || base == 8 || base == 10 || base == 16);

    let mut pos = 0;
    let mut base = base;
    let mut negative = false;

    // SAFETY: `s` is a valid null terminated string
    let bytes = unsafe { CStr::from_ptr(s) }.to_bytes();

    // Skip leading whitespace
    while pos < bytes.len() && bytes[pos].is_ascii_whitespace() {
        pos += 1;
    }

    // Handle sign
    if pos < bytes.len() {
        match bytes[pos] {
            b'+' => pos += 1,
            b'-' => {
                pos += 1;
                negative = true;
            }
            _ => {}
        }
    }

    // Handle base prefixes
    if (base == 16 || base == 0)
        && pos < bytes.len() - 1
        && bytes[pos] == b'0'
        && (bytes[pos + 1] == b'x' || bytes[pos + 1] == b'X')
    {
        pos += 2;
        base = 16;
    }
    if (base == 8 || base == 0) && pos < bytes.len() && bytes[pos] == b'0' {
        pos += 1;
        base = 8;
    }
    if base == 0 {
        base = 10;
    }

    let mut result: SafeNum = 0.into();
    while pos < bytes.len() {
        let symbol = bytes[pos];
        let value = match symbol {
            b'0'..=b'7' if base == 8 => symbol - b'0',
            b'0'..=b'9' if base == 10 || base == 16 => symbol - b'0',
            b'a'..=b'f' if base == 16 => symbol - b'a' + 10,
            b'A'..=b'F' if base == 16 => symbol - b'A' + 10,
            _ => break,
        };
        result = result * base + value;
        pos += 1;
    }

    if !endptr.is_null() {
        // SAFETY: `endptr` is a non-null pointer which is available for writing, `s` is a valid
        // non-null pointer, `pos` is guaranteed to be within `s` by `pos < bytes.len()` checks.
        unsafe { *endptr = s.add(pos) };
    }

    match c_ulong::try_from(result) {
        Ok(result) if negative => result.overflowing_neg().0,
        Ok(result) => result,
        _ => c_ulong::MAX,
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::ffi::CString;
    use std::ptr::null_mut;

    fn to_cstr(s: &str) -> CString {
        CString::new(s).unwrap()
    }

    fn do_strtoul(input: &str, base: i32) -> (c_ulong, Option<usize>) {
        let input_cstr = to_cstr(input);
        let mut end_ptr: *const c_char = null_mut();
        // SAFETY: `input_cstr` is a null terminated string, `end_ptr` is initialized null pointer
        let result = unsafe { strtoul(input_cstr.as_ptr(), &mut end_ptr, base) };

        let end_position = if end_ptr.is_null() {
            None
        } else {
            let start_ptr = input_cstr.as_ptr();
            // SAFETY: `end_ptr` is a pointer within the string that `start_ptr` points to
            Some(unsafe { end_ptr.offset_from(start_ptr) } as usize)
        };

        (result, end_position)
    }

    fn do_strtoul_no_endptr(input: &str, base: i32) -> c_ulong {
        let input_cstr = to_cstr(input);
        // SAFETY: `input_cstr` is a null terminated string
        unsafe { strtoul(input_cstr.as_ptr(), null_mut(), base) }
    }

    // strtoul tests

    #[test]
    fn strtoul_decimal() {
        let (r, end) = do_strtoul("12345", 10);
        assert_eq!(r, 12345);
        assert_eq!(end, Some(5));
    }

    #[test]
    fn strtoul_no_endptr() {
        let r = do_strtoul_no_endptr("12345", 10);
        assert_eq!(r, 12345);
    }

    #[test]
    fn strtoul_zero() {
        let (r, end) = do_strtoul("0", 10);
        assert_eq!(r, 0);
        assert_eq!(end, Some(1));
    }

    #[test]
    fn strtoul_empty() {
        let (r, end) = do_strtoul("", 10);
        assert_eq!(r, 0);
        // Empty input, end_ptr should point to the start
        assert_eq!(end, Some(0));
    }

    #[test]
    fn strtoul_empty_no_endptr() {
        let r = do_strtoul_no_endptr("", 10);
        assert_eq!(r, 0);
    }

    #[test]
    fn strtoul_invalid_characters() {
        let (r, end) = do_strtoul("123abc", 10);
        assert_eq!(r, 123);
        // Parsing stops at 'a', so end_ptr should point to index 3
        assert_eq!(end, Some(3));
    }

    #[test]
    fn strtoul_positive_sign() {
        let (r, end) = do_strtoul("+456", 10);
        assert_eq!(r, 456);
        assert_eq!(end, Some(4));
    }

    #[test]
    fn strtoul_negative_sign() {
        let (r, end) = do_strtoul("-1000", 10);
        assert_eq!(r, 18446744073709550616);
        assert_eq!(end, Some(5));
    }

    #[test]
    fn strtoul_negative_zero_sign() {
        let (r, end) = do_strtoul("-0", 10);
        assert_eq!(r, 0);
        assert_eq!(end, Some(2));
    }

    #[test]
    fn strtoul_prefix_spaces() {
        let (r, end) = do_strtoul("   456", 10);
        assert_eq!(r, 456);
        assert_eq!(end, Some(6));
    }

    #[test]
    fn strtoul_leading_zeroes() {
        let (r, end) = do_strtoul("0000456", 10);
        assert_eq!(r, 456);
        assert_eq!(end, Some(7));
    }

    #[test]
    fn strtoul_overflow() {
        let (r, end) = do_strtoul("999999999999999999999999999999", 10);
        assert_eq!(r, c_ulong::MAX);
        // Whole input string got processed, so end_ptr should point to the end
        assert_eq!(end, Some(30));
    }

    #[test]
    fn strtoul_octal() {
        let (r, end) = do_strtoul("12345", 8);
        assert_eq!(r, 0o12345);
        assert_eq!(end, Some(5));
    }

    #[test]
    fn strtoul_octal_prefix() {
        let (r, end) = do_strtoul("01234", 8);
        assert_eq!(r, 0o1234);
        assert_eq!(end, Some(5));
    }

    #[test]
    fn strtoul_octal_invalid_characters() {
        let (r, end) = do_strtoul("1289", 8);
        assert_eq!(r, 0o12);
        assert_eq!(end, Some(2));
    }

    #[test]
    fn strtoul_octal_prefix_spaces() {
        let (r, end) = do_strtoul("   0755", 8);
        assert_eq!(r, 0o755);
        assert_eq!(end, Some(7));
    }

    #[test]
    fn strtoul_octal_leading_zeroes() {
        let (r, end) = do_strtoul("0000456", 8);
        assert_eq!(r, 0o456);
        assert_eq!(end, Some(7));
    }

    #[test]
    fn strtoul_octal_overflow() {
        let (r, end) = do_strtoul("7777777777777777777777", 8);
        assert_eq!(r, c_ulong::MAX);
        assert_eq!(end, Some(22));
    }

    #[test]
    fn strtoul_hex() {
        let (r, end) = do_strtoul("12345", 16);
        assert_eq!(r, 0x12345);
        assert_eq!(end, Some(5));
    }

    #[test]
    fn strtoul_hex_prefix() {
        let (r, end) = do_strtoul("0x1234", 16);
        assert_eq!(r, 0x1234);
        assert_eq!(end, Some(6));
    }

    #[test]
    fn strtoul_hex_invalid_characters() {
        let (r, end) = do_strtoul("12g89", 16);
        assert_eq!(r, 0x12);
        assert_eq!(end, Some(2));
    }

    #[test]
    fn strtoul_hex_prefix_spaces() {
        let (r, end) = do_strtoul("   0x7F5", 16);
        assert_eq!(r, 0x7F5);
        assert_eq!(end, Some(8));
    }

    #[test]
    fn strtoul_hex_leading_zeroes() {
        let (r, end) = do_strtoul("0000456", 16);
        assert_eq!(r, 0x456);
        assert_eq!(end, Some(7));
    }

    #[test]
    fn strtoul_hex_overflow() {
        let (r, end) = do_strtoul("FFFFFFFFFFFFFFFFFFFF", 16);
        assert_eq!(r, c_ulong::MAX);
        assert_eq!(end, Some(20));
    }

    #[test]
    fn strtoul_autodetect_decimal() {
        let (r, end) = do_strtoul("12345", 0);
        assert_eq!(r, 12345);
        assert_eq!(end, Some(5));
    }

    #[test]
    fn strtoul_autodetect_octal() {
        let (r, end) = do_strtoul("01234", 0);
        assert_eq!(r, 0o1234);
        assert_eq!(end, Some(5));
    }

    #[test]
    fn strtoul_autodetect_hex() {
        let (r, end) = do_strtoul("0x1234", 0);
        assert_eq!(r, 0x1234);
        assert_eq!(end, Some(6));
    }

    #[test]
    fn strtoul_autodetect_hex_invalid() {
        let (r, end) = do_strtoul("0x12G34", 0);
        assert_eq!(r, 0x12);
        assert_eq!(end, Some(4));
    }

    #[test]
    fn strtoul_autodetect_hex_leading_spaces() {
        let (r, end) = do_strtoul("   0x7F5", 0);
        assert_eq!(r, 0x7F5);
        assert_eq!(end, Some(8));
    }

    #[test]
    fn strtoul_autodetect_hex_overflow() {
        let (r, end) = do_strtoul("0xFFFFFFFFFFFFFFFFFFFF", 0);
        assert_eq!(r, c_ulong::MAX);
        assert_eq!(end, Some(22));
    }
}
