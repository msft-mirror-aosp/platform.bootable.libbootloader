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

//! This library provides implementation for strcmp libc functions family.
//! https://en.cppreference.com/w/c/string/byte/strncmp

use core::cmp::Ordering;
use core::ffi::{c_char, c_int, CStr};

/// int strcmp(const char *s1, const char *s2);
///
/// # Safety
///
/// * `s1` and `s2` must be valid pointers to null terminated C strings.
#[no_mangle]
pub unsafe extern "C" fn strcmp(s1: *const c_char, s2: *const c_char) -> c_int {
    // SAFETY: `s1` and `s2` are valid null-terminated strings. References are only used
    // within function.
    let (lhs, rhs) = unsafe { (CStr::from_ptr(s1.cast()), CStr::from_ptr(s2.cast())) };
    Ord::cmp(lhs, rhs) as _
}

/// int strncmp(const char *s1, const char *s2, size_t n);
///
/// # Safety
///
/// * `s1` and `s2` must be at least nth sized or null terminated arrays.
#[no_mangle]
pub unsafe extern "C" fn strncmp(s1: *const c_char, s2: *const c_char, n: usize) -> c_int {
    for i in 0..n {
        // SAFETY: `i` is always within the bounds of `s1` and `s2` because it is limited by `n`,
        // and this statement is unreachable if a null character is already encountered in `s1`
        // or `s2`.
        let (l, r) = unsafe { (*s1.add(i), *s2.add(i)) };

        let cmp = l.cmp(&r);
        if cmp != Ordering::Equal || l == 0 {
            return cmp as _;
        }
    }
    Ordering::Equal as _
}

#[cfg(test)]
mod test {
    use super::*;
    use std::ffi::CString;

    fn to_cstr(s: &str) -> CString {
        CString::new(s).unwrap()
    }

    fn do_strcmp(left: &str, right: &str) -> c_int {
        let left_cstr = to_cstr(left);
        let right_cstr = to_cstr(right);
        // SAFETY: `left_cstr` and `right_cstr` are null terminated strings.
        unsafe { strcmp(left_cstr.as_ptr(), right_cstr.as_ptr()) }
    }

    fn do_strncmp(left: &str, right: &str, n: usize) -> c_int {
        let left_cstr = to_cstr(left);
        let right_cstr = to_cstr(right);
        // SAFETY: `left_cstr` and `right_cstr` are null terminated strings.
        unsafe { strncmp(left_cstr.as_ptr(), right_cstr.as_ptr(), n) }
    }

    fn do_strncmp_bytes(left: &[u8], right: &[u8], n: usize) -> c_int {
        // SAFETY: `left` and `right` are not null.
        unsafe { strncmp(left.as_ptr().cast(), right.as_ptr().cast(), n) }
    }

    // strcmp tests

    #[test]
    fn strcmp_same() {
        assert_eq!(do_strcmp("first", "first"), 0);
    }

    #[test]
    fn strcmp_same_special_characters() {
        assert_eq!(do_strcmp("!@#", "!@#"), 0);
    }

    #[test]
    fn strcmp_left_smaller() {
        assert_eq!(do_strcmp("first", "second"), -1);
    }

    #[test]
    fn strcmp_left_is_prefix_of_right() {
        assert_eq!(do_strcmp("first", "firstly"), -1);
    }

    #[test]
    fn strcmp_right_is_prefix_of_left() {
        assert_eq!(do_strcmp("firstly", "first"), 1);
    }

    #[test]
    fn strcmp_empty() {
        assert_eq!(do_strcmp("", ""), 0);
    }

    #[test]
    fn strcmp_empty_vs_non_empty() {
        assert_eq!(do_strcmp("", "nonempty"), -1);
    }

    #[test]
    fn strcmp_non_empty_vs_empty() {
        assert_eq!(do_strcmp("nonempty", ""), 1);
    }

    #[test]
    fn strcmp_case_sensitivity() {
        assert_eq!(do_strcmp("First", "first"), -1);
    }

    // strncmp tests

    #[test]
    fn strncmp_same_exact_length() {
        assert_eq!(do_strncmp("hello", "hello", 5), 0);
    }

    #[test]
    fn strncmp_same_partial_length() {
        assert_eq!(do_strncmp("hello", "hello", 3), 0);
    }

    #[test]
    fn strncmp_same_overflow() {
        assert_eq!(do_strncmp("hello", "hello", 100), 0);
    }

    #[test]
    fn strncmp_same_special_characters() {
        assert_eq!(do_strncmp("!@#", "!@#", 3), 0);
    }

    #[test]
    fn strncmp_different_exact_length() {
        assert_eq!(do_strncmp("hello", "world", 5), -1);
    }

    #[test]
    fn strncmp_different_partial_length() {
        assert_eq!(do_strncmp("hello", "world", 3), -1);
    }

    #[test]
    fn strncmp_left_is_prefix_of_right() {
        assert_eq!(do_strncmp("abc", "abcdef", 6), -1);
    }

    #[test]
    fn strncmp_right_is_prefix_of_left() {
        assert_eq!(do_strncmp("abcdef", "abc", 6), 1);
    }

    #[test]
    fn strncmp_empty_strings() {
        assert_eq!(do_strncmp("", "", 5), 0);
    }

    #[test]
    fn strncmp_empty_vs_non_empty() {
        assert_eq!(do_strncmp("", "hello", 5), -1);
    }

    #[test]
    fn strncmp_non_empty_vs_empty() {
        assert_eq!(do_strncmp("hello", "", 5), 1);
    }

    #[test]
    fn strncmp_case_sensitivity() {
        assert_eq!(do_strncmp("Hello", "hello", 5), -1);
    }

    #[test]
    fn strncmp_bytes_array_same_exact_length() {
        assert_eq!(do_strncmp_bytes(b"hello", b"hello", 5), 0);
    }

    #[test]
    fn strncmp_bytes_array_right_terminated() {
        assert_eq!(do_strncmp_bytes(b"hello", b"hel\0", 5), 1);
    }

    #[test]
    fn strncmp_bytes_array_left_terminated() {
        assert_eq!(do_strncmp_bytes(b"hel\0", b"hello", 5), -1);
    }
}
