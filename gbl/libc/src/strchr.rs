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

//! This library provides implementation for strchr libc functions family.
//! https://en.cppreference.com/w/c/string/byte/strchr

use core::ffi::{c_char, c_int, CStr};
use core::ptr::null_mut;

/// char *strchr(const char *str, int c);
///
/// # Safety
///
/// * `str` must be a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn strchr(ptr: *const c_char, ch: c_int) -> *mut c_char {
    assert!(!ptr.is_null());
    // SAFETY: `str` is a valid null terminated string.
    let bytes = unsafe { CStr::from_ptr(ptr) }.to_bytes_with_nul();
    let target = (ch & 0xff) as u8;
    for c in bytes.iter() {
        if *c == target {
            return c as *const _ as *mut _;
        }
    }
    null_mut()
}

/// char *strrchr(const char *str, int c);
///
/// # Safety
///
/// * `str` must be a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn strrchr(ptr: *const c_char, ch: c_int) -> *mut c_char {
    assert!(!ptr.is_null());
    // SAFETY: `str` is a null terminated string.
    let bytes = unsafe { CStr::from_ptr(ptr) }.to_bytes_with_nul();
    let target = (ch & 0xff) as u8;
    for c in bytes.iter().rev() {
        if *c == target {
            return c as *const _ as *mut _;
        }
    }
    null_mut()
}

#[cfg(test)]
mod test {
    use super::*;
    use std::ffi::CString;

    fn to_cstr(s: &str) -> CString {
        CString::new(s).unwrap()
    }

    fn do_strchr(input: &str, c: char) -> Option<usize> {
        let input_cstr = to_cstr(input);
        // SAFETY: `input_cstr` is a null terminated string.
        let result = unsafe { strchr(input_cstr.as_ptr(), c as c_int) };

        if result.is_null() {
            None
        } else {
            let start_ptr = input_cstr.as_ptr();
            // SAFETY: `result` is a pointer within the string that `start_ptr` points to.
            Some(unsafe { result.offset_from(start_ptr) as usize })
        }
    }

    fn do_strrchr(input: &str, c: char) -> Option<usize> {
        let input_cstr = to_cstr(input);
        // SAFETY: `input_cstr` is a null terminated string.
        let result = unsafe { strrchr(input_cstr.as_ptr(), c as c_int) };

        if result.is_null() {
            None
        } else {
            let start_ptr = input_cstr.as_ptr();
            // SAFETY: `result` is a pointer within the string that `start_ptr` points to.
            Some(unsafe { result.offset_from(start_ptr) as usize })
        }
    }

    // strchr tests

    #[test]
    fn strchr_find_first_occurrence() {
        let offset = do_strchr("hello", 'e');
        assert_eq!(offset, Some(1));
    }

    #[test]
    fn strchr_find_first_occurrence_special_character() {
        let offset = do_strchr("he!lo", '!');
        assert_eq!(offset, Some(2));
    }

    #[test]
    fn strchr_character_not_present() {
        let offset = do_strchr("hello", 'z');
        assert_eq!(offset, None);
    }

    #[test]
    fn strchr_find_first_occurrence_at_start() {
        let offset = do_strchr("hello", 'h');
        assert_eq!(offset, Some(0));
    }

    #[test]
    fn strchr_find_first_occurrence_at_end() {
        let offset = do_strchr("hello", 'o');
        assert_eq!(offset, Some(4));
    }

    #[test]
    fn strchr_empty_string() {
        let offset = do_strchr("", 'a');
        assert_eq!(offset, None);
    }

    #[test]
    fn strchr_find_first_occurrence_multiple() {
        let offset = do_strchr("hellohello", 'l');
        assert_eq!(offset, Some(2));
    }

    #[test]
    fn strchr_case_sensitivity() {
        let offset = do_strchr("Hello", 'h');
        assert_eq!(offset, None);
    }

    #[test]
    fn strchr_find_null_character() {
        let offset = do_strchr("Hello", '\0');
        assert_eq!(offset, Some(5));
    }

    // strrchr tests

    #[test]
    fn strrchr_find_last_occurrence() {
        let offset = do_strrchr("hello", 'l');
        assert_eq!(offset, Some(3));
    }

    #[test]
    fn strrchr_find_last_occurrence_special_character() {
        let offset = do_strrchr("he!lo!lo", '!');
        assert_eq!(offset, Some(5));
    }

    #[test]
    fn strrchr_character_not_present() {
        let offset = do_strrchr("hello", 'z');
        assert_eq!(offset, None);
    }

    #[test]
    fn strrchr_find_last_occurrence_at_start() {
        let offset = do_strrchr("hello", 'h');
        assert_eq!(offset, Some(0));
    }

    #[test]
    fn strrchr_find_last_occurrence_at_end() {
        let offset = do_strrchr("hello", 'o');
        assert_eq!(offset, Some(4));
    }

    #[test]
    fn strrchr_empty_string() {
        let offset = do_strrchr("", 'a');
        assert_eq!(offset, None);
    }

    #[test]
    fn strrchr_find_last_occurrence_multiple() {
        let offset = do_strrchr("hellohello", 'l');
        assert_eq!(offset, Some(8));
    }

    #[test]
    fn strrchr_case_sensitivity() {
        let offset = do_strrchr("Hello", 'h');
        assert_eq!(offset, None);
    }

    #[test]
    fn strrchr_find_null_character() {
        let offset = do_strchr("Hello", '\0');
        assert_eq!(offset, Some(5));
    }
}
