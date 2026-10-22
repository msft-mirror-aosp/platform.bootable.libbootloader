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

//! This file provides one possible implementation of the sysdeps functions for libavb.
//! Global allocator is required.

#![cfg_attr(not(test), no_std)]
// These are implementations of required C functions, see libavb sysdeps for docs.
#![allow(missing_docs)]

use core::ffi::{c_char, c_int, c_void};
use libc::{abort, gbl_free, gbl_malloc, memcmp, memcpy, memset, strcmp, strlen, strncmp};

const AVB_MALLOC_ALIGNMENT: usize = avb_bindgen::AVB_ALIGNMENT_SIZE as usize;

#[no_mangle]
pub extern "C" fn avb_abort() -> ! {
    abort()
}

#[no_mangle]
#[inline(always)]
#[allow(unused_attributes)]
pub extern "C" fn avb_malloc_(size: usize) -> *mut c_void {
    // SAFETY: libavb calls are compatible with libc counterparts, alignment the same as
    // avb_free
    unsafe { gbl_malloc(size, AVB_MALLOC_ALIGNMENT) }
}

/// Frees memory allocated by [avb_malloc_].
///
/// # Safety
///
/// `ptr` must be null or a pointer returned by [avb_malloc_] that has not already been freed.
#[no_mangle]
#[inline(always)]
#[allow(unused_attributes)]
pub unsafe extern "C" fn avb_free(ptr: *mut c_void) {
    // SAFETY: By this function's safety contract, `ptr` is null or came from `avb_malloc_`, which
    // allocates with `gbl_malloc` and the same alignment.
    unsafe { gbl_free(ptr, AVB_MALLOC_ALIGNMENT) }
}

/// Returns the length of a C string.
///
/// # Safety
///
/// `s` must point to a valid NUL-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn avb_strlen(s: *const c_char) -> usize {
    // SAFETY: By this function's safety contract, `s` is a valid NUL-terminated C string.
    unsafe { strlen(s) }
}

/// Divides `*dividend` by 10 in place and returns the remainder.
///
/// # Safety
///
/// `dividend` must be a valid, aligned pointer to a `u64` that nothing else accesses during the
/// call.
#[no_mangle]
pub unsafe extern "C" fn avb_div_by_10(dividend: *mut u64) -> u32 {
    // SAFETY: By this function's safety contract, `dividend` is valid, aligned, and not aliased.
    let val = unsafe { dividend.as_mut().unwrap() };
    let rem = *val % 10;
    *val /= 10;
    rem.try_into().unwrap()
}

/// Copies `n` bytes from `src` to `dest` and returns `dest`.
///
/// # Safety
///
/// `dest` must be valid for writes of `n` bytes, `src` must be valid for reads of `n` bytes, and
/// the two regions must not overlap.
#[no_mangle]
#[inline(always)]
#[allow(unused_attributes)]
pub unsafe extern "C" fn avb_memcpy(
    dest: *mut c_void,
    src: *const c_void,
    n: usize,
) -> *mut c_void {
    // SAFETY: By this function's safety contract, `dest` and `src` are valid for `n` bytes and do
    // not overlap.
    unsafe { memcpy(dest, src, n) }
}

/// Compares `n` bytes of `src1` and `src2`.
///
/// # Safety
///
/// `src1` and `src2` must each be valid for reads of `n` bytes.
#[no_mangle]
pub unsafe extern "C" fn avb_memcmp(src1: *const c_void, src2: *const c_void, n: usize) -> c_int {
    // SAFETY: By this function's safety contract, `src1` and `src2` are valid for reads of `n`
    // bytes.
    unsafe { memcmp(src1, src2, n) }
}

/// Sets `n` bytes of `dest` to `c` and returns `dest`.
///
/// # Safety
///
/// `dest` must be valid for writes of `n` bytes.
#[no_mangle]
pub unsafe extern "C" fn avb_memset(dest: *mut c_void, c: c_int, n: usize) -> *mut c_void {
    // SAFETY: By this function's safety contract, `dest` is valid for writes of `n` bytes.
    unsafe { memset(dest, c, n) }
}

/// Compares two C strings.
///
/// # Safety
///
/// `s1` and `s2` must each point to a valid NUL-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn avb_strcmp(s1: *const c_char, s2: *const c_char) -> c_int {
    // SAFETY: By this function's safety contract, `s1` and `s2` are valid NUL-terminated C
    // strings.
    unsafe { strcmp(s1, s2) }
}

/// Compares at most `n` bytes of two C strings.
///
/// # Safety
///
/// `s1` and `s2` must each be valid for reads up to `n` bytes or up to and including a NUL
/// terminator, whichever comes first.
#[no_mangle]
pub unsafe extern "C" fn avb_strncmp(s1: *const c_char, s2: *const c_char, n: usize) -> c_int {
    // SAFETY: By this function's safety contract, `s1` and `s2` are readable up to `n` bytes or
    // their NUL terminators.
    unsafe { strncmp(s1, s2, n) }
}
