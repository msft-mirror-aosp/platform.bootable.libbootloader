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
use libc::{gbl_free, gbl_malloc, memcmp, memcpy, memset, strcmp, strlen, strncmp};

const AVB_MALLOC_ALIGNMENT: usize = avb_bindgen::AVB_ALIGNMENT_SIZE as usize;

#[no_mangle]
pub extern "C" fn avb_abort() -> ! {
    panic!("avb_abort");
}

#[no_mangle]
pub extern "C" fn avb_malloc_(size: usize) -> *mut c_void {
    // SAFETY: libavb calls are compatible with libc counterparts, alignment the same as
    // avb_free
    unsafe { gbl_malloc(size, AVB_MALLOC_ALIGNMENT) }
}

#[no_mangle]
pub extern "C" fn avb_free(ptr: *mut c_void) {
    // SAFETY: libavb calls are compatible with libc counterparts, alignment the same as
    // avb_malloc_
    unsafe { gbl_free(ptr, AVB_MALLOC_ALIGNMENT) }
}

#[no_mangle]
pub extern "C" fn avb_strlen(s: *const c_char) -> usize {
    // SAFETY: libavb calls are compatible with libc counterparts
    unsafe { strlen(s) }
}

#[no_mangle]
pub extern "C" fn avb_div_by_10(dividend: *mut u64) -> u32 {
    // SAFETY: libavb guarantees to pass valid pointer to u64 integer here
    let val = unsafe { &mut *dividend };
    let rem = *val % 10;
    *val /= 10;
    rem.try_into().unwrap()
}

#[no_mangle]
pub extern "C" fn avb_memcpy(dest: *mut c_void, src: *const c_void, n: usize) -> *mut c_void {
    // SAFETY: libavb calls are compatible with libc counterparts
    unsafe { memcpy(dest, src, n) }
}

#[no_mangle]
pub extern "C" fn avb_memcmp(src1: *const c_void, src2: *const c_void, n: usize) -> c_int {
    // SAFETY: libavb calls are compatible with libc counterparts
    unsafe { memcmp(src1, src2, n) }
}

#[no_mangle]
pub extern "C" fn avb_memset(dest: *mut c_void, c: c_int, n: usize) -> *mut c_void {
    // SAFETY: libavb calls are compatible with libc counterparts
    unsafe { memset(dest, c, n) }
}

#[no_mangle]
pub extern "C" fn avb_strcmp(s1: *const c_char, s2: *const c_char) -> c_int {
    // SAFETY: libavb calls are compatible with libc counterparts
    unsafe { strcmp(s1, s2) }
}

#[no_mangle]
pub extern "C" fn avb_strncmp(s1: *const c_char, s2: *const c_char, n: usize) -> c_int {
    // SAFETY: libavb calls are compatible with libc counterparts
    unsafe { strncmp(s1, s2, n) }
}
