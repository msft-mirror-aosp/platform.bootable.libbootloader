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

extern crate alloc;
use alloc::alloc::{alloc, dealloc};
use core::{
    alloc::Layout,
    cmp::{min, Ord},
    ffi::CStr,
    mem::size_of,
    ptr::{null_mut, NonNull},
};

/// `avb_malloc_()` requires allocation to be word aligned.
const AVB_MALLOC_ALIGNMENT: usize = 2;

#[no_mangle]
pub extern "C" fn avb_abort() -> ! {
    panic!("avb_abort");
}

#[no_mangle]
pub extern "C" fn avb_malloc_(size: usize) -> *mut core::ffi::c_void {
    (|| {
        // Allocate extra to store the size value.
        let size = size_of::<usize>().checked_add(size)?;
        // SAFETY:
        // *  On success, `alloc` guarantees to allocate enough memory.
        // * `size.to_le_bytes().as_ptr()` is guaranteed valid memory.
        // * Alignment is 1 for bytes copy.
        unsafe {
            let ptr =
                NonNull::new(alloc(Layout::from_size_align(size, AVB_MALLOC_ALIGNMENT).ok()?))?;
            ptr.as_ptr().copy_from(size.to_le_bytes().as_ptr(), size_of::<usize>());
            let ptr = ptr.as_ptr().add(size_of::<usize>());
            Some(ptr)
        }
    })()
    .unwrap_or(null_mut()) as _
}

#[no_mangle]
pub extern "C" fn avb_free(ptr: *mut core::ffi::c_void) {
    assert_ne!(ptr, null_mut());
    let mut ptr = ptr as *mut u8;
    let mut size_bytes = [0u8; size_of::<usize>()];
    // SAFETY:
    // * `ptr` is allocated by `avb_malloc_` and guarantees to have enough memory for a preceding
    //   usize value and payload.
    // * `size_bytes.as_mut_ptr()` is a valid memory location.
    // * Alignment is 1 for bytes copy.
    unsafe {
        ptr = ptr.sub(size_of::<usize>());
        ptr.copy_to(size_bytes.as_mut_ptr(), size_of::<usize>())
    };
    let size = usize::from_le_bytes(size_bytes);
    // SAFETY: Call to global allocator.
    unsafe { dealloc(ptr, Layout::from_size_align(size, AVB_MALLOC_ALIGNMENT).unwrap()) };
}

#[no_mangle]
pub extern "C" fn avb_strlen(s: *const core::ffi::c_char) -> usize {
    // SAFETY: libavb guarantees to pass valid NULL-terminated strings to this function. The
    // returned reference is only used to compute string length.
    unsafe { CStr::from_ptr(s as *const _) }.to_bytes().len()
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
pub extern "C" fn avb_memcpy(
    dest: *mut core::ffi::c_void,
    src: *const core::ffi::c_void,
    n: usize,
) -> *mut core::ffi::c_void {
    // SAFETY: libavb guarantees to pass valid pointers.
    unsafe { (src.cast::<u8>()).copy_to(dest as *mut _, n) };
    dest
}

#[no_mangle]
pub extern "C" fn avb_memcmp(
    src1: *const core::ffi::c_void,
    src2: *const core::ffi::c_void,
    n: usize,
) -> core::ffi::c_int {
    // SAFETY: libavb guarantees to pass valid pointers. References are only used within function.
    let (lhs, rhs) = unsafe {
        (
            core::slice::from_raw_parts(src1 as *const u8, n),
            core::slice::from_raw_parts(src2 as *const u8, n),
        )
    };
    Ord::cmp(lhs, rhs) as i32
}

#[no_mangle]
pub extern "C" fn avb_strcmp(
    s1: *const core::ffi::c_char,
    s2: *const core::ffi::c_char,
) -> core::ffi::c_int {
    // SAFETY: libavb guarantees to pass valid NULL-terminated strings. References are only used
    // within function.
    let (lhs, rhs) = unsafe { (CStr::from_ptr(s1 as *const _), CStr::from_ptr(s2 as *const _)) };
    Ord::cmp(lhs, rhs) as i32
}

#[no_mangle]
pub extern "C" fn avb_strncmp(
    s1: *const core::ffi::c_char,
    s2: *const core::ffi::c_char,
    n: usize,
) -> core::ffi::c_int {
    // SAFETY: libavb guarantees to pass valid NULL-terminated strings. References are only used
    // within function.
    let (lhs, rhs) = unsafe { (CStr::from_ptr(s1 as *const _), CStr::from_ptr(s2 as *const _)) };
    let cmp_size = min(min(lhs.to_bytes().len(), rhs.to_bytes().len()), n);
    Ord::cmp(&lhs.to_bytes()[..cmp_size], &rhs.to_bytes()[..cmp_size]) as i32
}

#[no_mangle]
pub extern "C" fn avb_memset(
    dest: *mut core::ffi::c_void,
    c: core::ffi::c_int,
    n: usize,
) -> *mut core::ffi::c_void {
    // SAFETY: libavb guarantees to pass valid buffer. Reference is only used within function.
    let arr = unsafe { core::slice::from_raw_parts_mut(dest as *mut u8, n) };
    arr.fill(c as u8);
    dest
}
