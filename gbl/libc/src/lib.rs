// Copyright 2023-2024, The Android Open Source Project
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

//! This library provides implementation for a few libc functions for building third party C
//! libraries.

#![no_std]

extern crate alloc;

use alloc::alloc::{alloc, dealloc};

use core::{
    alloc::Layout,
    cmp::min,
    ffi::{c_char, c_int, c_ulong, c_void, CStr},
    mem::size_of,
    ptr::{null_mut, NonNull},
};

// Linking compiler built-in intrinsics to expose libc compatible implementations
// https://cs.android.com/android/platform/superproject/main/+/2e15fc2eadcb7db07bf6656086c50153bbafe7b6:prebuilts/rust/linux-x86/1.78.0/lib/rustlib/src/rust/vendor/compiler_builtins/src/mem/mod.rs;l=22
extern "C" {
    /// int memcmp(const void *src1, const void *src2, size_t n)
    pub fn memcmp(src1: *const c_void, src2: *const c_void, n: usize) -> c_int;
    /// void *memset(void *dest, int c, size_t n)
    pub fn memset(dest: *mut c_void, c: c_int, n: usize) -> *mut c_void;
    /// void *memcpy(void *dest, const void *src, size_t n)
    pub fn memcpy(dest: *mut c_void, src: *const c_void, n: usize) -> *mut c_void;
    /// size_t strlen(const char *s)
    pub fn strlen(s: *const c_char) -> usize;
}

/// Extended version of void *malloc(size_t size) with ptr alignment configuration support.
/// Libraries may have a different alignment requirements.
///
/// TODO(353089385): optimize allocation/deallocation by using EFI allocator directly for
/// some configurations
///
/// # Safety
///
/// * Returns a valid pointer to a memory block of `size` bytes, aligned to `alignment`, or null
///   on failure.
#[no_mangle]
pub unsafe extern "C" fn gbl_malloc(size: usize, alignment: usize) -> *mut c_void {
    (|| {
        // Allocate extra to store the size value.
        let size = size_of::<usize>().checked_add(size)?;
        // SAFETY:
        // *  On success, `alloc` guarantees to allocate enough memory.
        // * `size.to_le_bytes().as_ptr()` is guaranteed valid memory.
        // * Alignment is 1 for bytes copy.
        unsafe {
            let ptr = NonNull::new(alloc(Layout::from_size_align(size, alignment).ok()?))?;
            ptr.as_ptr().copy_from(size.to_le_bytes().as_ptr(), size_of::<usize>());
            let ptr = ptr.as_ptr().add(size_of::<usize>());
            Some(ptr)
        }
    })()
    .unwrap_or(null_mut()) as _
}

/// Extended version of void free(void *ptr) with ptr alignment configuration support.
///
/// TODO(353089385): optimize allocation/deallocation by using EFI allocator directly for
/// some configurations
///
/// # Safety
///
/// * `ptr` must be allocated by `gbl_malloc` and guarantee enough memory for a preceding
///   `usize` value and payload.
/// * `gbl_free` must be called with the same `alignment` as the corresponding `gbl_malloc` call.
#[no_mangle]
pub unsafe extern "C" fn gbl_free(ptr: *mut c_void, alignment: usize) {
    if ptr.is_null() {
        // follow libc free behavior
        return;
    }
    let mut ptr = ptr as *mut u8;
    let mut size_bytes = [0u8; size_of::<usize>()];
    // SAFETY:
    // * `ptr` is allocated by `gbl_malloc`
    // * `size_bytes.as_mut_ptr()` is a valid memory location.
    // * Alignment is 1 for bytes copy.
    unsafe {
        ptr = ptr.sub(size_of::<usize>());
        ptr.copy_to(size_bytes.as_mut_ptr(), size_of::<usize>());
    };
    let size = usize::from_le_bytes(size_bytes);
    // SAFETY: Call to global allocator.
    unsafe { dealloc(ptr, Layout::from_size_align(size, alignment).unwrap()) };
}

/// void *memchr(const void *ptr, int ch, size_t count);
///
/// # Safety
///
/// * `ptr` needs to be a buffer with at least `count` bytes.
/// * Returns the pointer within `ptr` buffer, or null if not found.
#[no_mangle]
pub unsafe extern "C" fn memchr(ptr: *const c_void, ch: c_int, count: c_ulong) -> *mut c_void {
    assert!(!ptr.is_null());
    let start = ptr as *const u8;
    let target = (ch & 0xff) as u8;
    for i in 0..count {
        // SAFETY: `ptr` buffer is assumed valid and bounded by count.
        let curr = unsafe { start.add(i.try_into().unwrap()) };
        // SAFETY: `ptr` buffer is assumed valid and bounded by count.
        if *unsafe { curr.as_ref().unwrap() } == target {
            return curr as *mut _;
        }
    }
    null_mut()
}

/// char *strrchr(const char *str, int c);
///
/// # Safety
///
/// * `str` needs to be a valid null-terminated C string.
/// * Returns the pointer within `str`, or null if not found.
#[no_mangle]
pub unsafe extern "C" fn strrchr(ptr: *const c_char, ch: c_int) -> *mut c_char {
    assert!(!ptr.is_null());
    // SAFETY: `str` is a valid null terminated string.
    let bytes = unsafe { CStr::from_ptr(ptr).to_bytes_with_nul() };
    let target = (ch & 0xff) as u8;
    for c in bytes.iter().rev() {
        if *c == target {
            return c as *const _ as *mut _;
        }
    }
    null_mut()
}

/// size_t strnlen(const char *s, size_t maxlen);
///
/// # Safety
///
/// * `s` must be a valid pointer to a null terminated C string.
#[no_mangle]
pub unsafe extern "C" fn strnlen(s: *const c_char, maxlen: usize) -> usize {
    // SAFETY: `s` is a valid pointer to a null terminated string.
    match unsafe { memchr(s as *const _, 0, maxlen.try_into().unwrap()) } {
        p if p.is_null() => maxlen,
        p => (p as usize) - (s as usize),
    }
}

/// int strcmp(const char *s1, const char *s2);
///
/// # Safety
///
/// * `s1` and `s2` must be valid pointers to null terminated C strings.
#[no_mangle]
pub unsafe extern "C" fn strcmp(s1: *const c_char, s2: *const c_char) -> c_int {
    // SAFETY: References are only used within function.
    let (lhs, rhs) = unsafe { (CStr::from_ptr(s1 as *const _), CStr::from_ptr(s2 as *const _)) };
    Ord::cmp(lhs, rhs) as i32
}

/// int strncmp(const char *s1, const char *s2, size_t n);
///
/// # Safety
///
/// * `s1` and `s2` must be valid pointers to null terminated C strings.
#[no_mangle]
pub unsafe extern "C" fn strncmp(s1: *const c_char, s2: *const c_char, n: usize) -> c_int {
    // SAFETY: References are only used within function.
    let (lhs, rhs) = unsafe { (CStr::from_ptr(s1 as *const _), CStr::from_ptr(s2 as *const _)) };
    let cmp_size = min(min(lhs.to_bytes().len(), rhs.to_bytes().len()), n);
    Ord::cmp(&lhs.to_bytes()[..cmp_size], &rhs.to_bytes()[..cmp_size]) as i32
}
