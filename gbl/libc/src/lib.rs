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

#![cfg_attr(not(test), no_std)]

extern crate alloc;

use alloc::alloc::{alloc, dealloc};
use core::{
    alloc::Layout,
    ffi::{c_char, c_int, c_ulong, c_void},
    mem::size_of_val,
    ptr::{null_mut, NonNull},
};
use safemath::SafeNum;

pub use strcmp::{strcmp, strncmp};

pub mod strchr;
pub mod strcmp;
pub mod strtoul;

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
/// # Safety
///
/// * Returns a valid pointer to a memory block of `size` bytes, aligned to `alignment`, or null
///   on failure.
#[no_mangle]
pub unsafe extern "C" fn gbl_malloc(request_size: usize, alignment: usize) -> *mut c_void {
    (|| {
        // Prefix data:
        let mut size = 0usize;
        let mut offset = 0usize;

        // Determine prefix size necessary to store data required for [gbl_free]: size, offset
        let prefix_size: usize = size_of_val(&size) + size_of_val(&offset);

        // Determine padding necessary to guarantee alignment. Padding includes prefix data.
        let pad: usize = (SafeNum::from(alignment) + prefix_size).try_into().ok()?;

        // Actual size to allocate. It includes padding to guarantee alignment.
        size = (SafeNum::from(request_size) + pad).try_into().ok()?;

        // SAFETY:
        // *  On success, `alloc` guarantees to allocate enough memory.
        let ptr = unsafe {
            // Due to manual aligning, there is no need for specific layout alignment.
            NonNull::new(alloc(Layout::from_size_align(size, 1).ok()?))?.as_ptr()
        };

        // Calculate the aligned address to return the caller.
        let ret_address = (SafeNum::from(ptr as usize) + prefix_size).round_up(alignment);

        // Calculate the offsets from the allocation start.
        let ret_offset = ret_address - (ptr as usize);
        let align_offset: usize = (ret_offset - size_of_val(&size)).try_into().ok()?;
        let size_offset: usize = (align_offset - size_of_val(&offset)).try_into().ok()?;
        offset = usize::try_from(ret_offset).ok()?;

        // SAFETY:
        // 'ptr' is guarantied to be valid:
        // - not NULL; Checked with `NonNull`
        // - it points to single block of memory big enough to hold size+offset (allocated this
        // way)
        // - memory is 1-byte aligned for [u8] slice
        // - ptr+offset is guarantied to point to the buffer of size 'size' as per allocation that
        // takes into account padding and prefix.
        unsafe {
            // Write metadata and return the caller's pointer.
            core::slice::from_raw_parts_mut(ptr.add(size_offset), size_of_val(&size))
                .copy_from_slice(&size.to_ne_bytes());
            core::slice::from_raw_parts_mut(ptr.add(align_offset), size_of_val(&offset))
                .copy_from_slice(&offset.to_ne_bytes());

            Some(ptr.add(offset))
        }
    })()
    .unwrap_or(null_mut()) as _
}

/// Extended version of void free(void *ptr) with ptr alignment configuration support.
///
/// # Safety
///
/// * `ptr` must be allocated by `gbl_malloc` and guarantee enough memory for a preceding
///   `usize` value and payload or null.
/// * `gbl_free` must be called with the same `alignment` as the corresponding `gbl_malloc` call.
#[no_mangle]
pub unsafe extern "C" fn gbl_free(ptr: *mut c_void, alignment: usize) {
    if ptr.is_null() {
        // follow libc free behavior
        return;
    }
    let mut ptr = ptr as *mut u8;

    let mut offset = 0usize;
    let mut size = 0usize;

    // Calculate offsets for size of align data
    let align_offset: usize = size_of_val(&size);
    let size_offset: usize = align_offset + size_of_val(&size);

    // Read size used in allocation from prefix data.
    offset = usize::from_ne_bytes(
        // SAFETY:
        // * `ptr` is allocated by `gbl_malloc` and has enough padding before `ptr` to hold
        // prefix data. Which consists of align and size values.
        // * Alignment is 1 for &[u8]
        unsafe { core::slice::from_raw_parts(ptr.sub(align_offset), size_of_val(&offset)) }
            .try_into()
            .unwrap(),
    );

    // Read offset for unaligned pointer from prefix data.
    size = usize::from_ne_bytes(
        // SAFETY:
        // * `ptr` is allocated by `gbl_malloc` and has enough padding before `ptr` to hold
        // prefix data. Which consists of align and size values.
        // * Alignment is 1 for &[u8]
        unsafe { core::slice::from_raw_parts(ptr.sub(size_offset), size_of_val(&size)) }
            .try_into()
            .unwrap(),
    );

    // SAFETY:
    // * `ptr` is allocated by `gbl_malloc` and has enough padding before `ptr` to hold
    // prefix data. ptr - offset must point to unaligned pointer to buffer, which was returned by
    // `alloc`, and must be passed to `dealloc`
    unsafe {
        // Calculate unaligned pointer returned by [alloc], which must be used in [dealloc]
        ptr = ptr.sub(offset);

        // Call to global allocator.
        dealloc(ptr, Layout::from_size_align(size, alignment).unwrap());
    };
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
