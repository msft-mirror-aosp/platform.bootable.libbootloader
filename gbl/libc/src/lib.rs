// Copyright 2023-2025, The Android Open Source Project
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

#[cfg(target_os = "linux")]
extern crate libc_deps_posix;

use alloc::alloc::{alloc, dealloc};
use core::{
    alloc::Layout,
    ffi::{c_char, c_int, c_ulong, c_void, CStr},
    mem::size_of_val,
    ptr::{null_mut, NonNull},
};
use safemath::SafeNum;

pub use strcmp::{strcmp, strncmp};

/// Binary search implementation.
pub mod bsearch;
pub mod print;
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

// Linking the platform-specific functionality expected to be provided by the
// library/app, which includes the GBL `libc`.
extern "Rust" {
    /// GBL `libc` expects user to provide platform-specific text output implementation
    /// to allow libc to expose it for external C libraries.
    ///
    /// A default POSIX-based implementation is available at `libc/deps/posix.rs`.
    /// An EFI-specific implementation is provided by `libefi/src/libc.rs`.
    fn gbl_print(d: &dyn core::fmt::Display);
}

/// Helper data structure to hold data that is stored before `ptr`. This data is used by
/// allocator/deallocator.
///
/// It is mainly used to have types and offsets in one place, and not duplicated as part of
/// alloc/dealloc implementation.
#[derive(Debug, Default)]
struct PrefixData {
    pub size: usize,
    pub offset: usize,
}

impl PrefixData {
    /// Determine prefix size necessary to store data required for [gbl_free]: size, offset
    pub fn required_size(&self) -> usize {
        size_of_val(&self.size) + size_of_val(&self.offset)
    }

    /// Reads prefix data based on ptr
    /// # SAFETY:
    /// * `ptr` must be allocated by `gbl_malloc` and has enough padding before `ptr` to hold
    /// prefix data. Which consists of offset and size values.
    pub unsafe fn from_ptr(ptr: *mut u8) -> PrefixData {
        let mut prefix = PrefixData::default();

        // Read size used in allocation from prefix data.
        prefix.offset = usize::from_ne_bytes(
            // SAFETY:
            // Function requires `ptr` to be allocated by `gbl_malloc` and has enough padding
            // before `ptr` to hold prefix data.
            unsafe {
                core::slice::from_raw_parts(
                    ptr.sub(size_of_val(&prefix.offset)),
                    size_of_val(&prefix.offset),
                )
            }
            .try_into()
            .unwrap(),
        );

        // Read offset for unaligned pointer from prefix data.
        prefix.size = usize::from_ne_bytes(
            // SAFETY:
            // Function requires `ptr` to be allocated by `gbl_malloc` and has enough padding
            // before `ptr` to hold prefix data.
            unsafe {
                core::slice::from_raw_parts(
                    ptr.sub(size_of_val(&prefix.offset) + size_of_val(&prefix.size)),
                    size_of_val(&prefix.size),
                )
            }
            .try_into()
            .unwrap(),
        );

        prefix
    }
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
        let mut prefix = PrefixData::default();

        // Determine padding necessary to guarantee alignment. Padding includes prefix data.
        let pad: usize = (SafeNum::from(alignment) + prefix.required_size()).try_into().ok()?;

        // Actual size to allocate. It includes padding to guarantee alignment.
        prefix.size = (SafeNum::from(request_size) + pad).try_into().ok()?;

        // SAFETY:
        // *  On success, `alloc` guarantees to allocate enough memory.
        let ptr = unsafe {
            // Due to manual aligning, there is no need for specific layout alignment.
            NonNull::new(alloc(Layout::from_size_align(prefix.size, 1).ok()?))?.as_ptr()
        };

        // Calculate the aligned address to return the caller.
        let ret_address =
            (SafeNum::from(ptr as usize) + prefix.required_size()).round_up(alignment);

        // Calculate the offsets from the allocation start.
        let ret_offset = ret_address - (ptr as usize);
        let offset_offset: usize = (ret_offset - size_of_val(&prefix.size)).try_into().ok()?;
        let size_offset: usize = (offset_offset - size_of_val(&prefix.offset)).try_into().ok()?;
        prefix.offset = usize::try_from(ret_offset).ok()?;

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
            core::slice::from_raw_parts_mut(ptr.add(size_offset), size_of_val(&prefix.size))
                .copy_from_slice(&prefix.size.to_ne_bytes());
            core::slice::from_raw_parts_mut(ptr.add(offset_offset), size_of_val(&prefix.offset))
                .copy_from_slice(&prefix.offset.to_ne_bytes());

            Some(ptr.add(prefix.offset))
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
    // SAFETY: gbl_free() safety requirement guarantees ptr is from gbl_malloc()
    let prefix = unsafe { PrefixData::from_ptr(ptr) };

    // SAFETY:
    // * `ptr` is allocated by `gbl_malloc` and has enough padding before `ptr` to hold
    // prefix data. ptr - offset must point to unaligned pointer to buffer, which was returned by
    // `alloc`, and must be passed to `dealloc`
    unsafe {
        // Calculate unaligned pointer returned by [alloc], which must be used in [dealloc]
        ptr = ptr.sub(prefix.offset);

        // Call to global allocator.
        dealloc(ptr, Layout::from_size_align(prefix.size, alignment).unwrap());
    };
}

/// Extended version of void *realloc(void *ptr, size_t size) with alignment support.
///
/// This implementation allocates a new block, copies the data, and frees the old block.
/// This avoids complex re-alignment logic that would be needed if the underlying allocator moved
/// the block.
///
/// In case new_size <= size and alignment is the same nothing is done. And function returns same
/// pointer.
///
/// # Safety
///
/// * `ptr` must be a pointer allocated by `gbl_malloc` or null.
/// * `gbl_realloc` must be called with the same `alignment` as the corresponding `gbl_malloc` call.
#[no_mangle]
pub unsafe extern "C" fn gbl_realloc(
    ptr: *mut c_void,
    new_size: usize,
    alignment: usize,
) -> *mut c_void {
    if ptr.is_null() {
        return unsafe { gbl_malloc(new_size, alignment) };
    }
    if new_size == 0 {
        // SAFETY:
        // * `ptr` is a pointer allocated by `gbl_malloc` and is not null.
        unsafe { gbl_free(ptr, alignment) };
        return null_mut();
    }

    // SAFETY: `gbl_realloc()` require ptr to be from `gbl_malloc()` and there is null check above
    let prefix = unsafe { PrefixData::from_ptr(ptr as *mut u8) };
    let old_usable = prefix.size - prefix.offset;

    // Don't need to reallocate if new size is <= old_size and alignment matches
    if new_size <= old_usable && ptr.align_offset(alignment) == 0 {
        return ptr;
    }

    // SAFETY: checking for null return value
    let new_ptr = unsafe { gbl_malloc(new_size, alignment) };
    if new_ptr.is_null() {
        return null_mut();
    }

    let copy_size = core::cmp::min(new_size, old_usable);

    // SAFETY: `ptr` and `new_ptr` are valid for `copy_size` bytes, and non-overlapping.
    unsafe { core::ptr::copy_nonoverlapping(ptr as *const u8, new_ptr as *mut u8, copy_size) };

    // SAFETY: `ptr` is pointer allocated by gbl_malloc as per function safety.
    unsafe { gbl_free(ptr, alignment) };
    new_ptr
}

/// void *memchr(const void *ptr, int ch, size_t count);
///
/// # Safety
///
/// * `ptr` needs to be a buffer with at least `count` bytes.
/// * Returns the pointer within `ptr` buffer, or null if not found.
#[cfg_attr(not(target_os = "linux"), no_mangle)]
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
#[cfg_attr(not(target_os = "linux"), no_mangle)]
pub unsafe extern "C" fn strnlen(s: *const c_char, maxlen: usize) -> usize {
    // SAFETY: `s` is a valid pointer to a null terminated string.
    match unsafe { memchr(s as *const _, 0, maxlen.try_into().unwrap()) } {
        p if p.is_null() => maxlen,
        p => (p as usize) - (s as usize),
    }
}

/// void *abort();
#[cfg_attr(not(target_os = "linux"), no_mangle)]
pub extern "C" fn abort() -> ! {
    panic!("aborted by 3d party code")
}

/// Rust panic handler called from C/C++ code.
///
/// # Safety
///
/// `msg` must be a valid pointer to a null-terminated C-string.
#[no_mangle]
pub unsafe extern "C" fn gbl_panic_from_c(msg: *const c_char) -> ! {
    // SAFETY:
    // * by function safety, the input is a valid null-terminated C-string
    // * the input outlives the returned `CStr`
    let msg = unsafe { CStr::from_ptr(msg) };
    match msg.to_str() {
        Ok(s) => panic!("{}", s),
        // If the string wasn't UTF-8 try to debug-print it, which surrounds it with quotes and
        // replaces any invalid characters as hex escape sequences.
        _ => panic!("[gbl_panic_from_c] {:?}", msg),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gbl_realloc_malloc() {
        // SAFETY: passing null is allowed. And should just allocate.
        let ptr = unsafe { gbl_realloc(core::ptr::null_mut(), 100, 8) };
        assert!(!ptr.is_null());
        // SAFETY: ptr is returned by `gbl_realloc()` (and internally `gbl_malloc`)
        unsafe { gbl_free(ptr, 8) };
    }

    #[test]
    fn test_gbl_realloc_free() {
        // SAFETY: checking returned value is not null before using.
        let ptr = unsafe { gbl_malloc(100, 8) };
        assert!(!ptr.is_null());
        // SAFETY: ptr is valid pointer not null after check.
        let new_ptr = unsafe { gbl_realloc(ptr, 0, 8) };
        assert!(new_ptr.is_null());
        // Note: Original `ptr` is freed by `gbl_realloc`, so we do not free it again.
    }

    #[test]
    fn test_gbl_realloc_grow() {
        // SAFETY: checking returned value is not null before using.
        let ptr = unsafe { gbl_malloc(10, 8) };
        assert!(!ptr.is_null());
        // Fill with sequential data
        for i in 0..10 {
            // SAFETY: `ptr` is valid [u8; 10] pointer. And index i < 10;
            unsafe { *(ptr as *mut u8).add(i) = i as u8 };
        }

        // Grow to 100 bytes
        // SAFETY: checking returned value is not null before using.
        // `ptr` is not null ptr returned by gbl_malloc.
        let new_ptr = unsafe { gbl_realloc(ptr, 100, 8) };
        assert!(!new_ptr.is_null());

        // Verify old data is preserved
        for i in 0..10 {
            // SAFETY: `ptr` is valid [u8; 10] pointer. And index i < 10;
            assert_eq!(unsafe { *(new_ptr as *const u8).add(i) }, i as u8);
        }

        // SAFETY: new_ptr is returned by `gbl_realloc()` (and internally `gbl_malloc`)
        unsafe { gbl_free(new_ptr, 8) };
    }

    #[test]
    fn test_gbl_realloc_shrink() {
        // SAFETY: checking returned value is not null before using.
        let ptr = unsafe { gbl_malloc(100, 8) };
        assert!(!ptr.is_null());
        // Fill with sequential data
        for i in 0..100 {
            // SAFETY: `ptr` is valid [u8; 100] pointer. And index i < 100;
            unsafe { *(ptr as *mut u8).add(i) = i as u8 };
        }

        // Shrink to 10 bytes
        // SAFETY: ptr is valid pointer from `gbl_malloc`. Result is checked for null.
        let new_ptr = unsafe { gbl_realloc(ptr, 10, 8) };
        assert!(!new_ptr.is_null());

        // Verify old data is preserved up to the new size
        for i in 0..10 {
            // SAFETY: `ptr` is valid [u8; 10] pointer. And index i < 10;
            assert_eq!(unsafe { *(new_ptr as *const u8).add(i) }, i as u8);
        }

        // SAFETY: ptr is returned by `gbl_realloc()` (and internally `gbl_malloc`)
        unsafe { gbl_free(new_ptr, 8) };
    }

    fn test_gbl_realloc_same_ptr_helper(
        old_size: usize,
        old_align: usize,
        new_size: usize,
        new_align: usize,
    ) {
        // SAFETY: checking returned value is not null before using.
        let ptr = unsafe { gbl_malloc(old_size, old_align) };
        assert!(!ptr.is_null());
        // Fill with sequential data
        for i in 0..old_size {
            // SAFETY: `ptr` is valid [u8; old_size] pointer. And index i < old_size;
            unsafe { *(ptr as *mut u8).add(i) = i as u8 };
        }

        // Realloc to now_size bytes
        // SAFETY: ptr is valid pointer from `gbl_malloc`. Result is checked for null.
        let new_ptr = unsafe { gbl_realloc(ptr, new_size, new_align) };
        assert!(!new_ptr.is_null());
        assert_eq!(new_ptr, ptr);

        // Verify old data is preserved
        for i in 0..new_size {
            // SAFETY: `ptr` is valid [u8; new_size] pointer. And index i < new_size;
            assert_eq!(unsafe { *(new_ptr as *const u8).add(i) }, i as u8);
        }

        // SAFETY: ptr is returned by `gbl_realloc()` (and internally `gbl_malloc`)
        unsafe { gbl_free(new_ptr, new_align) };
    }

    #[test]
    fn test_gbl_realloc_same_size_same_align() {
        test_gbl_realloc_same_ptr_helper(50, 16, 50, 16);
    }

    #[test]
    fn test_gbl_realloc_smaller_size_same_align() {
        test_gbl_realloc_same_ptr_helper(50, 16, 25, 16);
    }

    #[test]
    fn test_gbl_realloc_same_size_smaller_align() {
        test_gbl_realloc_same_ptr_helper(50, 16, 50, 8);
    }

    #[test]
    fn test_gbl_realloc_smaller_size_smaller_align() {
        test_gbl_realloc_same_ptr_helper(50, 16, 25, 8);
    }
}
