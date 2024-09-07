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

//! This file provides one possible implementation of the sysdeps functions for libufdt.
//! Global allocator is required.

#![cfg_attr(not(test), no_std)]

use core::ffi::c_void;
use libc::{gbl_free, gbl_malloc};

const DTO_MALLOC_ALIGNMENT: usize = 8;

/// void *malloc(size_t size)
///
/// # Safety:
///
/// * `return value` pointing buffer must be used within provided `size`
#[no_mangle]
pub unsafe extern "C" fn dto_malloc(size: usize) -> *mut c_void {
    // SAFETY: libufdt calls are compatible with libc counterparts, alignment the same as
    // dto_free
    unsafe { gbl_malloc(size, DTO_MALLOC_ALIGNMENT) }
}

/// void free(void *ptr)
///
/// # Safety:
///
/// * `ptr` must be a pointer allocated by `dto_malloc` or null
#[no_mangle]
pub unsafe extern "C" fn dto_free(ptr: *mut c_void) {
    // SAFETY: libufdt calls are compatible with libc counterparts, alignment the same as
    // dto_malloc
    unsafe { gbl_free(ptr, DTO_MALLOC_ALIGNMENT) }
}
