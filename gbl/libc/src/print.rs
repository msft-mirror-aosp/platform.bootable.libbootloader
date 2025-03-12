// Copyright 2025, The Android Open Source Project
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

//! This module provides printing back-end functions to be used by GBL format
//! printing implementation: libc/src/print.c

use crate::gbl_print;
use core::ffi::{c_char, CStr};

/// Back-end function to print a nul-terminated string.
///
/// # Safety:
///
/// * `s` must be a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn gbl_print_string(s: *const c_char) {
    if s.is_null() {
        return;
    }
    // SAFETY: `s` must be a valid nul-terminated C string.
    let cstr = unsafe { CStr::from_ptr(s) };

    // Safety:
    // * `gbl_print` is expected to be statically linked and expected
    // core::fmt::Display compatible types.
    unsafe {
        gbl_print(&cstr.to_string_lossy());
    }
}
