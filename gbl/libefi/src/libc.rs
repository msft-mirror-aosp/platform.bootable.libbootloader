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

//! This module provides platform-specific implementations required by GBL libc.
//! See `libc/src/lib.rs` for more details.
//!
//! This implementation relies on the EFI framework, so can be only used where
//! it's available.

use crate::efi_try_print;
use core::fmt::Write;
use liberror::Result;

/// EFI framework-based print implementation required by GBL `libc`.
#[no_mangle]
pub extern "Rust" fn gbl_print(s: &dyn core::fmt::Display) {
    efi_try_print!("{}", s);
}
