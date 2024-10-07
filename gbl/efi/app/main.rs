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

//! The GBL UEFI application.
//!
//! This just contains the minimal entry point and global hook declarations
//! needed for a full application build; all the logic should go in the
//! `gbl_efi` library instead.

#![no_std]
#![no_main]

#[cfg(target_arch = "riscv64")]
mod riscv64;

use core::{ffi::c_void, panic::PanicInfo};
use efi::{initialize, panic, EfiAllocator};
use efi_types::EfiSystemTable;
use gbl_efi::app_main;

#[panic_handler]
fn handle_panic(p_info: &PanicInfo) -> ! {
    panic(p_info)
}

#[no_mangle]
#[global_allocator]
static mut EFI_GLOBAL_ALLOCATOR: EfiAllocator = EfiAllocator::Uninitialized;

/// Pull in the sysdeps required by libavb so the linker can find them.
extern crate avb_sysdeps;

/// EFI application entry point. Does not return.
///
/// # Safety
/// `image_handle` and `systab_ptr` must be valid objects that adhere to the UEFI specification.
#[no_mangle]
pub unsafe extern "C" fn efi_main(image_handle: *mut c_void, systab_ptr: *mut EfiSystemTable) {
    // SAFETY:
    // * caller provides valid `image_handle` and `systab_ptr` objects
    // * we only call `initialize()` once
    let entry = unsafe { initialize(image_handle, systab_ptr) }.unwrap();
    app_main(entry).unwrap();
    loop {}
}
