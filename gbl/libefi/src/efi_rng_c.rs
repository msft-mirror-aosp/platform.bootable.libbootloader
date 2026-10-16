// Copyright 2026, The Android Open Source Project
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

//! C-visible wrappers for EFI based RNG functions.

#![cfg_attr(not(test), no_std)]

use core::slice::from_raw_parts_mut;
use efi::{
    protocol::random_number_generator::{RandomNumberGeneratorProtocol, RngAlgorithm},
    with_global_efi_entry,
};

/// Implementation of getentropy(2) for UEFI environment using EFI_RNG_PROTOCOL.
///
/// Safety:
/// * `buffer` must be a valid pointer to at least `length` bytes.
/// * It is the responsibility of initialization code to guarantee that the
///   global efi entry is valid.
#[no_mangle]
pub unsafe extern "C" fn getentropy(buffer: *mut u8, length: usize) -> core::ffi::c_int {
    if buffer.is_null() {
        return -1;
    }
    if length == 0 {
        return 0;
    }

    // Safety: `buffer` is valid for `length` bytes per function safety contract. Zero-initialize
    // first so `from_raw_parts_mut` never materializes `&mut [u8]` over uninitialized C memory.
    let mut buf = unsafe {
        core::ptr::write_bytes(buffer, 0, length);
        from_raw_parts_mut(buffer, length)
    };
    // Safety:
    // * It is the responsibility of initialization code to guarantee that the
    //   global efi entry is valid.
    let res = unsafe {
        with_global_efi_entry(|e| {
            e.system_table_checked()
                .and_then(|st| st.boot_services_checked())
                .and_then(|bs| bs.find_first_and_open::<RandomNumberGeneratorProtocol>())
                .and_then(|rng| rng.get_rng_bytes(RngAlgorithm::Default, &mut buf))
        })
    };

    if matches!(res, Ok(Ok(()))) {
        0
    } else {
        -1
    }
}
