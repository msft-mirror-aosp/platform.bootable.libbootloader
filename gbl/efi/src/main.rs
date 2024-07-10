// Copyright 2023, The Android Open Source Project
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

//! This EFI application implements a demo for booting Android/Fuchsia from disk. See
//! bootable/libbootloader/gbl/README.md for how to run the demo. See comments of
//! `android_boot:android_boot_demo()` and `fuchsia_boot:fuchsia_boot_demo()` for
//! supported/unsupported features at the moment.

#![no_std]
#![no_main]

// For the `vec!` macro
#[macro_use]
extern crate alloc;
use core::fmt::Write;

use efi::defs::EfiSystemTable;
use efi::protocol::android_boot::AndroidBootProtocol;
use efi::{efi_print, efi_println, initialize, panic};

#[macro_use]
mod utils;
use core::panic::PanicInfo;
use error::Result;
use utils::{loaded_image_path, wait_key_stroke};

#[cfg(target_arch = "riscv64")]
mod riscv64;

mod android_boot;
mod avb;
mod efi_blocks;
mod error;
mod fastboot;
mod fuchsia_boot;
mod net;

#[panic_handler]
fn handle_panic(p_info: &PanicInfo) -> ! {
    panic(p_info)
}

fn main(image_handle: *mut core::ffi::c_void, systab_ptr: *mut EfiSystemTable) -> Result<()> {
    // SAFETY: Called only once here upon EFI app entry.
    let entry = unsafe { initialize(image_handle, systab_ptr)? };

    efi_println!(entry, "****Rust EFI Application****");
    if let Ok(v) = loaded_image_path(&entry) {
        efi_println!(entry, "Image path: {}", v);
    }

    efi_println!(entry, "Press 'f' to enter fastboot.");
    match wait_key_stroke(&entry, 'f', 2000) {
        Ok(true) => {
            efi_println!(entry, "'f' pressed.");
            let android_boot_protocol = entry
                .system_table()
                .boot_services()
                .find_first_and_open::<AndroidBootProtocol>()
                .ok();
            fastboot::run_fastboot(&entry, android_boot_protocol.as_ref())?;
        }
        _ => {}
    }

    // For simplicity, we pick bootflow based on GPT layout.
    if fuchsia_boot::is_fuchsia_gpt(&entry).is_ok() {
        fuchsia_boot::fuchsia_boot_demo(entry)?;
    } else {
        android_boot::android_boot_demo(entry)?;
    }

    Ok(())
}

/// EFI application entry point. Does not return.
#[no_mangle]
pub extern "C" fn efi_main(image_handle: *mut core::ffi::c_void, systab_ptr: *mut EfiSystemTable) {
    main(image_handle, systab_ptr).unwrap();
    loop {}
}
