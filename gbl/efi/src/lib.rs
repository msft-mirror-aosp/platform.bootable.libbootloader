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

// For the `vec!` macro
#[macro_use]
extern crate alloc;
use core::fmt::Write;

use efi::{efi_print, efi_println, EfiEntry};
use libgbl::{GblOps, Result};

#[macro_use]
mod utils;
use utils::loaded_image_path;

mod android_boot;
mod avb;
mod efi_blocks;
mod error;
mod fastboot;
mod fuchsia_boot;
mod net;
mod ops;

enum TargetOs {
    Android,
    Fuchsia,
}

fn get_target_os(entry: &EfiEntry) -> TargetOs {
    let mut buf = [0u8; 1];
    if fuchsia_boot::is_fuchsia_gpt(&entry).is_ok()
        || entry
            .system_table()
            .runtime_services()
            .get_variable(&efi::GBL_EFI_VENDOR_GUID, efi::GBL_EFI_OS_BOOT_TARGET_VARNAME, &mut buf)
            .is_ok()
    {
        TargetOs::Fuchsia
    } else {
        TargetOs::Android
    }
}

/// GBL EFI application logic entry point.
pub fn app_main(entry: EfiEntry) -> Result<()> {
    let mut ops = ops::Ops { efi_entry: &entry, partitions: &[] };

    efi_println!(entry, "****Rust EFI Application****");
    if let Ok(v) = loaded_image_path(&entry) {
        efi_println!(entry, "Image path: {}", v);
    }

    match ops.should_stop_in_fastboot() {
        Ok(true) => {
            fastboot::fastboot(&entry)?;
        }
        Ok(false) => {}
        Err(e) => {
            efi_println!(entry, "Warning: error while checking fastboot trigger ({:?})", e);
            efi_println!(entry, "Ignoring error and continuing with normal boot");
        }
    }

    match get_target_os(&entry) {
        TargetOs::Fuchsia => fuchsia_boot::fuchsia_boot_demo(entry)?,
        TargetOs::Android => android_boot::android_boot_demo(entry)?,
    }

    Ok(())
}
