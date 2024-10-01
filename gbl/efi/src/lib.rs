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

#![cfg_attr(not(test), no_std)]

// For the `vec!` macro
#[macro_use]
extern crate alloc;

mod efi_blocks;
mod error;
mod ops;
#[macro_use]
mod utils;

// Currently un-testable modules.
//
// The libefi API surface is large and complex; rather than trying to mock it all out at once, we
// will selectively enable modules for test as they become mockable.
#[cfg(not(test))]
mod android_boot;
#[cfg(not(test))]
mod avb;
#[cfg(not(test))]
mod fastboot;
#[cfg(not(test))]
mod fuchsia_boot;
#[cfg(not(test))]
mod net;

// In tests, map the `efi_mocks` module as `efi`. This allows other modules to `use crate::efi`
// and automatically pick up the correct one.
#[cfg(not(test))]
pub(crate) use efi;
#[cfg(test)]
pub(crate) use efi_mocks as efi;

#[cfg(not(test))]
use {
    core::fmt::Write,
    efi::{efi_print, efi_println, EfiEntry},
    libgbl::Result,
    utils::loaded_image_path,
};

#[cfg(not(test))]
enum TargetOs {
    Android,
    Fuchsia,
}

#[cfg(not(test))]
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
#[cfg(not(test))]
pub fn app_main(entry: EfiEntry) -> Result<()> {
    efi_println!(entry, "****Generic Bootloader Application****");
    if let Ok(v) = loaded_image_path(&entry) {
        efi_println!(entry, "Image path: {}", v);
    }

    match get_target_os(&entry) {
        TargetOs::Fuchsia => fuchsia_boot::fuchsia_boot_demo(entry)?,
        TargetOs::Android => android_boot::android_boot_demo(entry)?,
    }

    Ok(())
}
