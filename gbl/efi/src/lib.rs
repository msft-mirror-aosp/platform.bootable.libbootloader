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

#![feature(never_type)]
#![cfg_attr(not(test), no_std)]

// For the `vec!` macro
#[macro_use]
extern crate alloc;

mod efi_blocks;
mod net;
mod ops;
#[macro_use]
pub mod utils;

// Currently un-testable modules.
//
// The libefi API surface is large and complex; rather than trying to mock it all out at once, we
// will selectively enable modules for test as they become mockable.
#[cfg(not(test))]
mod android_boot;
#[cfg(not(test))]
mod fastboot;
#[cfg(all(not(test), feature = "fuchsia"))]
mod fuchsia_boot;

// In tests, map the `efi_mocks` module as `efi`. This allows other modules to `use crate::efi`
// and automatically pick up the correct one.
#[cfg(not(test))]
pub(crate) use efi;
#[cfg(test)]
pub(crate) use efi_mocks as efi;

#[cfg(not(test))]
use {
    crate::{
        efi_blocks::{find_block_devices, EfiGblDisk},
        ops::Ops,
    },
    cfg_if::cfg_if,
    efi::{efi_println, report_error_and_reset, EfiEntry},
    libbuild_number::{format_build_fingerprint, format_build_vcs_info},
    libgbl::{Os, Result},
    utils::loaded_image_path,
};

#[cfg(not(test))]
enum TargetOs {
    Android,
    #[cfg(feature = "fuchsia")]
    Fuchsia,
}

#[cfg(not(test))]
fn get_target_os(_entry: &EfiEntry, _disks: &[EfiGblDisk]) -> TargetOs {
    cfg_if! {
        if #[cfg(feature = "fuchsia")] {
            let mut buf = [0u8; 1];
            if _entry
                .system_table()
                .runtime_services()
                .get_variable(&efi::GBL_EFI_VENDOR_GUID, efi::GBL_EFI_OS_BOOT_TARGET_VARNAME, &mut buf)
                .is_ok()
            {
                efi_println!(
                    _entry,
                    "`{}` is set. Proceeding as Fuchsia.",
                    efi::GBL_EFI_OS_BOOT_TARGET_VARNAME
                );
                TargetOs::Fuchsia
            } else if fuchsia_boot::is_fuchsia_gpt(_disks).is_ok() {
                efi_println!(_entry, "Partition layout looks like Fuchsia. Proceeding as Fuchsia");
                TargetOs::Fuchsia
            } else {
                efi_println!(_entry, "Proceeding as Android");
                TargetOs::Android
            }
        } else {
            TargetOs::Android
        }
    }
}

/// GBL EFI application logic entry point.
#[cfg(not(test))]
pub fn app_main(entry: EfiEntry) -> Result<!> {
    use libutils::get_sp;
    efi_println!(entry, "**** Generic Bootloader (GBL) ****");
    efi_println!(entry, "Fingerprint: {}", format_build_fingerprint!());
    efi_println!(entry, "VCS info: {}", format_build_vcs_info!());
    if let Ok(v) = loaded_image_path(&entry) {
        efi_println!(entry, "Image path: {v}");
    }

    let disks = find_block_devices(&entry).inspect_err(|e| {
        report_error_and_reset(&entry, e, efi_types::GBL_EFI_DEBUG_ERROR_TAG_PARTITION)
    })?;
    match get_target_os(&entry, &disks) {
        #[cfg(feature = "fuchsia")]
        TargetOs::Fuchsia => {
            let mut load: libgbl::android_boot::BootBuffer =
                utils::get_boot_buffer(&entry, 128 * 1024 * 1024)?.into();
            let mut ops = Ops::new(&entry, &disks[..], Some(Os::Fuchsia), get_sp());
            let images = fuchsia_boot::efi_fuchsia_load(&mut ops, load.scratch())?;
            drop(disks);
            fuchsia_boot::efi_fuchsia_boot(entry, images)?;
        }
        TargetOs::Android => {
            let load = utils::get_boot_buffer(&entry, 256 * 1024 * 1024)?;
            let mut ops = Ops::new(&entry, &disks[..], Some(Os::Android), get_sp());
            let (ramdisk, fdt, kernel, remains) =
                android_boot::efi_android_load(&mut ops, load.into())?;
            drop(disks);
            android_boot::efi_android_boot(entry, kernel, ramdisk, fdt, remains)?;
        }
    }
}
