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

//! This file provides common constants that are used in GBL

// TODO(b/380392958) Cleanup other used of the constants. Move them here as well.

use static_assertions::const_assert_eq;

/// Macro for defining Kibibyte-sized constants
#[macro_export]
macro_rules! KiB  (
    ($x:expr) => {
        $x*1024
    }
);
const_assert_eq!(KiB!(1), 1024);
const_assert_eq!(KiB!(5), 5 * 1024);

/// Macro for defining Mebibyte-sized constants
#[macro_export]
macro_rules! MiB  (
    ($x:expr) => {
        $x*KiB!(1024)
    }
);
const_assert_eq!(MiB!(1), 1024 * 1024);
const_assert_eq!(MiB!(5), 5 * 1024 * 1024);

pub use KiB;
pub use MiB;

/// Must be synced with the one defined in image loading protocol.
/// https://cs.android.com/android/kernel/superproject/+/common-android-mainline:bootable/libbootloader/gbl/docs/GBL_EFI_IMAGE_LOADING_PROTOCOL.md
pub const IMAGE_NAME_MAX_LEN: usize = 36;

/// Kernel image alignment requirement.
pub const KERNEL_ALIGNMENT: usize = MiB!(2);

/// Zircon Kernel image alignment requirement.
pub const ZIRCON_KERNEL_ALIGNMENT: usize = KiB!(64);

/// FDT image alignment requirement.
pub const FDT_ALIGNMENT: usize = 8;

/// Page size
pub const PAGE_SIZE: usize = KiB!(4);

/// This should be more than enough (Linux kernel MODULE_NAME_LEN is also 56).
/// Keep in sync with the constant defined in gbl_efi_fastboot_protocol.h
pub const FASTBOOT_PARTITION_TYPE_LEN: usize = 56;
