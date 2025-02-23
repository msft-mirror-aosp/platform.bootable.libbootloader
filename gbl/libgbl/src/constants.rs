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

use core::fmt::{Debug, Display, Formatter};
use liberror::Error;
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

/// Kernel image alignment requirement.
pub const KERNEL_ALIGNMENT: usize = MiB!(2);

/// Zircon Kernel image alignment requirement.
pub const ZIRCON_KERNEL_ALIGNMENT: usize = KiB!(64);

/// FDT image alignment requirement.
pub const FDT_ALIGNMENT: usize = 8;

/// Expected max size for BootCmd zbi item.
pub const BOOTCMD_SIZE: usize = KiB!(16);

/// Page size
pub const PAGE_SIZE: usize = KiB!(4);

/// Image names list.
/// Used for identifying what buffer size/alignment is necessary.
#[derive(Debug, PartialEq, Clone)]
pub enum ImageName {
    /// ZBI for Zircon kernel
    ZbiZircon,
    /// ZBI items
    ZbiItems,
    /// Boot
    Boot,
    /// FDT
    Fdt,
}

impl ImageName {
    /// Get alignment required for the [ImageName]
    pub fn alignment(&self) -> usize {
        match self {
            Self::ZbiZircon => ZIRCON_KERNEL_ALIGNMENT,
            Self::ZbiItems => PAGE_SIZE,
            Self::Boot => KERNEL_ALIGNMENT,
            Self::Fdt => FDT_ALIGNMENT,
        }
    }
}

impl Display for ImageName {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let str = match self {
            ImageName::ZbiZircon => "zbi_zircon",
            ImageName::ZbiItems => "zbi_items",
            ImageName::Boot => "boot",
            ImageName::Fdt => "fdt",
        };
        write!(f, "{str}")
    }
}

impl TryFrom<&str> for ImageName {
    type Error = Error;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Ok(match value {
            "zbi_zircon" => ImageName::ZbiZircon,
            "zbi_items" => ImageName::ZbiItems,
            "boot" => ImageName::Boot,
            "fdt" => ImageName::Fdt,
            _ => return Err(Error::InvalidInput),
        })
    }
}
