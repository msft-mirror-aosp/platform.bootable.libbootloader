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

//! # Generic Bootloader Library (GBL)
//!
//! TODO: b/312610098 - add documentation.
//!
//! The intended users of this library are firmware, bootloader, and bring-up teams at OEMs and SOC
//! vendors
//!
//! This library is `no_std` as it is intended for use in bootloaders that typically will not
//! support the Rust standard library. However, it does require `alloc` with a global allocator,
//! currently used for:
//! * libavb
//! * kernel decompression

#![feature(never_type)]
#![cfg_attr(not(any(test, android_dylib)), no_std)]
#![allow(async_fn_in_trait)]
extern crate avb;
extern crate core;
extern crate gbl_storage;
#[cfg(feature = "fuchsia")]
extern crate zbi;

pub mod android_boot;
pub mod constants;
pub mod decompress;
pub mod device_tree;
pub mod error;
pub mod fastboot;
#[cfg(feature = "fuchsia")]
pub mod fuchsia_boot;
pub mod gbl_avb;
pub mod metrics;
pub mod misc;
pub mod ops;
pub mod partition;
pub mod random;
pub mod slots;

pub use avb::Descriptor;
pub use error::{IntegrationError, Result};
pub use ops::{GblOps, Os};

#[cfg(test)]
pub(crate) mod tests {
    extern crate avb_sysdeps;
    extern crate avb_test;
    extern crate boringssl_sysdeps;
    extern crate libc_deps_posix;

    use std::{
        fs,
        path::{Path, PathBuf},
    };

    pub(crate) const TEST_PERMANENT_ATTRIBUTES_PATH: &str = "cert_permanent_attributes.bin";
    pub(crate) const TEST_PERMANENT_ATTRIBUTES_HASH_PATH: &str = "cert_permanent_attributes.hash";

    /// Returns the path to the given test file, or `None` if it can't be found.
    fn test_data_path(path: &str) -> Option<PathBuf> {
        let p = Path::new("../gbl+/libgbl/testdata").join(path);
        p.exists().then_some(p)
    }

    /// Returns the contents of a test data file.
    ///
    /// Panics if the requested file cannot be read.
    ///
    /// # Arguments
    /// * `path`: file path relative to the test data directory.
    pub(crate) fn read_test_data(path: impl AsRef<str>) -> Vec<u8> {
        let path = path.as_ref();
        match test_data_path(path) {
            Some(p) => fs::read(p).unwrap(),
            None => panic!("Could not find testdata {}", path),
        }
    }

    /// Returns the contents of a test data file as a string.
    ///
    /// Panics if the requested file cannot be read or is not valid UTF-8.
    pub(crate) fn read_test_data_as_str(path: impl AsRef<str>) -> String {
        String::from_utf8(read_test_data(path)).unwrap()
    }

    /// Returns true if `path` exists relative to the test data directory.
    pub(crate) fn test_data_exists(path: impl AsRef<str>) -> bool {
        test_data_path(path.as_ref()).is_some()
    }
}
