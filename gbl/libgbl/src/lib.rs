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

//! # Generic Boot Loader (gbl) Library
//!
//! TODO: b/312610098 - add documentation.
//!
//! The intended users of this library are firmware, bootloader, and bring-up teams at OEMs and SOC
//! Vendors
//!
//! This library is `no_std` as it is intended for use in bootloaders that typically will not
//! support the Rust standard library. However, it does require `alloc` with a global allocator,
//! currently used for:
//! * libavb
//! * kernel decompression

#![cfg_attr(not(any(test, android_dylib)), no_std)]
// TODO: b/312610985 - return warning for unused partitions
#![allow(async_fn_in_trait)]
// Needed for MaybeUninit::fill() experimental API
#![feature(maybe_uninit_fill)]
extern crate avb;
extern crate core;
extern crate gbl_storage;
extern crate spin;
extern crate zbi;

use avb::{HashtreeErrorMode, SlotVerifyData, SlotVerifyFlags};
use core::ffi::CStr;
use core::marker::PhantomData;

pub mod android_boot;
pub mod boot_mode;
pub mod boot_reason;
pub mod constants;
pub mod decompress;
pub mod device_tree;
pub mod error;
pub mod fastboot;
pub mod fuchsia_boot;
pub mod gbl_avb;
pub mod ops;
pub mod partition;

/// The 'slots' module, containing types and traits for
/// querying and modifying slotted boot behavior.
pub mod slots;

mod image_buffer;

use slots::{BootTarget, BootToken, Cursor, SuffixBytes};

pub use avb::Descriptor;
pub use boot_mode::BootMode;
pub use boot_reason::KnownBootReason;
pub use error::{IntegrationError, Result};
use liberror::Error;
pub use ops::{GblOps, Os};

/// GBL object that provides implementation of helpers for boot process.
pub struct Gbl<'a, 'd, G>
where
    G: GblOps<'a, 'd>,
{
    ops: &'a mut G,
    boot_token: Option<BootToken>,
    _get_image_buffer_lifetime: PhantomData<&'d ()>,
}

// TODO(b/312610985): Investigate whether to deprecate this and remove this allow.
#[allow(unused_variables)]
impl<'a, 'f, G> Gbl<'a, 'f, G>
where
    G: GblOps<'a, 'f>,
{
    /// Returns a new [Gbl] object.
    ///
    /// # Arguments
    /// * `ops` - the [GblOps] callbacks to use
    pub fn new(ops: &'a mut G) -> Self {
        Self { ops, boot_token: Some(BootToken(())), _get_image_buffer_lifetime: PhantomData }
    }

    /// Verify + Load Image Into memory
    ///
    /// Load from disk, validate with AVB
    ///
    /// # Arguments
    /// * `avb_ops` - implementation for `avb::Ops`
    /// * `partitions_to_verify` - names of all the partitions to verify with libavb.
    /// * `slot_verify_flags` - AVB slot verification flags
    /// * `boot_target` - [Optional] Boot Target
    ///
    /// # Returns
    /// * `Ok(SlotVerifyData)` - avb verification data
    /// * `Err(Error)` - on failure
    pub fn load_and_verify_image<'b>(
        &mut self,
        avb_ops: &mut impl avb::Ops<'b>,
        partitions_to_verify: &[&CStr],
        slot_verify_flags: SlotVerifyFlags,
        boot_target: Option<BootTarget>,
    ) -> Result<SlotVerifyData<'b>> {
        let bytes: SuffixBytes =
            if let Some(tgt) = boot_target { tgt.suffix().into() } else { Default::default() };

        let avb_suffix = CStr::from_bytes_until_nul(&bytes).map_err(Error::from)?;

        Ok(avb::slot_verify(
            avb_ops,
            partitions_to_verify,
            Some(avb_suffix),
            slot_verify_flags,
            HashtreeErrorMode::AVB_HASHTREE_ERROR_MODE_EIO,
        )
        .map_err(|v| v.without_verify_data())?)
    }

    /// Load Slot Manager Interface
    ///
    /// The default implementation loads from the `durable_boot` partition
    /// and writes changes back on the destruction of the cursor.
    ///
    /// # Returns
    ///
    /// * `Ok(Cursor)` - Cursor object that manages a Manager
    /// * `Err(Error)` - on failure
    pub fn load_slot_interface(
        &'a mut self,
        persist: &'a mut dyn FnMut(&mut [u8]) -> core::result::Result<(), Error>,
    ) -> Result<Cursor<'a>> {
        let boot_token = self.boot_token.take().ok_or(Error::OperationProhibited)?;
        self.ops.load_slot_interface(persist, boot_token)
    }
}

#[cfg(test)]
mod tests {
    extern crate avb_sysdeps;
    extern crate avb_test;
    extern crate libc_deps_posix;

    use super::*;
    use crate::ops::test::FakeGblOps;
    use avb::{CertPermanentAttributes, SlotVerifyError};
    use avb_test::{FakeVbmetaKey, TestOps};
    use libutils::aligned_offset;
    use std::{
        fs,
        ops::{Deref, DerefMut},
        path::Path,
    };
    use zerocopy::FromBytes;

    // Helper object for allocating aligned buffer.
    pub(crate) struct AlignedBuffer {
        buffer: Vec<u8>,
        size: usize,
        alignment: usize,
    }

    impl AlignedBuffer {
        /// Allocates a buffer.
        pub(crate) fn new(size: usize, alignment: usize) -> Self {
            Self { buffer: vec![0u8; alignment + size - 1], size, alignment }
        }

        /// Allocates a buffer and initializes with data.
        pub(crate) fn new_with_data(data: &[u8], alignment: usize) -> Self {
            let mut res = Self::new(data.len(), alignment);
            res.clone_from_slice(data);
            res
        }
    }

    impl Deref for AlignedBuffer {
        type Target = [u8];

        fn deref(&self) -> &Self::Target {
            let off = aligned_offset(&self.buffer, self.alignment).unwrap();
            &self.buffer[off..][..self.size]
        }
    }

    impl DerefMut for AlignedBuffer {
        fn deref_mut(&mut self) -> &mut Self::Target {
            let off = aligned_offset(&self.buffer, self.alignment).unwrap();
            &mut self.buffer[off..][..self.size]
        }
    }

    const TEST_ZIRCON_PARTITION_NAME: &str = "zircon_a";
    const TEST_ZIRCON_PARTITION_NAME_CSTR: &CStr = c"zircon_a";
    const TEST_ZIRCON_IMAGE_PATH: &str = "zircon_a.zbi";
    const TEST_ZIRCON_VBMETA_PATH: &str = "zircon_a.vbmeta";
    const TEST_ZIRCON_VBMETA_CERT_PATH: &str = "zircon_a.vbmeta.cert";
    const TEST_PUBLIC_KEY_PATH: &str = "testkey_rsa4096_pub.bin";
    const TEST_PERMANENT_ATTRIBUTES_PATH: &str = "cert_permanent_attributes.bin";
    const TEST_PERMANENT_ATTRIBUTES_HASH_PATH: &str = "cert_permanent_attributes.hash";
    const TEST_BAD_PERMANENT_ATTRIBUTES_PATH: &str = "cert_permanent_attributes.bad.bin";
    const TEST_BAD_PERMANENT_ATTRIBUTES_HASH_PATH: &str = "cert_permanent_attributes.bad.hash";
    const TEST_VBMETA_ROLLBACK_LOCATION: usize = 0; // Default value, we don't explicitly set this.
    pub const TEST_CERT_PIK_VERSION: u64 = 42;
    pub const TEST_CERT_PSK_VERSION: u64 = 42;

    /// Returns the contents of a test data file.
    ///
    /// Panicks if the requested file cannot be read.
    ///
    /// # Arguments
    /// * `path`: file path relative to libgbl's `testdata/` directory.
    fn testdata(path: &str) -> Vec<u8> {
        let full_path = Path::new("external/gbl/libgbl/testdata").join(path);
        fs::read(full_path).unwrap()
    }

    /// Creates and returns a configured avb `TestOps`.
    ///
    /// The initial state will verify successfully with:
    /// * a valid vbmeta image in the `vbmeta` partition, containing a hash descriptor for the
    ///   `TEST_ZIRCON_PARTITION_NAME` partition
    /// * an image in the `TEST_ZIRCON_PARTITION_NAME` partition matching the vbmeta hash
    /// * no preloaded partition data
    /// * a public key matching the vbmeta image
    /// * a valid vbmeta rollback index
    /// * a locked bootloader state
    ///
    /// The caller can modify any of this state as needed for their particular test.
    fn test_avb_ops() -> TestOps<'static> {
        let mut avb_ops = TestOps::default();

        avb_ops.add_partition(TEST_ZIRCON_PARTITION_NAME, testdata(TEST_ZIRCON_IMAGE_PATH));
        avb_ops.add_partition("vbmeta", testdata(TEST_ZIRCON_VBMETA_PATH));
        avb_ops.default_vbmeta_key = Some(FakeVbmetaKey::Avb {
            public_key: testdata(TEST_PUBLIC_KEY_PATH),
            public_key_metadata: None,
        });
        avb_ops.rollbacks.insert(TEST_VBMETA_ROLLBACK_LOCATION, Ok(0));
        avb_ops.unlock_state = Ok(false);

        avb_ops
    }

    /// Similar to `test_avb_ops()`, but with the avb_cert extension enabled.
    fn test_avb_cert_ops() -> TestOps<'static> {
        let mut avb_ops = test_avb_ops();

        // Replace vbmeta with the cert-signed version.
        avb_ops.add_partition("vbmeta", testdata(TEST_ZIRCON_VBMETA_CERT_PATH));

        // Tell `avb_ops` to use cert APIs and to route the default key through cert validation.
        avb_ops.use_cert = true;
        avb_ops.default_vbmeta_key = Some(FakeVbmetaKey::Cert);

        // Add the permanent attributes.
        let perm_attr_bytes = testdata(TEST_PERMANENT_ATTRIBUTES_PATH);
        let perm_attr_hash = testdata(TEST_PERMANENT_ATTRIBUTES_HASH_PATH);
        avb_ops.cert_permanent_attributes =
            Some(CertPermanentAttributes::read_from(&perm_attr_bytes[..]).unwrap());
        avb_ops.cert_permanent_attributes_hash = Some(perm_attr_hash.try_into().unwrap());

        // Add the rollbacks for the cert keys.
        avb_ops.rollbacks.insert(avb::CERT_PIK_VERSION_LOCATION, Ok(TEST_CERT_PIK_VERSION));
        avb_ops.rollbacks.insert(avb::CERT_PSK_VERSION_LOCATION, Ok(TEST_CERT_PSK_VERSION));

        avb_ops
    }

    #[test]
    fn test_load_and_verify_image_success() {
        let mut gbl_ops = FakeGblOps::default();
        let mut gbl = Gbl::new(&mut gbl_ops);
        let mut avb_ops = test_avb_ops();

        let res = gbl.load_and_verify_image(
            &mut avb_ops,
            &mut [&TEST_ZIRCON_PARTITION_NAME_CSTR],
            SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_NONE,
            None,
        );
        assert!(res.is_ok());
    }

    #[test]
    fn test_load_and_verify_image_verification_error() {
        let mut gbl_ops = FakeGblOps::default();
        let mut gbl = Gbl::new(&mut gbl_ops);
        let mut avb_ops = test_avb_ops();

        // Modify the kernel image, it should now fail to validate against the vbmeta image.
        avb_ops.partitions.get_mut(TEST_ZIRCON_PARTITION_NAME).unwrap().contents.as_mut_vec()[0] ^=
            0x01;

        let res = gbl.load_and_verify_image(
            &mut avb_ops,
            &mut [&TEST_ZIRCON_PARTITION_NAME_CSTR],
            SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_NONE,
            None,
        );
        assert_eq!(
            res.unwrap_err(),
            IntegrationError::AvbSlotVerifyError(SlotVerifyError::Verification(None))
        );
    }

    #[test]
    fn test_load_and_verify_image_io_error() {
        let mut gbl_ops = FakeGblOps::default();
        let mut gbl = Gbl::new(&mut gbl_ops);
        let mut avb_ops = test_avb_ops();

        // Erase the fake rollbacks, which will result in an I/O error when attempting to access.
        avb_ops.rollbacks.clear();

        let res = gbl.load_and_verify_image(
            &mut avb_ops,
            &mut [&TEST_ZIRCON_PARTITION_NAME_CSTR],
            SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_NONE,
            None,
        );
        assert_eq!(res.unwrap_err(), IntegrationError::AvbSlotVerifyError(SlotVerifyError::Io));
    }

    #[test]
    fn test_load_and_verify_image_with_cert_success() {
        let mut gbl_ops = FakeGblOps::default();
        let mut gbl = Gbl::new(&mut gbl_ops);
        let mut avb_ops = test_avb_cert_ops();

        let res = gbl.load_and_verify_image(
            &mut avb_ops,
            &mut [&TEST_ZIRCON_PARTITION_NAME_CSTR],
            SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_NONE,
            None,
        );
        assert!(res.is_ok());
    }

    #[test]
    fn test_load_and_verify_image_with_cert_permanent_attribute_mismatch_error() {
        let mut gbl_ops = FakeGblOps::default();
        let mut gbl = Gbl::new(&mut gbl_ops);
        let mut avb_ops = test_avb_cert_ops();

        // Swap in the corrupted permanent attributes, which should cause the vbmeta image to fail
        // validation due to key mismatch.
        let perm_attr_bytes = testdata(TEST_BAD_PERMANENT_ATTRIBUTES_PATH);
        let perm_attr_hash = testdata(TEST_BAD_PERMANENT_ATTRIBUTES_HASH_PATH);
        avb_ops.cert_permanent_attributes =
            Some(CertPermanentAttributes::read_from(&perm_attr_bytes[..]).unwrap());
        avb_ops.cert_permanent_attributes_hash = Some(perm_attr_hash.try_into().unwrap());

        let res = gbl.load_and_verify_image(
            &mut avb_ops,
            &mut [&TEST_ZIRCON_PARTITION_NAME_CSTR],
            SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_NONE,
            None,
        );
        assert_eq!(
            res.unwrap_err(),
            IntegrationError::AvbSlotVerifyError(SlotVerifyError::PublicKeyRejected(None))
        );
    }
}
