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
//! # Features
//! * `alloc` - enables AVB ops related logic that relies on allocation and depends on allocation.

// This code is intended for use in bootloaders that typically will not support
// the Rust standard library
#![cfg_attr(not(any(test, android_dylib)), no_std)]
// TODO: b/312610985 - return warning for unused partitions
#![allow(unused_variables, dead_code)]
#![allow(async_fn_in_trait)]
// TODO: b/312608163 - Adding ZBI library usage to check dependencies
extern crate avb;
extern crate core;
extern crate gbl_storage;
extern crate spin;
extern crate zbi;

use avb::{HashtreeErrorMode, SlotVerifyData, SlotVerifyError, SlotVerifyFlags};
use core::ffi::CStr;

pub mod boot_mode;
pub mod boot_reason;
pub mod error;
pub mod fastboot;
pub mod fuchsia_boot;
pub mod ops;
mod overlap;

/// The 'slots' module, containing types and traits for
/// querying and modifying slotted boot behavior.
pub mod slots;

use slots::{BootTarget, BootToken, Cursor, OneShot, SuffixBytes, UnbootableReason};

pub use avb::Descriptor;
pub use boot_mode::BootMode;
pub use boot_reason::KnownBootReason;
pub use error::{IntegrationError, Result};
use liberror::Error;
pub use ops::{
    AndroidBootImages, BootImages, DefaultGblOps, FuchsiaBootImages, GblAvbOps, GblOps, GblOpsError,
};

use overlap::is_overlap;

// TODO: b/312607649 - Replace placeholders with actual structures: https://r.android.com/2721974, etc
/// TODO: b/312607649 - placeholder type
pub struct Partition {}
/// TODO: b/312607649 - placeholder type
pub struct InfoStruct {}

/// Structure representing partition and optional address it is required to be loaded.
/// If no address is provided GBL will use default one.
pub struct PartitionRamMap<'b, 'c> {
    /// Partition details
    pub partition: &'b Partition,

    /// Optional memory region to load partitions.
    /// If it's not provided default values will be used.
    pub address: Option<&'c mut [u8]>,

    loaded: bool,
    verified: bool,
}

/// Boot Image in memory
pub struct BootImage<'a>(&'a mut [u8]);

/// Vendor Boot Image in memory
pub struct VendorBootImage<'a>(&'a mut [u8]);

/// Init Boot Image in memory
pub struct InitBootImage<'a>(&'a mut [u8]);

/// Kernel Image in memory
pub struct KernelImage<'a>(&'a mut [u8]);

/// Ramdisk in memory
pub struct Ramdisk<'a>(&'a mut [u8]);
/// Bootconfig in memory
pub struct Bootconfig<'a>(&'a mut [u8]);
/// DTB in memory
pub struct Dtb<'a>(&'a mut [u8]);

/// Create Boot Image from corresponding partition for `partitions_ram_map` and `avb_descriptors`
/// lists
pub fn get_boot_image<'a: 'b, 'b: 'c, 'c, 'd>(
    verified_data: &mut SlotVerifyData<'d>,
    partitions_ram_map: &'a mut [PartitionRamMap<'b, 'c>],
) -> (Option<BootImage<'c>>, &'a mut [PartitionRamMap<'b, 'c>]) {
    match partitions_ram_map.len() {
        0 => (None, partitions_ram_map),
        _ => {
            let (partition_map, tail) = partitions_ram_map.split_first_mut().unwrap();
            (partition_map.address.take().map(BootImage), tail)
        }
    }
}

/// Create Vendor Boot Image from corresponding partition for `partitions_ram_map` and
/// `avb_descriptors` lists
pub fn get_vendor_boot_image<'a: 'b, 'b: 'c, 'c, 'd>(
    verified_data: &mut SlotVerifyData<'d>,
    partitions_ram_map: &'a mut [PartitionRamMap<'b, 'c>],
) -> (Option<VendorBootImage<'c>>, &'a mut [PartitionRamMap<'b, 'c>]) {
    match partitions_ram_map.len() {
        0 => (None, partitions_ram_map),
        _ => {
            let (partition_map, tail) = partitions_ram_map.split_first_mut().unwrap();
            (partition_map.address.take().map(VendorBootImage), tail)
        }
    }
}

/// Create Init Boot Image from corresponding partition for `partitions` and `avb_descriptors` lists
pub fn get_init_boot_image<'a: 'b, 'b: 'c, 'c, 'd>(
    verified_data: &mut SlotVerifyData<'d>,
    partitions_ram_map: &'a mut [PartitionRamMap<'b, 'c>],
) -> (Option<InitBootImage<'c>>, &'a mut [PartitionRamMap<'b, 'c>]) {
    match partitions_ram_map.len() {
        0 => (None, partitions_ram_map),
        _ => {
            let (partition_map, tail) = partitions_ram_map.split_first_mut().unwrap();
            (partition_map.address.take().map(InitBootImage), tail)
        }
    }
}

/// Create separate image types from [avb::Descriptor]
pub fn get_images<'a: 'b, 'b: 'c, 'c, 'd>(
    verified_data: &mut SlotVerifyData<'d>,
    partitions_ram_map: &'a mut [PartitionRamMap<'b, 'c>],
) -> (
    Option<BootImage<'c>>,
    Option<InitBootImage<'c>>,
    Option<VendorBootImage<'c>>,
    &'a mut [PartitionRamMap<'b, 'c>],
) {
    let (boot_image, partitions_ram_map) = get_boot_image(verified_data, partitions_ram_map);
    let (init_boot_image, partitions_ram_map) =
        get_init_boot_image(verified_data, partitions_ram_map);
    let (vendor_boot_image, partitions_ram_map) =
        get_vendor_boot_image(verified_data, partitions_ram_map);
    (boot_image, init_boot_image, vendor_boot_image, partitions_ram_map)
}

/// GBL object that provides implementation of helpers for boot process.
pub struct Gbl<'a, G>
where
    G: GblOps,
{
    ops: &'a mut G,
    boot_token: Option<BootToken>,
}

impl<'a, G> Gbl<'a, G>
where
    G: GblOps,
{
    /// Returns a new [Gbl] object.
    ///
    /// # Arguments
    /// * `ops` - the [GblOps] callbacks to use
    pub fn new(ops: &'a mut G) -> Self {
        Self { ops, boot_token: Some(BootToken(())) }
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

        let avb_suffix = CStr::from_bytes_until_nul(&bytes)?;

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
    pub fn load_slot_interface<B: gbl_storage::AsBlockDevice>(
        &'a mut self,
        block_device: &'a mut B,
    ) -> Result<Cursor<'a, B>> {
        let boot_token = self.boot_token.take().ok_or(Error::OperationProhibited)?;
        self.ops.load_slot_interface::<B>(block_device, boot_token)
    }

    /// Info Load
    ///
    /// Unpack boot image in RAM
    ///
    /// # Arguments
    ///   * `boot_image_buffer` - Buffer that contains (Optionally Verified) Boot Image
    ///   * `boot_mode` - Boot Mode
    ///   * `boot_target` - [Optional] Boot Target
    ///
    /// # Returns
    ///
    /// * `Ok(InfoStruct)` - Info Struct (Concatenated kernel commandline - includes slot,
    /// bootconfig selection, normal_mode, Concatenated bootconfig) on success
    /// * `Err(Error)` - on failure
    pub fn unpack_boot_image(
        &self,
        boot_image_buffer: &BootImage,
        boot_target: Option<BootTarget>,
    ) -> Result<InfoStruct> {
        unimplemented!();
    }

    /// Kernel Load
    ///
    /// Prepare kernel in RAM for booting
    ///
    /// # Arguments
    ///   * `info` - Info Struct from Info Load
    ///   * `image_buffer` - Buffer that contains (Verified) Boot Image
    ///   * `load_buffer` - Kernel Load buffer
    ///
    /// # Returns
    ///
    /// * `Ok(())` - on success
    /// * `Err(Error)` - on failure
    pub fn kernel_load<'b>(
        &self,
        info: &InfoStruct,
        image_buffer: BootImage,
        load_buffer: &'b mut [u8],
    ) -> Result<KernelImage<'b>> {
        unimplemented!();
    }

    /// Ramdisk + Bootconfig Load
    ///
    /// Kernel Load
    /// (Could break this into a RD and Bootconfig specific function each, TBD)
    /// Prepare ramdisk/bootconfig in RAM for booting
    ///
    /// # Arguments
    ///   * `info` - Info Struct from Info Load
    ///   * `vendor_boot_image` - Buffer that contains (Verified) Vendor Boot Image
    ///   * `init_boot_image` - Buffer that contains (Verified) Init Boot Image
    ///   * `ramdisk_load_buffer` - Ramdisk Load buffer (not compressed). It will be filled with
    ///     a concatenation of `vendor_boot_image`, `init_boot_image` and bootconfig at the end.
    ///
    /// # Returns
    ///
    /// * `Ok(&str)` - on success returns Kernel command line
    /// * `Err(Error)` - on failure
    pub fn ramdisk_bootconfig_load(
        &self,
        info: &InfoStruct,
        vendor_boot_image: &VendorBootImage,
        init_boot_image: &InitBootImage,
        ramdisk: &mut Ramdisk,
    ) -> Result<&'static str> {
        unimplemented!();
    }

    /// DTB Update And Load
    ///
    /// Prepare DTB in RAM for booting
    ///
    /// # Arguments
    ///   * `info` - Info Struct from Info Load
    ///   * `vendor_boot_image_buffer` - Buffer that contains (Verified) Vendor Boot Image
    ///
    /// # Returns
    ///
    /// * `Ok()` - on success
    /// * `Err(Error)` - on failure
    pub fn dtb_update_and_load(
        &self,
        info: &InfoStruct,
        vendor_boot_image_buffer: VendorBootImage,
    ) -> Result<Dtb> {
        unimplemented!();
    }

    /// Kernel Jump
    ///
    ///
    /// # Arguments
    ///   * `kernel_load_buffer` - Kernel Load buffer
    ///   * `ramdisk_bootconfi_load_buffer` - Concatenated Ramdisk, (Bootconfig if present) Load
    ///   buffer
    ///   * `dtb_load_buffer` - DTB Load buffer
    ///   * `boot_token` - Consumable boot token
    ///
    /// # Returns
    ///
    /// * doesn't return on success
    /// * `Err(Error)` - on failure
    // Nevertype could be used here when it is stable https://github.com/serde-rs/serde/issues/812
    pub fn kernel_jump(
        &self,
        kernel_load_buffer: KernelImage,
        ramdisk_load_buffer: Ramdisk,
        dtb_load_buffer: Dtb,
        boot_token: BootToken,
    ) -> Result<()> {
        unimplemented!();
    }

    /// Load, verify, and boot
    ///
    /// Wrapper around the above functions for devices that don't need custom behavior between each
    /// step
    ///
    /// Warning: If the call to load_verify_boot fails, the device MUST
    ///          be restarted in order to make forward boot progress.
    ///          Callers MAY log the error, enter an interactive mode,
    ///          or take other actions before rebooting.
    ///
    /// # Arguments
    /// * `avb_ops` - implementation for `avb::Ops` that would be borrowed in result to prevent
    ///   changes to partitions until it is out of scope.
    /// * `partitions_to_verify` - names of all the partitions to verify with libavb.
    /// * `partitions_ram_map` - Partitions to verify and optional address for them to be loaded.
    /// * `slot_verify_flags` - AVB slot verification flags
    /// * `slot_cursor` - Cursor object that manages interactions with boot slot management
    /// * `kernel_load_buffer` - Buffer for loading the kernel.
    /// * `ramdisk_load_buffer` - Buffer for loading the ramdisk.
    /// * `fdt` - Buffer containing a flattened device tree blob.
    ///
    /// # Returns
    /// * doesn't return on success
    /// * `Err(Error)` - on failure
    // Nevertype could be used here when it is stable https://github.com/serde-rs/serde/issues/812
    #[allow(clippy::too_many_arguments)]
    pub fn load_verify_boot<'b: 'c, 'c, 'd: 'b, B: gbl_storage::AsBlockDevice>(
        &mut self,
        avb_ops: &mut impl avb::Ops<'b>,
        partitions_to_verify: &[&CStr],
        partitions_ram_map: &'d mut [PartitionRamMap<'b, 'c>],
        slot_verify_flags: SlotVerifyFlags,
        slot_cursor: Cursor<B>,
        kernel_load_buffer: &mut [u8],
        ramdisk_load_buffer: &mut [u8],
        fdt: &mut [u8],
    ) -> Result<()> {
        let dtb = Dtb(&mut fdt[..]);
        let mut ramdisk = Ramdisk(ramdisk_load_buffer);

        // Call the inner method which consumes the cursor
        // in order to properly manager cursor lifetime
        // and cleanup.
        let (kernel_image, token) = self.lvb_inner(
            avb_ops,
            &mut ramdisk,
            kernel_load_buffer,
            partitions_to_verify,
            partitions_ram_map,
            slot_verify_flags,
            slot_cursor,
        )?;

        self.kernel_jump(kernel_image, ramdisk, dtb, token)
    }

    fn is_unrecoverable_error(error: &IntegrationError) -> bool {
        // Note: these ifs are nested instead of chained because multiple
        //       expressions in an if-let is an unstable features
        if let IntegrationError::AvbSlotVerifyError(ref avb_error) = error {
            // These are the AVB errors that are not recoverable on a subsequent attempt.
            // If necessary in the future, this helper function can be moved to the GblOps trait
            // and customized for platform specific behavior.
            if matches!(
                avb_error,
                SlotVerifyError::Verification(_)
                    | SlotVerifyError::PublicKeyRejected
                    | SlotVerifyError::RollbackIndex
            ) {
                return true;
            }
        }
        false
    }

    fn lvb_inner<'b: 'c, 'c, 'd: 'b, 'e, B: gbl_storage::AsBlockDevice>(
        &mut self,
        avb_ops: &mut impl avb::Ops<'b>,
        ramdisk: &mut Ramdisk,
        kernel_load_buffer: &'e mut [u8],
        partitions_to_verify: &[&CStr],
        partitions_ram_map: &'d mut [PartitionRamMap<'b, 'c>],
        slot_verify_flags: SlotVerifyFlags,
        mut slot_cursor: Cursor<B>,
    ) -> Result<(KernelImage<'e>, BootToken)> {
        let mut oneshot_status = slot_cursor.ctx.get_oneshot_status();
        slot_cursor.ctx.clear_oneshot_status();

        if oneshot_status == Some(OneShot::Bootloader) {
            match self.ops.do_fastboot(&mut slot_cursor) {
                Ok(_) => oneshot_status = slot_cursor.ctx.get_oneshot_status(),
                Err(IntegrationError::UnificationError(Error::NotImplemented)) => (),
                Err(e) => return Err(e),
            }
        }

        let boot_target = match oneshot_status {
            None | Some(OneShot::Bootloader) => slot_cursor.ctx.get_boot_target()?,
            Some(OneShot::Continue(recovery)) => BootTarget::Recovery(recovery),
        };

        let mut verify_data = self
            .load_and_verify_image(
                avb_ops,
                partitions_to_verify,
                slot_verify_flags,
                Some(boot_target),
            )
            .map_err(|e: IntegrationError| {
                if let BootTarget::NormalBoot(slot) = boot_target {
                    if Self::is_unrecoverable_error(&e) {
                        let _ = slot_cursor.ctx.set_slot_unbootable(
                            slot.suffix,
                            UnbootableReason::VerificationFailure,
                        );
                    } else {
                        // Note: the call to mark_boot_attempt will fail if any of the following occur:
                        // * the target was already Unbootable before the call to load_and_verify_image
                        // * policy, I/O, or other errors in mark_boot_attempt
                        //
                        // We don't really care about those circumstances.
                        // The call here is a best effort attempt to decrement tries remaining.
                        let _ = slot_cursor.ctx.mark_boot_attempt();
                    }
                }
                e
            })?;

        let (boot_image, init_boot_image, vendor_boot_image, _) =
            get_images(&mut verify_data, partitions_ram_map);
        let boot_image = boot_image.ok_or(Error::MissingImage)?;
        let vendor_boot_image = vendor_boot_image.ok_or(Error::MissingImage)?;
        let init_boot_image = init_boot_image.ok_or(Error::MissingImage)?;

        if is_overlap(&[
            boot_image.0,
            vendor_boot_image.0,
            init_boot_image.0,
            &ramdisk.0,
            kernel_load_buffer,
        ]) {
            return Err(IntegrationError::UnificationError(Error::BufferOverlap));
        }

        let info_struct = self.unpack_boot_image(&boot_image, Some(boot_target))?;

        let kernel_image = self.kernel_load(&info_struct, boot_image, kernel_load_buffer)?;

        let cmd_line = self.ramdisk_bootconfig_load(
            &info_struct,
            &vendor_boot_image,
            &init_boot_image,
            ramdisk,
        )?;

        self.dtb_update_and_load(&info_struct, vendor_boot_image)?;

        let token = slot_cursor.ctx.mark_boot_attempt().map_err(|_| Error::OperationProhibited)?;

        Ok((kernel_image, token))
    }
}

#[cfg(test)]
mod tests {
    extern crate avb_sysdeps;
    extern crate avb_test;
    use super::*;
    use avb::{CertPermanentAttributes, SlotVerifyError};
    use avb_test::{FakeVbmetaKey, TestOps};
    use std::{fs, path::Path};
    use zerocopy::FromBytes;

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
        avb_ops.rollbacks.insert(TEST_VBMETA_ROLLBACK_LOCATION, 0);
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
        avb_ops.rollbacks.insert(avb::CERT_PIK_VERSION_LOCATION, TEST_CERT_PIK_VERSION);
        avb_ops.rollbacks.insert(avb::CERT_PSK_VERSION_LOCATION, TEST_CERT_PSK_VERSION);

        avb_ops
    }

    #[test]
    fn test_load_and_verify_image_success() {
        let mut gbl_ops = DefaultGblOps {};
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
        let mut gbl_ops = DefaultGblOps {};
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
        let mut gbl_ops = DefaultGblOps {};
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
        let mut gbl_ops = DefaultGblOps {};
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
        let mut gbl_ops = DefaultGblOps {};
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
            IntegrationError::AvbSlotVerifyError(SlotVerifyError::PublicKeyRejected)
        );
    }
}
