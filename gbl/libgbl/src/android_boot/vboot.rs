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

use crate::{
    gbl_avb::{
        ops::{GblAvbOps, AVB_DIGEST_KEY},
        state::{BootStateColor, KeyValidationStatus},
    },
    gbl_print, gbl_println, GblOps, Result,
};
use abr::SlotIndex;
use arrayvec::ArrayVec;
use avb::{slot_verify, HashtreeErrorMode, Ops as _, SlotVerifyFlags};
use bootparams::{bootconfig::BootConfigBuilder, entry::CommandlineParser};
use core::{ffi::CStr, fmt::Write};
use liberror::Error;

// Maximum number of partition allowed for verification.
//
// The value is randomly chosen for now. We can update it as we see more usecases.
const MAX_NUM_PARTITION: usize = 16;

// Type alias for ArrayVec of size `MAX_NUM_PARTITION`:
type ArrayMaxParts<T> = ArrayVec<T, MAX_NUM_PARTITION>;

/// A container holding partitions for libavb verification
pub(crate) struct PartitionsToVerify<'a> {
    partitions: ArrayMaxParts<&'a CStr>,
    preloaded: ArrayMaxParts<(&'a str, &'a [u8])>,
}

impl<'a> PartitionsToVerify<'a> {
    /// Appends a partition to verify
    #[cfg(test)]
    pub fn try_push(&mut self, name: &'a CStr) -> Result<()> {
        self.partitions.try_push(name).or(Err(Error::TooManyPartitions(MAX_NUM_PARTITION)))?;
        Ok(())
    }

    /// Appends a partition, along with its preloaded data
    pub fn try_push_preloaded(&mut self, name: &'a CStr, data: &'a [u8]) -> Result<()> {
        let err = Err(Error::TooManyPartitions(MAX_NUM_PARTITION));
        self.partitions.try_push(name).or(err)?;
        self.preloaded.try_push((name.to_str().unwrap(), data)).or(err)?;
        Ok(())
    }

    /// Appends partitions, along with preloaded data
    pub fn try_extend_preloaded(&mut self, partitions: &PartitionsToVerify<'a>) -> Result<()> {
        let err = Err(Error::TooManyPartitions(MAX_NUM_PARTITION));
        self.partitions.try_extend_from_slice(partitions.partitions()).or(err)?;
        self.preloaded.try_extend_from_slice(partitions.preloaded()).or(err)?;
        Ok(())
    }

    fn partitions(&self) -> &[&'a CStr] {
        &self.partitions
    }

    fn preloaded(&self) -> &[(&'a str, &'a [u8])] {
        &self.preloaded
    }
}

impl<'a> Default for PartitionsToVerify<'a> {
    fn default() -> Self {
        Self { partitions: ArrayMaxParts::new(), preloaded: ArrayMaxParts::new() }
    }
}

/// Android verified boot flow.
///
/// All relevant images from disk must be preloaded and provided as `partitions`; in its final
/// state `ops` will provide the necessary callbacks for where the images should go in RAM and
/// which ones are preloaded.
///
/// # Arguments
/// * `ops`: [GblOps] providing device-specific backend.
/// * `slot`: The slot index.
/// * `partitions`: [PartitionsToVerify] providing pre-loaded partitions.
/// * `bootconfig_builder`: object to write the bootconfig data into.
///
/// # Returns
/// `()` on success. Returns an error if verification process failed and boot cannot
/// continue, or if parsing the command line or updating the boot configuration fail.
pub(crate) fn avb_verify_slot<'a, 'b, 'c>(
    ops: &mut impl GblOps<'a, 'b>,
    slot: u8,
    partitions: &PartitionsToVerify<'c>,
    bootconfig_builder: &mut BootConfigBuilder,
) -> Result<()> {
    let slot = match slot {
        0 => SlotIndex::A,
        1 => SlotIndex::B,
        _ => {
            gbl_println!(ops, "AVB: Invalid slot index: {slot}");
            return Err(Error::InvalidInput.into());
        }
    };

    let mut avb_ops = GblAvbOps::new(ops, Some(slot), partitions.preloaded(), false);
    let unlocked = avb_ops.read_is_device_unlocked()?;
    let verify_result = slot_verify(
        &mut avb_ops,
        partitions.partitions(),
        Some(slot.into()),
        // TODO(b/337846185): Pass AVB_SLOT_VERIFY_FLAGS_RESTART_CAUSED_BY_HASHTREE_CORRUPTION in
        // case verity corruption is detected by HLOS.
        match unlocked {
            true => SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_ALLOW_VERIFICATION_ERROR,
            _ => SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_NONE,
        },
        // TODO(b/337846185): For demo, we use the same setting as Cuttlefish u-boot.
        // Pass AVB_HASHTREE_ERROR_MODE_MANAGED_RESTART_AND_EIO and handle EIO.
        HashtreeErrorMode::AVB_HASHTREE_ERROR_MODE_RESTART_AND_INVALIDATE,
    );
    let (color, verify_data) = match verify_result {
        Ok(ref verify_data) => {
            let color = match unlocked {
                false
                    if avb_ops.key_validation_status()? == KeyValidationStatus::ValidCustomKey =>
                {
                    BootStateColor::Yellow
                }
                false => BootStateColor::Green,
                true => BootStateColor::Orange,
            };

            gbl_println!(
                avb_ops.gbl_ops,
                "AVB verification passed. Device is unlocked: {unlocked}. Color: {color}"
            );

            (color, Some(verify_data))
        }
        // Non-fatal error, can continue booting since verify_data is available.
        Err(ref e) if e.verification_data().is_some() && unlocked => {
            let color = BootStateColor::Orange;

            gbl_println!(
                avb_ops.gbl_ops,
                "AVB verification failed with {e}. Device is unlocked: {unlocked}. Color: {color}. \
                Continue current boot attempt."
            );

            (color, Some(e.verification_data().unwrap()))
        }
        // Fatal error. Cannot boot.
        Err(ref e) => {
            let color = BootStateColor::Red;

            gbl_println!(
                avb_ops.gbl_ops,
                "AVB verification failed with {e}. Device is unlocked: {unlocked}. Color: {color}. \
                Cannot continue boot."
            );

            (color, None)
        }
    };

    // Gets digest from the result command line.
    let mut digest = None;
    if let Some(ref verify_data) = verify_data {
        for entry in CommandlineParser::new(verify_data.cmdline().to_str().unwrap()) {
            let entry = entry?;
            if entry.key == AVB_DIGEST_KEY {
                digest = entry.value;
            }
            write!(bootconfig_builder, "{}\n", entry).or(Err(Error::BufferTooSmall(None)))?;
        }
    }

    // Allowes FW to handle verification result.
    avb_ops.handle_verification_result(verify_data, color, digest)?;

    match color {
        BootStateColor::Red => Err(verify_result.unwrap_err().without_verify_data().into()),
        _ => {
            write!(bootconfig_builder, "androidboot.verifiedbootstate={}\n", color)
                .or(Err(Error::BufferTooSmall(None)))?;

            Ok(())
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        android_boot::load::tests::{
            dump_bootconfig, make_bootconfig, read_test_data, read_test_data_as_str,
            AvbResultBootconfigBuilder, TEST_PUBLIC_KEY_DIGEST,
        },
        ops::test::{FakeGblOps, FakeGblOpsStorage},
        IntegrationError::AvbIoError,
    };
    use avb::{IoError, SlotVerifyError};
    use std::{collections::HashMap, ffi::CStr};

    /// Helper for testing avb_verify_slot
    fn test_avb_verify_slot<'a>(
        partitions: &[(&CStr, &str)],
        partitions_to_verify: &PartitionsToVerify<'a>,
        device_unlocked: std::result::Result<bool, avb::IoError>,
        rollback_result: std::result::Result<u64, avb::IoError>,
        slot: u8,
        expected_reported_color: Option<BootStateColor>,
        expected_bootconfig: &[u8],
    ) -> Result<()> {
        let mut storage = FakeGblOpsStorage::default();
        for (part, file) in partitions {
            storage.add_raw_device(part, read_test_data(file));
        }
        let mut ops = FakeGblOps::new(&storage);
        ops.avb_ops.unlock_state = device_unlocked;
        ops.avb_ops.rollbacks = HashMap::from([(1, rollback_result)]);
        let mut out_color = None;
        let mut handler = |color,
                           _: Option<&CStr>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>| {
            out_color = Some(color);
            Ok(())
        };
        ops.avb_handle_verification_result = Some(&mut handler);
        ops.avb_key_validation_status = Some(Ok(KeyValidationStatus::Valid));

        let mut bootconfig_buffer = vec![0u8; 512 * 1024];
        let mut bootconfig_builder = BootConfigBuilder::new(&mut bootconfig_buffer).unwrap();
        let verify_result =
            avb_verify_slot(&mut ops, slot, partitions_to_verify, &mut bootconfig_builder);
        let bootconfig_bytes = bootconfig_builder.config_bytes();

        assert_eq!(out_color, expected_reported_color);
        assert_eq!(
            bootconfig_bytes,
            expected_bootconfig,
            "\nexpect: \n{}\nactual: \n{}\n",
            dump_bootconfig(expected_bootconfig),
            dump_bootconfig(bootconfig_bytes),
        );

        verify_result
    }

    #[test]
    fn test_avb_verify_slot_success() {
        let mut partitions_to_verify = PartitionsToVerify::default();
        partitions_to_verify.try_push(c"boot").unwrap();
        partitions_to_verify.try_push(c"init_boot").unwrap();
        partitions_to_verify.try_push(c"vendor_boot").unwrap();
        let partitions_data = [
            (c"boot_a", "boot_no_ramdisk_v4_a.img"),
            (c"init_boot_a", "init_boot_a.img"),
            (c"vendor_boot_a", "vendor_boot_v4_a.img"),
            (c"vbmeta_a", "vbmeta_v4_v4_init_boot_a.img"),
        ];
        let expected_bootconfig = AvbResultBootconfigBuilder::new()
            .vbmeta_size(read_test_data("vbmeta_v4_v4_init_boot_a.img").len())
            .digest(
                read_test_data_as_str("vbmeta_v4_v4_init_boot_a.digest.txt")
                    .strip_suffix("\n")
                    .unwrap(),
            )
            .partition_digest(
                "boot",
                read_test_data_as_str("vbmeta_v4_v4_init_boot_a.boot.digest.txt")
                    .strip_suffix("\n")
                    .unwrap(),
            )
            .partition_digest(
                "init_boot",
                read_test_data_as_str("vbmeta_v4_v4_init_boot_a.init_boot.digest.txt")
                    .strip_suffix("\n")
                    .unwrap(),
            )
            .partition_digest(
                "vendor_boot",
                read_test_data_as_str("vbmeta_v4_v4_init_boot_a.vendor_boot.digest.txt")
                    .strip_suffix("\n")
                    .unwrap(),
            )
            .public_key_digest(TEST_PUBLIC_KEY_DIGEST)
            .build();

        assert_eq!(
            test_avb_verify_slot(
                &partitions_data,
                &partitions_to_verify,
                // Unlocked result
                Ok(false),
                // Rollback index result
                Ok(0),
                // Slot
                0,
                // Expected color
                Some(BootStateColor::Green),
                // Expected bootcofnig
                &expected_bootconfig,
            ),
            Ok(()),
        );
    }

    #[test]
    fn test_avb_verify_slot_from_preloaded_success() {
        let boot = read_test_data("boot_no_ramdisk_v4_a.img");
        let init_boot = read_test_data("init_boot_a.img");
        let vendor_boot = read_test_data("vendor_boot_v4_a.img");

        let mut partitions_to_verify = PartitionsToVerify::default();
        partitions_to_verify.try_push_preloaded(c"boot", &boot).unwrap();
        partitions_to_verify.try_push_preloaded(c"init_boot", &init_boot).unwrap();
        partitions_to_verify.try_push_preloaded(c"vendor_boot", &vendor_boot).unwrap();
        let partitions_data = [
            // Required images aren't presented. Have to rely on preloaded.
            (c"vbmeta_a", "vbmeta_v4_v4_init_boot_a.img"),
        ];
        let expected_bootconfig = AvbResultBootconfigBuilder::new()
            .vbmeta_size(read_test_data("vbmeta_v4_v4_init_boot_a.img").len())
            .digest(
                read_test_data_as_str("vbmeta_v4_v4_init_boot_a.digest.txt")
                    .strip_suffix("\n")
                    .unwrap(),
            )
            .partition_digest(
                "boot",
                read_test_data_as_str("vbmeta_v4_v4_init_boot_a.boot.digest.txt")
                    .strip_suffix("\n")
                    .unwrap(),
            )
            .partition_digest(
                "init_boot",
                read_test_data_as_str("vbmeta_v4_v4_init_boot_a.init_boot.digest.txt")
                    .strip_suffix("\n")
                    .unwrap(),
            )
            .partition_digest(
                "vendor_boot",
                read_test_data_as_str("vbmeta_v4_v4_init_boot_a.vendor_boot.digest.txt")
                    .strip_suffix("\n")
                    .unwrap(),
            )
            .public_key_digest(TEST_PUBLIC_KEY_DIGEST)
            .build();

        assert_eq!(
            test_avb_verify_slot(
                &partitions_data,
                &partitions_to_verify,
                // Unlocked result
                Ok(false),
                // Rollback index result
                Ok(0),
                // Slot
                0,
                // Expected color
                Some(BootStateColor::Green),
                // Expected bootcofnig
                &expected_bootconfig,
            ),
            Ok(()),
        );
    }

    #[test]
    fn test_avb_verify_slot_success_unlocked() {
        let mut partitions_to_verify = PartitionsToVerify::default();
        partitions_to_verify.try_push(c"boot").unwrap();
        partitions_to_verify.try_push(c"init_boot").unwrap();
        partitions_to_verify.try_push(c"vendor_boot").unwrap();
        let partitions_data = [
            (c"boot_a", "boot_no_ramdisk_v4_a.img"),
            (c"init_boot_a", "init_boot_a.img"),
            (c"vendor_boot_a", "vendor_boot_v4_a.img"),
            (c"vbmeta_a", "vbmeta_v4_v4_init_boot_a.img"),
        ];
        let expected_bootconfig = AvbResultBootconfigBuilder::new()
            .vbmeta_size(read_test_data("vbmeta_v4_v4_init_boot_a.img").len())
            .digest(
                read_test_data_as_str("vbmeta_v4_v4_init_boot_a.digest.txt")
                    .strip_suffix("\n")
                    .unwrap(),
            )
            .partition_digest(
                "boot",
                read_test_data_as_str("vbmeta_v4_v4_init_boot_a.boot.digest.txt")
                    .strip_suffix("\n")
                    .unwrap(),
            )
            .partition_digest(
                "init_boot",
                read_test_data_as_str("vbmeta_v4_v4_init_boot_a.init_boot.digest.txt")
                    .strip_suffix("\n")
                    .unwrap(),
            )
            .partition_digest(
                "vendor_boot",
                read_test_data_as_str("vbmeta_v4_v4_init_boot_a.vendor_boot.digest.txt")
                    .strip_suffix("\n")
                    .unwrap(),
            )
            .public_key_digest(TEST_PUBLIC_KEY_DIGEST)
            .color(BootStateColor::Orange)
            .unlocked(true)
            .build();

        assert_eq!(
            test_avb_verify_slot(
                &partitions_data,
                &partitions_to_verify,
                // Unlocked result
                Ok(true),
                // Rollback index result
                Ok(0),
                // Slot
                0,
                // Expected color
                Some(BootStateColor::Orange),
                // Expected bootconfig
                &expected_bootconfig,
            ),
            Ok(()),
        );
    }

    #[test]
    fn test_avb_verify_slot_verification_failed_unlocked() {
        let mut partitions_to_verify = PartitionsToVerify::default();
        partitions_to_verify.try_push(c"boot").unwrap();
        partitions_to_verify.try_push(c"init_boot").unwrap();
        partitions_to_verify.try_push(c"vendor_boot").unwrap();
        let partitions_data = [
            (c"boot_a", "boot_no_ramdisk_v4_a.img"),
            (c"init_boot_a", "init_boot_a.img"),
            (c"vendor_boot_a", "vendor_boot_v4_a.img"),
            (c"vbmeta_a", "vbmeta_v4_v4_init_boot_a.img"),
        ];
        let expected_bootconfig = AvbResultBootconfigBuilder::new()
            .vbmeta_size(read_test_data("vbmeta_v4_v4_init_boot_a.img").len())
            .digest(
                read_test_data_as_str("vbmeta_v4_v4_init_boot_a.digest.txt")
                    .strip_suffix("\n")
                    .unwrap(),
            )
            .partition_digest(
                "boot",
                read_test_data_as_str("vbmeta_v4_v4_init_boot_a.boot.digest.txt")
                    .strip_suffix("\n")
                    .unwrap(),
            )
            .partition_digest(
                "init_boot",
                read_test_data_as_str("vbmeta_v4_v4_init_boot_a.init_boot.digest.txt")
                    .strip_suffix("\n")
                    .unwrap(),
            )
            .partition_digest(
                "vendor_boot",
                read_test_data_as_str("vbmeta_v4_v4_init_boot_a.vendor_boot.digest.txt")
                    .strip_suffix("\n")
                    .unwrap(),
            )
            .public_key_digest(TEST_PUBLIC_KEY_DIGEST)
            .color(BootStateColor::Orange)
            .unlocked(true)
            .build();

        assert_eq!(
            test_avb_verify_slot(
                &partitions_data,
                &partitions_to_verify,
                // Unlocked result
                Ok(true),
                // Rollback index result
                Ok(0),
                // Slot
                0,
                // Expected color
                Some(BootStateColor::Orange),
                // Expected bootconfig
                &expected_bootconfig,
            ),
            // Device is unlocked, so can continue boot
            Ok(()),
        );
    }

    #[test]
    fn test_avb_verify_slot_verification_fatal_failed_unlocked() {
        let mut partitions_to_verify = PartitionsToVerify::default();
        partitions_to_verify.try_push(c"boot").unwrap();
        partitions_to_verify.try_push(c"init_boot").unwrap();
        partitions_to_verify.try_push(c"vendor_boot").unwrap();
        let partitions_data = [
            (c"boot_a", "boot_no_ramdisk_v4_a.img"),
            (c"init_boot_a", "init_boot_a.img"),
            (c"vendor_boot_a", "vendor_boot_v4_a.img"),
            (c"vbmeta_a", "vbmeta_v4_v4_init_boot_a.img"),
        ];
        let expected_bootconfig = make_bootconfig("");

        assert_eq!(
            test_avb_verify_slot(
                &partitions_data,
                &partitions_to_verify,
                // Unlocked result
                Ok(true),
                // Get rollback index is failed
                Err(IoError::NoSuchValue),
                // Slot
                0,
                // Expected color
                Some(BootStateColor::Red),
                // Expected bootconfig
                &expected_bootconfig,
            ),
            // Fatal error, so cannot continue boot
            Err(SlotVerifyError::Io.into()),
        );
    }

    #[test]
    fn test_avb_verify_slot_verification_failed_locked() {
        let mut partitions_to_verify = PartitionsToVerify::default();
        partitions_to_verify.try_push(c"boot").unwrap();
        partitions_to_verify.try_push(c"init_boot").unwrap();
        partitions_to_verify.try_push(c"vendor_boot").unwrap();
        let partitions_data = [
            // Wrong boot image, expect verification to fail.
            (c"boot_a", "boot_v0_a.img"),
            (c"init_boot_a", "init_boot_a.img"),
            (c"vendor_boot_a", "vendor_boot_v4_a.img"),
            (c"vbmeta_a", "vbmeta_v4_v4_init_boot_a.img"),
        ];
        let expected_bootconfig = make_bootconfig("");

        assert_eq!(
            test_avb_verify_slot(
                &partitions_data,
                &partitions_to_verify,
                // Unlocked result
                Ok(false),
                // Rollback index result
                Ok(0),
                // Slot
                0,
                // Expected color
                Some(BootStateColor::Red),
                // Expected bootconfig
                &expected_bootconfig,
            ),
            // Cannot continue boot
            Err(SlotVerifyError::Verification(None).into()),
        );
    }

    #[test]
    fn test_avb_verify_slot_verification_failed_obtain_lock_status() {
        let partitions_to_verify = PartitionsToVerify::default();
        let expected_bootconfig = make_bootconfig("");

        assert_eq!(
            test_avb_verify_slot(
                &[],
                &partitions_to_verify,
                // Unlocked result
                Err(avb::IoError::NoSuchValue),
                // Rollback index result
                Ok(0),
                // Slot
                0,
                // Expected color
                None,
                // Expected bootconfig
                &expected_bootconfig,
            ),
            // Cannot continue boot
            Err(AvbIoError(IoError::NoSuchValue)),
        );
    }
}
