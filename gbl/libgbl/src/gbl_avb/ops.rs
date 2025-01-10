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

//! Gbl AVB operations.

use crate::{
    gbl_avb::state::{BootStateColor, KeyValidationStatus},
    gbl_print, gbl_println, GblOps,
};
use arrayvec::ArrayString;
use avb::{
    cert_validate_vbmeta_public_key, CertOps, CertPermanentAttributes, IoError, IoResult,
    Ops as AvbOps, PublicKeyForPartitionInfo, SlotVerifyData, SHA256_DIGEST_SIZE,
    SHA512_DIGEST_SIZE,
};
use core::fmt::Write;
use core::{
    cmp::{max, min},
    ffi::CStr,
};
use liberror::Error;
use safemath::SafeNum;
use uuid::Uuid;

/// The digest key in commandline provided by libavb.
pub const AVB_DIGEST_KEY: &str = "androidboot.vbmeta.digest";

// AVB cert tracks versions for the PIK and PSK; PRK cannot be changed so has no version info.
const AVB_CERT_NUM_KEY_VERSIONS: usize = 2;

/// Implements avb ops callbacks for [GblOps].
pub struct GblAvbOps<'a, T> {
    /// The underlying [GblOps].
    pub gbl_ops: &'a mut T,
    preloaded_partitions: &'a [(&'a str, &'a [u8])],
    /// Used for storing key versions to be set (location, version).
    ///
    /// These will initially be `None`, but if using the cert extensions they will be updated during
    /// verification. These values will not be automatically persisted to disk because whether to do
    /// so depends on other factors such as slot success state; it's up to the user to persist them
    /// post-verification if needed.
    // If `array_map` is imported in the future, consider switching to it.
    pub key_versions: [Option<(usize, u64)>; AVB_CERT_NUM_KEY_VERSIONS],
    /// True to use the AVB cert extensions.
    use_cert: bool,
    /// Avb public key validation status reported by validate_vbmeta_public_key.
    /// https://source.android.com/docs/security/features/verifiedboot/boot-flow#locked-devices-with-custom-root-of-trust
    key_validation_status: Option<KeyValidationStatus>,
}

impl<'a, 'p, 'q, T: GblOps<'p, 'q>> GblAvbOps<'a, T> {
    /// Creates a new [GblAvbOps].
    pub fn new(
        gbl_ops: &'a mut T,
        preloaded_partitions: &'a [(&'a str, &'a [u8])],
        use_cert: bool,
    ) -> Self {
        Self {
            gbl_ops,
            preloaded_partitions,
            key_versions: [None; AVB_CERT_NUM_KEY_VERSIONS],
            use_cert,
            key_validation_status: None,
        }
    }

    /// Returns the size of a partition.
    ///
    /// This will only consider the [GblOps] partitions. To include preloaded partitions as well,
    /// use [AvbOps::get_size_of_partition].
    fn partition_size(&mut self, partition: &str) -> IoResult<u64> {
        self.gbl_ops.partition_size(partition).or(Err(IoError::Io))?.ok_or(IoError::NoSuchPartition)
    }

    /// Allowes implementation side to handle verification result.
    pub fn handle_verification_result(
        &mut self,
        slot_verify: Option<&SlotVerifyData>,
        color: BootStateColor,
        digest: Option<&str>,
    ) -> IoResult<()> {
        // The Android build system automatically generates only the main vbmeta, but also allows
        // to have separate chained partitions like vbmeta_system (for system, product, system_ext,
        // etc.) or vbmeta_vendor (for vendor).
        // https://android.googlesource.com/platform/external/avb/+/master/README.md#build-system-integration
        //
        // It may also integrate chained vbmeta into system level metadata partitions such as boot
        // or init_boot, so they can be updated separately.
        // https://android.googlesource.com/platform/external/avb/+/master/README.md#gki-2_0-integration
        //
        // Custom chained partitions are also supported by the Android build system, but we expect
        // OEMs to follow about the same pattern.
        // https://android-review.googlesource.com/q/Id671e2c3aee9ada90256381cce432927df03169b
        let (
            boot_os_version,
            boot_security_patch,
            system_os_version,
            system_security_patch,
            vendor_os_version,
            vendor_security_patch,
        ) = match slot_verify {
            Some(slot_verify) => {
                let mut vbmeta = None;
                let mut vbmeta_boot = None;
                let mut vbmeta_system = None;
                let mut vbmeta_vendor = None;

                for data in slot_verify.vbmeta_data() {
                    match data.partition_name().to_str().unwrap_or_default() {
                        "vbmeta" => vbmeta = Some(data),
                        "boot" => vbmeta_boot = Some(data),
                        "vbmeta_system" => vbmeta_system = Some(data),
                        "vbmeta_vendor" => vbmeta_vendor = Some(data),
                        _ => {}
                    }
                }

                let data = vbmeta.ok_or(IoError::NoSuchPartition)?;
                let boot_data = vbmeta_boot.unwrap_or(data);
                let system_data = vbmeta_system.unwrap_or(data);
                let vendor_data = vbmeta_vendor.unwrap_or(data);

                (
                    boot_data.get_property_value("com.android.build.boot.os_version"),
                    boot_data.get_property_value("com.android.build.boot.security_patch"),
                    system_data.get_property_value("com.android.build.system.os_version"),
                    system_data.get_property_value("com.android.build.system.security_patch"),
                    vendor_data.get_property_value("com.android.build.vendor.os_version"),
                    vendor_data.get_property_value("com.android.build.vendor.security_patch"),
                )
            }
            None => (None, None, None, None, None, None),
        };

        // Convert digest rust string to null-terminated string by copying it into separate buffer.
        let mut digest_buffer = ArrayString::<{ 2 * SHA512_DIGEST_SIZE + 1 }>::new();
        let digest_cstr = match digest {
            Some(digest) => {
                write!(digest_buffer, "{}\0", digest).or(Err(IoError::InvalidValueSize))?;
                Some(
                    CStr::from_bytes_until_nul(digest_buffer.as_bytes())
                        .or(Err(IoError::InvalidValueSize))?,
                )
            }
            None => None,
        };

        self.gbl_ops.avb_handle_verification_result(
            color,
            digest_cstr,
            boot_os_version,
            boot_security_patch,
            system_os_version,
            system_security_patch,
            vendor_os_version,
            vendor_security_patch,
        )
    }

    /// Get vbmeta public key validation status reported by validate_vbmeta_public_key.
    pub fn key_validation_status(&self) -> IoResult<KeyValidationStatus> {
        self.key_validation_status.ok_or(IoError::NotImplemented)
    }
}

/// A helper function for converting `CStr` to `str`
fn cstr_to_str<E>(s: &CStr, err: E) -> Result<&str, E> {
    Ok(s.to_str().or(Err(err))?)
}

/// # Lifetimes
/// * `'a`: preloaded data lifetime
/// * `'b`: [GblOps] partition lifetime
impl<'a, 'b, 'c, T: GblOps<'b, 'c>> AvbOps<'a> for GblAvbOps<'a, T> {
    fn read_from_partition(
        &mut self,
        partition: &CStr,
        offset: i64,
        buffer: &mut [u8],
    ) -> IoResult<usize> {
        let part_str = cstr_to_str(partition, IoError::NoSuchPartition)?;
        let partition_size = SafeNum::from(self.partition_size(part_str)?);
        let read_off = match offset < 0 {
            true => partition_size - offset.abs(),
            _ => SafeNum::from(offset),
        };
        let read_sz = partition_size - read_off;
        let read_off = read_off.try_into().or(Err(IoError::RangeOutsidePartition))?;
        let read_sz =
            min(buffer.len(), read_sz.try_into().or(Err(IoError::RangeOutsidePartition))?);
        self.gbl_ops.read_from_partition_sync(part_str, read_off, &mut buffer[..read_sz]).map_err(
            |e| match e {
                Error::NotFound => IoError::NoSuchPartition,
                Error::ArithmeticOverflow(_) => IoError::RangeOutsidePartition,
                _ => IoError::Io,
            },
        )?;
        Ok(read_sz)
    }

    fn get_preloaded_partition(&mut self, partition: &CStr) -> IoResult<&'a [u8]> {
        let part_str = cstr_to_str(partition, IoError::NotImplemented)?;
        Ok(self
            .preloaded_partitions
            .iter()
            .find(|(name, _)| *name == part_str)
            .ok_or(IoError::NotImplemented)?
            .1)
    }

    fn validate_vbmeta_public_key(
        &mut self,
        public_key: &[u8],
        public_key_metadata: Option<&[u8]>,
    ) -> IoResult<bool> {
        let status = if self.use_cert {
            match cert_validate_vbmeta_public_key(self, public_key, public_key_metadata)? {
                true => KeyValidationStatus::Valid,
                false => KeyValidationStatus::Invalid,
            }
        } else {
            self.gbl_ops.avb_validate_vbmeta_public_key(public_key, public_key_metadata).or_else(
                |err| {
                    // TODO(b/337846185): Remove fallback once AVB protocol implementation is
                    // forced.
                    fallback_not_implemented(
                        self.gbl_ops,
                        err,
                        "validate_vbmeta_public_key",
                        KeyValidationStatus::ValidCustomKey,
                    )
                },
            )?
        };

        self.key_validation_status = Some(status);

        Ok(matches!(status, KeyValidationStatus::Valid | KeyValidationStatus::ValidCustomKey))
    }

    fn read_rollback_index(&mut self, rollback_index_location: usize) -> IoResult<u64> {
        self.gbl_ops.avb_read_rollback_index(rollback_index_location).or_else(|err| {
            // TODO(b/337846185): Remove fallback once AVB protocol implementation is
            // forced.
            fallback_not_implemented(self.gbl_ops, err, "read_rollback_index", 0)
        })
    }

    fn write_rollback_index(&mut self, rollback_index_location: usize, index: u64) -> IoResult<()> {
        self.gbl_ops.avb_write_rollback_index(rollback_index_location, index).or_else(|err| {
            // TODO(b/337846185): Remove fallback once AVB protocol implementation is
            // forced.
            fallback_not_implemented(self.gbl_ops, err, "write_rollback_index", ())
        })
    }

    fn read_is_device_unlocked(&mut self) -> IoResult<bool> {
        self.gbl_ops.avb_read_is_device_unlocked().or_else(|err| {
            // TODO(b/337846185): Remove fallback once AVB protocol implementation is
            // forced.
            fallback_not_implemented(self.gbl_ops, err, "read_is_device_unlocked", true)
        })
    }

    fn get_unique_guid_for_partition(&mut self, partition: &CStr) -> IoResult<Uuid> {
        // The ops is only used to check that a partition exists. GUID is not used.
        self.partition_size(cstr_to_str(partition, IoError::NoSuchPartition)?)?;
        Ok(Uuid::nil())
    }

    fn get_size_of_partition(&mut self, partition: &CStr) -> IoResult<u64> {
        match self.get_preloaded_partition(partition) {
            Ok(img) => Ok(img.len().try_into().unwrap()),
            _ => {
                let part_str = cstr_to_str(partition, IoError::NoSuchPartition)?;
                self.partition_size(part_str)
            }
        }
    }

    fn read_persistent_value(&mut self, name: &CStr, value: &mut [u8]) -> IoResult<usize> {
        self.gbl_ops.avb_read_persistent_value(name, value).or_else(|err| {
            // TODO(b/337846185): Remove fallback once AVB protocol implementation is
            // forced.
            fallback_not_implemented(self.gbl_ops, err, "read_persistent_value", 0)
        })
    }

    fn write_persistent_value(&mut self, name: &CStr, value: &[u8]) -> IoResult<()> {
        self.gbl_ops.avb_write_persistent_value(name, value).or_else(|err| {
            // TODO(b/337846185): Remove fallback once AVB protocol implementation is
            // forced.
            fallback_not_implemented(self.gbl_ops, err, "write_persistent_value", ())
        })
    }

    fn erase_persistent_value(&mut self, name: &CStr) -> IoResult<()> {
        self.gbl_ops.avb_erase_persistent_value(name).or_else(|err| {
            // TODO(b/337846185): Remove fallback once AVB protocol implementation is
            // forced.
            fallback_not_implemented(self.gbl_ops, err, "erase_persistent_value", ())
        })
    }

    fn validate_public_key_for_partition(
        &mut self,
        _partition: &CStr,
        _public_key: &[u8],
        _public_key_metadata: Option<&[u8]>,
    ) -> IoResult<PublicKeyForPartitionInfo> {
        // Not needed yet; eventually we will plumb this through [GblOps].
        unreachable!();
    }

    fn cert_ops(&mut self) -> Option<&mut dyn CertOps> {
        match self.use_cert {
            true => Some(self),
            false => None,
        }
    }
}

/// [GblAvbOps] always implements [CertOps], but it's only used if `use_cert` is set.
impl<'a, 'b, T: GblOps<'a, 'b>> CertOps for GblAvbOps<'_, T> {
    fn read_permanent_attributes(
        &mut self,
        attributes: &mut CertPermanentAttributes,
    ) -> IoResult<()> {
        self.gbl_ops.avb_cert_read_permanent_attributes(attributes)
    }

    fn read_permanent_attributes_hash(&mut self) -> IoResult<[u8; SHA256_DIGEST_SIZE]> {
        self.gbl_ops.avb_cert_read_permanent_attributes_hash()
    }

    fn set_key_version(&mut self, rollback_index_location: usize, key_version: u64) {
        // Checks if there is already an allocated slot for this location.
        let existing = self
            .key_versions
            .iter_mut()
            .find_map(|v| v.as_mut().filter(|(loc, _)| *loc == rollback_index_location));
        match existing {
            Some((_, val)) => *val = max(*val, key_version),
            _ => {
                // Finds an empty slot and stores the rollback index.
                *self
                    .key_versions
                    .iter_mut()
                    .find(|v| v.is_none())
                    .expect("Ran out of key version slots") =
                    Some((rollback_index_location, key_version))
            }
        }
    }

    fn get_random(&mut self, _: &mut [u8]) -> IoResult<()> {
        // Not needed yet; eventually we will plumb this through [GblOps].
        unimplemented!()
    }
}

fn fallback_not_implemented<'a, 'b, T>(
    ops: &mut impl GblOps<'a, 'b>,
    error: IoError,
    method_name: &str,
    value: T,
) -> IoResult<T> {
    match error {
        IoError::NotImplemented => {
            gbl_println!(
                ops,
                "WARNING: UEFI GblEfiAvbProtocol.{} implementation is missing. This will not be \
                permitted in the future.",
                method_name,
            );
            Ok(value)
        }
        err => Err(err),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ops::test::{FakeGblOps, FakeGblOpsStorage};

    // Returns test data consisting of `size` incrementing bytes (0-255 repeating).
    fn test_data(size: usize) -> Vec<u8> {
        let mut data = vec![0u8; size];
        for index in 0..data.len() {
            data[index] = index as u8;
        }
        data
    }

    #[test]
    fn read_from_partition_positive_off() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"test_part", test_data(512));

        let mut gbl_ops = FakeGblOps::new(&storage);
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);

        // Positive offset.
        let mut out = [0u8; 4];
        assert_eq!(avb_ops.read_from_partition(c"test_part", 1, &mut out[..]), Ok(4));
        assert_eq!(out, [1, 2, 3, 4]);
    }

    #[test]
    fn read_from_partition_negative_off() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"test_part", test_data(512));

        let mut gbl_ops = FakeGblOps::new(&storage);
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);

        // Negative offset should wrap from the end
        let mut out = [0u8; 6];
        assert_eq!(avb_ops.read_from_partition(c"test_part", -6, &mut out[..]), Ok(6));
        assert_eq!(out, [0xFA, 0xFB, 0xFC, 0xFD, 0xFE, 0xFF]);
    }

    #[test]
    fn read_from_partition_partial_read() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"test_part", test_data(512));

        let mut gbl_ops = FakeGblOps::new(&storage);
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);

        // Reading past the end of the partition should truncate.
        let mut out = [0u8; 6];
        assert_eq!(avb_ops.read_from_partition(c"test_part", -3, &mut out[..]), Ok(3));
        assert_eq!(out, [0xFD, 0xFE, 0xFF, 0, 0, 0]);
    }

    #[test]
    fn read_from_partition_out_of_bounds() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"test_part", test_data(512));

        let mut gbl_ops = FakeGblOps::new(&storage);
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);

        // Reads starting out of bounds should fail.
        let mut out = [0u8; 4];
        assert_eq!(
            avb_ops.read_from_partition(c"test_part", 513, &mut out[..]),
            Err(IoError::RangeOutsidePartition)
        );
        assert_eq!(
            avb_ops.read_from_partition(c"test_part", -513, &mut out[..]),
            Err(IoError::RangeOutsidePartition)
        );
    }

    #[test]
    fn read_from_partition_unknown_part() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);

        let mut out = [0u8; 4];
        assert_eq!(
            avb_ops.read_from_partition(c"unknown_part", 0, &mut out[..]),
            Err(IoError::NoSuchPartition)
        );
    }

    #[test]
    fn set_key_version_default() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        let avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);

        assert_eq!(avb_ops.key_versions, [None, None]);
    }

    #[test]
    fn set_key_version_once() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);

        avb_ops.set_key_version(5, 10);
        assert_eq!(avb_ops.key_versions, [Some((5, 10)), None]);
    }

    #[test]
    fn set_key_version_twice() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);

        avb_ops.set_key_version(5, 10);
        avb_ops.set_key_version(20, 40);
        assert_eq!(avb_ops.key_versions, [Some((5, 10)), Some((20, 40))]);
    }

    #[test]
    fn set_key_version_overwrite() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);

        avb_ops.set_key_version(5, 10);
        avb_ops.set_key_version(20, 40);
        avb_ops.set_key_version(5, 100);
        assert_eq!(avb_ops.key_versions, [Some((5, 100)), Some((20, 40))]);
    }

    // AVB's key version callback cannot return an error, so if it fails we panic.
    //
    // It's possible we could stash the failure somewhere and check it later, but we'd have to be
    // very careful, as failing to check the status would be a security vulnerability. For now it's
    // safer to panic, and we only ever expect the PSK and PIK to have key versions.
    #[test]
    #[should_panic(expected = "Ran out of key version slots")]
    fn set_key_version_overflow() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);

        avb_ops.set_key_version(5, 10);
        avb_ops.set_key_version(20, 40);
        avb_ops.set_key_version(40, 100);
    }

    #[test]
    fn validate_vbmeta_public_key_valid() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_key_validation_status = Some(Ok(KeyValidationStatus::Valid));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        assert_eq!(avb_ops.validate_vbmeta_public_key(&[], None), Ok(true));
        assert_eq!(avb_ops.key_validation_status(), Ok(KeyValidationStatus::Valid));
    }

    #[test]
    fn validate_vbmeta_public_key_valid_custom_key() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_key_validation_status = Some(Ok(KeyValidationStatus::ValidCustomKey));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        assert_eq!(avb_ops.validate_vbmeta_public_key(&[], None), Ok(true));
        assert_eq!(avb_ops.key_validation_status(), Ok(KeyValidationStatus::ValidCustomKey));
    }

    #[test]
    fn validate_vbmeta_public_key_invalid() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_key_validation_status = Some(Ok(KeyValidationStatus::Invalid));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        assert_eq!(avb_ops.validate_vbmeta_public_key(&[], None), Ok(false));
        assert_eq!(avb_ops.key_validation_status(), Ok(KeyValidationStatus::Invalid));
    }

    #[test]
    fn validate_vbmeta_public_key_failed() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_key_validation_status = Some(Err(IoError::Io));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        assert_eq!(avb_ops.validate_vbmeta_public_key(&[], None), Err(IoError::Io));
        assert!(avb_ops.key_validation_status().is_err());
    }

    // TODO(b/337846185): Remove test once AVB protocol implementation is forced.
    #[test]
    fn validate_vbmeta_public_key_not_implemented() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_key_validation_status = Some(Err(IoError::NotImplemented));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);

        assert_eq!(avb_ops.validate_vbmeta_public_key(&[], None), Ok(true));
        assert_eq!(avb_ops.key_validation_status(), Ok(KeyValidationStatus::ValidCustomKey));
    }

    #[test]
    fn read_rollback_index_read_value() {
        const EXPECTED_INDEX: usize = 1;
        const EXPECTED_VALUE: u64 = 100;

        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_ops.rollbacks.insert(EXPECTED_INDEX, Ok(EXPECTED_VALUE));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        assert_eq!(avb_ops.read_rollback_index(EXPECTED_INDEX), Ok(EXPECTED_VALUE));
    }

    #[test]
    fn read_rollback_index_error_handled() {
        let mut gbl_ops = FakeGblOps::new(&[]);

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        assert_eq!(avb_ops.read_rollback_index(0), Err(IoError::Io));
    }

    // TODO(b/337846185): Remove test once AVB protocol implementation is forced.
    #[test]
    fn read_rollback_index_not_implemented() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_ops.rollbacks.insert(0, Err(IoError::NotImplemented));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        assert_eq!(avb_ops.read_rollback_index(0), Ok(0));
    }

    #[test]
    fn write_rollback_index_write_value() {
        const EXPECTED_INDEX: usize = 1;
        const EXPECTED_VALUE: u64 = 100;

        let mut gbl_ops = FakeGblOps::new(&[]);

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        assert_eq!(avb_ops.write_rollback_index(EXPECTED_INDEX, EXPECTED_VALUE), Ok(()));
        assert_eq!(
            gbl_ops.avb_ops.rollbacks.get(&EXPECTED_INDEX),
            Some(Ok(EXPECTED_VALUE)).as_ref()
        );
    }

    #[test]
    fn write_rollback_index_error_handled() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_ops.rollbacks.insert(0, Err(IoError::Io));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        assert_eq!(avb_ops.write_rollback_index(0, 0), Err(IoError::Io));
    }

    // TODO(b/337846185): Remove test once AVB protocol implementation is forced.
    #[test]
    fn write_rollback_index_not_implemented() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_ops.rollbacks.insert(0, Err(IoError::NotImplemented));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        assert_eq!(avb_ops.write_rollback_index(0, 0), Ok(()));
    }

    #[test]
    fn read_is_device_unlocked_value_obtained() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_ops.unlock_state = Ok(true);

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);

        assert_eq!(avb_ops.read_is_device_unlocked(), Ok(true));
    }

    #[test]
    fn read_is_device_unlocked_error_handled() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_ops.unlock_state = Err(IoError::Io);

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        assert_eq!(avb_ops.read_is_device_unlocked(), Err(IoError::Io));
    }

    // TODO(b/337846185): Remove test once AVB protocol implementation is forced.
    #[test]
    fn read_is_device_unlocked_not_implemented() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_ops.unlock_state = Err(IoError::NotImplemented);

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        assert_eq!(avb_ops.read_is_device_unlocked(), Ok(true));
    }

    #[test]
    fn read_persistent_value_success() {
        const EXPECTED_NAME: &CStr = c"test";
        const EXPECTED_VALUE: &[u8] = b"test";

        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_ops.add_persistent_value(EXPECTED_NAME.to_str().unwrap(), Ok(EXPECTED_VALUE));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        let mut buffer = [0u8; EXPECTED_VALUE.len()];
        assert_eq!(
            avb_ops.read_persistent_value(EXPECTED_NAME, &mut buffer),
            Ok(EXPECTED_VALUE.len())
        );
        assert_eq!(buffer, EXPECTED_VALUE);
    }

    #[test]
    fn read_persistent_value_error() {
        const EXPECTED_NAME: &CStr = c"test";

        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_ops.add_persistent_value(EXPECTED_NAME.to_str().unwrap(), Err(IoError::Io));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        let mut buffer = [0u8; 4];
        assert_eq!(avb_ops.read_persistent_value(EXPECTED_NAME, &mut buffer), Err(IoError::Io));
    }

    // TODO(b/337846185): Remove test once AVB protocol implementation is forced.
    #[test]
    fn read_persistent_value_not_implemented() {
        const EXPECTED_NAME: &CStr = c"test";

        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops
            .avb_ops
            .add_persistent_value(EXPECTED_NAME.to_str().unwrap(), Err(IoError::NotImplemented));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        let mut buffer = [0u8; 0];
        assert_eq!(avb_ops.read_persistent_value(EXPECTED_NAME, &mut buffer), Ok(0));
    }

    #[test]
    fn write_persistent_value_success() {
        const EXPECTED_NAME: &CStr = c"test";
        const EXPECTED_VALUE: &[u8] = b"test";

        let mut gbl_ops = FakeGblOps::new(&[]);

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        assert_eq!(avb_ops.write_persistent_value(EXPECTED_NAME, EXPECTED_VALUE), Ok(()));

        assert_eq!(
            gbl_ops.avb_ops.persistent_values.get(EXPECTED_NAME.to_str().unwrap()),
            Some(Ok(EXPECTED_VALUE.to_vec())).as_ref()
        );
    }

    #[test]
    fn write_persistent_value_error() {
        const EXPECTED_NAME: &CStr = c"test";
        const EXPECTED_VALUE: &[u8] = b"test";

        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_ops.add_persistent_value(EXPECTED_NAME.to_str().unwrap(), Err(IoError::Io));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        assert_eq!(avb_ops.write_persistent_value(EXPECTED_NAME, EXPECTED_VALUE), Err(IoError::Io));
    }

    // TODO(b/337846185): Remove test once AVB protocol implementation is forced.
    #[test]
    fn write_persistent_value_not_implemented() {
        const EXPECTED_NAME: &CStr = c"test";
        const EXPECTED_VALUE: &[u8] = b"test";

        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops
            .avb_ops
            .add_persistent_value(EXPECTED_NAME.to_str().unwrap(), Err(IoError::NotImplemented));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        assert_eq!(avb_ops.write_persistent_value(EXPECTED_NAME, EXPECTED_VALUE), Ok(()));
    }

    #[test]
    fn erase_persistent_value_success() {
        const EXPECTED_NAME: &CStr = c"test";

        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_ops.add_persistent_value(EXPECTED_NAME.to_str().unwrap(), Ok(b"test"));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        assert_eq!(avb_ops.erase_persistent_value(EXPECTED_NAME), Ok(()));

        assert!(!gbl_ops.avb_ops.persistent_values.contains_key(EXPECTED_NAME.to_str().unwrap()));
    }

    #[test]
    fn erase_persistent_value_error() {
        const EXPECTED_NAME: &CStr = c"test";

        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_ops.add_persistent_value(EXPECTED_NAME.to_str().unwrap(), Err(IoError::Io));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        assert_eq!(avb_ops.erase_persistent_value(EXPECTED_NAME), Err(IoError::Io));
    }

    // TODO(b/337846185): Remove test once AVB protocol implementation is forced.
    #[test]
    fn erase_persistent_value_not_implemented() {
        const EXPECTED_NAME: &CStr = c"test";

        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops
            .avb_ops
            .add_persistent_value(EXPECTED_NAME.to_str().unwrap(), Err(IoError::NotImplemented));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);
        assert_eq!(avb_ops.erase_persistent_value(EXPECTED_NAME), Ok(()));
    }
}
