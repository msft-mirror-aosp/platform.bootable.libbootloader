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
    error::Error as GblError,
    fuchsia_boot::{zircon_part_name, SlotIndex},
    GblAvbOps, GblOps, IntegrationError, Result as GblResult,
};
use avb::{
    cert_validate_vbmeta_public_key, slot_verify, CertOps, CertPermanentAttributes,
    HashtreeErrorMode, IoError as AvbIoError, IoResult as AvbIoResult, Ops as AvbOps,
    PublicKeyForPartitionInfo, SlotVerifyError, SlotVerifyFlags, SHA256_DIGEST_SIZE,
};
use core::{
    cmp::{max, min},
    ffi::CStr,
};
use safemath::SafeNum;
use uuid::Uuid;

// For Fuchsia, maximum number of key version is 2.
const AVB_ATX_NUM_KEY_VERSIONS: usize = 2;

/// `GblZirconBootAvbOps` implements `avb::Ops` for GBL Zircon boot flow.
struct GblZirconBootAvbOps<'a, T: GblOps> {
    gbl_ops: &'a mut T,
    preloaded_partitions: &'a [(&'a str, &'a [u8])],
    // Used for storing key versions to be set. (location, version).
    // If `array_map` is imported in the future, consider switching to it.
    key_versions: [Option<(usize, u64)>; AVB_ATX_NUM_KEY_VERSIONS],
}

impl<'a, T: GblOps> GblZirconBootAvbOps<'a, T> {
    /// Returns the size of a partition.
    fn partition_size(&mut self, partition: &str) -> AvbIoResult<u64> {
        Ok(self
            .gbl_ops
            .partition_size(partition)
            .map_err(|_| AvbIoError::Io)?
            .ok_or(AvbIoError::NoSuchPartition)?)
    }

    /// Gets the `GblAvbOps`. Returns error if not supported.
    fn gbl_avb_ops(&mut self) -> AvbIoResult<impl GblAvbOps + '_> {
        self.gbl_ops.avb_ops().ok_or(AvbIoError::NotImplemented)
    }
}

/// A helper function for converting `CStr` to `str`
fn cstr_to_str<E>(s: &CStr, err: E) -> Result<&str, E> {
    Ok(s.to_str().map_err(|_| err)?)
}

impl<'a, T: GblOps> AvbOps<'a> for GblZirconBootAvbOps<'a, T> {
    fn read_from_partition(
        &mut self,
        partition: &CStr,
        offset: i64,
        buffer: &mut [u8],
    ) -> AvbIoResult<usize> {
        let part_str = cstr_to_str(partition, AvbIoError::NoSuchPartition)?;
        let partition_size = SafeNum::from(self.partition_size(part_str)?);
        let read_off = match offset < 0 {
            true => partition_size - offset.abs(),
            _ => SafeNum::from(offset),
        };
        let read_sz = partition_size - read_off;
        let read_off = read_off.try_into().map_err(|_| AvbIoError::Io)?;
        let read_sz: usize = min(buffer.len(), read_sz.try_into().map_err(|_| AvbIoError::Io)?);
        self.gbl_ops
            .read_from_partition_sync(part_str, read_off, &mut buffer[..read_sz])
            .map_err(|_| AvbIoError::Io)?;
        Ok(read_sz)
    }

    fn get_preloaded_partition(&mut self, partition: &CStr) -> AvbIoResult<&'a [u8]> {
        let part_str = cstr_to_str(partition, AvbIoError::NotImplemented)?;
        Ok(self
            .preloaded_partitions
            .iter()
            .find(|(name, _)| *name == part_str)
            .ok_or(AvbIoError::NotImplemented)?
            .1)
    }

    fn validate_vbmeta_public_key(
        &mut self,
        public_key: &[u8],
        public_key_metadata: Option<&[u8]>,
    ) -> AvbIoResult<bool> {
        cert_validate_vbmeta_public_key(self, public_key, public_key_metadata)
    }

    fn read_rollback_index(&mut self, rollback_index_location: usize) -> AvbIoResult<u64> {
        self.gbl_avb_ops()?.avb_read_rollback_index(rollback_index_location)
    }

    fn write_rollback_index(
        &mut self,
        rollback_index_location: usize,
        index: u64,
    ) -> AvbIoResult<()> {
        self.gbl_avb_ops()?.avb_write_rollback_index(rollback_index_location, index)
    }

    fn read_is_device_unlocked(&mut self) -> AvbIoResult<bool> {
        self.gbl_avb_ops()?.avb_read_is_device_unlocked()
    }

    fn get_unique_guid_for_partition(&mut self, partition: &CStr) -> AvbIoResult<Uuid> {
        // The ops is only used to check that a partition exists. GUID is not used.
        self.partition_size(cstr_to_str(partition, AvbIoError::NoSuchPartition)?)?;
        Ok(Uuid::nil())
    }

    fn get_size_of_partition(&mut self, partition: &CStr) -> AvbIoResult<u64> {
        match self.get_preloaded_partition(partition) {
            Ok(img) => Ok(img.len().try_into().unwrap()),
            _ => {
                let part_str = cstr_to_str(partition, AvbIoError::NoSuchPartition)?;
                self.partition_size(part_str)
            }
        }
    }

    fn read_persistent_value(&mut self, _name: &CStr, _value: &mut [u8]) -> AvbIoResult<usize> {
        // Fuchsia might need this in the future.
        unimplemented!();
    }

    fn write_persistent_value(&mut self, _name: &CStr, _value: &[u8]) -> AvbIoResult<()> {
        // Not needed by Fuchsia.
        unreachable!();
    }

    fn erase_persistent_value(&mut self, _name: &CStr) -> AvbIoResult<()> {
        // Not needed by Fuchsia.
        unreachable!();
    }

    fn validate_public_key_for_partition(
        &mut self,
        _partition: &CStr,
        _public_key: &[u8],
        _public_key_metadata: Option<&[u8]>,
    ) -> AvbIoResult<PublicKeyForPartitionInfo> {
        // Not needed by Fuchsia.
        unreachable!();
    }

    fn cert_ops(&mut self) -> Option<&mut dyn CertOps> {
        Some(self)
    }
}

impl<T: GblOps> CertOps for GblZirconBootAvbOps<'_, T> {
    fn read_permanent_attributes(
        &mut self,
        attributes: &mut CertPermanentAttributes,
    ) -> AvbIoResult<()> {
        self.gbl_avb_ops()?.avb_cert_read_permanent_attributes(attributes)
    }

    fn read_permanent_attributes_hash(&mut self) -> AvbIoResult<[u8; SHA256_DIGEST_SIZE]> {
        self.gbl_avb_ops()?.avb_cert_read_permanent_attributes_hash()
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
                *self.key_versions.iter_mut().find(|v| v.is_none()).unwrap() =
                    Some((rollback_index_location, key_version))
            }
        }
    }

    fn get_random(&mut self, bytes: &mut [u8]) -> AvbIoResult<()> {
        unimplemented!()
    }
}

/// Helper for getting the A/B/R suffix.
fn slot_suffix(slot: Option<SlotIndex>) -> Option<&'static CStr> {
    Some(match slot? {
        SlotIndex::A => c"_a",
        SlotIndex::B => c"_b",
        SlotIndex::R => c"_r",
    })
}

/// Verifies a loaded ZBI kernel.
pub(crate) fn zircon_verify_kernel<G: GblOps>(
    gbl_ops: &mut G,
    slot: Option<SlotIndex>,
    slot_booted_successfully: bool,
    zbi_kernel: &mut [u8],
) -> GblResult<()> {
    // Determines verify flags and error mode.
    let unlocked =
        gbl_ops.avb_ops().ok_or(GblError::NotImplemented)?.avb_read_is_device_unlocked()?;
    let mode = HashtreeErrorMode::AVB_HASHTREE_ERROR_MODE_EIO; // Don't care for fuchsia
    let flag = match unlocked {
        true => SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_ALLOW_VERIFICATION_ERROR,
        _ => SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_NONE,
    };

    // Verifies the kernel.
    let preloaded = [(zircon_part_name(slot), &zbi_kernel[..])];
    let mut avb_ops = GblZirconBootAvbOps {
        gbl_ops,
        preloaded_partitions: &preloaded[..],
        key_versions: [None; AVB_ATX_NUM_KEY_VERSIONS],
    };
    // TODO(b/334962583): Supports optional additional partitions to verify.
    let verify_res = slot_verify(&mut avb_ops, &[c"zircon"], slot_suffix(slot), flag, mode);
    let verified_success = verify_res.is_ok();
    let verify_data = match verify_res {
        Ok(v) => v,
        Err(SlotVerifyError::Verification(Some(v))) if unlocked => v,
        Err(e) => return Err(Into::<IntegrationError>::into(e.without_verify_data())),
    };

    // TODO(b/334962583): Collects ZBI items from vbmetadata and appends to the `zbi_kernel` buffer.

    // Increases rollback indices if the slot has successfully booted.
    if verified_success && slot_booted_successfully {
        for (loc, val) in verify_data.rollback_indexes().iter().enumerate() {
            if *val > 0 && avb_ops.read_rollback_index(loc)? != *val {
                avb_ops.write_rollback_index(loc, *val)?;
            }
        }

        // Increases rollback index values for Fuchsia key version locations.
        for key_version in avb_ops.key_versions {
            match key_version {
                Some((loc, rollback)) if avb_ops.read_rollback_index(loc)? != rollback => {
                    avb_ops.write_rollback_index(loc, rollback)?;
                }
                _ => {}
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{fuchsia_boot::test::*, fuchsia_boot::ZIRCON_KERNEL_ALIGN};
    use avb_bindgen::{AVB_CERT_PIK_VERSION_LOCATION, AVB_CERT_PSK_VERSION_LOCATION};

    // The cert test keys were both generated with rollback version 42.
    pub const TEST_CERT_PIK_VERSION: u64 = 42;
    pub const TEST_CERT_PSK_VERSION: u64 = 42;

    #[test]
    fn test_avb_ops_read_from_partition_positive_off() {
        let gbl_ops = &mut TestZirconBootGblOps::default();
        let zircon_a = gbl_ops.partitions.get(&"zircon_a").unwrap().clone();
        let mut avb_ops =
            GblZirconBootAvbOps { gbl_ops, preloaded_partitions: &[], key_versions: [None, None] };
        let mut out = vec![0u8; 512];
        // Positive offset.
        avb_ops.read_from_partition(c"zircon_a", 1, &mut out[..]).unwrap();
        assert_eq!(out, zircon_a[1..][..out.len()]);
    }

    #[test]
    fn test_avb_ops_read_from_partition_negative_off() {
        let gbl_ops = &mut TestZirconBootGblOps::default();
        let zircon_a = gbl_ops.partitions.get(&"zircon_a").unwrap().clone();
        let mut avb_ops =
            GblZirconBootAvbOps { gbl_ops, preloaded_partitions: &[], key_versions: [None, None] };
        let mut out = vec![0u8; 512];
        // Negative offset.
        avb_ops.read_from_partition(c"zircon_a", -1024, &mut out[..]).unwrap();
        assert_eq!(out, zircon_a[zircon_a.len() - 1024..][..out.len()]);
    }

    #[test]
    fn test_avb_ops_read_from_partition_partial_read() {
        let gbl_ops = &mut TestZirconBootGblOps::default();
        let zircon_a = gbl_ops.partitions.get(&"zircon_a").unwrap().clone();
        let mut avb_ops =
            GblZirconBootAvbOps { gbl_ops, preloaded_partitions: &[], key_versions: [None, None] };
        let mut out = vec![0u8; 512];
        // Partial read.
        avb_ops.read_from_partition(c"zircon_a", -256, &mut out[..]).unwrap();
        assert_eq!(out[..256], zircon_a[zircon_a.len() - 256..]);
    }

    #[test]
    fn test_verify_success() {
        let mut ops = TestZirconBootGblOps::default();
        let expect_rollback = ops.rollback_index.clone();
        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        let mut load_buffer = AlignedBuffer::new(zbi.len(), ZIRCON_KERNEL_ALIGN);
        load_buffer.get()[..zbi.len()].clone_from_slice(zbi);
        zircon_verify_kernel(&mut ops, Some(SlotIndex::A), false, load_buffer.get()).unwrap();

        // Slot is not successful, rollback index should not be updated.
        assert_eq!(expect_rollback, ops.rollback_index);
    }

    #[test]
    fn test_verify_update_rollback_index_for_successful_slot() {
        let mut ops = TestZirconBootGblOps::default();
        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        let mut load_buffer = AlignedBuffer::new(zbi.len(), ZIRCON_KERNEL_ALIGN);
        load_buffer.get()[..zbi.len()].clone_from_slice(zbi);
        zircon_verify_kernel(&mut ops, Some(SlotIndex::A), true, load_buffer.get()).unwrap();

        // Slot is successful, rollback index should be updated.
        // vbmeta_a has rollback index value 2 at location 1.
        assert_eq!(*ops.rollback_index.get(&1).unwrap(), 2);
        assert_eq!(
            *ops.rollback_index
                .get(&usize::try_from(AVB_CERT_PSK_VERSION_LOCATION).unwrap())
                .unwrap(),
            TEST_CERT_PIK_VERSION
        );
        assert_eq!(
            *ops.rollback_index
                .get(&usize::try_from(AVB_CERT_PIK_VERSION_LOCATION).unwrap())
                .unwrap(),
            TEST_CERT_PIK_VERSION
        );
    }

    #[test]
    fn test_verify_failed_on_corrupted_image() {
        let mut ops = TestZirconBootGblOps::default();
        let expect_rollback = ops.rollback_index.clone();
        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        let mut load_buffer = AlignedBuffer::new(zbi.len(), ZIRCON_KERNEL_ALIGN);
        load_buffer.get()[..zbi.len()].clone_from_slice(zbi);
        // Corrupts a random kernel bytes. Skips pass two ZBI headers.
        load_buffer.get()[64] = !load_buffer.get()[64];
        assert!(
            zircon_verify_kernel(&mut ops, Some(SlotIndex::A), true, load_buffer.get()).is_err()
        );
        // Rollback indes should not be updated on verification failure.
        assert_eq!(expect_rollback, ops.rollback_index);
    }

    #[test]
    fn test_verify_failed_on_rollback_protection() {
        let mut ops = TestZirconBootGblOps::default();
        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        let mut load_buffer = AlignedBuffer::new(zbi.len(), ZIRCON_KERNEL_ALIGN);
        load_buffer.get()[..zbi.len()].clone_from_slice(zbi);
        // vbmeta_a has rollback index value 2 at location 1. Setting min rollback value of 3 should
        // cause rollback protection failure.
        ops.rollback_index.insert(1, 3);
        let expect_rollback = ops.rollback_index.clone();
        assert!(
            zircon_verify_kernel(&mut ops, Some(SlotIndex::A), true, load_buffer.get()).is_err()
        );
        // Rollback indes should not be updated on verification failure.
        assert_eq!(expect_rollback, ops.rollback_index);
    }

    #[test]
    fn test_verify_failure_when_unlocked() {
        let mut ops = TestZirconBootGblOps::default();
        ops.avb_unlocked = true;
        let expect_rollback = ops.rollback_index.clone();

        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        let mut load_buffer = AlignedBuffer::new(zbi.len(), ZIRCON_KERNEL_ALIGN);
        load_buffer.get()[..zbi.len()].clone_from_slice(zbi);
        // Corrupts a random kernel bytes. Skips pass two ZBI headers.
        load_buffer.get()[64] = !load_buffer.get()[64];
        // Verification should proceeds OK.
        zircon_verify_kernel(&mut ops, Some(SlotIndex::A), true, load_buffer.get()).unwrap();
        // Rollback index should not be updated in any failure cases, even when unlocked.
        assert_eq!(expect_rollback, ops.rollback_index);
    }
}
