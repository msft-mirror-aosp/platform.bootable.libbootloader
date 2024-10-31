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

//! AVB operations.

use crate::GblOps;
use avb::{
    cert_validate_vbmeta_public_key, CertOps, CertPermanentAttributes, IoError, IoResult,
    Ops as AvbOps, PublicKeyForPartitionInfo, SHA256_DIGEST_SIZE,
};
use core::{
    cmp::{max, min},
    ffi::CStr,
};
use liberror::Error;
use safemath::SafeNum;
use uuid::Uuid;

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
}

impl<'a, 'p, T: GblOps<'p>> GblAvbOps<'a, T> {
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
        }
    }

    /// Returns the size of a partition.
    ///
    /// This will only consider the [GblOps] partitions. To include preloaded partitions as well,
    /// use [AvbOps::get_size_of_partition].
    fn partition_size(&mut self, partition: &str) -> IoResult<u64> {
        self.gbl_ops.partition_size(partition).or(Err(IoError::Io))?.ok_or(IoError::NoSuchPartition)
    }
}

/// A helper function for converting `CStr` to `str`
fn cstr_to_str<E>(s: &CStr, err: E) -> Result<&str, E> {
    Ok(s.to_str().or(Err(err))?)
}

/// # Lifetimes
/// * `'a`: preloaded data lifetime
/// * `'b`: [GblOps] partition lifetime
impl<'a, 'b, T: GblOps<'b>> AvbOps<'a> for GblAvbOps<'a, T> {
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
        match self.use_cert {
            true => cert_validate_vbmeta_public_key(self, public_key, public_key_metadata),
            false => {
                // Not needed yet; eventually we will plumb this through [GblOps].
                // For now just trust any vbmeta signature.
                Ok(true)
            }
        }
    }

    fn read_rollback_index(&mut self, rollback_index_location: usize) -> IoResult<u64> {
        self.gbl_ops.avb_read_rollback_index(rollback_index_location)
    }

    fn write_rollback_index(&mut self, rollback_index_location: usize, index: u64) -> IoResult<()> {
        self.gbl_ops.avb_write_rollback_index(rollback_index_location, index)
    }

    fn read_is_device_unlocked(&mut self) -> IoResult<bool> {
        self.gbl_ops.avb_read_is_device_unlocked()
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

    fn read_persistent_value(&mut self, _name: &CStr, _value: &mut [u8]) -> IoResult<usize> {
        // Not needed yet; eventually we will plumb this through [GblOps].
        unimplemented!();
    }

    fn write_persistent_value(&mut self, _name: &CStr, _value: &[u8]) -> IoResult<()> {
        // Not needed yet; eventually we will plumb this through [GblOps].
        unreachable!();
    }

    fn erase_persistent_value(&mut self, _name: &CStr) -> IoResult<()> {
        // Not needed yet; eventually we will plumb this through [GblOps].
        unreachable!();
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
impl<'a, T: GblOps<'a>> CertOps for GblAvbOps<'_, T> {
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

    fn get_random(&mut self, bytes: &mut [u8]) -> IoResult<()> {
        // Not needed yet; eventually we will plumb this through [GblOps].
        unimplemented!()
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
        storage.add_raw_device("test_part", test_data(512));

        let partitions = storage.as_partition_block_devices();
        let mut gbl_ops = FakeGblOps::new(&partitions);
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);

        // Positive offset.
        let mut out = [0u8; 4];
        assert_eq!(avb_ops.read_from_partition(c"test_part", 1, &mut out[..]), Ok(4));
        assert_eq!(out, [1, 2, 3, 4]);
    }

    #[test]
    fn read_from_partition_negative_off() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device("test_part", test_data(512));

        let partitions = storage.as_partition_block_devices();
        let mut gbl_ops = FakeGblOps::new(&partitions);
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);

        // Negative offset should wrap from the end
        let mut out = [0u8; 6];
        assert_eq!(avb_ops.read_from_partition(c"test_part", -6, &mut out[..]), Ok(6));
        assert_eq!(out, [0xFA, 0xFB, 0xFC, 0xFD, 0xFE, 0xFF]);
    }

    #[test]
    fn read_from_partition_partial_read() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device("test_part", test_data(512));

        let partitions = storage.as_partition_block_devices();
        let mut gbl_ops = FakeGblOps::new(&partitions);
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, &[], false);

        // Reading past the end of the partition should truncate.
        let mut out = [0u8; 6];
        assert_eq!(avb_ops.read_from_partition(c"test_part", -3, &mut out[..]), Ok(3));
        assert_eq!(out, [0xFD, 0xFE, 0xFF, 0, 0, 0]);
    }

    #[test]
    fn read_from_partition_out_of_bounds() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device("test_part", test_data(512));

        let partitions = storage.as_partition_block_devices();
        let mut gbl_ops = FakeGblOps::new(&partitions);
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
}
