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
    gbl_avb::{
        state::{KeyValidationStatus, VerificationStatus},
        AvbDeviceStatus, AvbPartition, AvbProperty,
    },
    metrics::GblTime,
    partition::split_partition_suffix,
    GblOps,
};
use abr::SlotIndex;
use arrayvec::ArrayString;
use avb::{
    cert_validate_vbmeta_public_key, CertOps, CertPermanentAttributes, Descriptor, IoError,
    IoResult, Ops as AvbOps, PublicKeyForPartitionInfo, SlotVerifyData, SHA256_DIGEST_SIZE,
    SHA512_DIGEST_SIZE,
};
use core::{
    cmp::{max, min},
    ffi::CStr,
    fmt::Write,
    mem::take,
    ops::Range,
};
use liberror::Error;
use safemath::SafeNum;
use uuid::Uuid;

#[cfg(feature = "gbl_dev")]
use crate::gbl_println;
#[cfg(feature = "gbl_dev")]
use core::fmt::Debug;

/// The digest key in AVB commandline.
pub const AVB_DIGEST_KEY: &str = "androidboot.vbmeta.digest";

// AVB cert tracks versions for the PIK and PSK; PRK cannot be changed so has no version info.
const AVB_CERT_NUM_KEY_VERSIONS: usize = 2;

/// Represents the state of preloaded buffer
pub enum PreloadBufferState<'a> {
    /// Loaded already
    Loaded(&'a [u8]),
    /// To be loaded.
    ToLoad(&'a mut [u8]),
}

/// Implements avb ops callbacks for [GblOps].
pub struct GblAvbOps<'a: 'c, 'b, 'c, T> {
    /// The underlying [GblOps].
    /// TODO(b/578053084): Make private to ensure GblAvbOps methods are used
    /// instead of accessing the underlying `gbl_ops` directly.
    pub gbl_ops: &'b mut T,
    slot: Option<SlotIndex>,
    /// Slotless partitions pre-loaded by the implementation. Provided to avoid redundant IO.
    preloaded_partitions: &'c mut [(&'a str, PreloadBufferState<'a>)],
    /// Used for storing key versions to be set (location, version).
    ///
    /// These will initially be `None`, but if using the cert extensions they will be updated during
    /// verification. These values will not be automatically persisted to disk because whether to do
    /// so depends on other factors such as slot success state; it's up to the user to persist them
    /// post-verification if needed.
    // If `array_map` is imported in the future, consider switching to it.
    key_versions: [Option<(usize, u64)>; AVB_CERT_NUM_KEY_VERSIONS],
    /// True to use the AVB cert extensions.
    use_cert: bool,
    /// Avb public key validation status reported by validate_vbmeta_public_key.
    /// https://source.android.com/docs/security/features/verifiedboot/boot-flow#locked-devices-with-custom-root-of-trust
    key_validation_status: Option<KeyValidationStatus>,
}

impl<'a, 'b, 'c, 'p, T: GblOps<'p>> GblAvbOps<'a, 'b, 'c, T> {
    /// Creates a new [GblAvbOps].
    pub fn new(
        gbl_ops: &'b mut T,
        slot: Option<SlotIndex>,
        preloaded_partitions: &'c mut [(&'a str, PreloadBufferState<'a>)],
        use_cert: bool,
    ) -> Self {
        Self {
            gbl_ops,
            slot,
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
        status: VerificationStatus,
        digest: Option<&str>,
    ) -> IoResult<()> {
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

        // Extracts all provided properties.
        let properties = slot_verify.map(|slot_verify| {
            slot_verify.vbmeta_data().iter().flat_map(|data| {
                let partition = data.partition_name();

                data.descriptors().unwrap().into_iter().filter_map(|descriptor| match descriptor {
                    Descriptor::Property(descriptor) => Some(AvbProperty {
                        partition,
                        key: descriptor.key_cstr,
                        value_with_nul: descriptor.value_with_nul,
                    }),
                    _ => None,
                })
            })
        });
        // Extracts all provided partitions.
        let partitions = slot_verify.map(|slot_verify| {
            slot_verify
                .partition_data()
                .into_iter()
                .map(|p| AvbPartition { name: p.partition_name(), data: p.data() })
        });

        self.gbl_ops.avb_handle_verification_result(status, digest_cstr, properties, partitions)
    }

    /// Helper for updating rollback indexes after verification is done.
    pub fn update_rollback_indexes(&mut self, data: &SlotVerifyData<'_>) -> IoResult<()> {
        // Rollback indexes provided by libavb
        let slot_indexes = data
            .rollback_indexes()
            .iter()
            .enumerate()
            .filter_map(|(location, &idx)| (idx > 0).then_some((location, idx)));

        // Saved key version rollback indexes
        let key_version_indexes = self.key_versions.clone().into_iter().filter_map(|opt| opt);

        slot_indexes.chain(key_version_indexes).try_for_each(|(loc, idx)| {
            let stored = self.read_rollback_index(loc)?;
            if idx > stored {
                self.write_rollback_index(loc, idx)?;
            }
            Ok(())
        })
    }

    /// Get vbmeta public key validation status reported by validate_vbmeta_public_key.
    pub fn key_validation_status(&self) -> IoResult<KeyValidationStatus> {
        self.key_validation_status.ok_or(IoError::NotImplemented)
    }

    /// Helper for getting AVB device status
    pub fn avb_read_device_status(&mut self) -> IoResult<AvbDeviceStatus> {
        let result = self.gbl_ops.avb_read_device_status();

        // On dev boards default to unlocked and no dm_verity_error, which allows boot to succeed.
        #[cfg(feature = "gbl_dev")]
        let result = self.with_dev_fallback(
            result,
            Ok(AvbDeviceStatus {
                is_unlocked: true,
                is_unlocked_critical: true,
                is_dm_verity_error: false,
                is_unlockable: true,
            }),
            "read device status",
        );

        result
    }

    /// For dev builds only, transforms unimplemented ops into default behavior.
    ///
    /// # Args
    /// * `result`: the result provided by the real [GblOps].
    /// * `fallback`: the result to fall back to if the op is unimplemented.
    /// * `log_name`: if the fallback value is used, some logs will be printed
    ///               containing this name and the fallback value.
    ///
    /// # Returns
    /// If `result` is `Err(IoError::NotImplemented)`, returns `fallback`.
    /// Otherwise returns `result` unchanged.
    #[cfg(feature = "gbl_dev")]
    fn with_dev_fallback<R: Debug>(
        &mut self,
        result: IoResult<R>,
        fallback: IoResult<R>,
        log_name: &str,
    ) -> IoResult<R> {
        match result {
            Err(IoError::NotImplemented) => {
                gbl_println!(
                    self.gbl_ops,
                    "AVB {} unimplemented, defaulting to {:?}",
                    log_name,
                    fallback
                );
                fallback
            }
            _ => result,
        }
    }

    /// For dev builds only, returns true if both cert ops return
    /// [IoError::NotImplemented].
    #[cfg(feature = "gbl_dev")]
    fn cert_ops_not_implemented(&mut self) -> bool {
        let mut attributes = CertPermanentAttributes {
            version: 0,
            product_root_public_key: [0u8; 1032],
            product_id: [0u8; 16],
        };
        self.read_permanent_attributes(&mut attributes) == Err(IoError::NotImplemented)
            && self.read_permanent_attributes_hash() == Err(IoError::NotImplemented)
    }

    /// Helper for getting the index of the buffer in `Self::preloaded_partitions` for the given
    /// partition.
    // We don't return the item reference because that would borrow the entire `self`.
    fn get_preloaded_pos(&self, partition: &CStr) -> IoResult<usize> {
        let part_str = cstr_to_str(partition, IoError::NotImplemented)?;

        let partition_name = match self.slot {
            // Extract partition slot and ensure it's matched.
            Some(slot) => {
                let (partition_name, partition_slot) =
                    split_slotted(part_str).map_err(|_| IoError::NotImplemented)?;

                if partition_slot != slot {
                    return Err(IoError::NotImplemented);
                }

                partition_name
            }
            _ => part_str,
        };

        self.preloaded_partitions
            .iter()
            .position(|(name, _)| *name == partition_name)
            .ok_or_else(|| IoError::NotImplemented)
    }
}

/// A helper function for converting `CStr` to `str`
fn cstr_to_str<E>(s: &CStr, err: E) -> Result<&str, E> {
    Ok(s.to_str().or(Err(err))?)
}

/// A helper function to split partition into base name and slot index
fn split_slotted(partition: &str) -> Result<(&str, SlotIndex), Error> {
    let (partition_name, slot_char) =
        split_partition_suffix(partition).ok_or(Error::InvalidInput)?;

    // Convert that single character into a SlotIndex
    let slot = slot_char.try_into().map_err(|_| Error::InvalidInput)?;

    Ok((partition_name, slot))
}

/// Helper for mapping disk read error to IoError.
fn map_read_err(err: Error) -> IoError {
    match err {
        Error::NotFound => IoError::NoSuchPartition,
        Error::ArithmeticOverflow(_) => IoError::RangeOutsidePartition,
        _ => IoError::Io,
    }
}

/// Helper to calculate partition read range based on requested `read_offset` (including negatives)
/// and provided `max_read_size` limitation.
fn calculate_partition_read_range(
    partition_size: SafeNum,
    read_offset: i64,
    max_read_size: usize,
) -> IoResult<Range<usize>> {
    let read_offset = match read_offset < 0 {
        true => partition_size - read_offset.abs(),
        _ => SafeNum::from(read_offset),
    }
    .try_into()
    .or(Err(IoError::RangeOutsidePartition))?;

    let read_size = min(
        max_read_size,
        (partition_size - read_offset).try_into().or(Err(IoError::RangeOutsidePartition))?,
    );

    Ok(read_offset..read_offset + read_size)
}

/// # Lifetimes
/// * `'a`: preloaded data lifetime
/// * `'b`: [GblOps] partition lifetime
impl<'a, 'b, 'c, 'p, T: GblOps<'p>> AvbOps<'a> for GblAvbOps<'a, 'b, 'c, T> {
    fn read_from_partition(
        &mut self,
        partition: &CStr,
        offset: i64,
        buffer: &mut [u8],
    ) -> IoResult<usize> {
        let part_str = cstr_to_str(partition, IoError::NoSuchPartition)?;
        let partition_size = self.partition_size(part_str)?;
        let read_range =
            calculate_partition_read_range(partition_size.into(), offset, buffer.len())?;
        let read_size = read_range.len();

        let start = self.gbl_ops.get_time().and_then(|t| t.current_tick().ok());
        let result = self
            .gbl_ops
            .read_from_partition_sync(
                part_str,
                read_range.start.try_into().unwrap(),
                &mut buffer[..read_size],
            )
            .map_err(map_read_err);
        if let Some(start) = start
            && let Some(delta) = self.gbl_ops.get_time().and_then(|t| t.elapsed_ticks(start).ok())
            && let Some(mut metrics) = self.gbl_ops.get_metrics()
        {
            metrics.add_io_timing_ticks(part_str, delta);
        }

        result?;
        Ok(read_size)
    }

    fn get_preloaded_partition(
        &mut self,
        partition: &CStr,
        num_bytes: usize,
    ) -> IoResult<&'a [u8]> {
        let res = &mut self.preloaded_partitions[self.get_preloaded_pos(partition)?].1;
        match res {
            PreloadBufferState::Loaded(v) => {
                v.get(..num_bytes).ok_or(IoError::RangeOutsidePartition)
            }
            PreloadBufferState::ToLoad(v) => {
                let out = v.get_mut(..num_bytes).ok_or(IoError::RangeOutsidePartition)?;
                let part_str = cstr_to_str(partition, IoError::NoSuchPartition)?;
                let start = self.gbl_ops.get_time().and_then(|t| t.current_tick().ok());
                let result =
                    self.gbl_ops.read_from_partition_sync(part_str, 0, out).map_err(map_read_err);
                if let Some(start) = start
                    && let Some(delta) =
                        self.gbl_ops.get_time().and_then(|t| t.elapsed_ticks(start).ok())
                    && let Some(mut metrics) = self.gbl_ops.get_metrics()
                {
                    metrics.add_io_timing_ticks(part_str, delta);
                }

                result?;
                // Note: we only take from v after everything is successful. If we take first and
                // then there is error and we return early, the buffer is lost.
                let buf = &mut take(v)[..num_bytes];
                *res = PreloadBufferState::Loaded(buf);
                Ok(buf)
            }
        }
    }

    fn validate_vbmeta_public_key(
        &mut self,
        public_key: &[u8],
        public_key_metadata: Option<&[u8]>,
    ) -> IoResult<bool> {
        let result = if self.use_cert {
            let result = cert_validate_vbmeta_public_key(self, public_key, public_key_metadata)
                .map(|ret| match ret {
                    true => KeyValidationStatus::Valid,
                    false => KeyValidationStatus::Invalid,
                });

            // `cert_validate_vbmeta_public_key` is a little trickier to
            // identify the not-implemented case, because
            // [IoError::NotImplemented] is only returned directly from ops
            // callbacks; top-level libavb APIs like this will end up converting
            // it to [IoError::Io] instead.
            //
            // To work around this, we make an additional call to each cert op
            // callback to check whether it's implemented or not.
            #[cfg(feature = "gbl_dev")]
            let result = match result {
                Err(IoError::Io) if self.cert_ops_not_implemented() => Err(IoError::NotImplemented),
                _ => result,
            };

            result
        } else {
            self.gbl_ops.avb_validate_vbmeta_public_key(public_key, public_key_metadata)
        };

        // On dev boards fall back to `Invalid`, which indicates that the
        // boot image was not signed but will still allow booting on
        // unlocked boards.
        #[cfg(feature = "gbl_dev")]
        let result =
            self.with_dev_fallback(result, Ok(KeyValidationStatus::Invalid), "validate vbmeta key");

        let status = result?;
        self.key_validation_status = Some(status);
        Ok(matches!(status, KeyValidationStatus::Valid | KeyValidationStatus::ValidCustomKey))
    }

    fn read_rollback_index(&mut self, rollback_index_location: usize) -> IoResult<u64> {
        let result = self.gbl_ops.avb_read_rollback_index(rollback_index_location);

        // On dev boards always read 0, which allows any version to boot.
        #[cfg(feature = "gbl_dev")]
        let result = self.with_dev_fallback(result, Ok(0), "read rollback index");

        result
    }

    fn write_rollback_index(&mut self, rollback_index_location: usize, index: u64) -> IoResult<()> {
        let result = self.gbl_ops.avb_write_rollback_index(rollback_index_location, index);

        // On dev boards writing rollback is a no-op, always return success.
        #[cfg(feature = "gbl_dev")]
        let result = self.with_dev_fallback(result, Ok(()), "write rollback index");

        result
    }

    fn read_is_device_unlocked(&mut self) -> IoResult<bool> {
        self.avb_read_device_status().map(|s| s.is_unlocked)
    }

    fn get_unique_guid_for_partition(&mut self, partition: &CStr) -> IoResult<Uuid> {
        // The ops is only used to check that a partition exists. GUID is not used.
        self.partition_size(cstr_to_str(partition, IoError::NoSuchPartition)?)?;
        Ok(Uuid::nil())
    }

    fn get_size_of_partition(&mut self, partition: &CStr) -> IoResult<u64> {
        match self.get_preloaded_pos(partition).map(|v| &mut self.preloaded_partitions[v].1) {
            Ok(PreloadBufferState::ToLoad(v)) => Ok(v.len().try_into().unwrap()),
            Ok(PreloadBufferState::Loaded(v)) => Ok(v.len().try_into().unwrap()),
            _ => self.partition_size(cstr_to_str(partition, IoError::NoSuchPartition)?),
        }
    }

    fn read_persistent_value(&mut self, name: &CStr, value: &mut [u8]) -> IoResult<usize> {
        let result = self.gbl_ops.avb_read_persistent_value(name, value);

        // On dev boards default to no persistent values. libavb will handle
        // this as a verification error and still allow booting when unlocked.
        #[cfg(feature = "gbl_dev")]
        let result =
            self.with_dev_fallback(result, Err(IoError::NoSuchValue), "read persistent value");

        result
    }

    fn write_persistent_value(&mut self, name: &CStr, value: &[u8]) -> IoResult<()> {
        let result = self.gbl_ops.avb_write_persistent_value(name, value);

        // On dev boards default to no persistent values. libavb will handle
        // this as a verification error and still allow booting when unlocked.
        #[cfg(feature = "gbl_dev")]
        let result =
            self.with_dev_fallback(result, Err(IoError::NoSuchValue), "write persistent value");

        result
    }

    fn erase_persistent_value(&mut self, name: &CStr) -> IoResult<()> {
        let result = self.gbl_ops.avb_erase_persistent_value(name);

        // On dev boards default to no persistent values. libavb will handle
        // this as a verification error and still allow booting when unlocked.
        #[cfg(feature = "gbl_dev")]
        let result =
            self.with_dev_fallback(result, Err(IoError::NoSuchValue), "erase persistent value");

        result
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
impl<'a, T: GblOps<'a>> CertOps for GblAvbOps<'_, '_, '_, T> {
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

/// Custom vbmeta flow support.
#[cfg(feature = "gbl_dev")]
pub(crate) mod custom_vbmeta {
    use super::*;

    /// To be used as `AvbOps` wrapper to allow running verification on top of custom
    /// RAM-provided `vbmeta` partition.
    pub struct CustomVbmetaAvbOps<'a, T> {
        /// Original AVB ops.
        pub ops: &'a mut T,
        /// Custom vbmeta data to boot with.
        pub vbmeta: &'a [u8],
        /// Override rollback indexes for custom vbmeta.
        pub rollback_indexes: &'a [(usize, u64)],
    }

    const VBMETA: &'static str = "vbmeta";

    /// Inherits everything from `AvbOps` but override a few to support run verification
    /// on top of custom RAM-provided `vbmeta` partition.
    impl<'a, T: AvbOps<'a>> AvbOps<'a> for CustomVbmetaAvbOps<'_, T> {
        fn get_unique_guid_for_partition(&mut self, partition: &CStr) -> IoResult<Uuid> {
            let (partition_name, _) =
                split_slotted(partition.to_str().unwrap()).map_err(|_| IoError::Io)?;

            match partition_name == VBMETA {
                true => Ok(Uuid::nil()),
                false => self.ops.get_unique_guid_for_partition(partition),
            }
        }

        fn get_size_of_partition(&mut self, partition: &CStr) -> IoResult<u64> {
            let (partition_name, _) =
                split_slotted(partition.to_str().unwrap()).map_err(|_| IoError::Io)?;

            match partition_name == VBMETA {
                true => Ok(self.vbmeta.len().try_into().unwrap()),
                false => self.ops.get_size_of_partition(partition),
            }
        }

        fn read_from_partition(
            &mut self,
            partition: &CStr,
            offset: i64,
            buffer: &mut [u8],
        ) -> IoResult<usize> {
            let (partition_name, _) =
                split_slotted(partition.to_str().unwrap()).map_err(|_| IoError::Io)?;

            match partition_name == VBMETA {
                true => {
                    let read_range = calculate_partition_read_range(
                        self.vbmeta.len().into(),
                        offset,
                        buffer.len(),
                    )?;
                    let read_size = read_range.len();

                    let vbmeta =
                        self.vbmeta.get(read_range).ok_or(IoError::RangeOutsidePartition)?;
                    buffer
                        .get_mut(..read_size)
                        .ok_or(IoError::RangeOutsidePartition)?
                        .copy_from_slice(vbmeta);

                    Ok(read_size)
                }
                false => self.ops.read_from_partition(partition, offset, buffer),
            }
        }

        fn read_rollback_index(&mut self, rollback_index_location: usize) -> IoResult<u64> {
            match self.rollback_indexes.iter().find(|(v, _)| *v == rollback_index_location) {
                Some((_, v)) => Ok(*v),
                _ => Err(IoError::NoSuchValue),
            }
        }

        fn validate_vbmeta_public_key(
            &mut self,
            _public_key: &[u8],
            _public_key_metadata: Option<&[u8]>,
        ) -> IoResult<bool> {
            // Always treats public key as invalid during custom vbmeta flow.
            Ok(false)
        }

        fn get_preloaded_partition(
            &mut self,
            partition: &CStr,
            num_bytes: usize,
        ) -> IoResult<&'a [u8]> {
            self.ops.get_preloaded_partition(partition, num_bytes)
        }

        fn cert_ops(&mut self) -> Option<&mut dyn CertOps> {
            None
        }

        // Unexpected to be called during custom vbmeta flow.

        fn write_rollback_index(
            &mut self,
            _rollback_index_location: usize,
            _index: u64,
        ) -> IoResult<()> {
            unreachable!();
        }

        fn read_is_device_unlocked(&mut self) -> IoResult<bool> {
            unreachable!();
        }

        fn read_persistent_value(&mut self, _name: &CStr, _value: &mut [u8]) -> IoResult<usize> {
            unreachable!();
        }

        fn write_persistent_value(&mut self, _name: &CStr, _value: &[u8]) -> IoResult<()> {
            unreachable!();
        }

        fn erase_persistent_value(&mut self, _name: &CStr) -> IoResult<()> {
            unreachable!();
        }

        fn validate_public_key_for_partition(
            &mut self,
            _partition: &CStr,
            _public_key: &[u8],
            _public_key_metadata: Option<&[u8]>,
        ) -> IoResult<PublicKeyForPartitionInfo> {
            unreachable!();
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        ops::test::{FakeGblOps, FakeGblOpsStorage},
        tests::{
            read_test_data, TEST_PERMANENT_ATTRIBUTES_HASH_PATH, TEST_PERMANENT_ATTRIBUTES_PATH,
        },
    };
    use avb::{CERT_PIK_VERSION_LOCATION, CERT_PSK_VERSION_LOCATION};
    use zerocopy::FromBytes;

    const TEST_CERT_PUBLIC_KEY_PATH: &str = "testkey_cert_psk.bin";
    const TEST_CERT_METADATA_PATH: &str = "cert_metadata.bin";

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
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);

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
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);

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
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);

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
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);

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
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);

        let mut out = [0u8; 4];
        assert_eq!(
            avb_ops.read_from_partition(c"unknown_part", 0, &mut out[..]),
            Err(IoError::NoSuchPartition)
        );
    }

    /// Helper function to test reading pre-loaded partitions.
    fn test_read_preloaded_partition(
        preloaded_partition: &str,
        slot: Option<SlotIndex>,
        partition_to_read: &CStr,
        expect_success: bool,
    ) {
        let mut gbl_ops = FakeGblOps::new(&[]);

        let data = &test_data(512);
        let slice = &data[..];
        let mut preloaded = [(preloaded_partition, PreloadBufferState::Loaded(slice))];
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, slot, &mut preloaded, false);

        match expect_success {
            true => {
                assert_eq!(
                    avb_ops.get_size_of_partition(partition_to_read),
                    Ok(data.len().try_into().unwrap())
                );
                assert_eq!(
                    avb_ops.get_preloaded_partition(partition_to_read, data.len()),
                    Ok(slice)
                );
            }
            false => {
                assert_eq!(
                    avb_ops.get_preloaded_partition(partition_to_read, data.len()),
                    Err(IoError::NotImplemented),
                );
            }
        }
    }

    #[test]
    fn read_from_preloaded_a_partition() {
        test_read_preloaded_partition(
            "test_partition",
            Some(SlotIndex::A),
            c"test_partition_a",
            true,
        );
    }

    #[test]
    fn read_from_preloaded_b_partition() {
        test_read_preloaded_partition(
            "test_partition",
            Some(SlotIndex::B),
            c"test_partition_b",
            true,
        );
    }

    #[test]
    fn read_from_preloaded_r_partition() {
        test_read_preloaded_partition(
            "test_partition",
            Some(SlotIndex::R),
            c"test_partition_r",
            true,
        );
    }

    #[test]
    fn read_from_preloaded_slotless_partition() {
        test_read_preloaded_partition("test_partition", None, c"test_partition", true);
    }

    #[test]
    fn read_from_preloaded_partition_wrong_slot() {
        // Ops are slotless but _a is used, so cannot read.
        test_read_preloaded_partition("test_partition", None, c"test_partition_a", false);

        // Ops are using A slot but slotless is getting read, so cannot read.
        test_read_preloaded_partition(
            "test_partition",
            Some(SlotIndex::A),
            c"test_partition",
            false,
        );

        // Ops are using A slot but _b is getting read, so cannot read.
        test_read_preloaded_partition(
            "test_partition",
            Some(SlotIndex::A),
            c"test_partition_b",
            false,
        );
    }

    #[test]
    fn test_lazy_preloaded_partition() {
        let part = c"test_part";
        let data = test_data(512);
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(part, &data[..]);

        let mut out = vec![0u8; data.len()];
        let mut preloaded = [(part.to_str().unwrap(), PreloadBufferState::ToLoad(&mut out[..]))];

        let mut gbl_ops = FakeGblOps::new(&storage);
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut preloaded[..], false);

        assert_eq!(avb_ops.get_size_of_partition(part), Ok(data.len().try_into().unwrap()));
        assert_eq!(avb_ops.get_preloaded_partition(part, data.len()).unwrap(), data);
        assert_eq!(out, data);
    }

    #[test]
    fn set_key_version_default() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        let avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);

        assert_eq!(avb_ops.key_versions, [None, None]);
    }

    #[test]
    fn set_key_version_once() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);

        avb_ops.set_key_version(5, 10);
        assert_eq!(avb_ops.key_versions, [Some((5, 10)), None]);
    }

    #[test]
    fn set_key_version_twice() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);

        avb_ops.set_key_version(5, 10);
        avb_ops.set_key_version(20, 40);
        assert_eq!(avb_ops.key_versions, [Some((5, 10)), Some((20, 40))]);
    }

    #[test]
    fn set_key_version_overwrite() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);

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
        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);

        avb_ops.set_key_version(5, 10);
        avb_ops.set_key_version(20, 40);
        avb_ops.set_key_version(40, 100);
    }

    /// Returns `value` in a dev build, [IoError::NotImplemented] in a prod build.
    fn dev_only<T>(value: IoResult<T>) -> IoResult<T> {
        match cfg!(feature = "gbl_dev") {
            true => value,
            false => Err(IoError::NotImplemented),
        }
    }

    #[test]
    fn validate_vbmeta_public_key_valid() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_key_validation_status = Some(Ok(KeyValidationStatus::Valid));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
        assert_eq!(avb_ops.validate_vbmeta_public_key(&[], None), Ok(true));
        assert_eq!(avb_ops.key_validation_status(), Ok(KeyValidationStatus::Valid));
    }

    #[test]
    fn validate_vbmeta_public_key_valid_custom_key() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_key_validation_status = Some(Ok(KeyValidationStatus::ValidCustomKey));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
        assert_eq!(avb_ops.validate_vbmeta_public_key(&[], None), Ok(true));
        assert_eq!(avb_ops.key_validation_status(), Ok(KeyValidationStatus::ValidCustomKey));
    }

    #[test]
    fn validate_vbmeta_public_key_invalid() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_key_validation_status = Some(Ok(KeyValidationStatus::Invalid));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
        assert_eq!(avb_ops.validate_vbmeta_public_key(&[], None), Ok(false));
        assert_eq!(avb_ops.key_validation_status(), Ok(KeyValidationStatus::Invalid));
    }

    #[test]
    fn validate_vbmeta_public_key_failed() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_key_validation_status = Some(Err(IoError::Io));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
        assert_eq!(avb_ops.validate_vbmeta_public_key(&[], None), Err(IoError::Io));
        assert!(avb_ops.key_validation_status().is_err());
    }

    #[test]
    fn validate_vbmeta_public_key_not_implemented() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_key_validation_status = Some(Err(IoError::NotImplemented));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);

        // Dev should succeed but report invalid key, prod should fail.
        assert_eq!(avb_ops.validate_vbmeta_public_key(&[], None), dev_only(Ok(false)));
        assert_eq!(avb_ops.key_validation_status(), dev_only(Ok(KeyValidationStatus::Invalid)));
    }

    /// Creates a [FakeGblOps] with all the necessary configuration to
    /// successfully validate the vbmeta key using the libavb cert extension.
    ///
    /// # Returns
    /// A tuple containing:
    /// * the [FakeGblOps]
    /// * the corresponding vbmeta public key
    /// * the corresponding vbmeta public key metadata
    fn create_fake_gbl_ops_with_cert() -> (FakeGblOps<'static>, Vec<u8>, Vec<u8>) {
        let mut gbl_ops = FakeGblOps::new(&[]);

        // Cert verification requires both permanent attribute ops plus reading
        // rollback indices for the signing keys.
        gbl_ops.avb_ops.cert_permanent_attributes = Some(
            CertPermanentAttributes::read_from(&read_test_data(TEST_PERMANENT_ATTRIBUTES_PATH))
                .unwrap(),
        );
        gbl_ops.avb_ops.cert_permanent_attributes_hash =
            Some(read_test_data(TEST_PERMANENT_ATTRIBUTES_HASH_PATH).try_into().unwrap());
        gbl_ops.avb_ops.rollbacks.insert(CERT_PIK_VERSION_LOCATION, Ok(0));
        gbl_ops.avb_ops.rollbacks.insert(CERT_PSK_VERSION_LOCATION, Ok(0));

        (
            gbl_ops,
            read_test_data(TEST_CERT_PUBLIC_KEY_PATH),
            read_test_data(TEST_CERT_METADATA_PATH),
        )
    }

    #[test]
    fn cert_validate_vbmeta_public_key_valid() {
        let (mut gbl_ops, public_key, metadata) = create_fake_gbl_ops_with_cert();

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], true);
        assert_eq!(avb_ops.validate_vbmeta_public_key(&public_key, Some(&metadata)), Ok(true));
        assert_eq!(avb_ops.key_validation_status(), Ok(KeyValidationStatus::Valid));
    }

    #[test]
    fn cert_validate_vbmeta_public_key_invalid() {
        let (mut gbl_ops, mut public_key, metadata) = create_fake_gbl_ops_with_cert();

        // Modify the public key so it no longer matches the perm attributes.
        public_key[0] ^= 0x01;

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], true);
        assert_eq!(avb_ops.validate_vbmeta_public_key(&public_key, Some(&metadata)), Ok(false));
        assert_eq!(avb_ops.key_validation_status(), Ok(KeyValidationStatus::Invalid));
    }

    #[test]
    fn cert_validate_vbmeta_public_key_failed() {
        let (mut gbl_ops, public_key, metadata) = create_fake_gbl_ops_with_cert();

        // Setting the fake perm attributes to `None` causes [IoError::Io].
        gbl_ops.avb_ops.cert_permanent_attributes = None;

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], true);
        assert_eq!(
            avb_ops.validate_vbmeta_public_key(&public_key, Some(&metadata)),
            Err(IoError::Io)
        );
        assert!(avb_ops.key_validation_status().is_err());
    }

    #[test]
    fn cert_validate_vbmeta_public_key_not_implemented() {
        // Start with regular [FakeGblOps] without cert backends so we can
        // make sure everything reports [IoError::NotImplemented].
        let mut gbl_ops = FakeGblOps::new(&[]);

        // Cert verification requires both permanent attribute ops plus reading
        // rollback indices for the signing keys.
        gbl_ops.avb_cert_read_permanent_attributes_not_implemented = true;
        gbl_ops.avb_cert_read_permanent_attributes_hash_not_implemented = true;
        gbl_ops.avb_ops.rollbacks.insert(CERT_PIK_VERSION_LOCATION, Err(IoError::NotImplemented));
        gbl_ops.avb_ops.rollbacks.insert(CERT_PSK_VERSION_LOCATION, Err(IoError::NotImplemented));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], true);
        // Dev should succeed but report invalid key, prod should fail.
        //
        // Because of the extra complications detecting the not-implemented case
        // for cert verification, in prod builds this ends up failing with
        // [IoError::Io] rather than [IoError::NotImplemented] like the other
        // ops do. This could cause some minor confusion for developers, but it
        // doesn't seem worth adding the workaround logic to prod builds.
        assert_eq!(
            avb_ops.validate_vbmeta_public_key(&[], None),
            match cfg!(feature = "gbl_dev") {
                true => Ok(false),
                false => Err(IoError::Io),
            }
        );
        assert_eq!(avb_ops.key_validation_status(), dev_only(Ok(KeyValidationStatus::Invalid)));
    }

    #[test]
    fn read_rollback_index_read_value() {
        const EXPECTED_INDEX: usize = 1;
        const EXPECTED_VALUE: u64 = 100;

        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_ops.rollbacks.insert(EXPECTED_INDEX, Ok(EXPECTED_VALUE));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
        assert_eq!(avb_ops.read_rollback_index(EXPECTED_INDEX), Ok(EXPECTED_VALUE));
    }

    #[test]
    fn read_rollback_index_error_handled() {
        let mut gbl_ops = FakeGblOps::new(&[]);

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
        assert_eq!(avb_ops.read_rollback_index(0), Err(IoError::Io));
    }

    #[test]
    fn read_rollback_index_not_implemented() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_ops.rollbacks.insert(0, Err(IoError::NotImplemented));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);

        // Dev should always return 0, prod should fail.
        assert_eq!(avb_ops.read_rollback_index(0), dev_only(Ok(0)));
    }

    #[test]
    fn write_rollback_index_write_value() {
        const EXPECTED_INDEX: usize = 1;
        const EXPECTED_VALUE: u64 = 100;

        let mut gbl_ops = FakeGblOps::new(&[]);

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
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

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
        assert_eq!(avb_ops.write_rollback_index(0, 0), Err(IoError::Io));
    }

    #[test]
    fn write_rollback_index_not_implemented() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_ops.rollbacks.insert(0, Err(IoError::NotImplemented));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
        // Dev should always succeed, prod should fail.
        assert_eq!(avb_ops.write_rollback_index(0, 0), dev_only(Ok(())));
    }

    #[test]
    fn read_is_device_unlocked_value_obtained() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_device_status.is_unlocked = true;

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);

        assert_eq!(avb_ops.read_is_device_unlocked(), Ok(true));
    }

    #[test]
    fn read_is_device_unlocked_error_handled() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_device_status.set_err(IoError::Io);

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
        assert_eq!(avb_ops.read_is_device_unlocked(), Err(IoError::Io));
    }

    #[test]
    fn read_is_device_unlocked_not_implemented() {
        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_device_status.set_err(IoError::NotImplemented);

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
        // Dev should report unlocked, prod should fail.
        assert_eq!(avb_ops.read_is_device_unlocked(), dev_only(Ok(true)));
    }

    #[test]
    fn read_persistent_value_success() {
        const EXPECTED_NAME: &CStr = c"test";
        const EXPECTED_VALUE: &[u8] = b"test";

        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_ops.add_persistent_value(EXPECTED_NAME.to_str().unwrap(), Ok(EXPECTED_VALUE));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
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

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
        let mut buffer = [0u8; 4];
        assert_eq!(avb_ops.read_persistent_value(EXPECTED_NAME, &mut buffer), Err(IoError::Io));
    }

    #[test]
    fn read_persistent_value_not_implemented() {
        const EXPECTED_NAME: &CStr = c"test";

        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops
            .avb_ops
            .add_persistent_value(EXPECTED_NAME.to_str().unwrap(), Err(IoError::NotImplemented));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
        let mut buffer = [0u8; 0];
        // Dev should report no such value, prod should fail.
        assert_eq!(
            avb_ops.read_persistent_value(EXPECTED_NAME, &mut buffer),
            dev_only(Err(IoError::NoSuchValue))
        );
    }

    #[test]
    fn write_persistent_value_success() {
        const EXPECTED_NAME: &CStr = c"test";
        const EXPECTED_VALUE: &[u8] = b"test";

        let mut gbl_ops = FakeGblOps::new(&[]);

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
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

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
        assert_eq!(avb_ops.write_persistent_value(EXPECTED_NAME, EXPECTED_VALUE), Err(IoError::Io));
    }

    #[test]
    fn write_persistent_value_not_implemented() {
        const EXPECTED_NAME: &CStr = c"test";
        const EXPECTED_VALUE: &[u8] = b"test";

        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops
            .avb_ops
            .add_persistent_value(EXPECTED_NAME.to_str().unwrap(), Err(IoError::NotImplemented));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
        // Dev should report no such value, prod should fail.
        assert_eq!(
            avb_ops.write_persistent_value(EXPECTED_NAME, EXPECTED_VALUE),
            dev_only(Err(IoError::NoSuchValue))
        );
    }

    #[test]
    fn erase_persistent_value_success() {
        const EXPECTED_NAME: &CStr = c"test";

        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_ops.add_persistent_value(EXPECTED_NAME.to_str().unwrap(), Ok(b"test"));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
        assert_eq!(avb_ops.erase_persistent_value(EXPECTED_NAME), Ok(()));

        assert!(!gbl_ops.avb_ops.persistent_values.contains_key(EXPECTED_NAME.to_str().unwrap()));
    }

    #[test]
    fn erase_persistent_value_error() {
        const EXPECTED_NAME: &CStr = c"test";

        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops.avb_ops.add_persistent_value(EXPECTED_NAME.to_str().unwrap(), Err(IoError::Io));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
        assert_eq!(avb_ops.erase_persistent_value(EXPECTED_NAME), Err(IoError::Io));
    }

    #[test]
    fn erase_persistent_value_not_implemented() {
        const EXPECTED_NAME: &CStr = c"test";

        let mut gbl_ops = FakeGblOps::new(&[]);
        gbl_ops
            .avb_ops
            .add_persistent_value(EXPECTED_NAME.to_str().unwrap(), Err(IoError::NotImplemented));

        let mut avb_ops = GblAvbOps::new(&mut gbl_ops, None, &mut [], false);
        // Dev should report no such value, prod should fail.
        assert_eq!(
            avb_ops.erase_persistent_value(EXPECTED_NAME),
            dev_only(Err(IoError::NoSuchValue))
        );
    }
}
