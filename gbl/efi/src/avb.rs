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

// This is an example implementation of the libavb rust wrapper backend in the EFI environment. It
// is mainly for use by the boot demo. Eventually, these backends will be implemented from the
// `GblOps` interface in libgbl, where EFI services will be one level lower as its backend instead.

use avb::{IoError, IoResult, Ops as AvbOps, PublicKeyForPartitionInfo};
use core::ffi::CStr;
use libgbl::GblOps;
use uuid::Uuid;

extern crate avb_sysdeps;

/// [AvbOps] implementation for [GblOps].
// TODO(b/363074091): this code is now platform-independent; move it into libgbl.
pub struct GblEfiAvbOps<'a, G> {
    gbl_ops: &'a mut G,
    preloaded_partitions: Option<&'a [(&'a str, &'a [u8])]>,
}

/// # Lifetimes
/// * `'a`: borrowed data minimum lifetime
/// * `'b`: [GblOps] partition lifetime
impl<'a, 'b, G: GblOps<'b>> GblEfiAvbOps<'a, G> {
    pub fn new(
        gbl_ops: &'a mut G,
        preloaded_partitions: Option<&'a [(&'a str, &'a [u8])]>,
    ) -> Self {
        Self { gbl_ops, preloaded_partitions }
    }

    /// Returns the size of a partition.
    fn partition_size(&mut self, partition: &str) -> IoResult<u64> {
        self.gbl_ops.partition_size(partition).or(Err(IoError::Io))?.ok_or(IoError::NoSuchPartition)
    }
}

/// A helper function for converting CStr to str
fn cstr_to_str<E>(s: &CStr, err: E) -> Result<&str, E> {
    Ok(s.to_str().map_err(|_| err)?)
}

impl<'a, 'b, G: GblOps<'b>> AvbOps<'a> for GblEfiAvbOps<'a, G> {
    fn read_from_partition(
        &mut self,
        partition: &CStr,
        offset: i64,
        buffer: &mut [u8],
    ) -> IoResult<usize> {
        let part_str = cstr_to_str(partition, IoError::NoSuchPartition)?;
        let partition_size: u64 =
            self.partition_size(part_str)?.try_into().map_err(|_| IoError::Oom)?;
        let read_off: u64 = match offset < 0 {
            true => {
                partition_size.checked_sub(offset.abs() as u64).ok_or(IoError::InvalidValueSize)?
            }
            _ => offset.try_into().map_err(|_| IoError::InvalidValueSize)?,
        };
        self.gbl_ops.read_from_partition_sync(part_str, read_off, buffer).or(Err(IoError::Io))?;
        Ok(buffer.len())
    }

    fn get_preloaded_partition(&mut self, partition: &CStr) -> IoResult<&'a [u8]> {
        let part_str = cstr_to_str(partition, IoError::NotImplemented)?;
        Ok(self
            .preloaded_partitions
            .ok_or(IoError::NotImplemented)?
            .iter()
            .find(|(name, _)| *name == part_str)
            .ok_or(IoError::NotImplemented)?
            .1)
    }

    fn validate_vbmeta_public_key(
        &mut self,
        _public_key: &[u8],
        _public_key_metadata: Option<&[u8]>,
    ) -> IoResult<bool> {
        // Not supported until we add our GBL specific EFI protocol that does this.
        Ok(true)
    }

    fn read_rollback_index(&mut self, _rollback_index_location: usize) -> IoResult<u64> {
        // Not supported until we add our GBL specific EFI protocol that does this.
        Ok(0)
    }

    fn write_rollback_index(
        &mut self,
        _rollback_index_location: usize,
        _index: u64,
    ) -> IoResult<()> {
        // Not supported until we add our GBL specific EFI protocol that does this.
        Ok(())
    }

    fn read_is_device_unlocked(&mut self) -> IoResult<bool> {
        // Not supported until we add our GBL specific EFI protocol that does this.
        // For now always consider unlocked.
        Ok(true)
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
        // Not supported until we add our GBL specific EFI protocol that does this.
        unimplemented!();
    }

    fn write_persistent_value(&mut self, _name: &CStr, _value: &[u8]) -> IoResult<()> {
        // Not supported until we add our GBL specific EFI protocol that does this.
        unimplemented!();
    }

    fn erase_persistent_value(&mut self, _name: &CStr) -> IoResult<()> {
        // Not supported until we add our GBL specific EFI protocol that does this.
        unimplemented!();
    }

    fn validate_public_key_for_partition(
        &mut self,
        _partition: &CStr,
        _public_key: &[u8],
        _public_key_metadata: Option<&[u8]>,
    ) -> IoResult<PublicKeyForPartitionInfo> {
        // Not supported until we add our GBL specific EFI protocol that does this.
        unimplemented!();
    }
}
