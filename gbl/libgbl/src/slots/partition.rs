// Copyright (C) 2024  Google LLC
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

use super::BootToken;
use zerocopy::{AsBytes, ByteSlice, FromBytes, FromZeroes, Ref};

/// Tracks whether slot metadata differs from on-disk representation.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum CacheStatus {
    /// Slot metadata is the same as on disk
    Clean,
    /// Slot metadata has been modified
    Dirty,
}

/// Custom error type
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum MetadataParseError {
    /// The magic number field was corrupted
    BadMagic,
    /// The version of the structure is unsupported
    BadVersion,
    /// The struct checksum check failed
    BadChecksum,
    /// The deserialization buffer is too small
    BufferTooSmall,
}

/// Trait that describes the operations all slot metadata implementations must support
/// to be used as the backing store in a SlotBlock.
pub trait MetadataBytes: Copy + AsBytes + FromBytes + FromZeroes + Default {
    /// Returns a zerocopy reference to Self if buffer
    /// represents a valid serialization of Self.
    /// Implementors should check for invariants,
    /// e.g. checksums, magic numbers, and version numbers.
    ///
    /// Returns Err if the buffer does not represent a valid structure.
    fn validate<B: ByteSlice>(buffer: B) -> Result<Ref<B, Self>, MetadataParseError>;

    /// Called right before writing metadata back to disk.
    /// Implementors should restore invariants,
    /// update checksums, or take other appropriate actions.
    fn prepare_for_sync(&mut self);
}

/// Generalized description of a partition-backed ABR metadata structure.
pub struct SlotBlock<'a, MB: MetadataBytes> {
    /// The partition the metadata was read from and will be written back to.
    pub partition: &'a str,
    /// The offset from the beginning of the partition in bytes.
    pub partition_offset: u64,

    // Internally tracked cache clean/dirty info
    cache_status: CacheStatus,
    // SlotBlock holds the boot token until mark_boot_attempt gets called.
    boot_token: Option<BootToken>,
    // Serialized slot metadata
    data: MB,
}

impl<'a, MB: MetadataBytes> SlotBlock<'a, MB> {
    /// Note to those implementing Manager for SlotBlock<'_, CustomType>:
    /// Be very, very careful with custody of the boot token.
    /// If you release it outside of the implementation of Manager::mark_boot_attempt,
    /// mark_boot_attempt will fail and the kernel may boot without tracking the attempt.
    /// If you lose the token, the only way to get it back is to reboot the device.
    pub fn take_boot_token(&mut self) -> Option<BootToken> {
        self.boot_token.take()
    }

    /// Returns a mutable reference to the slot metadata and marks the cache as dirty.
    pub fn get_mut_data(&mut self) -> &mut MB {
        self.cache_status = CacheStatus::Dirty;
        &mut self.data
    }

    /// Returns an immutable reference to the slot metadata
    pub fn get_data(&self) -> &MB {
        &self.data
    }

    #[cfg(test)]
    /// Returns the cache status
    pub fn cache_status(&self) -> CacheStatus {
        self.cache_status
    }

    /// Attempt to deserialize a slot control block
    ///
    /// # Returns
    /// * `SlotBlock` - returns either the deserialized
    ///                 representation of the slot control block
    ///                 OR a fresh, default valued slot control block
    ///                 if there was an internal error.
    ///
    ///                 TODO(b/329116902): errors are logged
    pub fn deserialize<B: ByteSlice>(
        buffer: B,
        partition: &'a str,
        partition_offset: u64,
        boot_token: BootToken,
    ) -> Self {
        // TODO(b/329116902): log failures
        // validate(buffer)
        // .inspect_err(|e| {
        //     eprintln!("ABR metadata failed verification, using metadata defaults: {e}")
        // })
        let (data, cache_status) = match MB::validate(buffer) {
            Ok(data) => (*data, CacheStatus::Clean),
            Err(_) => (Default::default(), CacheStatus::Dirty),
        };

        SlotBlock { cache_status, boot_token: Some(boot_token), data, partition, partition_offset }
    }

    /// Write back slot metadata to disk.
    /// The MetadataBytes type should reestablish any invariants when
    /// `prepare_for_sync` is called, e.g. recalculating checksums.
    ///
    /// Does NOT write back to disk if no changes have been made and the cache is clean.
    /// Panics if the write attempt fails.
    pub fn sync_to_disk<BlockDev: gbl_storage::AsBlockDevice>(&mut self, block_dev: &mut BlockDev) {
        if self.cache_status == CacheStatus::Clean {
            return;
        }

        self.data.prepare_for_sync();

        match block_dev.write_gpt_partition(
            self.partition,
            self.partition_offset,
            self.get_mut_data().as_bytes_mut(),
        ) {
            Ok(_) => self.cache_status = CacheStatus::Clean,
            Err(e) => panic!("{}", e),
        };
    }
}

#[cfg(test)]
impl<MB: MetadataBytes> Default for SlotBlock<'_, MB> {
    /// Returns a default valued SlotBlock.
    /// Only used in tests because BootToken cannot be constructed out of crate.
    fn default() -> Self {
        Self {
            partition: "",
            partition_offset: 0,
            cache_status: CacheStatus::Clean,
            boot_token: Some(BootToken(())),
            data: Default::default(),
        }
    }
}
