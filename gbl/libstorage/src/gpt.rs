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

use crate::{read_async, write_async, BlockIoAsync, Result};
use core::{
    convert::TryFrom,
    default::Default,
    mem::{align_of, size_of},
    num::NonZeroU64,
    str::from_utf8,
};
use crc32fast::Hasher;
use liberror::Error;
use libutils::aligned_subslice;
use safemath::SafeNum;
use zerocopy::{AsBytes, FromBytes, FromZeroes, Ref};

const GPT_GUID_LEN: usize = 16;
/// The maximum number of UTF-16 characters in a GPT partition name, including termination.
pub const GPT_NAME_LEN_U16: usize = 36;
const GPT_NAME_LEN_U8: usize = 2 * GPT_GUID_LEN;

/// The top-level GPT header.
#[repr(C, packed)]
#[derive(Debug, Default, Copy, Clone, AsBytes, FromBytes, FromZeroes)]
pub struct GptHeader {
    /// Magic bytes; must be [GPT_MAGIC].
    pub magic: u64,
    /// Header version.
    pub revision: u32,
    /// Header size in bytes.
    pub size: u32,
    /// CRC of the first `size` bytes, calculated with this field zeroed.
    pub crc32: u32,
    /// Reserved; must be set to 0.
    pub reserved0: u32,
    /// The on-disk block location of this header.
    pub current: u64,
    /// The on-disk block location of the other header.
    pub backup: u64,
    /// First usable block for partition contents.
    pub first: u64,
    /// Last usable block for partition contents (inclusive).
    pub last: u64,
    /// Disk GUID.
    pub guid: [u8; GPT_GUID_LEN],
    /// Starting block for the partition entries array.
    pub entries: u64,
    /// Number of partition entries.
    pub entries_count: u32,
    /// The size of each partition entry in bytes.
    pub entries_size: u32,
    /// CRC of the partition entries array.
    pub entries_crc: u32,
}

impl GptHeader {
    /// Cast a bytes slice into a GptHeader structure.
    fn from_bytes(bytes: &mut [u8]) -> &mut GptHeader {
        Ref::<_, GptHeader>::new_from_prefix(bytes).unwrap().0.into_mut()
    }

    /// Update the header crc32 value.
    pub fn update_crc(&mut self) {
        self.crc32 = 0;
        self.crc32 = crc32(self.as_bytes());
    }
}

/// GptEntry is the partition entry data structure in the GPT.
#[repr(C)]
#[derive(Debug, Copy, Clone, AsBytes, FromBytes, FromZeroes, PartialEq)]
pub struct GptEntry {
    /// Partition type GUID.
    pub part_type: [u8; GPT_GUID_LEN],
    /// Unique partition GUID.
    pub guid: [u8; GPT_GUID_LEN],
    /// First block.
    pub first: u64,
    /// Last block (inclusive).
    pub last: u64,
    /// Partition flags.
    pub flags: u64,
    /// Partition name in UTF-16.
    pub name: [u16; GPT_NAME_LEN_U16],
}

impl GptEntry {
    /// Return the partition entry size in blocks.
    pub fn blocks(&self) -> Result<u64> {
        // Must perform "+1" first before subtracting `self.first`. Otherwise if partition size is
        // zero, where `self.first > self.last`, arithmetic will overflow.
        u64::try_from(SafeNum::from(self.last) + 1 - self.first).map_err(Into::into)
    }

    /// Return whether this is a `NULL` entry. The first null entry marks the end of the partition
    /// entries.
    fn is_null(&self) -> bool {
        self.first == 0 && self.last == 0
    }

    /// Decode the partition name into a string. A length N utf16 string can be at most 2N utf8
    /// bytes. Therefore, a safe size of `buffer` is 2*GPT_NAME_LEN_U16 = 72.
    pub fn name_to_str<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a str> {
        let mut index = 0;
        for c in char::decode_utf16(self.name) {
            match c.unwrap_or(char::REPLACEMENT_CHARACTER) {
                '\0' => break,
                c if c.len_utf8() <= buffer[index..].len() => {
                    index += c.encode_utf8(&mut buffer[index..]).len()
                }
                _ => return Err(Error::InvalidInput), // Not enough space in `buffer`.
            }
        }
        // SAFETY:
        // _unchecked should be OK here since we wrote each utf8 byte ourselves,
        // but it's just an optimization, checked version would be fine also.
        unsafe { Ok(core::str::from_utf8_unchecked(&buffer[..index])) }
    }
}

impl core::fmt::Display for GptEntry {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        // Format: partition name: "abc", [first, last]: [123, 456]
        let mut name_conversion_buffer = [0u8; GPT_NAME_LEN_U16 * 2];
        let name = self.name_to_str(&mut name_conversion_buffer).map_err(|_| core::fmt::Error)?;
        write!(f, "partition name: \"{}\", [first, last]: [{}, {}]", name, self.first, self.last)
    }
}

// core::mem::offset_of!(GptHeader, crc32) is unsatble feature and rejected by the compiler in our
// settings. We pre-compute the value here.
const GPT_CRC32_OFFSET: u64 = 16;
const GPT_ENTRY_ALIGNMENT: u64 = align_of::<GptEntry>() as u64;
const GPT_ENTRY_SIZE: u64 = size_of::<GptEntry>() as u64;
const GPT_MAX_NUM_ENTRIES: u64 = 128;
const GPT_HEADER_SIZE: u64 = size_of::<GptHeader>() as u64; // 92 bytes.
const GPT_HEADER_SIZE_PADDED: u64 =
    (GPT_HEADER_SIZE + GPT_ENTRY_ALIGNMENT - 1) / GPT_ENTRY_ALIGNMENT * GPT_ENTRY_ALIGNMENT;
/// GPT header magic bytes ("EFI PART" in ASCII).
pub const GPT_MAGIC: u64 = 0x5452415020494645;

enum HeaderType {
    Primary,
    Secondary,
}

/// `Partition` contains information about a GPT partition.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Partition {
    entry: GptEntry,
    block_size: u64,
    decoded_name: Option<([u8; GPT_NAME_LEN_U8], usize)>,
}

impl Partition {
    /// Creates a new instance.
    fn new(entry: GptEntry, block_size: u64) -> Self {
        let mut buf = [0u8; GPT_NAME_LEN_U8];
        let decoded_name = match entry.name_to_str(&mut buf[..]).ok().map(|v| v.len()) {
            Some(len) => Some((buf, len)),
            _ => None,
        };
        Self { entry, block_size, decoded_name }
    }

    /// Gets the decoded partition name.
    pub fn name(&self) -> Option<&str> {
        // Correct by construction. `from_utf8` should not fail.
        self.decoded_name.as_ref().map(|(buf, sz)| from_utf8(&buf[..*sz]).unwrap())
    }

    /// Returns the partition size in bytes.
    pub fn size(&self) -> Result<u64> {
        u64::try_from(SafeNum::from(self.entry.blocks()?) * self.block_size).map_err(Error::from)
    }

    /// Returns the block size of this partition.
    pub fn block_size(&self) -> u64 {
        self.block_size
    }

    /// Returns the partition entry structure in the GPT header.
    pub fn gpt_entry(&self) -> &GptEntry {
        &self.entry
    }

    /// Returns the partition's absolute start/end offset in number of bytes.
    pub fn absolute_range(&self) -> Result<(u64, u64)> {
        let start = SafeNum::from(self.entry.first) * self.block_size;
        let end = (SafeNum::from(self.entry.last) + 1) * self.block_size;
        Ok((start.try_into()?, end.try_into()?))
    }

    /// Checks a given sub range and returns its absolute offset.
    pub fn check_range(&self, off: u64, size: u64) -> Result<u64> {
        let off = SafeNum::from(off);
        let end: u64 = (off + size).try_into()?;
        match end > self.size()? {
            true => Err(Error::BadIndex(end as usize)),
            _ => Ok((off + self.absolute_range()?.0).try_into()?),
        }
    }
}

/// `PartitionIterator` iterates all GPT partition entries.
pub struct PartitionIterator<'a, 'b> {
    gpt_cache: &'b GptCache<'a>,
    idx: usize,
}

impl Iterator for PartitionIterator<'_, '_> {
    type Item = Partition;

    fn next(&mut self) -> Option<Self::Item> {
        let res = self
            .gpt_cache
            .entries()
            .ok()?
            .get(self.idx)
            .map(|v| Partition::new(*v, self.gpt_cache.info.block_size))?;
        self.idx += 1;
        Some(res)
    }
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, AsBytes, FromBytes, FromZeroes)]
struct GptInfo {
    // The number of valid entries in the entries array.
    // May change as partitions are added or removed.
    num_valid_entries: Option<NonZeroU64>,
    // The maximum number of elements available in the entries array.
    // Note: this is GREATER THAN OR EQUAL TO the number of valid entries
    // and LESS THAN OR EQUAL TO the value of GPT_MAX_NUM_ENTRIES.
    // Values other than GPT_MAX_NUM_ENTRIES are mostly used in unit tests.
    max_entries: u64,
    // Block size of the GPT disk.
    block_size: u64,
}

impl GptInfo {
    fn from_bytes(bytes: &mut [u8]) -> &mut Self {
        Ref::<_, GptInfo>::new_from_prefix(bytes).unwrap().0.into_mut()
    }

    fn num_valid_entries(&self) -> Result<u64> {
        Ok(self.num_valid_entries.ok_or(Error::InvalidInput)?.get())
    }
}

/// GptCache contains the GPT header/entries information loaded from storage.
pub struct GptCache<'a> {
    info: &'a mut GptInfo,
    /// Raw bytes of primary GPT header.
    primary_header: &'a mut [u8],
    /// Raw bytes of primary GPT entries.
    primary_entries: &'a mut [u8],
    /// Raw bytes of secondary GPT header.
    secondary_header: &'a mut [u8],
    /// Raw bytes of secondary GPT entries.
    secondary_entries: &'a mut [u8],
}

impl<'a> GptCache<'a> {
    /// Create an uninitialized GptCache instance from a provided buffer.
    ///
    /// # Args:
    ///
    /// * `max_entries`: Maximum number of entries allowed.
    ///
    /// * `buffer`: Buffer for creating the object. Must have a size at least
    ///   `GptCache::required_buffer_size(max_entries)`.
    pub fn from_uninit(max_entries: u64, buffer: &'a mut [u8]) -> Result<GptCache<'a>> {
        if max_entries > GPT_MAX_NUM_ENTRIES
            || buffer.len() < Self::required_buffer_size(max_entries)?
        {
            return Err(Error::InvalidInput);
        }
        let buffer = aligned_subslice(buffer, GPT_ENTRY_ALIGNMENT)?;
        *GptInfo::from_bytes(buffer) =
            GptInfo { num_valid_entries: None, max_entries, block_size: 0 };
        Self::from_existing(buffer)
    }

    /// Reconstructs an existing GptCache struct from a buffer previously created with
    /// `Self::from_uninit()` and that has been initialized with `AsyncBlockDevice::sync_gpt()`.
    ///
    /// The method simply partitions the input buffer and populate the `GptInfo` struct and
    /// primary/secondary header/entries slices. It assumes that the buffer contains a valid
    /// GptInfo struct.
    pub fn from_existing(buffer: &'a mut [u8]) -> Result<GptCache<'a>> {
        let buffer = aligned_subslice(buffer, GPT_ENTRY_ALIGNMENT)?;
        let (info, remain) = Ref::<_, GptInfo>::new_from_prefix(buffer).unwrap();
        let entries_size = SafeNum::from(info.max_entries) * GPT_ENTRY_SIZE;
        let header_size: usize = SafeNum::from(GPT_HEADER_SIZE_PADDED).try_into()?;
        let split_pos = entries_size + header_size;
        let (primary, secondary) = remain.split_at_mut(split_pos.try_into()?);
        let (primary_header, primary_entries) = primary.split_at_mut(header_size);
        let (secondary_header, secondary_entries) = secondary.split_at_mut(header_size);

        Ok(Self {
            info: info.into_mut(),
            primary_header,
            primary_entries,
            secondary_header,
            secondary_entries: &mut secondary_entries[..entries_size.try_into()?],
        })
    }

    /// Creates a new `GptCache` instance that borrows the internal data of this instance.
    pub fn as_mut_instance(&mut self) -> GptCache<'_> {
        GptCache {
            info: &mut self.info,
            primary_header: &mut self.primary_header,
            primary_entries: &mut self.primary_entries,
            secondary_header: &mut self.secondary_header,
            secondary_entries: &mut self.secondary_entries,
        }
    }

    /// Returns an iterator to GPT partition entries.
    pub fn partition_iter(&self) -> PartitionIterator {
        PartitionIterator { gpt_cache: self, idx: 0 }
    }

    /// The minimum buffer size needed for `Self::from_uninit()`
    pub fn required_buffer_size(max_entries: u64) -> Result<usize> {
        let entries_size = SafeNum::from(max_entries) * GPT_ENTRY_SIZE;
        usize::try_from(
            ((entries_size + GPT_HEADER_SIZE_PADDED) * 2)
                + size_of::<GptInfo>()
                + GPT_ENTRY_ALIGNMENT
                - 1,
        )
        .map_err(Into::<Error>::into)
    }

    /// Checks if a read/write range into a GPT partition overflows and returns the range's absolute
    /// offset in number of bytes.
    pub fn check_range(&self, part_name: &str, offset: u64, size: usize) -> Result<u64> {
        self.find_partition(part_name)?.check_range(offset, u64::try_from(size)?)
    }

    /// Return the list of GPT entries.
    ///
    /// If the object does not contain a valid GPT, the method returns Error.
    fn entries(&self) -> Result<&[GptEntry]> {
        self.check_valid()?;
        Ok(&Ref::<_, [GptEntry]>::new_slice(&self.primary_entries[..]).unwrap().into_slice()
            [..usize::try_from(self.info.num_valid_entries()?)?])
    }

    /// Returns the total number of partitions.
    pub fn num_partitions(&self) -> Result<usize> {
        Ok(self.entries()?.len())
    }

    /// Gets the `idx`th partition.
    pub fn get_partition(&self, idx: usize) -> Result<Partition> {
        let entry = *self.entries()?.get(idx).ok_or(Error::BadIndex(idx))?;
        Ok(Partition::new(entry, self.info.block_size))
    }

    /// Returns the `Partition` for a partition.
    ///
    /// # Args
    ///
    /// * `part`: Name of the partition.
    pub fn find_partition(&self, part: &str) -> Result<Partition> {
        for entry in self.entries()? {
            let mut name_conversion_buffer = [0u8; GPT_NAME_LEN_U16 * 2];
            if entry.name_to_str(&mut name_conversion_buffer)? != part {
                continue;
            }
            return Ok(Partition::new(*entry, self.info.block_size));
        }
        Err(Error::NotFound)
    }

    /// Checks whether the GptCache has been initialized.
    fn check_valid(&self) -> Result<()> {
        self.info.num_valid_entries()?;
        Ok(())
    }

    /// Helper function for loading and validating GPT header and entries.
    async fn validate_gpt(
        &mut self,
        io: &mut impl BlockIoAsync,
        scratch: &mut [u8],
        header_type: HeaderType,
    ) -> Result<bool> {
        let (header_start, header_bytes, entries) = match header_type {
            HeaderType::Primary => {
                (io.info().block_size.into(), &mut self.primary_header, &mut self.primary_entries)
            }
            HeaderType::Secondary => (
                (SafeNum::from(io.info().num_blocks) - 1) * io.info().block_size,
                &mut self.secondary_header,
                &mut self.secondary_entries,
            ),
        };
        read_async(io, header_start.try_into()?, header_bytes, scratch).await?;
        let header =
            Ref::<_, GptHeader>::new_from_prefix(header_bytes.as_bytes()).unwrap().0.into_ref();

        if header.magic != GPT_MAGIC {
            return Ok(false);
        }

        let entries_size = SafeNum::from(header.entries_count) * GPT_ENTRY_SIZE;
        let entries_offset = SafeNum::from(header.entries) * io.info().block_size;
        if self.info.max_entries < header.entries_count.into()
            || u64::try_from(entries_size + entries_offset)?
                > ((SafeNum::from(io.info().num_blocks) - 1) * io.info().block_size).try_into()?
        {
            return Ok(false);
        }

        let crc32_offset = SafeNum::from(GPT_CRC32_OFFSET).try_into()?;
        let mut hasher = Hasher::new();
        hasher.update(&header.as_bytes()[..crc32_offset]);
        hasher.update(&[0u8; size_of::<u32>()]);
        hasher.update(&header.as_bytes()[crc32_offset + size_of::<u32>()..]);
        if hasher.finalize() != header.crc32 {
            return Ok(false);
        }

        // Load the entries
        let out = &mut entries[..entries_size.try_into()?];
        read_async(io, entries_offset.try_into()?, out, scratch).await?;
        // Validate entries crc32.
        Ok(header.entries_crc == crc32(out))
    }

    /// Load and sync GPT from a block device.
    pub(crate) async fn load_and_sync(
        &mut self,
        io: &mut impl BlockIoAsync,
        scratch: &mut [u8],
    ) -> Result<()> {
        self.info.num_valid_entries = None;

        let block_size = io.info().block_size;
        let total_blocks: SafeNum = io.info().num_blocks.into();

        let primary_header_blk = 1;
        let primary_header_pos = block_size;
        let secondary_header_blk = total_blocks - 1;
        let secondary_header_pos = secondary_header_blk * block_size;

        // Entries position for restoring.
        let primary_entries_blk = 2;
        let primary_entries_pos = SafeNum::from(primary_entries_blk) * block_size;
        let primary_valid = self.validate_gpt(io, scratch, HeaderType::Primary).await?;
        let secondary_valid = self.validate_gpt(io, scratch, HeaderType::Secondary).await?;

        let primary_header = GptHeader::from_bytes(self.primary_header);
        let secondary_header = GptHeader::from_bytes(self.secondary_header);
        if !primary_valid {
            if !secondary_valid {
                return Err(Error::NoGpt);
            }
            // Restore to primary
            primary_header.as_bytes_mut().clone_from_slice(secondary_header.as_bytes());
            self.primary_entries.clone_from_slice(&self.secondary_entries);
            primary_header.current = primary_header_blk;
            primary_header.backup = secondary_header_blk.try_into()?;
            primary_header.entries = primary_entries_blk;
            primary_header.update_crc();

            write_async(io, primary_header_pos, primary_header.as_bytes_mut(), scratch).await?;
            write_async(io, primary_entries_pos.try_into()?, self.primary_entries, scratch).await?
        } else if !secondary_valid {
            // Restore to secondary
            let secondary_entries_pos = secondary_header_pos
                - (SafeNum::from(self.info.max_entries) * core::mem::size_of::<GptEntry>());
            let secondary_entries_blk = secondary_entries_pos / block_size;

            secondary_header.as_bytes_mut().clone_from_slice(primary_header.as_bytes());
            self.secondary_entries.clone_from_slice(&self.primary_entries);
            secondary_header.current = secondary_header_blk.try_into()?;
            secondary_header.backup = primary_header_blk;
            secondary_header.entries = secondary_entries_blk.try_into()?;
            secondary_header.update_crc();

            write_async(
                io,
                secondary_header_pos.try_into()?,
                secondary_header.as_bytes_mut(),
                scratch,
            )
            .await?;
            write_async(io, secondary_entries_pos.try_into()?, self.secondary_entries, scratch)
                .await?;
        }

        // Calculate actual number of GPT entries by finding the first invalid entry.
        let entries =
            Ref::<_, [GptEntry]>::new_slice(&self.primary_entries[..]).unwrap().into_slice();
        self.info.num_valid_entries =
            NonZeroU64::new(match entries.iter().position(|e| e.is_null()) {
                Some(idx) => idx as u64,
                _ => self.info.max_entries,
            });
        self.info.block_size = block_size;
        Ok(())
    }
}

/// Checks if a read/write range into a GPT partition overflows and returns the range's absolute
/// offset in the block device.
pub(crate) fn check_gpt_rw_params(
    gpt_cache_buffer: &mut [u8],
    part_name: &str,
    offset: u64,
    size: usize,
) -> Result<u64> {
    GptCache::from_existing(gpt_cache_buffer)?.check_range(part_name, offset, size)
}

fn crc32(data: &[u8]) -> u32 {
    let mut hasher = Hasher::new();
    hasher.update(data);
    hasher.finalize()
}

#[cfg(test)]
pub(crate) mod test {
    use super::*;
    use gbl_storage_testlib::{
        alignment_scratch_size, AsBlockDevice, BackingStore, TestBlockDevice,
        TestBlockDeviceBuilder,
    };

    /// Helper function to extract the gpt header from a test block device.
    fn gpt(dev: &mut TestBlockDevice) -> GptCache {
        let info = dev.info();
        let (_, gpt) = dev.scratch.split_at_mut(alignment_scratch_size(info).unwrap());
        GptCache::from_existing(gpt).unwrap()
    }

    #[test]
    fn test_load_and_sync() {
        let mut dev: TestBlockDevice = include_bytes!("../test/gpt_test_1.bin").as_slice().into();
        dev.sync_gpt().unwrap();

        let gpt_cache = gpt(&mut dev);
        assert_eq!(gpt_cache.partition_iter().count(), 2);
        gpt_cache.find_partition("boot_a").unwrap();
        gpt_cache.find_partition("boot_b").unwrap();
        assert!(gpt_cache.find_partition("boot_c").is_err());
    }

    #[test]
    fn test_gpt_buffer_too_small() {
        let mut dev: TestBlockDevice = include_bytes!("../test/gpt_test_1.bin").as_slice().into();
        dev.scratch = vec![0u8; dev.scratch.len() - 1];
        assert!(dev.sync_gpt().is_err());
    }

    #[test]
    fn test_gpt_too_many_entries() {
        let mut dev = TestBlockDeviceBuilder::new()
            .set_data(include_bytes!("../test/gpt_test_1.bin"))
            .set_max_gpt_entries(129)
            .build();
        assert!(dev.sync_gpt().is_err());
    }

    #[test]
    fn test_load_gpt_primary() {
        let disk = include_bytes!("../test/gpt_test_1.bin");
        let mut dev: TestBlockDevice = disk.as_slice().into();

        // Corrupt secondary.
        dev.io.storage[disk.len() - 512..].fill(0);
        dev.sync_gpt().unwrap();

        let gpt_cache = gpt(&mut dev);
        assert_eq!(gpt_cache.partition_iter().count(), 2);
        gpt_cache.find_partition("boot_a").unwrap();
        gpt_cache.find_partition("boot_b").unwrap();
        assert!(gpt_cache.find_partition("boot_c").is_err());

        // Check that secondary is restored
        assert_eq!(dev.io.storage, disk);
    }

    #[test]
    fn test_load_gpt_secondary() {
        let disk = include_bytes!("../test/gpt_test_1.bin");
        let mut dev: TestBlockDevice = disk.as_slice().into();

        // Corrupt primary.
        dev.io.storage[512..1024].fill(0);
        dev.sync_gpt().unwrap();

        let gpt_cache = gpt(&mut dev);
        assert_eq!(gpt_cache.partition_iter().count(), 2);
        gpt_cache.find_partition("boot_a").unwrap();
        gpt_cache.find_partition("boot_b").unwrap();

        // Check that primary is restored
        assert_eq!(dev.io.storage, disk);
    }

    #[test]
    fn test_good_gpt_no_repair_write() {
        let mut dev: TestBlockDevice = include_bytes!("../test/gpt_test_1.bin").as_slice().into();
        dev.sync_gpt().unwrap();

        assert_eq!(dev.io.num_writes, 0);
    }

    #[test]
    fn test_load_gpt_incorrect_magic() {
        let disk = include_bytes!("../test/gpt_test_1.bin");
        let mut dev = TestBlockDeviceBuilder::new().set_data(disk).build();
        dev.sync_gpt().unwrap();

        let gpt = gpt(&mut dev);
        let primary_header = &mut gpt.primary_header[..GPT_HEADER_SIZE.try_into().unwrap()];
        let gpt_header = GptHeader::from_bytes(primary_header);
        gpt_header.magic = 0x123456;
        gpt_header.update_crc();
        let primary_header = Vec::from(primary_header);
        dev.io.storage[512..512 + primary_header.len()].clone_from_slice(&primary_header);

        dev.sync_gpt().unwrap();

        // Check that incorrect magic header is restored
        assert_eq!(dev.io.storage, disk);
    }

    #[test]
    fn test_load_gpt_exceeds_max_entries() {
        let mut dev = TestBlockDeviceBuilder::new()
            .set_data(include_bytes!("../test/gpt_test_1.bin"))
            .set_max_gpt_entries(127)
            .build();

        assert!(dev.sync_gpt().is_err());
    }

    #[test]
    fn test_load_gpt_non_max_entries() {
        // Create a header with non-max entries_count
        let disk = include_bytes!("../test/gpt_test_1.bin");
        let mut dev = TestBlockDeviceBuilder::new().set_data(disk).build();
        let block_size: usize = dev.io.block_size.try_into().unwrap();
        dev.sync_gpt().unwrap();

        let gpt = gpt(&mut dev);
        let primary_header = &mut gpt.primary_header[..GPT_HEADER_SIZE.try_into().unwrap()];
        let gpt_header = GptHeader::from_bytes(primary_header);
        gpt_header.entries_count = 2;
        // Update entries crc32
        gpt_header.entries_crc =
            crc32(&gpt.primary_entries[..(2 * GPT_ENTRY_SIZE).try_into().unwrap()]);
        gpt_header.update_crc();
        // Update to primary.
        let primary_header = Vec::from(primary_header);
        dev.io.storage[block_size..block_size + primary_header.len()]
            .clone_from_slice(&primary_header);

        // Corrupt secondary. Sync ok
        dev.io.storage[disk.len() - block_size..].fill(0);
        dev.sync_gpt().unwrap();

        // Corrup primary. Sync ok
        dev.io.storage[block_size..(block_size * 2)].fill(0);
        dev.sync_gpt().unwrap();
    }

    #[test]
    fn test_uninitialized_gpt() {
        // Load a good GPT first.
        let mut dev = TestBlockDeviceBuilder::new()
            .set_data(include_bytes!("../test/gpt_test_1.bin"))
            .build();
        dev.sync_gpt().unwrap();
        dev.io.storage[..64 * 1024].fill(0);
        // Load a bad GPT. Validate that the valid state is reset.
        assert!(dev.sync_gpt().is_err());
        assert!(gpt(&mut dev).find_partition("").is_err());
    }

    #[test]
    fn test_gpt_read() {
        let mut dev = TestBlockDeviceBuilder::new()
            .set_data(include_bytes!("../test/gpt_test_1.bin"))
            .build();
        dev.sync_gpt().unwrap();

        let expect_boot_a = include_bytes!("../test/boot_a.bin");
        let expect_boot_b = include_bytes!("../test/boot_b.bin");

        let mut actual_boot_a = vec![0u8; expect_boot_a.len()];
        let mut actual_boot_b = vec![0u8; expect_boot_b.len()];

        dev.read_gpt_partition("boot_a", 0, &mut actual_boot_a).unwrap();
        assert_eq!(expect_boot_a.to_vec(), actual_boot_a);
        // partial read
        actual_boot_a = actual_boot_a[1..].to_vec();
        dev.read_gpt_partition("boot_a", 1, &mut actual_boot_a).unwrap();
        assert_eq!(expect_boot_a[1..].to_vec(), actual_boot_a);

        dev.read_gpt_partition("boot_b", 0, &mut actual_boot_b).unwrap();
        assert_eq!(expect_boot_b.to_vec(), actual_boot_b);
        // partial read
        actual_boot_b = actual_boot_b[1..].to_vec();
        dev.read_gpt_partition("boot_b", 1, &mut actual_boot_b).unwrap();
        assert_eq!(expect_boot_b[1..].to_vec(), actual_boot_b);
    }

    #[test]
    fn test_gpt_write() {
        let mut dev = TestBlockDeviceBuilder::new()
            .set_data(include_bytes!("../test/gpt_test_1.bin"))
            .build();
        dev.sync_gpt().unwrap();

        let mut expect_boot_a = include_bytes!("../test/boot_a.bin").to_vec();
        expect_boot_a.reverse();
        let mut expect_boot_b = include_bytes!("../test/boot_b.bin").to_vec();
        expect_boot_b.reverse();

        let mut actual_boot_a = vec![0u8; expect_boot_a.len()];
        let mut actual_boot_b = vec![0u8; expect_boot_b.len()];

        // "boot_a" partition
        // Mutable version
        dev.write_gpt_partition("boot_a", 0, expect_boot_a.as_mut_slice()).unwrap();
        dev.read_gpt_partition("boot_a", 0, &mut actual_boot_a).unwrap();
        assert_eq!(expect_boot_a.to_vec(), actual_boot_a);
        // Mutable version, partial write.
        dev.write_gpt_partition("boot_a", 1, expect_boot_a[1..].as_mut()).unwrap();
        dev.read_gpt_partition("boot_a", 1, &mut actual_boot_a[1..]).unwrap();
        assert_eq!(expect_boot_a[1..], actual_boot_a[1..]);

        // "boot_b" partition
        // Mutable version
        dev.write_gpt_partition("boot_b", 0, expect_boot_b.as_mut_slice()).unwrap();
        dev.read_gpt_partition("boot_b", 0, &mut actual_boot_b).unwrap();
        assert_eq!(expect_boot_b.to_vec(), actual_boot_b);
        // Mutable version, partial write.
        dev.write_gpt_partition("boot_b", 1, expect_boot_b[1..].as_mut()).unwrap();
        dev.read_gpt_partition("boot_b", 1, &mut actual_boot_b[1..]).unwrap();
        assert_eq!(expect_boot_b[1..], actual_boot_b[1..]);
    }

    #[test]
    fn test_gpt_rw_overflow() {
        let mut dev = TestBlockDeviceBuilder::new()
            .set_data(include_bytes!("../../libstorage/test/gpt_test_1.bin"))
            .build();
        dev.sync_gpt().unwrap();

        let mut boot_a = [0u8; include_bytes!("../test/boot_a.bin").len()];
        let mut boot_b = [0u8; include_bytes!("../test/boot_b.bin").len()];

        assert!(dev.read_gpt_partition("boot_a", 1, &mut boot_a).is_err());
        assert!(dev.write_gpt_partition("boot_a", 1, boot_a.as_mut_slice()).is_err());

        assert!(dev.read_gpt_partition("boot_b", 1, &mut boot_b).is_err());
        assert!(dev.write_gpt_partition("boot_b", 1, boot_b.as_mut_slice()).is_err());
    }

    #[test]
    fn test_zero_partition_size() {
        let mut dev =
            TestBlockDeviceBuilder::new().add_partition("zero_size", BackingStore::Size(0)).build();
        dev.sync_gpt().unwrap();
        assert_eq!(gpt(&mut dev).partition_iter().next().unwrap().size().unwrap(), 0);
    }
}
