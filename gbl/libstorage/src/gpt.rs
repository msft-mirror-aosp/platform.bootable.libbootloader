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

use crate::{aligned_subslice, read, write_bytes_mut, BlockIo, Result, StorageError};
use core::default::Default;
use core::mem::{align_of, size_of};
use core::num::NonZeroU64;
use crc32fast::Hasher;
use safemath::SafeNum;
use zerocopy::{AsBytes, FromBytes, FromZeroes, Ref};

const GPT_GUID_LEN: usize = 16;
pub const GPT_NAME_LEN_U16: usize = 36;

#[repr(C, packed)]
#[derive(Debug, Default, Copy, Clone, AsBytes, FromBytes, FromZeroes)]
pub struct GptHeader {
    pub magic: u64,
    pub revision: u32,
    pub size: u32,
    pub crc32: u32,
    pub reserved0: u32,
    pub current: u64,
    pub backup: u64,
    pub first: u64,
    pub last: u64,
    pub guid: [u8; GPT_GUID_LEN],
    pub entries: u64,
    pub entries_count: u32,
    pub entries_size: u32,
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
#[derive(Debug, Copy, Clone, AsBytes, FromBytes, FromZeroes)]
pub struct GptEntry {
    pub part_type: [u8; GPT_GUID_LEN],
    pub guid: [u8; GPT_GUID_LEN],
    pub first: u64,
    pub last: u64,
    pub flags: u64,
    pub name: [u16; GPT_NAME_LEN_U16],
}

impl GptEntry {
    /// Return the partition entry size in blocks.
    pub fn blocks(&self) -> Result<u64> {
        u64::try_from((SafeNum::from(self.last) - self.first) + 1).map_err(|e| e.into())
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
                _ => return Err(StorageError::InvalidInput), // Not enough space in `buffer`.
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
pub const GPT_MAGIC: u64 = 0x5452415020494645;

enum HeaderType {
    Primary,
    Secondary,
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
        Ok(self.num_valid_entries.ok_or_else(|| StorageError::InvalidInput)?.get())
    }
}

/// An object that contains the GPT header/entries information.
pub(crate) struct Gpt<'a> {
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

impl<'a> Gpt<'a> {
    /// Create an uninitialized Gpt instance from a provided buffer.
    ///
    /// # Args:
    ///
    /// * `max_entries`: Maximum number of entries allowed.
    ///
    /// * `buffer`: Buffer for creating the object. Must have a size at least
    ///   `Gpt::required_buffer_size(max_entries)`.
    pub(crate) fn new_from_buffer(max_entries: u64, buffer: &'a mut [u8]) -> Result<Gpt<'a>> {
        if max_entries > GPT_MAX_NUM_ENTRIES
            || buffer.len() < Self::required_buffer_size(max_entries)?
        {
            return Err(StorageError::InvalidInput);
        }
        let buffer = aligned_subslice(buffer, GPT_ENTRY_ALIGNMENT)?;
        *GptInfo::from_bytes(buffer) =
            GptInfo { num_valid_entries: None, max_entries, block_size: 0 };
        Self::from_existing(buffer)
    }

    /// Reconstruct an existing Gpt struct from a buffer previously created with `new_from_buffer`.
    ///
    /// The method simply partitions the input buffer and populate the `GptInfo` struct and
    /// primary/secondary header/entries slices. It assumes that the buffer contains a valid
    /// GptInfo struct.
    pub fn from_existing(buffer: &'a mut [u8]) -> Result<Gpt<'a>> {
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

    /// The minimum buffer size needed for `new_from_buffer()`
    pub(crate) fn required_buffer_size(max_entries: u64) -> Result<usize> {
        let entries_size = SafeNum::from(max_entries) * GPT_ENTRY_SIZE;
        (((entries_size + GPT_HEADER_SIZE_PADDED) * 2) + size_of::<GptInfo>() + GPT_ENTRY_ALIGNMENT
            - 1)
        .try_into()
        .map_err(|e: safemath::Error| e.into())
    }

    /// Return the list of GPT entries.
    ///
    /// If the object does not contain a valid GPT, the method returns Error.
    pub(crate) fn entries(&self) -> Result<&[GptEntry]> {
        self.check_valid()?;
        Ok(&Ref::<_, [GptEntry]>::new_slice(&self.primary_entries[..]).unwrap().into_slice()
            [..self.info.num_valid_entries()?.try_into()?])
    }

    /// Search for a partition entry.
    ///
    /// If partition doesn't exist, the method returns `Ok(None)`.
    ///
    /// If the object does not contain a valid GPT, the method returns Error.
    pub(crate) fn find_partition(&self, part: &str) -> Result<&GptEntry> {
        for entry in self.entries()? {
            let mut name_conversion_buffer = [0u8; GPT_NAME_LEN_U16 * 2];
            if entry.name_to_str(&mut name_conversion_buffer)? != part {
                continue;
            }
            return Ok(entry);
        }
        Err(StorageError::NotExist)
    }

    /// Check whether the Gpt has been initialized.
    fn check_valid(&self) -> Result<()> {
        self.info.num_valid_entries()?;
        Ok(())
    }

    /// Helper function for loading and validating GPT header and entries.
    fn validate_gpt(
        &mut self,
        blk_dev: &mut (impl BlockIo + ?Sized),
        scratch: &mut [u8],
        header_type: HeaderType,
    ) -> Result<bool> {
        let (header_start, header_bytes, entries) = match header_type {
            HeaderType::Primary => {
                (blk_dev.block_size().into(), &mut self.primary_header, &mut self.primary_entries)
            }
            HeaderType::Secondary => (
                (SafeNum::from(blk_dev.num_blocks()) - 1) * blk_dev.block_size(),
                &mut self.secondary_header,
                &mut self.secondary_entries,
            ),
        };
        read(blk_dev, header_start.try_into()?, header_bytes, scratch)?;
        let header =
            Ref::<_, GptHeader>::new_from_prefix(header_bytes.as_bytes()).unwrap().0.into_ref();

        if header.magic != GPT_MAGIC {
            return Ok(false);
        }

        let entries_size = SafeNum::from(header.entries_count) * GPT_ENTRY_SIZE;
        let entries_offset = SafeNum::from(header.entries) * blk_dev.block_size();
        if self.info.max_entries < header.entries_count.into()
            || u64::try_from(entries_size + entries_offset)?
                > ((SafeNum::from(blk_dev.num_blocks()) - 1) * blk_dev.block_size()).try_into()?
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
        read(blk_dev, entries_offset.try_into()?, out, scratch)?;
        // Validate entries crc32.
        Ok(header.entries_crc == crc32(out))
    }

    /// Load and sync GPT from a block device.
    fn load_and_sync(
        &mut self,
        blk_dev: &mut (impl BlockIo + ?Sized),
        scratch: &mut [u8],
    ) -> Result<()> {
        self.info.num_valid_entries = None;

        let block_size = blk_dev.block_size();
        let total_blocks: SafeNum = blk_dev.num_blocks().into();

        let primary_header_blk = 1;
        let primary_header_pos = block_size;
        let secondary_header_blk = total_blocks - 1;
        let secondary_header_pos = secondary_header_blk * block_size;

        // Entries position for restoring.
        let primary_entries_blk = 2;
        let primary_entries_pos = SafeNum::from(primary_entries_blk) * block_size;
        let primary_valid = self.validate_gpt(blk_dev, scratch, HeaderType::Primary)?;
        let secondary_valid = self.validate_gpt(blk_dev, scratch, HeaderType::Secondary)?;

        let primary_header = GptHeader::from_bytes(self.primary_header);
        let secondary_header = GptHeader::from_bytes(self.secondary_header);
        if !primary_valid {
            if !secondary_valid {
                return Err(StorageError::NoValidGpt);
            }
            // Restore to primary
            primary_header.as_bytes_mut().clone_from_slice(secondary_header.as_bytes());
            self.primary_entries.clone_from_slice(&self.secondary_entries);
            primary_header.current = primary_header_blk;
            primary_header.backup = secondary_header_blk.try_into()?;
            primary_header.entries = primary_entries_blk;
            primary_header.update_crc();

            write_bytes_mut(blk_dev, primary_header_pos, primary_header.as_bytes_mut(), scratch)?;
            write_bytes_mut(
                blk_dev,
                primary_entries_pos.try_into()?,
                self.primary_entries,
                scratch,
            )?
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

            write_bytes_mut(
                blk_dev,
                secondary_header_pos.try_into()?,
                secondary_header.as_bytes_mut(),
                scratch,
            )?;
            write_bytes_mut(
                blk_dev,
                secondary_entries_pos.try_into()?,
                self.secondary_entries,
                scratch,
            )?;
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

/// Wrapper of gpt.load_and_sync(). Library internal helper for AsBlockDevice::sync_gpt().
pub(crate) fn gpt_sync(
    blk_dev: &mut (impl BlockIo + ?Sized),
    gpt: &mut Gpt,
    scratch: &mut [u8],
) -> Result<()> {
    gpt.load_and_sync(blk_dev, scratch)
}

/// Checks if a read/write range into a GPT partition overflows and returns the range's absolute
/// offset in the block device.
pub(crate) fn check_gpt_rw_params(
    gpt_cache_buffer: &mut [u8],
    part_name: &str,
    offset: u64,
    size: usize,
) -> Result<u64> {
    let gpt = Gpt::from_existing(gpt_cache_buffer)?;
    let entry = gpt.find_partition(part_name)?;
    let end: u64 = (SafeNum::from(offset) + size).try_into()?;
    let total_size = SafeNum::from(entry.blocks()?) * gpt.info.block_size;
    match end <= total_size.try_into()? {
        true => Ok((SafeNum::from(entry.first) * gpt.info.block_size + offset).try_into()?),
        false => Err(StorageError::OutOfRange),
    }
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
        alignment_scratch_size, AsBlockDevice, TestBlockDevice, TestBlockDeviceBuilder,
    };

    /// Helper function to extract the gpt header from a test block device.
    /// This function lives here and not as a method of TestBlockDevice so that
    /// the Gpt type doesn't have to be exported.
    fn gpt(dev: &mut TestBlockDevice) -> Gpt {
        let (_, gpt) = dev.scratch.split_at_mut(alignment_scratch_size(&mut dev.io).unwrap());
        Gpt::from_existing(gpt).unwrap()
    }

    #[test]
    fn test_new_from_buffer() {
        let mut dev: TestBlockDevice = include_bytes!("../test/gpt_test_1.bin").as_slice().into();
        dev.sync_gpt().unwrap();

        assert_eq!(dev.partition_iter().count(), 2);
        dev.find_partition("boot_a").unwrap();
        dev.find_partition("boot_b").unwrap();
        assert!(dev.find_partition("boot_c").is_err());
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

        assert_eq!(dev.partition_iter().count(), 2);
        dev.find_partition("boot_a").unwrap();
        dev.find_partition("boot_b").unwrap();
        assert!(dev.find_partition("boot_c").is_err());

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

        assert_eq!(dev.partition_iter().count(), 2);
        dev.find_partition("boot_a").unwrap();
        dev.find_partition("boot_b").unwrap();

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
        assert!(dev.find_partition("").is_err());
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
}
