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

use crate::{
    add, div, mul, round_up, sub, to_usize, BlockDevice, Result, StorageError, WriteBuffer,
};
use core::default::Default;
use core::mem::{align_of, size_of};
use crc32fast::Hasher;
use zerocopy::{AsBytes, FromBytes, LayoutVerified};

const GPT_GUID_LEN: usize = 16;
const GPT_NAME_LEN: usize = 36;

#[repr(C, packed)]
#[derive(Debug, Default, Copy, Clone, FromBytes, AsBytes)]
struct GptHeader {
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
        LayoutVerified::<_, GptHeader>::new_from_prefix(bytes).unwrap().0.into_mut()
    }

    /// Update the header crc32 value.
    fn update_crc(&mut self) {
        self.crc32 = 0;
        self.crc32 = crc32(self.as_bytes());
    }
}

/// GptEntry is the partition entry data structure in the GPT.
#[repr(C)]
#[derive(Debug, Copy, Clone, FromBytes, AsBytes)]
pub struct GptEntry {
    pub part_type: [u8; GPT_GUID_LEN],
    pub guid: [u8; GPT_GUID_LEN],
    pub first: u64,
    pub last: u64,
    pub flags: u64,
    pub name: [u16; GPT_NAME_LEN],
}

impl GptEntry {
    /// Return the partition entry size in blocks.
    pub fn blocks(&self) -> Result<usize> {
        add(sub(to_usize(self.last)?, to_usize(self.first)?)?, 1)
    }

    /// Return whether this is a `NULL` entry. The first null entry marks the end of the partition
    /// entries.
    fn is_null(&self) -> bool {
        self.first == 0 && self.last == 0
    }

    /// Decode the partition name into a string. A length N utf16 string can be at most 2N utf8
    /// bytes. Therefore, a safe size of `buffer` is 2*GPT_NAME_LEN = 72.
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
        let mut name_conversion_buffer = [0u8; GPT_NAME_LEN * 2];
        let name = self.name_to_str(&mut name_conversion_buffer).map_err(|_| core::fmt::Error)?;
        write!(f, "partition name: \"{}\", [first, last]: [{}, {}]", name, self.first, self.last)
    }
}

// core::mem::offset_of!(GptHeader, crc32) is unsatble feature and rejected by the compiler in our
// settings. We pre-compute the value here.
const GPT_CRC32_OFFSET: usize = 16;
const GPT_ENTRY_ALIGNMENT: usize = align_of::<GptEntry>();
const GPT_ENTRY_SIZE: usize = size_of::<GptEntry>();
const GPT_MAX_NUM_ENTRIES: usize = 128;
const GPT_MAX_ENTRIES_SIZE: usize = GPT_MAX_NUM_ENTRIES * GPT_ENTRY_SIZE;
const GPT_HEADER_SIZE: usize = size_of::<GptHeader>(); // 92 bytes.
const GPT_HEADER_SIZE_PADDED: usize =
    (GPT_HEADER_SIZE + GPT_ENTRY_ALIGNMENT - 1) / GPT_ENTRY_ALIGNMENT * GPT_ENTRY_ALIGNMENT;
const GPT_MAGIC: u64 = 0x5452415020494645;

enum HeaderType {
    Primary,
    Secondary,
}

/// An object that contains the GPT header/entries information.
pub struct Gpt<'a> {
    valid: bool,
    num_valid_entries: usize,
    max_entries: usize,
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
    /// * `max_entries`: Maximum number of entries allowed. A smaller value gives smaller buffer
    ///   size requirement by `required_buffer_size()`. However GPT headers whose entries_count
    ///   field is greater than this value will be rejected. Note that most tools and OS fix the
    ///   `entries_count` value to the max value 128 regardless of the actual number of partition
    ///   entries used. Thus unless you have full control of GPT generation in your entire system
    ///   where you can always ensure a smaller bound on it, it is recommended to always pass 128.
    ///
    /// * `buffer`: Buffer for creating the object. Must have a size at least
    ///   `Gpt::required_buffer_size(max_entries)`.
    pub fn new_from_buffer(max_entries: usize, buffer: &'a mut [u8]) -> Result<Gpt<'a>> {
        if max_entries > GPT_MAX_NUM_ENTRIES
            || buffer.len() < Self::required_buffer_size(max_entries)?
        {
            return Err(StorageError::InvalidInput);
        }

        let addr_value = buffer.as_ptr() as usize;
        let aligned = &mut buffer[sub(round_up(addr_value, GPT_ENTRY_ALIGNMENT)?, addr_value)?..];
        let entries_size = mul(max_entries, GPT_ENTRY_SIZE)?;
        let (primary, secondary) = aligned.split_at_mut(GPT_HEADER_SIZE_PADDED + entries_size);
        let (primary_header, primary_entries) = primary.split_at_mut(GPT_HEADER_SIZE_PADDED);
        let (secondary_header, secondary_entries) = secondary.split_at_mut(GPT_HEADER_SIZE_PADDED);

        Ok(Self {
            valid: false,
            num_valid_entries: 0,
            max_entries: max_entries,
            primary_header: primary_header,
            primary_entries: primary_entries,
            secondary_header: secondary_header,
            secondary_entries: &mut secondary_entries[..entries_size],
        })
    }

    /// The minimum buffer size needed for `new_from_buffer()`
    pub fn required_buffer_size(max_entries: usize) -> Result<usize> {
        // Add 7 more bytes to accommodate 8-byte alignment.
        let entries_size = mul(max_entries, GPT_ENTRY_SIZE)?;
        add(mul(2, add(GPT_HEADER_SIZE_PADDED, entries_size)?)?, GPT_ENTRY_ALIGNMENT - 1)
    }

    /// Return the list of GPT entries.
    ///
    /// If the object does not contain a valid GPT, the method returns Error.
    pub fn entries(&self) -> Result<&[GptEntry]> {
        self.check_valid()?;
        Ok(&LayoutVerified::<_, [GptEntry]>::new_slice(&self.primary_entries[..])
            .unwrap()
            .into_slice()[..self.num_valid_entries as usize])
    }

    /// Search for a partition entry.
    ///
    /// If partition doesn't exist, the method returns `Ok(None)`.
    ///
    /// If the object does not contain a valid GPT, the method returns Error.
    pub fn find_partition(&self, part: &str) -> Result<Option<&GptEntry>> {
        for entry in self.entries()? {
            let mut name_conversion_buffer = [0u8; GPT_NAME_LEN * 2];
            if entry.name_to_str(&mut name_conversion_buffer)? != part {
                continue;
            }
            return Ok(Some(entry));
        }
        Ok(None)
    }

    /// Check whether the Gpt has been initialized.
    fn check_valid(&self) -> Result<()> {
        match self.valid {
            true => Ok(()),
            false => Err(StorageError::InvalidInput),
        }
    }

    /// Helper function for loading and validating GPT header and entries.
    fn validate_gpt(
        &mut self,
        blk_dev: &mut (impl BlockDevice + ?Sized),
        scratch: &mut [u8],
        header_type: HeaderType,
    ) -> Result<bool> {
        let (header_start, header_bytes, entries) = match header_type {
            HeaderType::Primary => {
                (blk_dev.block_size(), &mut self.primary_header, &mut self.primary_entries)
            }
            HeaderType::Secondary => (
                mul(sub(blk_dev.num_blocks(), 1)?, blk_dev.block_size())?,
                &mut self.secondary_header,
                &mut self.secondary_entries,
            ),
        };
        blk_dev.read(header_start, header_bytes, scratch)?;
        let header = LayoutVerified::<_, GptHeader>::new_from_prefix(&header_bytes[..])
            .unwrap()
            .0
            .into_ref();

        if header.magic != GPT_MAGIC {
            return Ok(false);
        }

        let entries_size = mul(header.entries_count as usize, GPT_ENTRY_SIZE)?;
        let entries_offset = mul(header.entries as usize, blk_dev.block_size())?;
        if header.entries_count as usize > self.max_entries
            || add(entries_size, entries_offset)?
                > mul(sub(blk_dev.num_blocks(), 1)?, blk_dev.block_size())?
        {
            return Ok(false);
        }

        let mut hasher = Hasher::new();
        hasher.update(&header.as_bytes()[..GPT_CRC32_OFFSET]);
        hasher.update(&[0u8; size_of::<u32>()]);
        hasher.update(&header.as_bytes()[GPT_CRC32_OFFSET + size_of::<u32>()..]);
        if hasher.finalize() != header.crc32 {
            return Ok(false);
        }

        // Load the entries
        let out = &mut entries[..entries_size];
        blk_dev.read(entries_offset, out, scratch)?;
        // Validate entries crc32.
        Ok(header.entries_crc == crc32(out))
    }

    /// Load and sync GPT from a block device.
    fn load_and_sync(
        &mut self,
        blk_dev: &mut (impl BlockDevice + ?Sized),
        scratch: &mut [u8],
    ) -> Result<()> {
        self.valid = false;

        let block_size = blk_dev.block_size();
        let total_blocks = blk_dev.num_blocks();

        let primary_header_blk = 1;
        let primary_header_pos = block_size;
        let secondary_header_blk = sub(total_blocks, 1)?;
        let secondary_header_pos = mul(secondary_header_blk, block_size)?;

        // Entries position for restoring.
        let primary_entries_blk = 2;
        let primary_entries_pos = mul(primary_entries_blk, block_size)?;
        let secondary_entries_pos = sub(secondary_header_pos, GPT_MAX_ENTRIES_SIZE)?;
        let secondary_entries_blk = div(secondary_entries_pos, block_size)?;

        let primary_valid = self.validate_gpt(blk_dev, scratch, HeaderType::Primary)?;
        let secondary_valid = self.validate_gpt(blk_dev, scratch, HeaderType::Secondary)?;

        let primary_header = GptHeader::from_bytes(&mut self.primary_header[..]);
        let secondary_header = GptHeader::from_bytes(&mut self.secondary_header[..]);
        if !primary_valid {
            if !secondary_valid {
                return Err(StorageError::NoValidGpt);
            }
            // Restore to primary
            primary_header.as_bytes_mut().clone_from_slice(secondary_header.as_bytes());
            self.primary_entries.clone_from_slice(&self.secondary_entries);
            primary_header.current = primary_header_blk as u64;
            primary_header.backup = secondary_header_blk as u64;
            primary_header.entries = primary_entries_blk as u64;
            primary_header.update_crc();
            blk_dev.write(primary_header_pos, primary_header.as_bytes_mut(), scratch)?;
            blk_dev.write(primary_entries_pos, &mut self.primary_entries[..], scratch)?
        } else if !secondary_valid {
            // Restore to secondary
            secondary_header.as_bytes_mut().clone_from_slice(primary_header.as_bytes());
            self.secondary_entries.clone_from_slice(&self.primary_entries);
            secondary_header.current = secondary_header_blk as u64;
            secondary_header.backup = primary_header_blk as u64;
            secondary_header.entries = secondary_entries_blk as u64;
            secondary_header.update_crc();
            blk_dev.write(secondary_header_pos, secondary_header.as_bytes_mut(), scratch)?;
            blk_dev.write(secondary_entries_pos, &mut self.secondary_entries[..], scratch)?;
        }

        self.valid = true;
        // Calculate actual number of GPT entries by finding the first invalid entry.
        let entries = LayoutVerified::<_, [GptEntry]>::new_slice(&self.primary_entries[..])
            .unwrap()
            .into_slice();
        self.num_valid_entries = match entries.iter().position(|e| e.is_null()) {
            Some(idx) => idx,
            _ => self.max_entries,
        };
        Ok(())
    }
}

/// Wrapper of gpt.load_and_sync(). Library internal helper for BlockDevice::sync_gpt().
pub(crate) fn gpt_sync(
    blk_dev: &mut (impl BlockDevice + ?Sized),
    gpt: &mut Gpt,
    scratch: &mut [u8],
) -> Result<()> {
    gpt.load_and_sync(blk_dev, scratch)
}

/// Check if a relative offset/len into a partition overflows and returns the absolute offset.
fn check_offset(
    blk_dev: &mut (impl BlockDevice + ?Sized),
    entry: &GptEntry,
    offset: usize,
    len: usize,
) -> Result<usize> {
    match add(offset, len)? <= mul(entry.blocks()?, blk_dev.block_size())? {
        true => Ok(add(mul(to_usize(entry.first)?, blk_dev.block_size())?, offset)?),
        false => Err(StorageError::OutOfRange),
    }
}

/// Read GPT partition. Library internal helper for BlockDevice::read_gpt_partition().
pub(crate) fn read_gpt_partition(
    blk_dev: &mut (impl BlockDevice + ?Sized),
    gpt: &Gpt,
    part_name: &str,
    offset: usize,
    out: &mut [u8],
    scratch: &mut [u8],
) -> Result<()> {
    match gpt.find_partition(part_name) {
        Ok(Some(e)) => {
            let abs_offset = check_offset(blk_dev, e, offset, out.len())?;
            blk_dev.read(abs_offset, out, scratch)
        }
        _ => Err(StorageError::NotExist),
    }
}

/// Write GPT partition. Library internal helper for BlockDevice::write_gpt_partition().
pub(crate) fn write_gpt_partition<B>(
    blk_dev: &mut (impl BlockDevice + ?Sized),
    gpt: &Gpt,
    part_name: &str,
    offset: usize,
    mut data: B,
    scratch: &mut [u8],
) -> Result<()>
where
    B: WriteBuffer,
{
    match gpt.find_partition(part_name) {
        Ok(Some(e)) => {
            let abs_offset = check_offset(blk_dev, e, offset, data.data_len()?)?;
            blk_dev.write(abs_offset, data, scratch)
        }
        _ => Err(StorageError::NotExist),
    }
}

fn crc32(data: &[u8]) -> u32 {
    let mut hasher = Hasher::new();
    hasher.update(data);
    hasher.finalize()
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::required_scratch_size;
    use crate::test::TestBlockDevice;

    struct GptBlockDevice {
        pub blk: TestBlockDevice,
        pub num_writes: usize,
    }

    impl BlockDevice for GptBlockDevice {
        fn block_size(&mut self) -> usize {
            self.blk.block_size()
        }

        fn num_blocks(&mut self) -> usize {
            self.blk.num_blocks()
        }

        fn alignment(&mut self) -> usize {
            self.blk.alignment()
        }

        fn read_blocks(&mut self, blk_offset: usize, out: &mut [u8]) -> bool {
            self.blk.read_blocks(blk_offset, out)
        }

        fn write_blocks(&mut self, blk_offset: usize, data: &[u8]) -> bool {
            self.num_writes += 1;
            self.blk.write_blocks(blk_offset, data)
        }
    }

    // Helper to create a block device and a scratch
    fn gpt_device(data: &[u8]) -> (GptBlockDevice, Vec<u8>) {
        let mut blk_dev =
            GptBlockDevice { blk: TestBlockDevice::new_with_data(1, 512, data), num_writes: 0 };
        let scratch = vec![0u8; required_scratch_size(&mut blk_dev.blk).unwrap()];
        (blk_dev, scratch)
    }

    #[test]
    fn test_new_from_buffer() {
        let disk = include_bytes!("../test/gpt_test.bin").to_vec();
        let (mut dev, mut scratch) = gpt_device(&disk);

        let mut buffer = vec![0u8; Gpt::required_buffer_size(128).unwrap()];
        let mut gpt = Gpt::new_from_buffer(128, &mut buffer[..]).unwrap();
        dev.sync_gpt(&mut gpt, &mut scratch).unwrap();

        assert_eq!(gpt.entries().unwrap().len(), 2);
        gpt.find_partition("boot_a").unwrap().unwrap();
        gpt.find_partition("boot_b").unwrap().unwrap();
        assert!(gpt.find_partition("boot_c").unwrap().is_none());
    }

    #[test]
    fn test_new_from_buffer_too_small() {
        let mut buffer = vec![0u8; Gpt::required_buffer_size(128).unwrap() - 1];
        assert!(Gpt::new_from_buffer(128, &mut buffer[..]).is_err());
    }

    #[test]
    fn test_new_from_buffer_too_many_entries() {
        let mut buffer = vec![0u8; Gpt::required_buffer_size(129).unwrap()];
        assert!(Gpt::new_from_buffer(129, &mut buffer[..]).is_err());
    }

    #[test]
    fn test_load_gpt_primary() {
        let disk = include_bytes!("../test/gpt_test.bin").to_vec();
        let (mut dev, mut scratch) = gpt_device(&disk);

        // Corrupt secondary.
        dev.blk.storage[disk.len() - 512..].fill(0);
        let mut buffer = vec![0u8; Gpt::required_buffer_size(128).unwrap()];
        let mut gpt = Gpt::new_from_buffer(128, &mut buffer[..]).unwrap();
        dev.sync_gpt(&mut gpt, &mut scratch).unwrap();

        assert_eq!(gpt.entries().unwrap().len(), 2);
        gpt.find_partition("boot_a").unwrap().unwrap();
        gpt.find_partition("boot_b").unwrap().unwrap();
        assert!(gpt.find_partition("boot_c").unwrap().is_none());

        // Check that secondary is restored
        assert_eq!(dev.blk.storage, disk);
    }

    #[test]
    fn test_load_gpt_secondary() {
        let disk = include_bytes!("../test/gpt_test.bin").to_vec();
        let (mut dev, mut scratch) = gpt_device(&disk);

        // Corrupt primary.
        dev.blk.storage[512..1024].fill(0);
        let mut buffer = vec![0u8; Gpt::required_buffer_size(128).unwrap()];
        let mut gpt = Gpt::new_from_buffer(128, &mut buffer[..]).unwrap();

        dev.sync_gpt(&mut gpt, &mut scratch).unwrap();
        assert_eq!(gpt.entries().unwrap().len(), 2);
        gpt.find_partition("boot_a").unwrap().unwrap();
        gpt.find_partition("boot_b").unwrap().unwrap();

        // Check that primary is restored
        assert_eq!(dev.blk.storage, disk);
    }

    #[test]
    fn test_good_gpt_no_repair_write() {
        let mut buffer = vec![0u8; Gpt::required_buffer_size(128).unwrap()];
        let mut gpt = Gpt::new_from_buffer(128, &mut buffer[..]).unwrap();
        let disk = include_bytes!("../test/gpt_test.bin").to_vec();
        let (mut dev, mut scratch) = gpt_device(&disk);
        dev.sync_gpt(&mut gpt, &mut scratch).unwrap();
        assert_eq!(dev.num_writes, 0);
    }

    #[test]
    fn test_load_gpt_incorrect_magic() {
        let disk = include_bytes!("../test/gpt_test.bin").to_vec();
        let (mut dev, mut scratch) = gpt_device(&disk);
        let mut buffer = vec![0u8; Gpt::required_buffer_size(128).unwrap()];
        let mut gpt = Gpt::new_from_buffer(128, &mut buffer[..]).unwrap();
        dev.sync_gpt(&mut gpt, &mut scratch).unwrap();

        let primary_header = &mut gpt.primary_header[..GPT_HEADER_SIZE];
        let gpt_header = GptHeader::from_bytes(primary_header);
        gpt_header.magic = 0x123456;
        gpt_header.update_crc();
        dev.blk.storage[512..512 + primary_header.len()].clone_from_slice(&primary_header);

        dev.sync_gpt(&mut gpt, &mut scratch).unwrap();

        // Check that incorrect magic header is restored
        assert_eq!(dev.blk.storage, disk);
    }

    #[test]
    fn test_load_gpt_exceeds_max_entries() {
        let disk = include_bytes!("../test/gpt_test.bin").to_vec();
        let (mut dev, mut scratch) = gpt_device(&disk);
        let mut buffer = vec![0u8; Gpt::required_buffer_size(127).unwrap()];
        let mut gpt = Gpt::new_from_buffer(127, &mut buffer[..]).unwrap();
        assert!(dev.sync_gpt(&mut gpt, &mut scratch).is_err());
    }

    #[test]
    fn test_load_gpt_non_max_entries() {
        // Create a header with non-max entries_count
        let disk = include_bytes!("../test/gpt_test.bin").to_vec();
        let (mut dev, mut scratch) = gpt_device(&disk);
        let mut buffer = vec![0u8; Gpt::required_buffer_size(128).unwrap()];
        let mut gpt = Gpt::new_from_buffer(128, &mut buffer[..]).unwrap();
        dev.sync_gpt(&mut gpt, &mut scratch).unwrap();

        let primary_header = &mut gpt.primary_header[..GPT_HEADER_SIZE];
        let gpt_header = GptHeader::from_bytes(primary_header);
        gpt_header.entries_count = 2;
        // Update entries crc32
        gpt_header.entries_crc = crc32(&gpt.primary_entries[..2 * GPT_ENTRY_SIZE]);
        gpt_header.update_crc();
        // Update to primary.
        dev.blk.storage[512..512 + primary_header.len()].clone_from_slice(primary_header);

        // Reload.
        gpt = Gpt::new_from_buffer(2, &mut buffer[..]).unwrap();
        // Corrupt secondary. Sync ok
        dev.blk.storage[disk.len() - 512..].fill(0);
        dev.sync_gpt(&mut gpt, &mut scratch).unwrap();

        // Corrup primary. Sync ok
        dev.blk.storage[512..1024].fill(0);
        dev.sync_gpt(&mut gpt, &mut scratch).unwrap();
    }

    #[test]
    fn test_uninitialized_gpt() {
        let mut buffer = vec![0u8; Gpt::required_buffer_size(128).unwrap()];
        let mut gpt = Gpt::new_from_buffer(128, &mut buffer[..]).unwrap();

        // Load a good GPT first.
        {
            let disk = include_bytes!("../test/gpt_test.bin").to_vec();
            let (mut dev, mut scratch) = gpt_device(&disk);
            dev.sync_gpt(&mut gpt, &mut scratch).unwrap();
        }

        // Load a bad GPT. Validate that the valid state is reset.
        {
            let (mut dev, mut scratch) = gpt_device(&vec![0u8; 64 * 1024]);
            assert!(dev.sync_gpt(&mut gpt, &mut scratch).is_err());
            assert!(gpt.entries().is_err());
            assert!(gpt.find_partition("").is_err());
        }
    }

    #[test]
    fn test_gpt_read() {
        let (mut dev, mut scratch) = gpt_device(include_bytes!("../test/gpt_test.bin"));
        let mut buffer = vec![0u8; Gpt::required_buffer_size(128).unwrap()];
        let mut gpt = Gpt::new_from_buffer(128, &mut buffer[..]).unwrap();
        dev.sync_gpt(&mut gpt, &mut scratch).unwrap();

        let expect_boot_a = include_bytes!("../test/boot_a.bin");
        let expect_boot_b = include_bytes!("../test/boot_b.bin");

        let mut actual_boot_a = vec![0u8; expect_boot_a.len()];
        let mut actual_boot_b = vec![0u8; expect_boot_b.len()];

        dev.read_gpt_partition(&gpt, "boot_a", 0, &mut actual_boot_a, &mut scratch).unwrap();
        assert_eq!(expect_boot_a.to_vec(), actual_boot_a);
        // partial read
        actual_boot_a = actual_boot_a[1..].to_vec();
        dev.read_gpt_partition(&gpt, "boot_a", 1, &mut actual_boot_a, &mut scratch).unwrap();
        assert_eq!(expect_boot_a[1..].to_vec(), actual_boot_a);

        dev.read_gpt_partition(&gpt, "boot_b", 0, &mut actual_boot_b, &mut scratch).unwrap();
        assert_eq!(expect_boot_b.to_vec(), actual_boot_b);
        // partial read
        actual_boot_b = actual_boot_b[1..].to_vec();
        dev.read_gpt_partition(&gpt, "boot_b", 1, &mut actual_boot_b, &mut scratch).unwrap();
        assert_eq!(expect_boot_b[1..].to_vec(), actual_boot_b);
    }

    #[test]
    fn test_gpt_write() {
        let (mut dev, mut scratch) = gpt_device(include_bytes!("../test/gpt_test.bin"));
        let mut buffer = vec![0u8; Gpt::required_buffer_size(128).unwrap()];
        let mut gpt = Gpt::new_from_buffer(128, &mut buffer[..]).unwrap();
        dev.sync_gpt(&mut gpt, &mut scratch).unwrap();

        let mut expect_boot_a = include_bytes!("../test/boot_a.bin").to_vec();
        expect_boot_a.reverse();
        let mut expect_boot_b = include_bytes!("../test/boot_b.bin").to_vec();
        expect_boot_b.reverse();

        let mut actual_boot_a = vec![0u8; expect_boot_a.len()];
        let mut actual_boot_b = vec![0u8; expect_boot_b.len()];

        // "boot_a" partition
        // Mutable version
        dev.write_gpt_partition(&gpt, "boot_a", 0, &mut expect_boot_a[..], &mut scratch).unwrap();
        dev.read_gpt_partition(&gpt, "boot_a", 0, &mut actual_boot_a, &mut scratch).unwrap();
        assert_eq!(expect_boot_a.to_vec(), actual_boot_a);
        // Mutable version, partial write.
        dev.write_gpt_partition(&gpt, "boot_a", 1, &expect_boot_a[1..], &mut scratch).unwrap();
        dev.read_gpt_partition(&gpt, "boot_a", 1, &mut actual_boot_a[1..], &mut scratch).unwrap();
        assert_eq!(expect_boot_a[1..], actual_boot_a[1..]);
        // Immutable version
        dev.write_gpt_partition(&gpt, "boot_a", 0, &expect_boot_a[..] as &[u8], &mut scratch)
            .unwrap();
        dev.read_gpt_partition(&gpt, "boot_a", 0, &mut actual_boot_a, &mut scratch).unwrap();
        assert_eq!(expect_boot_a.to_vec(), actual_boot_a);
        // Immutable version, partial write.
        dev.write_gpt_partition(&gpt, "boot_a", 1, &expect_boot_a[1..] as &[u8], &mut scratch)
            .unwrap();
        dev.read_gpt_partition(&gpt, "boot_a", 1, &mut actual_boot_a[1..], &mut scratch).unwrap();
        assert_eq!(expect_boot_a[1..], actual_boot_a[1..]);

        // "boot_b" partition
        // Mutable version
        dev.write_gpt_partition(&gpt, "boot_b", 0, &mut expect_boot_b[..], &mut scratch).unwrap();
        dev.read_gpt_partition(&gpt, "boot_b", 0, &mut actual_boot_b, &mut scratch).unwrap();
        assert_eq!(expect_boot_b.to_vec(), actual_boot_b);
        // Mutable version, partial write.
        dev.write_gpt_partition(&gpt, "boot_b", 1, &expect_boot_b[1..], &mut scratch).unwrap();
        dev.read_gpt_partition(&gpt, "boot_b", 1, &mut actual_boot_b[1..], &mut scratch).unwrap();
        assert_eq!(expect_boot_b[1..], actual_boot_b[1..]);
        // Immutable version
        dev.write_gpt_partition(&gpt, "boot_b", 0, &expect_boot_b[..] as &[u8], &mut scratch)
            .unwrap();
        dev.read_gpt_partition(&gpt, "boot_b", 0, &mut actual_boot_b, &mut scratch).unwrap();
        assert_eq!(expect_boot_b.to_vec(), actual_boot_b);
        // Immutable version, partial write.
        dev.write_gpt_partition(&gpt, "boot_b", 1, &expect_boot_b[1..] as &[u8], &mut scratch)
            .unwrap();
        dev.read_gpt_partition(&gpt, "boot_b", 1, &mut actual_boot_b[1..], &mut scratch).unwrap();
        assert_eq!(expect_boot_b[1..], actual_boot_b[1..]);
    }

    #[test]
    fn test_gpt_rw_overflow() {
        let (mut dev, mut scratch) = gpt_device(include_bytes!("../test/gpt_test.bin"));
        let mut buffer = vec![0u8; Gpt::required_buffer_size(128).unwrap()];
        let mut gpt = Gpt::new_from_buffer(128, &mut buffer[..]).unwrap();
        dev.sync_gpt(&mut gpt, &mut scratch).unwrap();

        let mut boot_a = [0u8; include_bytes!("../test/boot_a.bin").len()];
        let mut boot_b = [0u8; include_bytes!("../test/boot_b.bin").len()];

        assert!(dev.read_gpt_partition(&gpt, "boot_a", 1, &mut boot_a, &mut scratch).is_err());
        assert!(dev.write_gpt_partition(&gpt, "boot_a", 1, &mut boot_a[..], &mut scratch).is_err());
        assert!(dev.write_gpt_partition(&gpt, "boot_a", 1, &boot_a[..], &mut scratch).is_err());

        assert!(dev.read_gpt_partition(&gpt, "boot_b", 1, &mut boot_b, &mut scratch).is_err());
        assert!(dev.write_gpt_partition(&gpt, "boot_b", 1, &mut boot_b[..], &mut scratch).is_err());
        assert!(dev.write_gpt_partition(&gpt, "boot_b", 1, &boot_b[..], &mut scratch).is_err());
    }
}
