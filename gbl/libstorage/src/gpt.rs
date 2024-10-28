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
use liberror::{Error, GptError};
use libutils::aligned_subslice;
use safemath::SafeNum;
use zerocopy::{AsBytes, FromBytes, FromZeroes, Ref};

/// Number of bytes in GUID.
pub const GPT_GUID_LEN: usize = 16;
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

    /// Computes the actual crc32 value.
    fn calculate_header_crc(&self) -> u32 {
        let mut hasher = Hasher::new();
        hasher.update(&self.as_bytes()[..GPT_CRC32_OFFSET]);
        hasher.update(&[0u8; size_of::<u32>()]);
        hasher.update(&self.as_bytes()[GPT_CRC32_OFFSET + size_of::<u32>()..]);
        hasher.finalize()
    }

    /// Update the header crc32 value.
    pub fn update_crc(&mut self) {
        self.crc32 = self.calculate_header_crc();
    }

    /// Updates entries and header crc according to the given entries buffer.
    #[cfg(test)]
    fn update_entries_crc(&mut self, entries: &[u8]) {
        let size = SafeNum::from(self.entries_count) * self.entries_size;
        self.entries_crc = crc32(&entries[..size.try_into().unwrap()]);
        self.update_crc();
    }
}

/// Checks a header against a block device.
///
/// # Args
///
/// * `io`: An implementation of [BlockIoAsync],
/// * `max_allowed_entries`: The maximum allowed number of GPT entries on this block device that was
///   passed to `GptCache::from_uninit()` when creating `GptCache`. `GptCache` only uses enough
///   buffer for holding `max_allowed_entries` number of entry to reduce memory usage. If the actual
///   entry count is greater than this value, the API will error out.
/// * `header`: The GPT header to verify.
/// * `is_primary`: If the header is a primary header.
fn check_header(
    io: &mut impl BlockIoAsync,
    max_allowed_entries: u64,
    header: &GptHeader,
    is_primary: bool,
) -> Result<()> {
    let num_blks = SafeNum::from(io.info().num_blocks);
    let blk_sz = io.info().block_size;

    // GPT spec requires that at least 128 entries worth of space be reserved.
    let min_reserved_entries_blk =
        SafeNum::from(GPT_MAX_NUM_ENTRIES) * size_of::<GptEntry>() / blk_sz;
    // Minimum space needed: 2 * (header + entries) + MBR.
    let min_disk_blks: u64 = ((min_reserved_entries_blk + 1) * 2 + 1).try_into().unwrap();
    if min_disk_blks > u64::try_from(num_blks).unwrap() {
        return Err(Error::GptError(GptError::DiskTooSmall));
    }

    if header.magic != GPT_MAGIC {
        return Err(Error::GptError(GptError::IncorrectMagic(header.magic)));
    }

    if header.calculate_header_crc() != header.crc32 {
        return Err(Error::GptError(GptError::IncorrectHeaderCrc));
    }

    if header.size != size_of::<GptHeader>().try_into().unwrap() {
        return Err(Error::GptError(GptError::UnexpectedHeaderSize {
            actual: header.size,
            expect: size_of::<GptHeader>(),
        }));
    }

    if header.entries_size != size_of::<GptEntry>().try_into().unwrap() {
        return Err(Error::GptError(GptError::UnexpectedEntrySize {
            actual: header.entries_size,
            expect: size_of::<GptEntry>(),
        }));
    }

    // Checks first/last usable block.
    //
    // Assuming maximum range where partition entries are adjacent to GPT headers.
    //
    // Should leave a minimum space for MBR + primary header + primary entries before.
    let min_first: u64 = (min_reserved_entries_blk + 2).try_into().unwrap();
    // Should leave a minimum space for secondary header + secondary entries space after.
    let max_last: u64 = (num_blks - 1 - min_reserved_entries_blk - 1).try_into().unwrap();
    if header.first > header.last + 1 || header.first < min_first || header.last > max_last {
        return Err(Error::GptError(GptError::InvalidFirstLastUsableBlock {
            first: header.first,
            last: header.last,
            range: (min_first, max_last),
        }));
    }

    // Checks entries starting block.
    if is_primary {
        // For primary header, entries must be before first usable block and can hold up to
        // `GPT_MAX_NUM_ENTRIES` entries
        let right: u64 =
            (SafeNum::from(header.first) - min_reserved_entries_blk).try_into().unwrap();
        if !(header.entries >= 2 && header.entries <= right) {
            return Err(Error::GptError(GptError::InvalidPrimaryEntriesStart {
                value: header.entries,
                expect_range: (2, right),
            }));
        }
    } else {
        // For secondary header, entries must be after last usable block and can hold up to
        // `GPT_MAX_NUM_ENTRIES` entries.
        if !(header.entries > header.last && header.entries <= max_last + 1) {
            return Err(Error::GptError(GptError::InvalidSecondaryEntriesStart {
                value: header.entries,
                expect_range: (header.last + 1, max_last + 1),
            }));
        }
    }

    if header.entries_count > max_allowed_entries.try_into().unwrap() {
        return Err(Error::GptError(GptError::NumberOfEntriesOverflow {
            entries: header.entries_count,
            max_allowed: max_allowed_entries,
        }));
    }

    Ok(())
}

/// Verifies the given entries against a verifed GPT header.
///
/// # Args
///
/// * `header`: The verified GPT header corresponding to the entries.
/// * `entries`: The buffer containing the entries.
fn check_entries(header: &GptHeader, entries: &[u8]) -> Result<()> {
    // Checks entries CRC.
    assert!(header.entries_count <= GPT_MAX_NUM_ENTRIES.try_into().unwrap());
    let entries_size: usize =
        (SafeNum::from(header.entries_count) * GPT_ENTRY_SIZE).try_into().unwrap();
    let entries = entries.get(..entries_size).ok_or(Error::GptError(GptError::EntriesTruncated))?;
    if header.entries_crc != crc32(entries) {
        return Err(Error::GptError(GptError::IncorrectEntriesCrc));
    }

    // Checks each entry.
    let entries = Ref::<_, [GptEntry]>::new_slice(entries)
        .ok_or(Error::GptError(GptError::EntriesTruncated))?
        .into_slice();
    let entries = &entries[..header.entries_count.try_into().unwrap()];
    for (idx, ele) in entries.iter().take_while(|v| !v.is_null()).enumerate() {
        // Error information uses 1-base partition index.
        let idx = idx.checked_add(1).unwrap();
        let (first, last) = (ele.first, ele.last);
        if first > last + 1 || last > header.last || first < header.first {
            return Err(Error::GptError(GptError::InvalidPartitionRange {
                idx,
                part_range: (first, last),
                usable_range: (header.first, header.last),
            }));
        } else if ele.part_type == [0u8; GPT_GUID_LEN] {
            return Err(Error::GptError(GptError::ZeroPartitionTypeGUID { idx }));
        } else if ele.guid == [0u8; GPT_GUID_LEN] {
            return Err(Error::GptError(GptError::ZeroPartitionUniqueGUID { idx }));
        }
    }
    Ok(())
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
const GPT_CRC32_OFFSET: usize = 16;
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

/// Contains result of GPT syncing/restoration.
#[derive(Copy, Clone, PartialEq, Debug, Default)]
pub enum GptSyncResult {
    /// Both primary and secondary GPT are valid.
    #[default]
    BothValid,
    /// Primary GPT is invalid and restored.
    PrimaryRestored(Error),
    /// Secondary GPT is invalid and restored.
    SecondaryRestored(Error),
    /// Neither primary or secondary GPT is valid.
    NoValidGpt {
        /// Primary GPT verify error.
        primary: Error,
        /// Secondary GPT verify error.
        secondary: Error,
    },
}

impl GptSyncResult {
    /// Combined into a result
    pub fn res(&self) -> Result<()> {
        match self {
            Self::NoValidGpt { primary: e, .. } => Err(*e),
            _ => Ok(()),
        }
    }
}

impl core::fmt::Display for GptSyncResult {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::BothValid => write!(f, "Found valid GPT."),
            Self::PrimaryRestored(e) => write!(f, "Primary GPT restored due to {e:?}."),
            Self::SecondaryRestored(e) => write!(f, "Secondary GPT restored due to {e:?}."),
            Self::NoValidGpt { primary, secondary } => {
                write!(f, "No valid GPT. primary: {primary:?}, secondary: {secondary:?}.")
            }
        }
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
    async fn load_and_validate_gpt(
        &mut self,
        io: &mut impl BlockIoAsync,
        scratch: &mut [u8],
        hdr_type: HeaderType,
    ) -> Result<()> {
        let (header_start, header_bytes, entries) = match hdr_type {
            HeaderType::Primary => {
                (io.info().block_size.into(), &mut self.primary_header, &mut self.primary_entries)
            }
            HeaderType::Secondary => (
                (SafeNum::from(io.info().num_blocks) - 1) * io.info().block_size,
                &mut self.secondary_header,
                &mut self.secondary_entries,
            ),
        };

        // Loads the header
        read_async(io, header_start.try_into()?, header_bytes, scratch).await?;
        let header =
            Ref::<_, GptHeader>::new_from_prefix(header_bytes.as_bytes()).unwrap().0.into_ref();
        // Checks header.
        check_header(io, self.info.max_entries, &header, matches!(hdr_type, HeaderType::Primary))?;
        // Loads the entries.
        let entries_size = SafeNum::from(header.entries_count) * GPT_ENTRY_SIZE;
        let entries_offset = SafeNum::from(header.entries) * io.info().block_size;
        let out = &mut entries[..entries_size.try_into().unwrap()];
        read_async(io, entries_offset.try_into().unwrap(), out, scratch).await?;
        // Checks entries.
        check_entries(&header, entries)
    }

    /// Loads and syncs GPT from a block device.
    ///
    /// * Returns Ok(sync_result) if disk IO is successful, where `sync_result` contains the GPT
    ///   verification and restoration result,
    /// * Returns Err() if disk IO encounters error.
    pub(crate) async fn load_and_sync(
        &mut self,
        io: &mut impl BlockIoAsync,
        scratch: &mut [u8],
    ) -> Result<GptSyncResult> {
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
        let primary_res = self.load_and_validate_gpt(io, scratch, HeaderType::Primary).await;
        let secondary_res = self.load_and_validate_gpt(io, scratch, HeaderType::Secondary).await;

        let primary_header = GptHeader::from_bytes(self.primary_header);
        let secondary_header = GptHeader::from_bytes(self.secondary_header);
        let sync_res = match (primary_res, secondary_res) {
            (Err(primary), Err(secondary)) => GptSyncResult::NoValidGpt { primary, secondary },
            (Err(e), Ok(())) => {
                // Restores to primary
                primary_header.as_bytes_mut().clone_from_slice(secondary_header.as_bytes());
                self.primary_entries.clone_from_slice(&self.secondary_entries);
                primary_header.current = primary_header_blk;
                primary_header.backup = secondary_header_blk.try_into()?;
                primary_header.entries = primary_entries_blk;
                primary_header.update_crc();

                write_async(io, primary_header_pos, primary_header.as_bytes_mut(), scratch).await?;
                write_async(io, primary_entries_pos.try_into()?, self.primary_entries, scratch)
                    .await?;
                GptSyncResult::PrimaryRestored(e)
            }
            (Ok(()), Err(e)) => {
                // Restores to secondary
                let secondary_entries_pos = secondary_header_pos
                    - SafeNum::from(self.info.max_entries) * primary_header.entries_size;
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
                GptSyncResult::SecondaryRestored(e)
            }
            _ => GptSyncResult::BothValid,
        };

        // Calculates actual number of GPT entries by finding the first invalid entry.
        let entries =
            Ref::<_, [GptEntry]>::new_slice(&self.primary_entries[..]).unwrap().into_slice();
        self.info.num_valid_entries =
            NonZeroU64::new(match entries.iter().position(|e| e.is_null()) {
                Some(idx) => idx as u64,
                _ => self.info.max_entries,
            });
        self.info.block_size = block_size;
        Ok(sync_res)
    }
}

/// Updates GPT on a block device.
pub(crate) async fn update_gpt(
    io: &mut impl BlockIoAsync,
    scratch: &mut [u8],
    mbr_primary: &mut [u8],
    gpt_cache: &mut GptCache<'_>,
) -> Result<()> {
    let blk_sz: usize = io.info().block_size.try_into()?;
    let header = mbr_primary
        .get(blk_sz..)
        .map(|v| v.get(..blk_sz))
        .flatten()
        .ok_or(Error::BufferTooSmall(Some(blk_sz * 2)))?;
    let header = Ref::<_, GptHeader>::new_from_prefix(header).unwrap().0.into_ref();
    check_header(io, gpt_cache.info.max_entries, &header, true)?;
    let entries_off: usize = (SafeNum::from(blk_sz) * header.entries).try_into()?;
    let entries_size: usize =
        (SafeNum::from(header.entries_count) * header.entries_size).try_into().unwrap();
    let entries = mbr_primary
        .get(entries_off..)
        .map(|v| v.get(..entries_size))
        .flatten()
        .ok_or(Error::BufferTooSmall(Some(entries_off + entries_size)))?;
    check_entries(&header, entries)?;
    write_async(io, 0, mbr_primary, scratch).await?;
    gpt_cache.load_and_sync(io, scratch).await?.res()
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
    use gbl_async::block_on;
    use gbl_storage_testlib::{
        alignment_scratch_size, AsBlockDevice, BackingStore, GptSyncResult, TestBlockDevice,
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

    /// A helper for testing restoration of invalid primary/secondary header modified by caller.
    fn test_gpt_sync_restore<'a>(
        modify_primary: impl FnOnce(&mut GptHeader, Ref<&mut [u8], [GptEntry]>),
        modify_secondary: impl FnOnce(&mut GptHeader, Ref<&mut [u8], [GptEntry]>),
        expect_primary_err: Error,
        expect_secondary_err: Error,
    ) {
        let disk_orig = include_bytes!("../test/gpt_test_1.bin");

        // Restores from secondary to primary.
        let mut disk = disk_orig.to_vec();
        let (header, entries) = (&mut disk[512..]).split_at_mut(512);
        let mut header = GptHeader::from_bytes(header);
        modify_primary(&mut header, Ref::<_, [GptEntry]>::new_slice(entries).unwrap());
        let mut dev = TestBlockDeviceBuilder::new().set_data(&disk).build();
        let (mut dev, mut gpt) = dev.as_gpt_dev().into_blk_and_gpt();
        assert_ne!(dev.io().storage, disk_orig);
        let sync_res = block_on(dev.sync_gpt(&mut gpt)).unwrap();
        assert_eq!(sync_res, GptSyncResult::PrimaryRestored(expect_primary_err));
        assert_eq!(dev.io().storage, disk_orig);

        // Restores from primary to secondary.
        let mut disk = disk_orig.to_vec();
        let (entries, header) = (&mut disk[512..]).split_last_chunk_mut::<512>().unwrap();
        let (_, entries) = entries.split_last_chunk_mut::<{ 512 * 32 }>().unwrap();
        let mut header = GptHeader::from_bytes(&mut header[..]);
        modify_secondary(&mut header, Ref::<_, [GptEntry]>::new_slice(&mut entries[..]).unwrap());
        let mut dev = TestBlockDeviceBuilder::new().set_data(&disk).build();
        let (mut dev, mut gpt) = dev.as_gpt_dev().into_blk_and_gpt();
        assert_ne!(dev.io().storage, disk_orig);
        let sync_res = block_on(dev.sync_gpt(&mut gpt)).unwrap();
        assert_eq!(sync_res, GptSyncResult::SecondaryRestored(expect_secondary_err));
        assert_eq!(dev.io().storage, disk_orig);
    }

    #[test]
    fn test_sync_gpt_incorrect_magic() {
        fn modify(hdr: &mut GptHeader, _: Ref<&mut [u8], [GptEntry]>) {
            hdr.magic = 0x123456;
            hdr.update_crc();
        }
        let err = Error::GptError(GptError::IncorrectMagic(0x123456));
        test_gpt_sync_restore(modify, modify, err, err);
    }

    #[test]
    fn test_sync_gpt_incorrect_crc() {
        fn modify(hdr: &mut GptHeader, _: Ref<&mut [u8], [GptEntry]>) {
            hdr.crc32 = !hdr.crc32;
        }
        let err = Error::GptError(GptError::IncorrectHeaderCrc);
        test_gpt_sync_restore(modify, modify, err, err);
    }

    #[test]
    fn test_sync_gpt_unexpected_header_size() {
        fn modify(hdr: &mut GptHeader, _: Ref<&mut [u8], [GptEntry]>) {
            hdr.size += 1;
            hdr.update_crc();
        }
        let err = Error::GptError(GptError::UnexpectedHeaderSize { actual: 93, expect: 92 });
        test_gpt_sync_restore(modify, modify, err, err);
    }

    #[test]
    fn test_sync_gpt_unexpected_entry_size() {
        fn modify(hdr: &mut GptHeader, _: Ref<&mut [u8], [GptEntry]>) {
            hdr.entries_size += 1;
            hdr.update_crc();
        }
        let err = Error::GptError(GptError::UnexpectedEntrySize { actual: 129, expect: 128 });
        test_gpt_sync_restore(modify, modify, err, err);
    }

    #[test]
    fn test_sync_gpt_first_usable_gt_last() {
        fn modify(hdr: &mut GptHeader, _: Ref<&mut [u8], [GptEntry]>) {
            hdr.first = hdr.last;
            hdr.last = hdr.first - 2;
            hdr.update_crc();
        }
        let err = Error::GptError(GptError::InvalidFirstLastUsableBlock {
            first: 94,
            last: 92,
            range: (34, 94),
        });
        test_gpt_sync_restore(modify, modify, err, err);
    }

    #[test]
    fn test_sync_gpt_first_usable_out_of_range() {
        fn modify(hdr: &mut GptHeader, _: Ref<&mut [u8], [GptEntry]>) {
            hdr.first = 33;
            hdr.update_crc();
        }
        let err = Error::GptError(GptError::InvalidFirstLastUsableBlock {
            first: 33,
            last: 94,
            range: (34, 94),
        });
        test_gpt_sync_restore(modify, modify, err, err);
    }

    #[test]
    fn test_sync_gpt_last_usable_out_of_range() {
        fn modify(hdr: &mut GptHeader, _: Ref<&mut [u8], [GptEntry]>) {
            hdr.last += 1;
            hdr.update_crc();
        }
        let err = Error::GptError(GptError::InvalidFirstLastUsableBlock {
            first: 34,
            last: 95,
            range: (34, 94),
        });
        test_gpt_sync_restore(modify, modify, err, err);
    }

    #[test]
    fn test_sync_gpt_primary_entries_out_of_range() {
        test_gpt_sync_restore(
            |hdr, _| {
                hdr.entries = 1;
                hdr.update_crc();
            },
            |hdr, _| {
                hdr.entries = hdr.last;
                hdr.update_crc();
            },
            Error::GptError(GptError::InvalidPrimaryEntriesStart {
                value: 1,
                expect_range: (2, 2),
            }),
            Error::GptError(GptError::InvalidSecondaryEntriesStart {
                value: 94,
                expect_range: (95, 95),
            }),
        );
    }

    #[test]
    fn test_sync_gpt_incorrect_entry_crc() {
        fn modify(hdr: &mut GptHeader, _: Ref<&mut [u8], [GptEntry]>) {
            hdr.entries_crc = !hdr.entries_crc;
            hdr.update_crc();
        }
        let err = Error::GptError(GptError::IncorrectEntriesCrc);
        test_gpt_sync_restore(modify, modify, err, err);
    }

    #[test]
    fn test_sync_gpt_partition_range_overflow() {
        fn modify(hdr: &mut GptHeader, mut entries: Ref<&mut [u8], [GptEntry]>) {
            entries[1].last = hdr.last + 1;
            hdr.update_entries_crc(entries.as_bytes());
        }
        let err = Error::GptError(GptError::InvalidPartitionRange {
            idx: 2,
            part_range: (50, 95),
            usable_range: (34, 94),
        });
        test_gpt_sync_restore(modify, modify, err, err);
    }

    #[test]
    fn test_sync_gpt_invalid_partition_range() {
        fn modify(hdr: &mut GptHeader, mut entries: Ref<&mut [u8], [GptEntry]>) {
            entries[1].first = entries[1].last;
            entries[1].last = entries[1].first - 2;
            hdr.update_entries_crc(entries.as_bytes());
        }
        let err = Error::GptError(GptError::InvalidPartitionRange {
            idx: 2,
            part_range: (73, 71),
            usable_range: (34, 94),
        });
        test_gpt_sync_restore(modify, modify, err, err);
    }

    #[test]
    fn test_sync_gpt_zero_partition_type_guid() {
        fn modify(hdr: &mut GptHeader, mut entries: Ref<&mut [u8], [GptEntry]>) {
            entries[1].part_type = [0u8; GPT_GUID_LEN];
            hdr.update_entries_crc(entries.as_bytes());
        }
        let err = Error::GptError(GptError::ZeroPartitionTypeGUID { idx: 2 });
        test_gpt_sync_restore(modify, modify, err, err);
    }

    #[test]
    fn test_sync_gpt_zero_partition_unique_guid() {
        fn modify(hdr: &mut GptHeader, mut entries: Ref<&mut [u8], [GptEntry]>) {
            entries[1].guid = [0u8; GPT_GUID_LEN];
            hdr.update_entries_crc(entries.as_bytes());
        }
        let err = Error::GptError(GptError::ZeroPartitionUniqueGUID { idx: 2 });
        test_gpt_sync_restore(modify, modify, err, err);
    }

    #[test]
    fn test_load_gpt_disk_too_small() {
        let disk_orig = include_bytes!("../test/gpt_test_1.bin");
        let mut disk = disk_orig.to_vec();
        // Resizes so that it's not enough to hold a full 128 maximum entries.
        // MBR + (header + entries) * 2 - 1
        disk.resize((1 + (32 + 1) * 2 - 1) * 512, 0);
        let mut dev = TestBlockDeviceBuilder::new().set_data(&disk).build();
        let (mut dev, mut gpt) = dev.as_gpt_dev().into_blk_and_gpt();
        let sync_res = block_on(dev.sync_gpt(&mut gpt)).unwrap();
        let err = Error::GptError(GptError::DiskTooSmall);
        assert_eq!(sync_res, GptSyncResult::NoValidGpt { primary: err, secondary: err });
    }

    #[test]
    fn test_load_gpt_exceeds_max_entries() {
        let mut dev = TestBlockDeviceBuilder::new()
            .set_data(include_bytes!("../test/gpt_test_1.bin"))
            .set_max_gpt_entries(127)
            .build();
        let (mut dev, mut gpt) = dev.as_gpt_dev().into_blk_and_gpt();
        let sync_res = block_on(dev.sync_gpt(&mut gpt)).unwrap();
        let err =
            Error::GptError(GptError::NumberOfEntriesOverflow { entries: 128, max_allowed: 127 });
        assert_eq!(sync_res, GptSyncResult::NoValidGpt { primary: err, secondary: err });
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
    fn test_update_gpt() {
        let disk_orig = include_bytes!("../test/gpt_test_1.bin");
        let mut disk = disk_orig.to_vec();
        // Erases all GPT headers.
        disk[512..][..512].fill(0);
        disk.last_chunk_mut::<512>().unwrap().fill(0);

        let mut dev = TestBlockDeviceBuilder::new().set_data(&disk).build();
        let (mut dev, mut gpt) = dev.as_gpt_dev().into_blk_and_gpt();

        assert_ne!(dev.io().storage, disk_orig);
        let mut mbr_primary = disk_orig[..34 * 512].to_vec();
        block_on(dev.update_gpt(&mut mbr_primary, &mut gpt)).unwrap();
        assert_eq!(dev.io().storage, disk_orig);
    }

    #[test]
    fn test_update_gpt_buffer_truncated() {
        let mut disk = include_bytes!("../test/gpt_test_1.bin").to_vec();
        let mut dev = TestBlockDeviceBuilder::new().set_data(&disk).build();
        let (mut dev, mut gpt) = dev.as_gpt_dev().into_blk_and_gpt();

        // Less than 1 MBR block.
        assert_eq!(
            block_on(dev.update_gpt(&mut disk[..511], &mut gpt)),
            Err(Error::BufferTooSmall(Some(1024)))
        );

        // Less than MBR + GPT header.
        assert_eq!(
            block_on(dev.update_gpt(&mut disk[..1023], &mut gpt)),
            Err(Error::BufferTooSmall(Some(1024)))
        );

        // Less than MBR + GPT header + entries.
        assert_eq!(
            block_on(dev.update_gpt(&mut disk[..34 * 512 - 1], &mut gpt)),
            Err(Error::BufferTooSmall(Some(34 * 512)))
        );
    }

    #[test]
    fn test_update_gpt_check_header_fail() {
        let disk = include_bytes!("../test/gpt_test_1.bin");
        let mut dev = TestBlockDeviceBuilder::new()
            .set_data(include_bytes!("../test/gpt_test_1.bin"))
            .build();
        let (mut dev, mut gpt) = dev.as_gpt_dev().into_blk_and_gpt();
        let mut mbr_primary = disk[..34 * 512].to_vec();
        // Corrupts the first byte of the GPT header.
        mbr_primary[512] = !mbr_primary[512];
        assert_eq!(
            block_on(dev.update_gpt(&mut mbr_primary, &mut gpt)),
            Err(Error::GptError(GptError::IncorrectMagic(0x54524150204946BA)))
        );
    }

    #[test]
    fn test_update_gpt_check_entries_fail() {
        let disk = include_bytes!("../test/gpt_test_1.bin");
        let mut dev = TestBlockDeviceBuilder::new()
            .set_data(include_bytes!("../test/gpt_test_1.bin"))
            .build();
        let (mut dev, mut gpt) = dev.as_gpt_dev().into_blk_and_gpt();
        let mut mbr_primary = disk[..34 * 512].to_vec();
        // Corrupts the first byte of the entries.
        mbr_primary[1024] = !mbr_primary[1024];
        assert_eq!(
            block_on(dev.update_gpt(&mut mbr_primary, &mut gpt)),
            Err(Error::GptError(GptError::IncorrectEntriesCrc))
        );
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
