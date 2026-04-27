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

use crate::{BlockIo, Disk, Result};
use core::{
    array::from_fn,
    cell::RefMut,
    cmp::max,
    cmp::min,
    convert::TryFrom,
    default::Default,
    fmt::{Debug, Formatter},
    mem::size_of,
    num::NonZeroU64,
    ops::{Deref, DerefMut},
    str::from_utf8,
};
use crc32fast::Hasher;
use gbl_async::block_on;
use liberror::{Error, GptError};
use libutils::buffer_pool::BufferPool;
use safemath::SafeNum;
use zerocopy::{
    ByteSlice, FromBytes, FromZeros, Immutable, IntoBytes, KnownLayout, Ref, SplitByteSlice,
};

/// Number of bytes in GUID.
pub const GPT_GUID_LEN: usize = 16;
/// The maximum number of UTF-16 characters in a GPT partition name, including termination.
pub const GPT_NAME_LEN_U16: usize = 36;
const GPT_NAME_LEN_U8: usize = 2 * GPT_GUID_LEN;

/// GptGuid wrapper.
#[repr(transparent)]
#[derive(
    Copy, Clone, Debug, Default, PartialEq, Eq, Immutable, FromBytes, IntoBytes, KnownLayout,
)]
pub struct GptGuid(pub [u8; GPT_GUID_LEN]);

impl core::fmt::Display for GptGuid {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let guid = self.0;
        write!(
            f,
            "{:02x}{:02x}{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}\
            {:02x}{:02x}{:02x}{:02x}",
            // Data1 (LE)
            guid[3],
            guid[2],
            guid[1],
            guid[0],
            // Data2 (LE)
            guid[5],
            guid[4],
            // Data3 (LE)
            guid[7],
            guid[6],
            // Data4 (BE)
            guid[8],
            guid[9],
            // Data5 (BE)
            guid[10],
            guid[11],
            guid[12],
            guid[13],
            guid[14],
            guid[15]
        )
    }
}

/// The top-level GPT header.
#[repr(C, packed)]
#[derive(
    Debug, Default, Copy, Clone, Immutable, IntoBytes, FromBytes, KnownLayout, PartialEq, Eq,
)]
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
    pub guid: GptGuid,
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
    /// Casts a byte slice into a GptHeader structure.
    pub fn from_bytes(bytes: &[u8]) -> &Self {
        Ref::into_ref(Ref::<_, GptHeader>::new_from_prefix(bytes).unwrap().0)
    }

    /// Casts a byte slice into a mutable GptHeader structure.
    pub fn from_bytes_mut(bytes: &mut [u8]) -> &mut Self {
        Ref::into_mut(Ref::<_, GptHeader>::new_from_prefix(bytes).unwrap().0)
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
    fn update_entries_crc(&mut self, entries: &[u8]) {
        let size = SafeNum::from(self.entries_count) * self.entries_size;
        self.entries_crc = crc32(&entries[..size.try_into().unwrap()]);
        self.update_crc();
    }
}

fn min_gpt_entries_size(entries: u32) -> SafeNum {
    gpt_entries_size(max(entries, GPT_MIN_NUM_ENTRIES.try_into().unwrap()))
}

fn gpt_entries_size<T>(entries: T) -> SafeNum
where
    SafeNum: From<T>,
{
    SafeNum::from(entries) * GPT_ENTRY_SIZE
}

/// Computes min number of blocks for the `entries` partitions reserved space in GPT.
fn min_gpt_entries_blk(block_size: u64) -> Result<u64> {
    gpt_entries_blk(block_size, GPT_MIN_NUM_ENTRIES.try_into().unwrap())
}

/// Computes the number of blocks for the `entries` partitions reserved space in GPT.
fn gpt_entries_blk(block_size: u64, entries: u32) -> Result<u64> {
    let size: u64 = gpt_entries_size(entries).try_into().unwrap();
    match size % block_size {
        0 => Ok(size / block_size),
        _ => Err(Error::InvalidInput),
    }
}

/// Verifies GptHeader fields including CRC
fn check_header_fields(header: &GptHeader) -> Result<()> {
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

    if header.entries_count > GPT_MAX_NUM_ENTRIES.try_into().unwrap() {
        return Err(Error::GptError(GptError::NumberOfEntriesOverflow {
            entries: header.entries_count,
            max_allowed: GPT_MAX_NUM_ENTRIES,
        }));
    }

    Ok(())
}

/// Checks a header against a block device.
///
/// # Args
///
/// * `io`: An implementation of [BlockIo],
/// * `header`: The GPT header to verify.
/// * `is_primary`: If the header is a primary header.
fn check_header(io: &impl BlockIo, header: &GptHeader, is_primary: bool) -> Result<()> {
    let num_blks = SafeNum::from(io.info().num_blocks);

    // GPT spec requires that at least 128 entries worth of space be reserved.
    // But a lot of devices have custom entries count. So there is no point in verify against 128.

    // Minimum space needed: 2 * (header + 0 * entries) + MBR.
    let min_disk_blks: u64 = 2 * 1 + 1;
    if min_disk_blks > u64::try_from(num_blks).unwrap() {
        return Err(Error::GptError(GptError::DiskTooSmall));
    }

    check_header_fields(header)?;

    let expected_current: u64 = match is_primary {
        true => 1,
        false => (num_blks - 1).try_into()?,
    };
    if header.current != expected_current {
        return Err(Error::GptError(GptError::UnexpectedHeaderLba {
            actual: header.current,
            expect: expected_current,
        }));
    }

    // Checks first/last usable block.
    //
    // Assuming maximum range where partition entries are adjacent to GPT headers.
    //
    // Should leave a minimum space for MBR + primary header + primary entries before.
    // But assume min entries can be 0.
    let min_first: u64 = 2;
    // Should leave a minimum space for secondary header (no secondary entries space after).
    let max_last: u64 = (num_blks - 1 - 1).try_into().unwrap();
    if header.first > header.last + 1 || header.first < min_first || header.last > max_last {
        return Err(Error::GptError(GptError::InvalidFirstLastUsableBlock {
            first: header.first,
            last: header.last,
            range: (min_first, max_last),
        }));
    }

    // Checks entries starting block.
    if is_primary {
        // For primary header, entries must be before first usable block and no entries.
        // Assuming min 0 entries allowed.
        let right: u64 = header.first;
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
    let entries_size: usize = gpt_entries_size(header.entries_count).try_into().unwrap();
    let entries = entries.get(..entries_size).ok_or(Error::GptError(GptError::EntriesTruncated))?;
    if header.entries_crc != crc32(entries) {
        return Err(Error::GptError(GptError::IncorrectEntriesCrc));
    }

    // Checks each entry.
    let entries = Ref::<_, [GptEntry]>::new_slice(entries)
        .ok_or(Error::GptError(GptError::EntriesTruncated))?
        .into_slice();
    let entries = &entries[..header.entries_count.try_into().unwrap()];
    for (idx, ele) in entries.iter().enumerate().filter(|(_, v)| !v.is_null()) {
        // Error information uses 1-base partition index.
        let idx = idx.checked_add(1).unwrap();
        let (first, last) = (ele.first, ele.last);
        if first > last + 1 || last > header.last || first < header.first {
            return Err(Error::GptError(GptError::InvalidPartitionRange {
                idx,
                part_range: (first, last),
                usable_range: (header.first, header.last),
            }));
        } else if ele.guid.0 == [0u8; GPT_GUID_LEN] {
            return Err(Error::GptError(GptError::ZeroPartitionUniqueGUID { idx }));
        }
    }

    // Checks overlap between partition ranges.
    // Sorts an index array because we don't want to modify input.
    let mut sorted_indices: [u8; GPT_MAX_NUM_ENTRIES] = from_fn(|i| i.try_into().unwrap());
    sorted_indices.sort_unstable_by_key(|v| match entries.get(usize::try_from(*v).unwrap()) {
        Some(v) if !v.is_null() => v.first,
        _ => u64::MAX,
    });

    let actual = entries.iter().filter(|v| !v.is_null()).count();
    if actual > 1 {
        for i in 0..actual - 1 {
            let prev: usize = sorted_indices[i].try_into().unwrap();
            let next: usize = sorted_indices[i + 1].try_into().unwrap();
            if entries[prev].last >= entries[next].first {
                return Err(Error::GptError(GptError::PartitionRangeOverlap {
                    prev: (prev + 1, entries[prev].first, entries[prev].last),
                    next: (next + 1, entries[next].first, entries[next].last),
                }));
            }
        }
    }

    Ok(())
}

/// GptEntry is the partition entry data structure in the GPT.
#[repr(C, packed)]
#[derive(Copy, Clone, Debug, PartialEq, Immutable, FromBytes, IntoBytes, KnownLayout)]
pub struct GptEntry {
    /// Partition type GUID.
    pub part_type: GptGuid,
    /// Unique partition GUID.
    pub guid: GptGuid,
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
    ///
    /// Per UEFI spec, a Partition Type GUID of zero marks the entry as unused.
    fn is_null(&self) -> bool {
        self.part_type.0 == [0u8; GPT_GUID_LEN] || (self.first == 0 && self.last == 0)
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

    /// Checks if the partition name is the same as the given.
    pub fn match_name(&self, part: &str) -> Result<bool> {
        Ok(self.name_to_str(&mut [0u8; GPT_NAME_LEN_U16 * 2][..])? == part)
    }
}

impl core::fmt::Display for GptEntry {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        // Format: partition name: "abc", [first, last]: [123, 456]
        let mut name_conversion_buffer = [0u8; GPT_NAME_LEN_U16 * 2];
        let name = self.name_to_str(&mut name_conversion_buffer).map_err(|_| core::fmt::Error)?;
        // Note: The bracket around `{ self.first }` is for forcing a copy of the field because
        // GptEntry is a packed structure.
        write!(f, "partition: \"{}\", first: {}, last: {}", name, { self.first }, { self.last })
    }
}

// core::mem::offset_of!(GptHeader, crc32) is unstable feature and rejected by the compiler in our
// settings. We pre-compute the value here.
const GPT_CRC32_OFFSET: usize = 16;
const GPT_ENTRY_SIZE: usize = size_of::<GptEntry>();
/// Minimum partitions' entries in GPT header
pub const GPT_MIN_NUM_ENTRIES: usize = 128;
/// Maximum partitions' entries in GPT header
pub const GPT_MAX_NUM_ENTRIES: usize = 256;
/// GPT header magic bytes ("EFI PART" in ASCII).
pub const GPT_MAGIC: u64 = 0x5452415020494645;

enum HeaderType {
    Primary,
    Secondary,
}

/// `Partition` contains information about a GPT partition.
#[derive(Copy, Clone, Debug, PartialEq)]
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
pub struct PartitionIterator<'a> {
    entries: &'a [GptEntry],
    block_size: u64,
    idx: usize,
}

impl Iterator for PartitionIterator<'_> {
    type Item = Partition;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.entries.len() {
            let entry = &self.entries[self.idx];
            self.idx += 1;
            if !entry.is_null() {
                return Some(Partition::new(*entry, self.block_size));
            }
        }
        None
    }
}

/// Contains result of GPT syncing/restoration.
#[derive(Copy, Clone, Debug, Default, PartialEq)]
pub enum GptSyncResult {
    /// Both primary and secondary GPT are valid.
    #[default]
    BothValid,
    /// Secondary GPT is valid. Primary GPT is invalid.
    PrimaryError(Error),
    /// Secondary GPT is valid. Primary GPT is invalid and restored.
    PrimaryRestored(Error),
    /// Primary GPT is valid. Secondary GPT is invalid.
    SecondaryError(Error),
    /// Primary GPT is valid. Secondary GPT is invalid and restored.
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
            Self::PrimaryError(e) => write!(f, "Found secondary GPT. Bad primary GPT {e:?}."),
            Self::PrimaryRestored(e) => {
                write!(f, "Found secondary GPT. Restored bad primary GPT {e:?}.")
            }
            Self::SecondaryError(e) => write!(f, "Found primary GPT. Bad secondary GPT {e:?}."),
            Self::SecondaryRestored(e) => {
                write!(f, "Found primary GPT. Restored bad secondary GPT {e:?}.")
            }
            Self::NoValidGpt { primary, secondary } => {
                write!(f, "No valid GPT. primary: {primary:?}, secondary: {secondary:?}.")
            }
        }
    }
}

/// A packed wrapper of `Option<NonZeroU64>`
#[repr(C, packed)]
#[derive(Copy, Clone, Debug, Immutable, FromBytes, IntoBytes, KnownLayout)]
struct BlockSize(Option<NonZeroU64>);

/// Represents the structure of a load buffer for loading/verifying/syncing up to N GPT entries.
#[repr(C, packed)]
#[derive(Copy, Clone, Debug, Immutable, FromBytes, IntoBytes)]
pub struct GptLoadBufferN<const N: usize> {
    // GPT doesn't care about block size. But it's easier to have it available for computing offset
    // and size in bytes for partitions. It's also used as a flag for indicating whether a valid
    // GPT is loaded.
    block_size: BlockSize,
    primary_header: GptHeader,
    secondary_header: GptHeader,
    primary_entries: [GptEntry; N],
    secondary_entries: [GptEntry; N],
}

impl<const N: usize> Deref for GptLoadBufferN<N> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.as_bytes()
    }
}

impl<const N: usize> DerefMut for GptLoadBufferN<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_bytes_mut()
    }
}

/// Contains references corresponding to different GPT header parts.
/// Includes maximum number of entries that can fit in a given buffer
///
/// The structure is simply for organizing together the individual references of fields in
/// `GptLoadBufferN` parsed from a raw buffer. Note that we can't parse a `Ref<B, GptLoadBufferN>`
/// directly from a buffer because the number of entries (length of [GptEntry]) in this case needs
/// to be computed at run time based on the buffer size.
struct LoadBufferRef<B: ByteSlice> {
    block_size: Ref<B, BlockSize>,
    primary_header: Ref<B, GptHeader>,
    secondary_header: Ref<B, GptHeader>,
    primary_entries: Ref<B, [GptEntry]>,
    secondary_entries: Ref<B, [GptEntry]>,
}

impl<B: SplitByteSlice> LoadBufferRef<B> {
    fn from(buffer: B) -> Self {
        let n = min(GPT_MAX_NUM_ENTRIES, max_supported_entries(&buffer[..]).unwrap());
        let (block_size, rest) = Ref::new_from_prefix(buffer).unwrap();
        let (primary_header, rest) = Ref::new_from_prefix(rest).unwrap();
        let (secondary_header, rest) = Ref::new_from_prefix(rest).unwrap();
        let (primary_entries, rest) = Ref::new_slice_from_prefix(rest, n).unwrap();
        let (secondary_entries, _) = Ref::new_slice_from_prefix(rest, n).unwrap();
        Self { block_size, primary_header, secondary_header, primary_entries, secondary_entries }
    }

    /// Unpacks into the secondary GPT header/entries
    fn secondary(self) -> (Ref<B, GptHeader>, Ref<B, [GptEntry]>) {
        (self.secondary_header, self.secondary_entries)
    }
}

/// The minimum buffer size needed for creating a [Gpt] that can load `entries` number of
/// partitions.
///
/// # Returns
///
/// * Returns Ok(size) on success.
/// * Returns Err(Error::InvalidInput) if max_entries is greater than 256.
pub fn gpt_buffer_size(entries: usize) -> Result<usize> {
    match entries > GPT_MAX_NUM_ENTRIES {
        true => Err(Error::InvalidInput),
        _ => (SafeNum::from(size_of::<GptLoadBufferN<0>>()) + gpt_entries_size(entries) * 2)
            .try_into()
            .map_err(|e: safemath::Error| e.into()),
    }
}

/// Computes the maximum number of entries that can be loaded if using the given buffer for [Gpt].
fn max_supported_entries(buf: &[u8]) -> Result<usize> {
    match buf.len() < size_of::<GptLoadBufferN<0>>() {
        true => Err(Error::BufferTooSmall(Some(size_of::<GptLoadBufferN<0>>()))),
        _ => Ok((buf.len() - size_of::<GptLoadBufferN<0>>()) / 2 / GPT_ENTRY_SIZE),
    }
}

/// [Gpt] manages a buffer for loading, verifying and syncing GPT.
pub struct Gpt<B> {
    buffer: B,
}

impl<'a> Gpt<RefMut<'a, [u8]>> {
    /// Converts a `RefMut<Gpt<B>>` to `Gpt<RefMut<[u8]>>`. The buffer generic type is eliminated in
    /// the return.
    pub fn transpose_ref_mut(val: RefMut<'a, Gpt<impl DerefMut<Target = [u8]>>>) -> Self {
        Gpt { buffer: RefMut::map(val, |v| &mut v.buffer[..]) }
    }
}

impl<B: DerefMut<Target = [u8]>> Gpt<B> {
    /// Create an uninitialized Gpt instance from a provided buffer.
    ///
    /// The created [Gpt] can then be used in `Disk::sync_gpt()` for loading, verifying and syncing
    /// GPT on disk.
    ///
    /// # Args:
    ///
    /// * `buffer`: A buffer to use for loading, verifying and syncing primary and secondary GPT.
    ///   The size of the buffer determines the maximum number of partition entries that can be
    ///   loaded. If actual number of partitions, specified by `entries_count` in the GPT header,
    ///   exceeds it, verification and sync will eventually fail with `Error::BufferTooSmall`.
    ///   `gpt_buffer_size(num_entries)` can be used to compute the required size of buffer for
    ///   loading a specific number of entries. Note that most tools and OS fix the `entries_count`
    ///   value to the max 128 regardless of the actual number of partition entries used. Thus
    ///   unless you have full control of GPT generation in your entire system where you can always
    ///   ensure a smaller bound on it, it is recommended to always provide enough buffer for
    ///   loading 128 entries.
    ///
    /// # Returns
    ///
    /// * Returns Ok(Self) on success.
    /// * Returns Err(Error::BufferTooSmall) if buffer is less than the minimum size.
    pub fn new(mut buffer: B) -> Result<Self> {
        max_supported_entries(&buffer[..])?;
        LoadBufferRef::from(&mut buffer[..]).block_size.0 = None;
        Ok(Self { buffer })
    }

    /// Returns the maximum allowed entries.
    pub fn max_entries(&self) -> usize {
        max_supported_entries(&self.buffer[..]).unwrap()
    }

    /// Creates an instance of `Gpt<&mut [u8]>` that borrows the internal GPT buffer.
    pub fn as_borrowed(&mut self) -> Gpt<&mut [u8]> {
        Gpt { buffer: &mut self.buffer[..] }
    }

    /// Returns an iterator to GPT partition entries.
    ///
    /// If the object does not contain a valid GPT, the method returns Error.
    pub fn partition_iter(&self) -> Result<PartitionIterator<'_>> {
        let block_size = self.check_valid()?;
        let load = LoadBufferRef::from(&self.buffer[..]);
        let entries_count = load.primary_header.entries_count;
        let entries = &load.primary_entries.into_slice()[..entries_count.try_into()?];
        Ok(PartitionIterator { entries, idx: 0, block_size })
    }

    /// Checks if a read/write range into a GPT partition overflows and returns the range's absolute
    /// offset in number of bytes.
    pub fn check_range(&self, part_name: &str, offset: u64, size: usize) -> Result<u64> {
        self.find_partition(part_name)?.check_range(offset, u64::try_from(size)?)
    }

    /// Return the list of GPT entries.
    ///
    /// If there is not a valid GPT, the method returns Error.
    pub fn entries(&self) -> Result<PartitionIterator<'_>> {
        self.partition_iter()
    }

    /// Returns the total number of partitions.
    pub fn num_partitions(&self) -> Result<usize> {
        Ok(self.entries()?.count())
    }

    /// Gets the `idx`th partition.
    pub fn get_partition(&self, idx: usize) -> Result<Partition> {
        self.entries()?.nth(idx).ok_or(Error::BadIndex(idx))
    }

    /// Returns the `Partition` for a partition.
    ///
    /// # Args
    ///
    /// * `part`: Name of the partition.
    pub fn find_partition(&self, part: &str) -> Result<Partition> {
        self.entries()?.find(|e| e.name() == Some(part)).ok_or(Error::NotFound)
    }

    /// Checks whether the Gpt has been initialized and returns the block size.
    fn check_valid(&self) -> Result<u64> {
        // Block size is used as a flag that indicates that headers were verified
        // And only set in `load_and_sync()` on success.
        Ok(LoadBufferRef::from(&self.buffer[..]).block_size.0.ok_or(Error::InvalidState)?.get())
    }

    /// Helper function for loading and validating GPT header and entries.
    async fn load_and_validate_gpt(
        &mut self,
        disk: &Disk<impl BlockIo, impl BufferPool>,
        hdr_type: HeaderType,
    ) -> Result<()> {
        let blk_sz = disk.io().info().block_size;
        let load = LoadBufferRef::from(&mut self.buffer[..]);
        let (header_start, mut header, mut entries) = match hdr_type {
            HeaderType::Primary => (blk_sz, load.primary_header, load.primary_entries),
            HeaderType::Secondary => (
                ((SafeNum::from(disk.io().info().num_blocks) - 1) * blk_sz).try_into()?,
                load.secondary_header,
                load.secondary_entries,
            ),
        };

        // Loads the header
        disk.read(header_start, Ref::bytes_mut(&mut header)).await?;
        // Checks header.
        check_header(disk.io(), &header, matches!(hdr_type, HeaderType::Primary))?;
        // Loads the entries.
        let entries_size: usize = gpt_entries_size(header.entries_count).try_into()?;
        let entries_bytes = entries
            .as_bytes_mut()
            .get_mut(..entries_size)
            .ok_or(Error::GptError(GptError::EntriesTruncated))?;
        entries_bytes.as_mut()[entries_size..].fill(0);
        let entries_offset = SafeNum::from(header.entries) * blk_sz;
        disk.read(entries_offset.try_into()?, entries_bytes.as_mut()).await?;
        // Checks entries.
        check_entries(&header, entries_bytes)
    }

    /// Loads and syncs GPT from a block device.
    ///
    /// * Returns Ok(sync_result) if disk IO is successful, where `sync_result` contains the GPT
    ///   verification and restoration result,
    /// * Returns Err() if disk IO encounters error.
    pub(crate) async fn load_and_sync(
        &mut self,
        disk: &Disk<impl BlockIo, impl BufferPool>,
        repair: bool,
    ) -> Result<GptSyncResult> {
        let blk_sz = disk.io().info().block_size;
        let nonzero_blk_sz = NonZeroU64::new(blk_sz).ok_or(Error::InvalidInput)?;
        let total_blocks: SafeNum = disk.io().info().num_blocks.into();

        let primary_header_blk = 1;
        let primary_header_pos = blk_sz;
        let secondary_header_blk = total_blocks - 1;

        // Entries position for restoring.
        let primary_entries_blk = 2;
        let primary_entries_pos = SafeNum::from(primary_entries_blk) * blk_sz;
        let primary_res = self.load_and_validate_gpt(disk, HeaderType::Primary).await;
        let secondary_res = self.load_and_validate_gpt(disk, HeaderType::Secondary).await;

        let LoadBufferRef {
            mut block_size,
            mut primary_header,
            mut secondary_header,
            mut primary_entries,
            mut secondary_entries,
        } = LoadBufferRef::from(&mut self.buffer[..]);
        block_size.0 = None;
        let primary_entries = primary_entries.as_bytes_mut();
        let secondary_entries = secondary_entries.as_bytes_mut();
        let sync_res = match (primary_res, secondary_res) {
            (Err(primary), Err(secondary)) => {
                // No valid GPT, wipe the underlying bytes to avoid exposing garbage via accessors.
                primary_header.as_bytes_mut().fill(0);
                primary_entries.fill(0);
                GptSyncResult::NoValidGpt { primary, secondary }
            }
            (Ok(()), Ok(())) if is_consistent(&primary_header, &secondary_header) => {
                GptSyncResult::BothValid
            }
            (Err(e), Ok(())) => {
                // Restores to primary
                let entries_size = gpt_entries_size(secondary_header.entries_count).try_into()?;
                primary_header.as_bytes_mut().clone_from_slice(secondary_header.as_bytes());
                primary_entries[..entries_size]
                    .clone_from_slice(&secondary_entries[..entries_size]);
                primary_entries[entries_size..].fill(0);
                primary_header.current = primary_header_blk;
                primary_header.backup = secondary_header_blk.try_into()?;
                primary_header.entries = primary_entries_blk;
                primary_header.update_crc();

                match repair {
                    true => {
                        disk.write(primary_header_pos, primary_header.as_bytes_mut()).await?;
                        disk.write(
                            primary_entries_pos.try_into()?,
                            &mut primary_entries[..entries_size],
                        )
                        .await?;
                        GptSyncResult::PrimaryRestored(e)
                    }
                    _ => GptSyncResult::PrimaryError(e),
                }
            }
            (Ok(()), v) => {
                // Restores to secondary
                let entries_size = gpt_entries_size(primary_header.entries_count).try_into()?;
                let pos = secondary_header_blk * blk_sz;
                let secondary_entries_pos = pos - entries_size;
                let secondary_entries_blk = secondary_entries_pos / blk_sz;

                secondary_header.as_bytes_mut().clone_from_slice(primary_header.as_bytes());
                secondary_entries[..entries_size]
                    .clone_from_slice(&primary_entries[..entries_size]);
                secondary_entries[entries_size..].fill(0);
                secondary_header.current = secondary_header_blk.try_into()?;
                secondary_header.backup = primary_header_blk;
                secondary_header.entries = secondary_entries_blk.try_into()?;
                secondary_header.update_crc();

                let e = match v {
                    Err(e) => e,
                    _ => Error::GptError(GptError::DifferentFromPrimary),
                };
                match repair {
                    true => {
                        disk.write(pos.try_into()?, secondary_header.as_bytes_mut()).await?;
                        disk.write(
                            secondary_entries_pos.try_into()?,
                            &mut secondary_entries[..entries_size],
                        )
                        .await?;
                        GptSyncResult::SecondaryRestored(e)
                    }
                    _ => GptSyncResult::SecondaryError(e),
                }
            }
        };

        if !matches!(sync_res, GptSyncResult::NoValidGpt { .. }) {
            block_size.0 = Some(nonzero_blk_sz);
        }
        Ok(sync_res)
    }

    /// Get `entries_count` from GPT header if it is valid
    pub fn entries_count(&self) -> Result<u32> {
        self.check_valid()?;
        let load_buffer = LoadBufferRef::from(&self.buffer[..]);
        Ok(load_buffer.primary_header.entries_count)
    }
}

/// Checks whether primary and secondary header
fn is_consistent(primary: &GptHeader, secondary: &GptHeader) -> bool {
    let mut expected_secondary = *primary;
    expected_secondary.crc32 = secondary.crc32;
    expected_secondary.current = secondary.current;
    expected_secondary.backup = 1;
    expected_secondary.entries = secondary.entries;
    &expected_secondary == secondary
}

/// A [Gpt] that owns a `GptLoadBufferN<N>` and can load up to N partition entries.
///
/// Note: The size of this type increases with N and can be expensive to store on stack. It is
/// typically intended for resource abundant environment such as test.
pub type GptN<const N: usize> = Gpt<GptLoadBufferN<N>>;

/// Creates an instance of GptN.
pub fn new_gpt_n<const N: usize>() -> GptN<N> {
    Gpt::new(GptLoadBufferN::<N>::new_zeroed()).unwrap()
}

/// A [Gpt] that owns a `GptLoadBufferN<256>` and can load the maximum 256 partition entries.
///
/// Note: The size of this type is approximately 50K and can be expensive to store on stack. It
/// is typically intended for resource abundant environment such as test.
pub type GptMax = GptN<GPT_MAX_NUM_ENTRIES>;

/// Creates an instance of GptMax.
pub fn new_gpt_max() -> GptMax {
    new_gpt_n::<GPT_MAX_NUM_ENTRIES>()
}

/// Updates GPT on a block device.
///
/// # Args
///
/// * `disk`: to write GPT
/// * `mbr_primary`: A buffer containing the MBR block, primary GPT header and entries.
/// * `resize`: If set to true, the method updates the last partition to cover the rest of the
///    storage.
/// * `gpt`: The output [Gpt] to update.
pub(crate) async fn update_gpt(
    disk: &Disk<impl BlockIo, impl BufferPool>,
    mbr_primary: &mut [u8],
    resize: bool,
    gpt: &mut Gpt<impl DerefMut<Target = [u8]>>,
) -> Result<()> {
    let blk_sz: usize = disk.io().info().block_size.try_into()?;
    let (header, remain) = mbr_primary
        .get_mut(blk_sz..)
        .map(|v| v.split_at_mut_checked(blk_sz))
        .flatten()
        .ok_or(Error::BufferTooSmall(Some(blk_sz * 2)))?;
    let header = Ref::into_mut(Ref::<_, GptHeader>::new_from_prefix(&mut header[..]).unwrap().0);

    // Adjusts last usable block according to this device in case the GPT was generated for a
    // different disk size. If this results in some partition being out of range, it will be
    // caught during `check_header()`.
    let entries_blk = min_gpt_entries_size(header.entries_count) / blk_sz;
    // Reserves only secondary GPT header and entries.
    let num_blks = SafeNum::from(disk.io().info().num_blocks);
    header.last = (num_blks - entries_blk - 2).try_into().unwrap();
    header.backup = (num_blks - 1).try_into().unwrap();
    header.update_crc();

    check_header(disk.io(), &header, true)?;
    // Computes entries offset in bytes relative to `remain`
    let entries_off: usize = ((SafeNum::from(header.entries) - 2) * blk_sz).try_into().unwrap();
    let entries_size: usize =
        (SafeNum::from(header.entries_count) * header.entries_size).try_into().unwrap();
    let entries = remain
        .get_mut(entries_off..)
        .map(|v| v.get_mut(..entries_size))
        .flatten()
        .ok_or(Error::BufferTooSmall(Some(2 * blk_sz + entries_off + entries_size)))?;
    check_entries(&header, entries)?;

    if resize {
        // Updates the last entry to cover the rest of the storage.
        let gpt_entries =
            Ref::<_, [GptEntry]>::new_slice(&mut entries[..]).unwrap().into_mut_slice();
        gpt_entries.iter_mut().filter(|e| !e.is_null()).last().map(|v| v.last = header.last);
        header.update_entries_crc(entries);
        // Re-verifies everything.
        check_header(disk.io(), &header, true).unwrap();
        check_entries(&header, entries).unwrap();
    }

    disk.write(0, mbr_primary).await?;
    disk.sync_gpt(gpt, true).await?.res()
}

/// Erases GPT if there is one on the device.
pub(crate) async fn erase_gpt(
    disk: &Disk<impl BlockIo, impl BufferPool>,
    gpt: &mut Gpt<impl DerefMut<Target = [u8]>>,
) -> Result<()> {
    match disk.sync_gpt(gpt, false).await?.res() {
        Err(_) => Ok(()), // No valid GPT. Nothing to erase.
        _ => {
            let blk_sz = disk.block_info().block_size;
            let mut load = LoadBufferRef::from(&mut gpt.buffer[..]);
            let entries_size = gpt_entries_size(load.primary_header.entries_count);
            let scratch = load.primary_entries.as_bytes_mut();
            // Invalidate GPT first.
            load.block_size.0 = None;
            // Erases primary header/entries.
            let header = load.primary_header.current;
            let entries = load.primary_header.entries;
            disk.fill(header * blk_sz, blk_sz, 0, scratch).await?;
            disk.fill(entries * blk_sz, entries_size.try_into().unwrap(), 0, scratch).await?;
            // Erases secondary header/entries.
            let header = load.secondary_header.current;
            let entries = load.secondary_header.entries;
            disk.fill(header * blk_sz, blk_sz, 0, scratch).await?;
            disk.fill(entries * blk_sz, entries_size.try_into().unwrap(), 0, scratch).await?;
            Ok(())
        }
    }
}

/// Computes the minimum blocks needed for creating a GPT.
fn min_required_blocks(block_size: u64) -> Result<u64> {
    // MBR + primary/secondary GPT header block + primary/secondary entries blocks.
    Ok(1 + (1 + min_gpt_entries_blk(block_size)?) * 2)
}

/// `GptBuilder` provides API for modifying/creating GPT partition table on a disk.
pub struct GptBuilder<D, G> {
    disk: D,
    gpt: G,
}

impl<D: Debug, G: Debug> Debug for GptBuilder<D, G> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::result::Result<(), core::fmt::Error> {
        write!(f, "GptBuilder {{ disk: {:?}, gpt: {:?} }}", self.disk, self.gpt)
    }
}
// Generic parameters:
//
// * T: The type that implement BlockIo.
// * S: The type for the scratch buffer in `Self::disk`.
// * B: The type for the GPT buffer in `Self::gpt`.
// * D: The type for `Self::disk` which can dereference to a Disk<T, S>.
// * G: The type for `Self::gpt` which can dereference to a Gpt<B>.
impl<'a, T, P, B, D, G> GptBuilder<D, G>
where
    T: BlockIo,
    P: BufferPool,
    B: DerefMut<Target = [u8]>,
    D: Deref<Target = Disk<T, P>>,
    G: DerefMut<Target = Gpt<B>>,
{
    /// Creates a new instance.
    ///
    /// The method always re-syncs the GPT. If `disk` does not contain a valid GPT, a new GPT is
    /// started from scratch.
    ///
    /// The partition entries will always be sorted when writing back to disk by `Self::persist()`.
    ///
    /// # Returns
    ///
    /// * Returns Ok((Self, true)) if an instance is created and the disk has a valid GPT.
    /// * Returns Ok((Self, false)) if an instance is created but disk does not have a valid GPT.
    /// * Returns Err() otherwise.
    pub fn new(disk: D, mut gpt: G) -> Result<(Self, bool)> {
        if disk.block_info().num_blocks < min_required_blocks(disk.block_info().block_size)? {
            return Err(Error::GptError(GptError::DiskTooSmall));
        }
        let has_valid_gpt = block_on(disk.sync_gpt(&mut gpt, true))?.res().is_ok();
        // Uses the buffer for secondary GPT header/entries as construction buffer, as it is not
        // used by Gpt once loaded and synced.
        let (mut header, mut entries) = LoadBufferRef::from(&mut gpt.buffer[..]).secondary();
        if !has_valid_gpt {
            header.as_bytes_mut().fill(0);
            entries.as_bytes_mut().fill(0);
            let entries_blk = min_gpt_entries_blk(disk.block_info().block_size).unwrap();
            // Initializes a secondary header.
            let num_blks = SafeNum::from(disk.block_info().num_blocks);
            header.magic = GPT_MAGIC;
            header.current = (num_blks - 1).try_into().unwrap();
            header.backup = 1;
            header.size = size_of::<GptHeader>().try_into().unwrap();
            header.first = 1 + 1 + entries_blk; // MBR + GPT header blocks + entries block
            header.last = (num_blks - 1 - entries_blk - 1).try_into().unwrap();
            header.entries = (num_blks - 1 - entries_blk).try_into().unwrap();
            header.entries_count = 0;
            header.entries_size = size_of::<GptEntry>().try_into().unwrap();
        }
        // Normalizes `entries_count` to actual valid entries. Some GPT disk fixes `entries_count`
        // to 128.
        header.entries_count = entries.iter().filter(|v| !v.is_null()).count().try_into().unwrap();
        entries.sort_unstable_by_key(|v| match v.is_null() {
            true => u64::MAX,
            _ => v.first,
        });
        Ok((Self { disk, gpt }, has_valid_gpt))
    }

    /// Removes a partition.
    ///
    /// # Returns
    ///
    /// * Returns Ok(true) if found and removed.
    /// * Returns Ok(false) if not found.
    /// * Returns Err() otherwise.
    pub fn remove(&mut self, part: &str) -> Result<bool> {
        let (mut header, mut entries) = LoadBufferRef::from(&mut self.gpt.buffer[..]).secondary();
        let entries = &mut entries[..header.entries_count.try_into().unwrap()];
        match entries.iter().position(|v| v.match_name(part).unwrap_or(false)) {
            Some(n) => {
                // Shift the elements behind forward.
                entries[n..].rotate_left(1);
                // Zeroizes the last element.
                entries.last_mut().unwrap().as_bytes_mut().fill(0);
                header.entries_count -= 1;
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    /// Inserts a new partition before a partition.
    ///
    /// # Args
    ///
    /// * `idx`: Index of the partition to insert before. If index is out of range of valid entries,
    ///   the partition will be inserted at the last.
    /// * `name`: Name of the partition.
    /// * `part_type`: Type GUID.
    /// * `unique_guid`: Unique GUID.
    /// * `flags`: Partition flag.
    /// * `size`: If Some(_), specifies the size in number of bytes for the partition. The method
    ///   will round it up to multiple of disk block size and check that there is enough space for
    ///   the partition. If None, the method will insert the partition and consumes all the
    ///   available space in between.
    fn insert_before(
        &mut self,
        idx: usize,
        name: &str,
        part_type: [u8; GPT_GUID_LEN],
        unique_guid: [u8; GPT_GUID_LEN],
        flags: u64,
        size: Option<u64>,
    ) -> Result<()> {
        let (mut header, mut entries) = LoadBufferRef::from(&mut self.gpt.buffer[..]).secondary();
        // Gets position to the first NULL entry.
        let n = entries.iter().position(|v| v.is_null()).ok_or(Error::OutOfResources)?;
        let entries = &mut entries[..n + 1];
        // Caps `idx` to no more than the first NULL entry.
        let idx = min(n, idx);
        // Comptues the ending block index (non-inclusive) of the previous partition entry.
        // Entries are guaranteed sorted in `Self::new()`.
        let prev_end = match idx {
            0 => header.first,
            _ => entries[idx - 1].last + 1,
        };
        // Comptues the starting block index (inclusive) of the next partition entry.
        let next_start = match idx == n {
            true => header.last + 1,
            _ => entries[idx].first,
        };
        // Computes the size in number of blocks
        let blk_sz = self.disk.block_info().block_size;
        let blocks: u64 = match size {
            Some(v) => (SafeNum::from(v).round_up(blk_sz) / blk_sz).try_into()?,
            _ => next_start - prev_end, // If not given, uses up all the gap space
        };
        // Checks if there is enough space.
        if next_start - prev_end < blocks {
            return Err(Error::OutOfResources);
        }
        // Inserts the new entry.
        entries[idx..].rotate_right(1);
        let entry = &mut entries[idx];
        assert!(entry.is_null());
        entry.part_type = GptGuid(part_type);
        entry.guid = GptGuid(unique_guid);
        entry.flags = flags;
        entry.first = prev_end;
        entry.last = prev_end + blocks - 1;
        for (idx, ele) in name.encode_utf16().enumerate() {
            match idx < GPT_NAME_LEN_U16 {
                true => entry.name[idx] = ele,
                _ => break,
            }
        }
        header.entries_count += 1;
        Ok(())
    }

    /// Adds a partition.
    ///
    /// # Args
    ///
    /// * `name`: Name of the partition.
    /// * `part_type`: Type GUID.
    /// * `unique_guid`: Unique GUID.
    /// * `flags`: Partition flag.
    /// * `size`: If Some(_), specifies the size in number of bytes for the partition. The method
    ///   will round it up to multiple of disk block size and search for the first large enough
    ///   space in the unused spae for putting the partition. If None, the method will add the
    ///   partition at the last and have it consume all remaining usable disk space.
    pub fn add(
        &mut self,
        name: &str,
        part_type: [u8; GPT_GUID_LEN],
        unique_guid: [u8; GPT_GUID_LEN],
        flags: u64,
        size: Option<u64>,
    ) -> Result<()> {
        let (header, _) = LoadBufferRef::from(&mut self.gpt.buffer[..]).secondary();
        let entry_count = usize::try_from(header.entries_count).unwrap();
        let search_start = size.is_some().then_some(0).unwrap_or(entry_count);
        for i in search_start..entry_count + 1 {
            if self.insert_before(i, name, part_type, unique_guid, flags, size).is_ok() {
                return Ok(());
            }
        }
        Err(Error::OutOfResources)
    }

    /// Persists the constructed GPT table to the disk and syncs. The builder is consumed.
    pub async fn persist(mut self) -> Result<()> {
        let (mut header, mut entries) = LoadBufferRef::from(&mut self.gpt.buffer[..]).secondary();
        let entries = &mut entries[..header.entries_count.try_into()?];
        header.update_entries_crc(entries.as_bytes());
        // Check validity. Should not fail if implementation is correct.
        check_header(self.disk.io(), &header, false).unwrap();
        check_entries(&header, entries.as_bytes()).unwrap();
        let blk_sz = self.disk.block_info().block_size;
        // Writes to secondary header/ entries
        self.disk.write(header.current * blk_sz, header.as_bytes_mut()).await?;
        self.disk.write(header.entries * blk_sz, entries.as_bytes_mut()).await?;
        // Clears primary header magic
        self.disk.write(blk_sz, &mut 0u64.to_be_bytes()).await?;
        // Re-syncs GPT
        self.disk.sync_gpt(&mut self.gpt, true).await?.res()
    }
}

/// Helper for calculcating the Crc32.
fn crc32(data: &[u8]) -> u32 {
    let mut hasher = Hasher::new();
    hasher.update(data);
    hasher.finalize()
}

#[cfg(test)]
pub(crate) mod test {
    use super::*;
    use crate::{gpt::GptError::NumberOfEntriesOverflow, test::TestDisk};
    use gbl_async::block_on;
    use libtestutils::AlignedBuffer;

    // helper functions for constant calculation
    const fn round_down(v: usize, blk: usize) -> usize {
        v - (v % blk)
    }
    const fn round_up(v: usize, blk: usize) -> usize {
        round_down((v + blk) - 1, blk)
    }
    const BLOCK_SIZE: usize = 512;
    const MBR_BLKS: usize = 1;
    const MBR_SIZE: usize = MBR_BLKS * BLOCK_SIZE;
    const GPT_HEADER_NO_ENTRIES_SIZE: usize = size_of::<GptHeader>();
    const GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE: usize =
        round_up(GPT_HEADER_NO_ENTRIES_SIZE, BLOCK_SIZE);

    /// A helper to calculate bytes to read for a GPT header depending on the entries count.
    fn gpt_header_size_block_align<T>(entries_count: T) -> usize
    where
        SafeNum: From<T>,
    {
        let size: SafeNum = gpt_entries_size(entries_count) + GPT_HEADER_NO_ENTRIES_SIZE;
        size.round_up(BLOCK_SIZE).try_into().unwrap()
    }

    /// A helper to calculate bytes to read for a GPT header and MBR depending on the entries count.
    fn mbr_gpt_header_size_block_align<T>(entries_count: T) -> usize
    where
        SafeNum: From<T>,
    {
        let size: SafeNum = gpt_entries_size(entries_count) + MBR_SIZE + GPT_HEADER_NO_ENTRIES_SIZE;
        size.round_up(BLOCK_SIZE).try_into().unwrap()
    }

    /// A helper for creating a [TestDisk] from given data.
    fn test_disk(data: impl AsRef<[u8]>) -> TestDisk {
        // All tests cases use pre-generated GPT disk of 512 block size.
        TestDisk::new_ram_alloc(
            BLOCK_SIZE.try_into().unwrap(),
            BLOCK_SIZE.try_into().unwrap(),
            data.as_ref().to_vec(),
        )
        .unwrap()
    }

    /// A helper for creating a [TestDisk] from given data and a [Gpt] for 256 entries.
    fn test_disk_and_gpt(data: impl AsRef<[u8]>) -> (TestDisk, GptMax) {
        (test_disk(data), new_gpt_max())
    }

    fn get_gpt_test_1_data() -> [(u32, &'static [u8]); 2] {
        [
            (128, &include_bytes!("../test/gpt_test_1.bin")[..]),
            (256, &include_bytes!("../test/gpt_256_test_1.bin")[..]),
        ]
    }
    const TEST_1_DATA_BOOT_A_SIZE: u64 = 8 * 1024;
    const TEST_1_DATA_BOOT_B_SIZE: u64 = 12 * 1024;

    #[test]
    fn test_load_and_sync() {
        for (_, data) in get_gpt_test_1_data() {
            let (dev, mut gpt) = test_disk_and_gpt(data);
            block_on(dev.sync_gpt(&mut gpt, true)).unwrap();

            assert_eq!(gpt.partition_iter().unwrap().count(), 2);
            gpt.find_partition("boot_a").unwrap();
            gpt.find_partition("boot_b").unwrap();
            assert!(gpt.find_partition("boot_c").is_err());

            // Creating a new [Gpt] using the same buffer should reset the valid state.
            let gpt = Gpt::new(gpt.buffer).unwrap();
            assert!(gpt.partition_iter().is_err());
            assert!(gpt.find_partition("boot_a").is_err());
            assert!(gpt.find_partition("boot_b").is_err());
        }
    }

    #[test]
    fn test_check_header_invalid_current() {
        let data = get_gpt_test_1_data()[0].1;
        let mut data = data.to_vec();
        let header = GptHeader::from_bytes_mut(&mut data[512..]);
        header.current = 2; // Invalid, should be 1
        header.update_crc();

        let dev = test_disk(data);
        let mut gpt = new_gpt_max();
        let sync_res = block_on(dev.sync_gpt(&mut gpt, true)).unwrap();
        match sync_res {
            GptSyncResult::PrimaryRestored(Error::GptError(GptError::UnexpectedHeaderLba {
                actual,
                expect,
            })) => {
                assert_eq!(actual, 2);
                assert_eq!(expect, 1);
            }
            _ => panic!("Expected PrimaryRestored with UnexpectedHeaderLba, got {:?}", sync_res),
        }
    }

    #[test]
    fn test_update_gpt_rejects_invalid_current() {
        let data = get_gpt_test_1_data()[0].1;
        let dev = test_disk(data);
        let mut gpt = new_gpt_max();

        let mut download = get_gpt_test_1_data()[0].1.to_vec();
        let header = GptHeader::from_bytes_mut(&mut download[512..]);
        header.current = 2; // Invalid, should be 1
        header.update_crc();

        let res = block_on(update_gpt(&dev, &mut download, false, &mut gpt));
        match res {
            Err(Error::GptError(GptError::UnexpectedHeaderLba { actual, expect })) => {
                assert_eq!(actual, 2);
                assert_eq!(expect, 1);
            }
            _ => panic!("Expected UnexpectedHeaderLba, got {:?}", res),
        }
    }

    #[test]
    fn test_load_with_unaligned_buffer() {
        for (entries_count, data) in get_gpt_test_1_data() {
            let size = ((18 + entries_count / 128 * 16) * 1024).try_into().unwrap();
            let mut buffer = AlignedBuffer::new(size, 8);
            let buffer = &mut buffer[1..];
            assert_ne!(buffer.as_ptr() as usize % 2, 0);
            let disk = test_disk(data);
            let mut gpt = Gpt::new(buffer).unwrap();
            block_on(disk.sync_gpt(&mut gpt, true)).unwrap();
        }
    }

    #[test]
    fn test_gpt_buffer_too_small() {
        assert!(Gpt::new(vec![0u8; size_of::<GptLoadBufferN<0>>() - 1]).is_err());
    }

    #[test]
    fn test_gpt_buffer_not_enough_for_all_entries() {
        fn test_gpt_buffer_not_enough_for_all_entries_impl<const N: usize>(data: &[u8]) {
            let dev = test_disk(data);
            let mut gpt = new_gpt_n::<N>();
            assert_eq!(gpt.max_entries(), N);
            assert!(block_on(dev.sync_gpt(&mut gpt, true)).unwrap().res().is_err());
        }

        for (entries_count, data) in get_gpt_test_1_data() {
            match entries_count {
                128 => test_gpt_buffer_not_enough_for_all_entries_impl::<127>(data),
                256 => test_gpt_buffer_not_enough_for_all_entries_impl::<255>(data),
                _ => panic!(),
            }
        }
    }

    #[test]
    fn test_good_gpt_no_repair_write() {
        for (entries_count, data) in get_gpt_test_1_data() {
            let (dev, mut gpt) = test_disk_and_gpt(data);
            assert_eq!(gpt.max_entries(), 256);
            assert_eq!(block_on(dev.sync_gpt(&mut gpt, false)).unwrap(), GptSyncResult::BothValid);
            assert_eq!(gpt.entries_count(), Ok(entries_count));
        }
    }

    #[test]
    fn test_good_gpt_too_big_unsupported() {
        let (dev, mut gpt) = test_disk_and_gpt(include_bytes!("../test/gpt_too_big.bin"));
        assert_eq!(
            block_on(dev.sync_gpt(&mut gpt, true)).unwrap(),
            GptSyncResult::NoValidGpt {
                primary: Error::GptError(NumberOfEntriesOverflow {
                    entries: 260,
                    max_allowed: GPT_MAX_NUM_ENTRIES
                }),
                secondary: Error::GptError(NumberOfEntriesOverflow {
                    entries: 260,
                    max_allowed: GPT_MAX_NUM_ENTRIES
                })
            }
        );
    }

    #[test]
    fn test_gpt_invalid_returns_errors() {
        let (dev, mut gpt) = test_disk_and_gpt(include_bytes!("../test/gpt_too_big.bin"));
        let sync_res = block_on(dev.sync_gpt(&mut gpt, true)).unwrap();
        assert!(matches!(sync_res, GptSyncResult::NoValidGpt { .. }));
        assert!(gpt.check_valid().is_err());
        assert!(gpt.entries().is_err());
    }

    /// A helper for testing restoration of invalid primary/secondary header modified by caller.
    fn test_gpt_sync_restore<'a>(
        modify_primary: impl FnOnce(&mut GptHeader, Ref<&mut [u8], [GptEntry]>),
        modify_secondary: impl FnOnce(&mut GptHeader, Ref<&mut [u8], [GptEntry]>),
        expect_primary_err: Error,
        expect_secondary_err: Error,
        _entries_count: u32,
        disk_orig: &[u8],
    ) {
        // Restores from secondary to primary.
        let mut disk = disk_orig.to_vec();
        let (header, entries) =
            (&mut disk[MBR_SIZE..]).split_at_mut(GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE);
        let mut header = GptHeader::from_bytes_mut(header);
        modify_primary(&mut header, Ref::<_, [GptEntry]>::new_slice(entries).unwrap());
        let (dev, mut gpt) = test_disk_and_gpt(&disk);
        assert_ne!(dev.io().storage().deref(), disk_orig);
        let sync_res = block_on(dev.sync_gpt(&mut gpt, true)).unwrap();
        assert_eq!(sync_res, GptSyncResult::PrimaryRestored(expect_primary_err));
        assert_eq!(dev.io().storage().deref(), disk_orig);

        // Syncs without restoring primary.
        let (dev, mut gpt) = test_disk_and_gpt(&disk);
        assert_ne!(dev.io().storage().deref(), disk_orig);
        let sync_res = block_on(dev.sync_gpt(&mut gpt, false)).unwrap();
        assert_eq!(sync_res, GptSyncResult::PrimaryError(expect_primary_err));
        assert_eq!(dev.io().storage().deref(), disk);

        // Restores from primary to secondary.
        let mut disk = disk_orig.to_vec();
        let (entries, header) = (&mut disk[MBR_SIZE..])
            .split_last_chunk_mut::<GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE>()
            .unwrap();
        let mut header = GptHeader::from_bytes_mut(&mut header[..]);
        let (_, entries) = entries
            .split_at_mut_checked(
                entries.len() - usize::try_from(gpt_entries_size(header.entries_count)).unwrap(),
            )
            .unwrap();
        modify_secondary(&mut header, Ref::<_, [GptEntry]>::new_slice(&mut entries[..]).unwrap());
        let (dev, mut gpt) = test_disk_and_gpt(&disk);
        assert_ne!(dev.io().storage().deref(), disk_orig);
        let sync_res = block_on(dev.sync_gpt(&mut gpt, true)).unwrap();
        assert_eq!(sync_res, GptSyncResult::SecondaryRestored(expect_secondary_err));
        assert_eq!(dev.io().storage().deref(), disk_orig);

        // Syncs without restoring secondary.
        let (dev, mut gpt) = test_disk_and_gpt(&disk);
        assert_ne!(dev.io().storage().deref(), disk_orig);
        let sync_res = block_on(dev.sync_gpt(&mut gpt, false)).unwrap();
        assert_eq!(sync_res, GptSyncResult::SecondaryError(expect_secondary_err));
        assert_eq!(dev.io().storage().deref(), disk);
    }

    #[test]
    fn test_sync_gpt_incorrect_magic() {
        fn modify(hdr: &mut GptHeader, _: Ref<&mut [u8], [GptEntry]>) {
            hdr.magic = 0x123456;
            hdr.update_crc();
        }
        let err = Error::GptError(GptError::IncorrectMagic(0x123456));

        for (entries, data) in get_gpt_test_1_data() {
            test_gpt_sync_restore(modify, modify, err, err, entries, data);
        }
    }

    #[test]
    fn test_sync_gpt_incorrect_crc() {
        fn modify(hdr: &mut GptHeader, _: Ref<&mut [u8], [GptEntry]>) {
            hdr.crc32 = !hdr.crc32;
        }
        let err = Error::GptError(GptError::IncorrectHeaderCrc);
        for (entries, data) in get_gpt_test_1_data() {
            test_gpt_sync_restore(modify, modify, err, err, entries, data);
        }
    }

    #[test]
    fn test_sync_gpt_unexpected_header_size() {
        fn modify(hdr: &mut GptHeader, _: Ref<&mut [u8], [GptEntry]>) {
            hdr.size += 1;
            hdr.update_crc();
        }
        let err = Error::GptError(GptError::UnexpectedHeaderSize { actual: 93, expect: 92 });
        for (entries, data) in get_gpt_test_1_data() {
            test_gpt_sync_restore(modify, modify, err, err, entries, data);
        }
    }

    #[test]
    fn test_sync_gpt_unexpected_entry_size() {
        fn modify(hdr: &mut GptHeader, _: Ref<&mut [u8], [GptEntry]>) {
            hdr.entries_size += 1;
            hdr.update_crc();
        }
        let err = Error::GptError(GptError::UnexpectedEntrySize { actual: 129, expect: 128 });
        for (entries, data) in get_gpt_test_1_data() {
            test_gpt_sync_restore(modify, modify, err, err, entries, data);
        }
    }

    #[test]
    fn test_sync_gpt_first_usable_gt_last() {
        fn modify(hdr: &mut GptHeader, _: Ref<&mut [u8], [GptEntry]>) {
            hdr.first = hdr.last;
            hdr.last = hdr.first - 2;
            hdr.update_crc();
        }
        for (entries_count, data) in get_gpt_test_1_data() {
            let err = match entries_count {
                128 => Error::GptError(GptError::InvalidFirstLastUsableBlock {
                    first: 94,
                    last: 92,
                    range: (2, 126),
                }),
                256 => Error::GptError(GptError::InvalidFirstLastUsableBlock {
                    first: 190,
                    last: 188,
                    range: (2, 254),
                }),
                _ => unimplemented!(),
            };
            test_gpt_sync_restore(modify, modify, err, err, entries_count, data);
        }
    }

    #[test]
    fn test_sync_gpt_first_usable_out_of_range() {
        fn modify(hdr: &mut GptHeader, _: Ref<&mut [u8], [GptEntry]>) {
            hdr.first = 1;
            hdr.update_crc();
        }
        for (entries_count, data) in get_gpt_test_1_data() {
            let err = match entries_count {
                128 => Error::GptError(GptError::InvalidFirstLastUsableBlock {
                    first: 1,
                    last: 94,
                    range: (2, 126),
                }),
                256 => Error::GptError(GptError::InvalidFirstLastUsableBlock {
                    first: 1,
                    last: 190,
                    range: (2, 254),
                }),
                _ => unimplemented!(),
            };
            test_gpt_sync_restore(modify, modify, err, err, entries_count, data);
        }
    }

    #[test]
    fn test_sync_gpt_last_usable_out_of_range() {
        for (entries_count, data) in get_gpt_test_1_data() {
            let modify = |hdr: &mut GptHeader, _: Ref<&mut [u8], [GptEntry]>| {
                hdr.last +=
                    1 + gpt_entries_blk(BLOCK_SIZE.try_into().unwrap(), entries_count).unwrap();
                hdr.update_crc();
            };
            let err = match entries_count {
                128 => Error::GptError(GptError::InvalidFirstLastUsableBlock {
                    first: 34,
                    last: 127,
                    range: (2, 126),
                }),
                256 => Error::GptError(GptError::InvalidFirstLastUsableBlock {
                    first: 66,
                    last: 255,
                    range: (2, 254),
                }),
                _ => unimplemented!(),
            };
            test_gpt_sync_restore(modify, modify, err, err, entries_count, data);
        }
    }

    #[test]
    fn test_sync_gpt_primary_entries_out_of_range() {
        for (entries_count, data) in get_gpt_test_1_data() {
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
                    expect_range: (
                        2,
                        match entries_count {
                            128 => 34,
                            256 => 66,
                            _ => unimplemented!(),
                        },
                    ),
                }),
                match entries_count {
                    128 => Error::GptError(GptError::InvalidSecondaryEntriesStart {
                        value: 94,
                        expect_range: (95, 127),
                    }),
                    256 => Error::GptError(GptError::InvalidSecondaryEntriesStart {
                        value: 190,
                        expect_range: (191, 255),
                    }),
                    _ => unimplemented!(),
                },
                entries_count,
                data,
            );
        }
    }

    #[test]
    fn test_sync_gpt_incorrect_entry_crc() {
        fn modify(hdr: &mut GptHeader, _: Ref<&mut [u8], [GptEntry]>) {
            hdr.entries_crc = !hdr.entries_crc;
            hdr.update_crc();
        }
        let err = Error::GptError(GptError::IncorrectEntriesCrc);
        for (entries_count, data) in get_gpt_test_1_data() {
            test_gpt_sync_restore(modify, modify, err, err, entries_count, data);
        }
    }

    #[test]
    fn test_sync_gpt_partition_range_overflow() {
        fn modify(hdr: &mut GptHeader, mut entries: Ref<&mut [u8], [GptEntry]>) {
            entries[1].last = hdr.last + 1;
            hdr.update_entries_crc(entries.as_bytes());
        }
        for (entries_count, data) in get_gpt_test_1_data() {
            let err = match entries_count {
                128 => Error::GptError(GptError::InvalidPartitionRange {
                    idx: 2,
                    part_range: (50, 95),
                    usable_range: (34, 94),
                }),
                256 => Error::GptError(GptError::InvalidPartitionRange {
                    idx: 2,
                    part_range: (82, 191),
                    usable_range: (66, 190),
                }),
                _ => unimplemented!(),
            };

            test_gpt_sync_restore(modify, modify, err, err, entries_count, data);
        }
    }

    #[test]
    fn test_sync_gpt_invalid_partition_range() {
        fn modify(hdr: &mut GptHeader, mut entries: Ref<&mut [u8], [GptEntry]>) {
            entries[1].first = entries[1].last;
            entries[1].last = entries[1].first - 2;
            hdr.update_entries_crc(entries.as_bytes());
        }

        for (entries_count, data) in get_gpt_test_1_data() {
            let err = match entries_count {
                128 => Error::GptError(GptError::InvalidPartitionRange {
                    idx: 2,
                    part_range: (73, 71),
                    usable_range: (34, 94),
                }),
                256 => Error::GptError(GptError::InvalidPartitionRange {
                    idx: 2,
                    part_range: (105, 103),
                    usable_range: (66, 190),
                }),
                _ => unimplemented!(),
            };
            test_gpt_sync_restore(modify, modify, err, err, entries_count, data);
        }
    }

    #[test]
    fn test_sync_gpt_partition_overlap() {
        fn modify(hdr: &mut GptHeader, mut entries: Ref<&mut [u8], [GptEntry]>) {
            entries[0].last = entries[1].first;
            entries.swap(0, 1);
            hdr.update_entries_crc(entries.as_bytes());
        }
        for (entries_count, data) in get_gpt_test_1_data() {
            let err = match entries_count {
                128 => Error::GptError(GptError::PartitionRangeOverlap {
                    prev: (2, 34, 50),
                    next: (1, 50, 73),
                }),
                256 => Error::GptError(GptError::PartitionRangeOverlap {
                    prev: (2, 66, 82),
                    next: (1, 82, 105),
                }),
                _ => unimplemented!(),
            };
            test_gpt_sync_restore(modify, modify, err, err, entries_count, data);
        }
    }

    fn apply_to_primary_and_secondary(
        disk: &mut [u8],
        modify: impl Fn(&mut GptHeader, Ref<&mut [u8], [GptEntry]>) + Copy,
    ) {
        let (hdr, entries) =
            (&mut disk[MBR_SIZE..]).split_at_mut(GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE);
        let mut hdr = GptHeader::from_bytes_mut(hdr);
        let n = usize::try_from(gpt_entries_size(hdr.entries_count)).unwrap();
        modify(&mut hdr, Ref::<_, [GptEntry]>::new_slice(&mut entries[..n]).unwrap());

        let (entries, hdr) = (&mut disk[MBR_SIZE..])
            .split_last_chunk_mut::<GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE>()
            .unwrap();
        let mut hdr = GptHeader::from_bytes_mut(&mut hdr[..]);
        let (_, entries) = entries.split_at_mut_checked(entries.len() - n).unwrap();
        modify(&mut hdr, Ref::<_, [GptEntry]>::new_slice(entries).unwrap());
    }

    #[test]
    fn test_sync_gpt_post_null_zero_type_entry_is_unused() {
        fn modify(hdr: &mut GptHeader, mut entries: Ref<&mut [u8], [GptEntry]>) {
            let entry_size = size_of::<GptEntry>();
            entries.as_bytes_mut()[entry_size..2 * entry_size].fill(0);
            entries[2] = entries[0];
            entries[2].part_type = GptGuid([0u8; GPT_GUID_LEN]);
            hdr.update_entries_crc(entries.as_bytes());
        }
        for (_, data) in get_gpt_test_1_data() {
            let mut disk = data.to_vec();
            apply_to_primary_and_secondary(&mut disk, modify);
            let (dev, mut gpt) = test_disk_and_gpt(&disk);
            assert!(block_on(dev.sync_gpt(&mut gpt, false)).is_ok());
            let entries = gpt.entries().unwrap();
            assert_eq!(entries.count(), 1);
        }
    }

    #[test]
    fn test_sync_gpt_post_null_overlap() {
        fn modify(hdr: &mut GptHeader, mut entries: Ref<&mut [u8], [GptEntry]>) {
            let entry_size = size_of::<GptEntry>();
            entries.as_bytes_mut()[entry_size..2 * entry_size].fill(0);
            entries[2] = entries[0];
            entries[2].first = entries[0].first + 1;
            hdr.update_entries_crc(entries.as_bytes());
        }
        for (entries_count, data) in get_gpt_test_1_data() {
            let err = match entries_count {
                128 => Error::GptError(GptError::PartitionRangeOverlap {
                    prev: (1, 34, 49),
                    next: (3, 35, 49),
                }),
                256 => Error::GptError(GptError::PartitionRangeOverlap {
                    prev: (1, 66, 81),
                    next: (3, 67, 81),
                }),
                _ => unimplemented!(),
            };
            test_gpt_sync_restore(modify, modify, err, err, entries_count, data);
        }
    }

    #[test]
    fn test_sync_gpt_zero_partition_type_guid_is_unused() {
        fn modify(hdr: &mut GptHeader, mut entries: Ref<&mut [u8], [GptEntry]>) {
            entries[1].part_type = GptGuid([0u8; GPT_GUID_LEN]);
            hdr.update_entries_crc(entries.as_bytes());
        }
        for (_, data) in get_gpt_test_1_data() {
            let mut disk = data.to_vec();
            apply_to_primary_and_secondary(&mut disk, modify);
            let (dev, mut gpt) = test_disk_and_gpt(&disk);
            assert!(block_on(dev.sync_gpt(&mut gpt, false)).is_ok());
            let entries = gpt.entries().unwrap();
            assert_eq!(entries.count(), 1);
        }
    }

    #[test]
    fn test_sync_gpt_zero_partition_unique_guid() {
        fn modify(hdr: &mut GptHeader, mut entries: Ref<&mut [u8], [GptEntry]>) {
            entries[1].guid = GptGuid([0u8; GPT_GUID_LEN]);
            hdr.update_entries_crc(entries.as_bytes());
        }
        let err = Error::GptError(GptError::ZeroPartitionUniqueGUID { idx: 2 });
        for (entries_count, data) in get_gpt_test_1_data() {
            test_gpt_sync_restore(modify, modify, err, err, entries_count, data);
        }
    }

    #[test]
    fn test_load_gpt_disk_primary_override_secondary() {
        for (_, data) in get_gpt_test_1_data() {
            let mut disk = data.to_vec();
            // Modifies secondary header.
            let secondary_hdr = GptHeader::from_bytes_mut(
                disk.last_chunk_mut::<GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE>().unwrap(),
            );
            secondary_hdr.revision = !secondary_hdr.revision;
            secondary_hdr.update_crc();
            let (dev, mut gpt) = test_disk_and_gpt(&disk);
            assert_eq!(
                block_on(dev.sync_gpt(&mut gpt, true)).unwrap(),
                GptSyncResult::SecondaryRestored(Error::GptError(GptError::DifferentFromPrimary)),
            );
        }
    }

    #[test]
    fn test_load_gpt_disk_too_small() {
        for (_entries_count, data) in get_gpt_test_1_data() {
            let mut disk = data.to_vec();
            // MBR + (header + 0 * entries) * 2 - 1
            disk.resize(MBR_SIZE + GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE * 2 - BLOCK_SIZE, 0);
            let (dev, mut gpt) = test_disk_and_gpt(&disk);
            let sync_res = block_on(dev.sync_gpt(&mut gpt, true)).unwrap();
            assert_eq!(
                sync_res,
                GptSyncResult::NoValidGpt {
                    primary: Error::GptError(GptError::DiskTooSmall),
                    secondary: Error::GptError(GptError::DiskTooSmall)
                }
            );
        }
    }

    #[test]
    fn test_uninitialized_gpt() {
        for (_, data) in get_gpt_test_1_data() {
            // Load a good GPT first.
            let (dev, mut gpt) = test_disk_and_gpt(&data);
            assert_eq!(block_on(dev.sync_gpt(&mut gpt, true)).unwrap(), GptSyncResult::BothValid);
            gpt.find_partition("boot_a").unwrap();
            // Corrupt GPT.
            block_on(dev.write(0, &mut vec![0u8; data.len()])).unwrap();
            assert!(block_on(dev.sync_gpt(&mut gpt, true)).unwrap().res().is_err());
            assert!(gpt.find_partition("").is_err());
        }
    }

    #[test]
    fn test_update_gpt() {
        for (entries_count, data) in get_gpt_test_1_data() {
            let entries_count: usize = entries_count.try_into().unwrap();
            let mut disk = data.to_vec();
            // Erases all GPT headers.
            disk[MBR_BLKS..][..GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE].fill(0);
            disk.last_chunk_mut::<BLOCK_SIZE>().unwrap().fill(0);

            let (dev, mut gpt) = test_disk_and_gpt(&disk);

            assert_ne!(dev.io().storage().deref(), data);
            let size: SafeNum =
                gpt_entries_size(entries_count) + MBR_SIZE + GPT_HEADER_NO_ENTRIES_SIZE;
            let len: usize = size.round_up(BLOCK_SIZE).try_into().unwrap();
            let mut mbr_primary = data[..len].to_vec();
            block_on(dev.update_gpt(&mut mbr_primary, false, &mut gpt)).unwrap();
            assert_eq!(dev.io().storage().deref(), data);
        }
    }

    #[test]
    fn test_update_gpt_has_existing_valid_secondary() {
        for (entries_count, disk_orig) in get_gpt_test_1_data() {
            let mut disk = disk_orig.to_vec();
            // Erases all GPT headers.
            disk[MBR_SIZE..][..GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE].fill(0);
            // Leaves a valid but different secondary GPT.
            let secondary_hdr = GptHeader::from_bytes_mut(
                disk.last_chunk_mut::<GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE>().unwrap(),
            );
            secondary_hdr.revision = !secondary_hdr.revision;
            secondary_hdr.update_crc();

            let (dev, mut gpt) = test_disk_and_gpt(&disk);

            assert_ne!(dev.io().storage().deref(), disk_orig);
            let mut mbr_primary =
                disk_orig[..mbr_gpt_header_size_block_align(entries_count)].to_vec();
            block_on(dev.update_gpt(&mut mbr_primary, false, &mut gpt)).unwrap();
            assert_eq!(dev.io().storage().deref(), disk_orig);
        }
    }

    #[test]
    fn test_update_gpt_last_usable_adjusted() {
        for (entries_count, disk_orig) in get_gpt_test_1_data() {
            let mut disk = disk_orig.to_vec();
            // Erases all GPT headers.
            disk[MBR_SIZE..][..GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE].fill(0);
            disk.last_chunk_mut::<GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE>().unwrap().fill(0);
            // Doubles the disk size.
            disk.resize(disk_orig.len() * 2, 0);

            let (dev, mut gpt) = test_disk_and_gpt(&disk);

            assert_ne!(dev.io().storage().deref(), disk_orig);
            let mut mbr_primary =
                disk_orig[..mbr_gpt_header_size_block_align(entries_count)].to_vec();
            block_on(dev.update_gpt(&mut mbr_primary, true, &mut gpt)).unwrap();
            let expected_last =
                (disk.len() - gpt_header_size_block_align(entries_count)) / BLOCK_SIZE - 1;

            let storage = dev.io.storage();
            let (primary, secondary) =
                storage.split_last_chunk::<GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE>().unwrap();
            let primary_hdr = GptHeader::from_bytes(&primary[MBR_SIZE..]);
            let secondary_hdr = GptHeader::from_bytes(secondary);
            // Header's last usable block is updated.
            assert_eq!({ primary_hdr.last }, expected_last.try_into().unwrap());
            assert_eq!({ primary_hdr.backup }, (disk.len() / BLOCK_SIZE - 1).try_into().unwrap());
            assert_eq!({ secondary_hdr.last }, expected_last.try_into().unwrap());
        }
    }

    #[test]
    fn test_update_gpt_resize() {
        for (entries_count, disk_orig) in get_gpt_test_1_data() {
            let mut disk = disk_orig.to_vec();
            // Erases all GPT headers.
            disk[MBR_SIZE..][..GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE].fill(0);
            disk.last_chunk_mut::<GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE>().unwrap().fill(0);
            // Doubles the disk size.
            disk.resize(disk_orig.len() * 2, 0);

            let (dev, mut gpt) = test_disk_and_gpt(&disk);

            assert_ne!(dev.io().storage().deref(), disk_orig);
            let mut mbr_primary =
                disk_orig[..mbr_gpt_header_size_block_align(entries_count)].to_vec();
            block_on(dev.update_gpt(&mut mbr_primary, true, &mut gpt)).unwrap();
            // Last entry is extended.
            let expected_last =
                (disk.len() - gpt_header_size_block_align(entries_count)) / BLOCK_SIZE - 1;
            assert_eq!(
                { gpt.entries().unwrap().nth(1).unwrap().gpt_entry().last },
                expected_last.try_into().unwrap()
            );
        }
    }

    #[test]
    fn test_update_gpt_new_partition_out_of_range() {
        for (entries_count, data) in get_gpt_test_1_data() {
            // `gpt_test_1.bin` has a 8k "boot_a" and a 12k "boot_b". Thus partitions space is 40
            // blocks (512 bytes block size) and in total the GPT disk needs (40 + 1 + (33) * 2) = 107
            // blocks.
            let partitions_size: usize =
                round_up(8 * 1024, BLOCK_SIZE) + round_up(12 * 1024, BLOCK_SIZE);
            let len = partitions_size
                + mbr_gpt_header_size_block_align(entries_count)
                + gpt_header_size_block_align(entries_count);
            let len_blks = len / BLOCK_SIZE;
            let (dev, mut gpt) = test_disk_and_gpt(&vec![0u8; (len_blks - 1) * BLOCK_SIZE]);
            let mut mbr_primary = data[..gpt_header_size_block_align(entries_count)].to_vec();
            assert!(block_on(dev.update_gpt(&mut mbr_primary, true, &mut gpt)).is_err());
        }
    }

    #[test]
    fn test_update_gpt_buffer_truncated() {
        for (entries_count, data) in get_gpt_test_1_data() {
            let mut disk = data.to_vec();
            let (dev, mut gpt) = test_disk_and_gpt(&disk);

            // Less than 1 MBR block.
            let actual_size = SafeNum::from(MBR_SIZE);
            let len: usize = actual_size.round_up(BLOCK_SIZE).try_into().unwrap();
            assert_eq!(
                block_on(dev.update_gpt(&mut disk[..len - 1], false, &mut gpt)),
                Err(Error::BufferTooSmall(Some(MBR_SIZE + GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE)))
            );

            // Less than MBR + GPT header.
            let actual_size = actual_size + GPT_HEADER_NO_ENTRIES_SIZE;
            let len: usize = actual_size.round_up(BLOCK_SIZE).try_into().unwrap();
            assert_eq!(
                block_on(dev.update_gpt(&mut disk[..len - 1], false, &mut gpt)),
                Err(Error::BufferTooSmall(Some(MBR_SIZE + GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE)))
            );

            // Less than MBR + GPT header + entries.
            let actual_size =
                actual_size + usize::try_from(gpt_entries_size(entries_count)).unwrap();
            let len: usize = actual_size.round_up(BLOCK_SIZE).try_into().unwrap();
            assert_eq!(
                block_on(dev.update_gpt(&mut disk[..len - 1], false, &mut gpt)),
                Err(Error::BufferTooSmall(Some(len)))
            );
        }
    }

    // Returns (actual size, len in bytes rounded to block size)
    fn get_primary_size_len<T>(entries_count: T) -> (SafeNum, usize)
    where
        SafeNum: From<T>,
    {
        let size: SafeNum = gpt_entries_size(entries_count) + MBR_SIZE + GPT_HEADER_NO_ENTRIES_SIZE;
        let len: usize = size.round_up(BLOCK_SIZE).try_into().unwrap();
        (size, len)
    }

    #[test]
    fn test_update_gpt_check_header_fail() {
        for (entries_count, data) in get_gpt_test_1_data() {
            let disk = data;
            let (dev, mut gpt) = test_disk_and_gpt(&disk);
            let (_, len) = get_primary_size_len(entries_count);
            let mut mbr_primary = disk[..len].to_vec();
            // Corrupts the first byte of the GPT header.
            mbr_primary[BLOCK_SIZE] = !mbr_primary[BLOCK_SIZE];
            assert_eq!(
                block_on(dev.update_gpt(&mut mbr_primary, false, &mut gpt)),
                Err(Error::GptError(GptError::IncorrectMagic(0x54524150204946BA)))
            );
        }
    }

    #[test]
    fn test_update_gpt_check_entries_fail() {
        for (entries_count, data) in get_gpt_test_1_data() {
            let disk = data;
            let (dev, mut gpt) = test_disk_and_gpt(&disk);
            let size: SafeNum =
                gpt_entries_size(entries_count) + MBR_SIZE + GPT_HEADER_NO_ENTRIES_SIZE;
            let len: usize = size.round_up(BLOCK_SIZE).try_into().unwrap();
            let mut mbr_primary = disk[..len].to_vec();
            // Corrupts the first byte of the entries.
            let len: usize = SafeNum::from(MBR_SIZE + GPT_HEADER_NO_ENTRIES_SIZE)
                .round_up(BLOCK_SIZE)
                .try_into()
                .unwrap();
            mbr_primary[len] = !mbr_primary[len];
            assert_eq!(
                block_on(dev.update_gpt(&mut mbr_primary, false, &mut gpt)),
                Err(Error::GptError(GptError::IncorrectEntriesCrc))
            );
        }
    }

    #[test]
    fn test_erase_gpt_no_gpt() {
        let (dev, mut gpt) = test_disk_and_gpt(&[0u8; 1024 * 1024]);
        block_on(dev.erase_gpt(&mut gpt)).unwrap();
    }

    #[test]
    fn test_erase_gpt() {
        for (entries_count, data) in get_gpt_test_1_data() {
            let (dev, mut gpt) = test_disk_and_gpt(data);
            block_on(dev.erase_gpt(&mut gpt)).unwrap();
            let size: SafeNum = gpt_entries_size(entries_count) + GPT_HEADER_NO_ENTRIES_SIZE;
            let len: usize = size.round_up(BLOCK_SIZE).try_into().unwrap();
            let mut expected_vec = Vec::with_capacity(len);
            expected_vec.resize(len, 0u8);
            assert_eq!(dev.io().storage().deref()[MBR_SIZE..][..len], expected_vec);
            // New scope to simplify lifetime for dev.io().storage()
            {
                let storage = dev.io().storage();
                let dev_size = storage.len();
                assert_eq!(storage.split_at_checked(dev_size - len).unwrap().1, expected_vec);
            }
            assert!(matches!(
                block_on(dev.sync_gpt(&mut gpt, true)).unwrap(),
                GptSyncResult::NoValidGpt { .. }
            ));
        }
    }

    #[test]
    fn test_zero_partition_size() {
        for (_entries_count, data) in get_gpt_test_1_data() {
            let disk = data.to_vec();
            let (dev, mut gpt) = test_disk_and_gpt(&disk);
            let (mut builder, _) = GptBuilder::new(&dev, &mut gpt).unwrap();
            assert_eq!(builder.remove("boot_a"), Ok(true));
            assert_eq!(builder.remove("boot_b"), Ok(true));
            builder.add("boot_b", [1u8; GPT_GUID_LEN], [1u8; GPT_GUID_LEN], 0, Some(0)).unwrap();
            block_on(builder.persist()).unwrap();
            assert_eq!(gpt.partition_iter().unwrap().next().unwrap().size().unwrap(), 0);
        }
    }

    #[test]
    fn test_sync_gpt_non_sorted_entries() {
        for (_entries_count, data) in get_gpt_test_1_data() {
            let mut disk = data.to_vec();
            let (header, entries) =
                disk[MBR_SIZE..].split_at_mut(GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE);
            let header = GptHeader::from_bytes_mut(header);
            let mut entries = Ref::<_, [GptEntry]>::new_slice(entries).unwrap();
            // Makes partition non-sorted.
            entries.swap(0, 1);
            header.update_entries_crc(entries.as_bytes());
            let (dev, mut gpt) = test_disk_and_gpt(&disk);
            block_on(dev.sync_gpt(&mut gpt, true)).unwrap().res().unwrap();
        }
    }

    #[test]
    fn test_gpt_builder_initialize_gpt_if_no_valid_gpt() {
        let (dev, mut gpt) = test_disk_and_gpt(vec![0u8; 1024 * 1024]);
        let (builder, valid) = GptBuilder::new(&dev, &mut gpt).unwrap();
        assert!(!valid);
        block_on(builder.persist()).unwrap();
        // A new GPT is created.
        block_on(dev.sync_gpt(&mut gpt, true)).unwrap().res().unwrap();
        assert!(gpt.partition_iter().unwrap().next().is_none());
    }

    #[test]
    fn test_gpt_builder_remove_partition() {
        for (_entries_count, data) in get_gpt_test_1_data() {
            let (dev, mut gpt) = test_disk_and_gpt(data);
            let (mut builder, valid) = GptBuilder::new(&dev, &mut gpt).unwrap();
            assert!(valid);
            assert_eq!(builder.remove("boot_b"), Ok(true));
            assert_eq!(builder.remove("non-existent"), Ok(false));
            block_on(builder.persist()).unwrap();
            block_on(dev.sync_gpt(&mut gpt, true)).unwrap().res().unwrap();
            let part_iter = gpt.partition_iter().unwrap();
            assert_eq!(
                part_iter.map(|v| v.name().unwrap().into()).collect::<Vec<String>>(),
                ["boot_a"]
            );
        }
    }

    #[test]
    fn test_gpt_builder_add_partition_find_first() {
        for (entries_count, data) in get_gpt_test_1_data() {
            let (dev, mut gpt) = test_disk_and_gpt(data);
            let (mut builder, _) = GptBuilder::new(&dev, &mut gpt).unwrap();
            assert!(builder.remove("boot_a").unwrap());
            // Adds at the beginning.
            const NEW_PARTITION_0_SIZE: u64 = 1024;
            builder
                .add(
                    "new_0",
                    [1u8; GPT_GUID_LEN],
                    [1u8; GPT_GUID_LEN],
                    0,
                    Some(NEW_PARTITION_0_SIZE),
                )
                .unwrap();
            // Adds following "new_0"
            const NEW_PARTITION_1_SIZE: u64 = 1;
            builder
                .add(
                    "new_1",
                    [1u8; GPT_GUID_LEN],
                    [1u8; GPT_GUID_LEN],
                    0,
                    Some(NEW_PARTITION_1_SIZE),
                )
                .unwrap();
            block_on(builder.persist()).unwrap();
            block_on(dev.sync_gpt(&mut gpt, true)).unwrap().res().unwrap();

            let expected_start: u64 =
                mbr_gpt_header_size_block_align(entries_count).try_into().unwrap();
            let expected_end = expected_start + NEW_PARTITION_0_SIZE;
            assert_eq!(
                gpt.find_partition("new_0").unwrap().absolute_range().unwrap(),
                (expected_start, expected_end)
            );
            let expected_start: u64 = expected_end;
            let expected_end = expected_start
                + u64::try_from(round_up(NEW_PARTITION_1_SIZE.try_into().unwrap(), BLOCK_SIZE))
                    .unwrap();
            assert_eq!(
                gpt.find_partition("new_1").unwrap().absolute_range().unwrap(),
                (expected_start, expected_end)
            );
            let expected_start: u64 = u64::try_from(mbr_gpt_header_size_block_align(entries_count))
                .unwrap()
                + TEST_1_DATA_BOOT_A_SIZE;
            let expected_end = expected_start + TEST_1_DATA_BOOT_B_SIZE;
            assert_eq!(
                gpt.find_partition("boot_b").unwrap().absolute_range().unwrap(),
                (expected_start, expected_end)
            );
        }
    }

    #[test]
    fn test_gpt_builder_non_sorted_add_partition() {
        for (entries_count, data) in get_gpt_test_1_data() {
            let mut disk = data.to_vec();
            let (dev, mut gpt) = test_disk_and_gpt(&disk);
            let (header, entries) =
                disk[MBR_SIZE..].split_at_mut(GPT_HEADER_NO_ENTRIES_FULL_BLOCK_SIZE);
            let header = GptHeader::from_bytes_mut(header);
            let mut entries = Ref::<_, [GptEntry]>::new_slice(entries).unwrap();
            // Makes partition non-sorted.
            entries.swap(0, 1);
            header.update_entries_crc(entries.as_bytes());

            let (mut builder, _) = GptBuilder::new(&dev, &mut gpt).unwrap();
            // Adds following boot_b.
            const NEW_PARTITION_SIZE: u64 = 1024;
            builder
                .add("new", [1u8; GPT_GUID_LEN], [1u8; GPT_GUID_LEN], 0, Some(NEW_PARTITION_SIZE))
                .unwrap();
            block_on(builder.persist()).unwrap();

            let expected_start: u64 =
                mbr_gpt_header_size_block_align(entries_count).try_into().unwrap();
            let expected_end = expected_start + TEST_1_DATA_BOOT_A_SIZE;
            assert_eq!(
                gpt.find_partition("boot_a").unwrap().absolute_range().unwrap(),
                (expected_start, expected_end)
            );
            let expected_start = expected_end;
            let expected_end = expected_start + TEST_1_DATA_BOOT_B_SIZE;
            assert_eq!(
                gpt.find_partition("boot_b").unwrap().absolute_range().unwrap(),
                (expected_start, expected_end)
            );
            let expected_start = expected_end;
            let expected_end = expected_start + NEW_PARTITION_SIZE;
            assert_eq!(
                gpt.find_partition("new").unwrap().absolute_range().unwrap(),
                (expected_start, expected_end)
            );
        }
    }

    #[test]
    fn test_gpt_builder_add_partition_append() {
        for (entries_count, data) in get_gpt_test_1_data() {
            let (dev, mut gpt) = test_disk_and_gpt(data);
            let (mut builder, _) = GptBuilder::new(&dev, &mut gpt).unwrap();
            assert!(builder.remove("boot_b").unwrap());
            // Adds following "boot_a".
            const NEW_PARTITION_SIZE: u64 = 1024;
            builder
                .add("new_0", [1u8; GPT_GUID_LEN], [1u8; GPT_GUID_LEN], 0, Some(NEW_PARTITION_SIZE))
                .unwrap();
            // Consumes the rest of the space.
            builder.add("new_1", [1u8; GPT_GUID_LEN], [1u8; GPT_GUID_LEN], 0, None).unwrap();
            block_on(builder.persist()).unwrap();
            block_on(dev.sync_gpt(&mut gpt, true)).unwrap().res().unwrap();

            let expected_start: u64 =
                mbr_gpt_header_size_block_align(entries_count).try_into().unwrap();
            let expected_end = expected_start + TEST_1_DATA_BOOT_A_SIZE;
            assert_eq!(
                gpt.find_partition("boot_a").unwrap().absolute_range().unwrap(),
                (expected_start, expected_end)
            );
            let expected_start = expected_end;
            let expected_end = expected_start + NEW_PARTITION_SIZE;
            assert_eq!(
                gpt.find_partition("new_0").unwrap().absolute_range().unwrap(),
                (expected_start, expected_end)
            );
            let expected_start = expected_end;
            let expected_end =
                u64::try_from(data.len() - gpt_header_size_block_align(entries_count)).unwrap();
            assert_eq!(
                gpt.find_partition("new_1").unwrap().absolute_range().unwrap(),
                (expected_start, expected_end)
            );
        }
    }

    #[test]
    fn test_gpt_builder_not_enough_resource() {
        // Create a Gpt that can only load 1 entry.
        let mut gpt = new_gpt_n::<1>();
        let dev = test_disk(vec![0u8; 64 * 1024]);
        let (mut builder, _) = GptBuilder::new(&dev, &mut gpt).unwrap();
        builder.add("new_0", [1u8; GPT_GUID_LEN], [1u8; GPT_GUID_LEN], 0, Some(1024)).unwrap();
        assert!(builder.add("new_1", [1u8; GPT_GUID_LEN], [1u8; GPT_GUID_LEN], 0, None).is_err());
    }
}
