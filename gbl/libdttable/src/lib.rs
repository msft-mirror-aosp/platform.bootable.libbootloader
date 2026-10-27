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

//! This library provides a wrapper APIs for libdttable_c
//! https://source.android.com/docs/core/architecture/dto/partitions

#![cfg_attr(not(test), no_std)]

use core::mem::size_of;
use libdttable_bindgen::{
    dt_table_entry, dt_table_entry_v1, dt_table_entry_v2, dt_table_header, DT_TABLE_MAGIC,
};
use liberror::{Error, Result};
use safemath::SafeNum;
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout, Ref};

/// Rust wrapper for the dt table header
#[repr(transparent)]
#[derive(Copy, Clone, Debug, PartialEq, Immutable, FromBytes, IntoBytes, KnownLayout)]
struct DtTableHeader(dt_table_header);

impl DtTableHeader {
    /// Get magic handling the bytes order
    fn magic(&self) -> u32 {
        u32::from_be(self.0.magic)
    }

    /// Get the entry layout version handling the bytes order
    fn version(&self) -> u32 {
        u32::from_be(self.0.version)
    }

    /// Get dt_entry_count handling the bytes order
    fn dt_entry_count(&self) -> u32 {
        u32::from_be(self.0.dt_entry_count)
    }

    /// Get dt_entry_size handling the bytes order
    fn dt_entry_size(&self) -> u32 {
        u32::from_be(self.0.dt_entry_size)
    }

    /// Get dt_entries_offset handling the bytes order
    fn dt_entries_offset(&self) -> u32 {
        u32::from_be(self.0.dt_entries_offset)
    }
}

/// Maximum number of `custom` metadata words an entry can carry. Defined by the
/// largest supported entry layout, `dt_table_entry_v2` (`custom[11]`).
pub const MAX_CUSTOM_LEN: usize = 11;

/// Metadata provided by entry header.
///
/// This is a version-independent view of an entry: `id` and `rev` are present
/// in every layout, while `custom` exposes the version-dependent number of
/// OEM-defined fields (4 for v0, 3 for v1, up to 11 for v2).
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct DtTableMetadata {
    /// id field from corresponding entry header
    pub id: u32,
    /// rev field from corresponding entry header
    pub rev: u32,
    /// custom fields, zero-padded, only the first `custom_len` are meaningful
    custom: [u32; MAX_CUSTOM_LEN],
    /// number of meaningful entries in `custom`
    custom_len: usize,
}

impl DtTableMetadata {
    /// Builds metadata from host-order `id`/`rev` and host-order custom fields.
    fn new(id: u32, rev: u32, custom: &[u32]) -> Self {
        let mut buf = [0u32; MAX_CUSTOM_LEN];
        buf[..custom.len()].copy_from_slice(custom);
        Self { id, rev, custom: buf, custom_len: custom.len() }
    }

    /// OEM-defined custom selection fields.
    pub fn custom(&self) -> &[u32] {
        &self.custom[..self.custom_len]
    }
}

/// A version-independent, decoded view of one entry: where its dtb payload
/// lives, plus its selection metadata.
struct DtTableEntryView {
    /// Big-endian-decoded offset of the dtb payload from the head of the image.
    dtb_offset: u32,
    /// Big-endian-decoded size of the dtb payload.
    dtb_size: u32,
    /// Version-independent selection metadata.
    metadata: DtTableMetadata,
}

impl DtTableEntryView {
    /// Builds a view from one entry's raw big-endian fields.
    fn from_be<const N: usize>(
        dt_offset: u32,
        dt_size: u32,
        id: u32,
        rev: u32,
        custom: [u32; N],
    ) -> Self {
        Self {
            dtb_offset: u32::from_be(dt_offset),
            dtb_size: u32::from_be(dt_size),
            metadata: DtTableMetadata::new(
                u32::from_be(id),
                u32::from_be(rev),
                &custom.map(u32::from_be),
            ),
        }
    }
}

/// `dt_table_entry` layout version, taken from `dt_table_header.version`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum DtTableEntryVersion {
    V0,
    V1,
    V2,
}

impl DtTableEntryVersion {
    /// Maps a raw header `version` value to a known layout.
    fn from_header(value: u32) -> Result<Self> {
        match value {
            0 => Ok(Self::V0),
            1 => Ok(Self::V1),
            2 => Ok(Self::V2),
            _ => Err(Error::UnsupportedVersion),
        }
    }

    /// `sizeof(struct dt_table_entry*)` for this version, i.e. the on-disk
    /// stride between consecutive entries.
    fn entry_size(self) -> usize {
        match self {
            Self::V0 => size_of::<dt_table_entry>(),
            Self::V1 => size_of::<dt_table_entry_v1>(),
            Self::V2 => size_of::<dt_table_entry_v2>(),
        }
    }
}

/// Parsed entry records, typed by the image's entry version.
enum DtTableEntries<'a> {
    V0(Ref<&'a [u8], [dt_table_entry]>),
    V1(Ref<&'a [u8], [dt_table_entry_v1]>),
    V2(Ref<&'a [u8], [dt_table_entry_v2]>),
}

impl<'a> DtTableEntries<'a> {
    /// Parses `buffer` as a slice of entries for the given `version`. `buffer`
    /// length must be an exact multiple of the version's entry size.
    fn parse(version: DtTableEntryVersion, buffer: &'a [u8]) -> Result<Self> {
        Ok(match version {
            DtTableEntryVersion::V0 => Self::V0(Ref::new_slice(buffer).ok_or(Error::InvalidInput)?),
            DtTableEntryVersion::V1 => Self::V1(Ref::new_slice(buffer).ok_or(Error::InvalidInput)?),
            DtTableEntryVersion::V2 => Self::V2(Ref::new_slice(buffer).ok_or(Error::InvalidInput)?),
        })
    }

    /// Returns the `n`th entry as a version-independent view.
    fn get(&self, n: usize) -> Result<DtTableEntryView> {
        match self {
            Self::V0(entries) => entries
                .get(n)
                .map(|e| DtTableEntryView::from_be(e.dt_offset, e.dt_size, e.id, e.rev, e.custom)),
            Self::V1(entries) => entries
                .get(n)
                .map(|e| DtTableEntryView::from_be(e.dt_offset, e.dt_size, e.id, e.rev, e.custom)),
            Self::V2(entries) => entries
                .get(n)
                .map(|e| DtTableEntryView::from_be(e.dt_offset, e.dt_size, e.id, e.rev, e.custom)),
        }
        .ok_or(Error::BadIndex(n))
    }

    /// Number of parsed entries.
    fn len(&self) -> usize {
        match self {
            Self::V0(entries) => entries.len(),
            Self::V1(entries) => entries.len(),
            Self::V2(entries) => entries.len(),
        }
    }
}

/// Device tree blob obtained from multidt table image
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct DtTableEntry<'a> {
    /// dtb payload extracted from image
    pub dtb: &'a [u8],
    /// Metadata provided by corresponding entry header
    pub metadata: DtTableMetadata,
}

/// Represents entire multidt table image
pub struct DtTableImage<'a> {
    buffer: &'a [u8],
    entries: DtTableEntries<'a>,
}

/// To iterate over entries.
pub struct DtTableImageIterator<'a, 'b> {
    table_image: &'b DtTableImage<'a>,
    current_index: usize,
}

impl<'a, 'b> Iterator for DtTableImageIterator<'a, 'b> {
    type Item = DtTableEntry<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current_index < self.table_image.entries_count() {
            let result = self.table_image.nth_entry(self.current_index).unwrap();
            self.current_index += 1;
            Some(result)
        } else {
            None
        }
    }
}

impl<'a> DtTableImage<'a> {
    /// Verify and parse passed buffer following multidt table structure
    pub fn from_bytes(buffer: &'a [u8]) -> Result<DtTableImage<'a>> {
        let (header_layout, _) = Ref::new_from_prefix(buffer)
            .ok_or(Error::BufferTooSmall(Some(size_of::<DtTableHeader>())))?;

        let header: &DtTableHeader = &header_layout;
        if header.magic() != DT_TABLE_MAGIC {
            return Err(Error::BadMagic);
        }

        let version = DtTableEntryVersion::from_header(header.version())?;
        if header.dt_entry_size() as usize != version.entry_size() {
            return Err(Error::InvalidInput);
        }

        let entries_offset: SafeNum = header.dt_entries_offset().into();
        let entry_size: SafeNum = header.dt_entry_size().into();
        let entries_count: SafeNum = header.dt_entry_count().into();

        let entries_start = entries_offset.try_into()?;
        let entries_end = (entries_offset + entry_size * entries_count).try_into()?;

        let entries_buffer = buffer
            .get(entries_start..entries_end)
            .ok_or(Error::BufferTooSmall(Some(entries_end)))?;
        let entries = DtTableEntries::parse(version, entries_buffer)?;

        Ok(DtTableImage { buffer, entries })
    }

    /// Get amount of presented dt entries in the multidt table image
    pub fn entries_count(&self) -> usize {
        self.entries.len()
    }

    /// Returns an iterator over the entries in the DT table image
    pub fn entries<'b>(&'b self) -> DtTableImageIterator<'a, 'b> {
        DtTableImageIterator { table_image: self, current_index: 0 }
    }

    /// Get nth dtb buffer with multidt table structure metadata
    pub fn nth_entry(&self, n: usize) -> Result<DtTableEntry<'a>> {
        let entry = self.entries.get(n)?;

        let dtb_offset: SafeNum = entry.dtb_offset.into();
        let dtb_size: SafeNum = entry.dtb_size.into();

        let dtb_start: usize = dtb_offset.try_into()?;
        let dtb_end: usize = (dtb_offset + dtb_size).try_into()?;

        let dtb_buffer =
            self.buffer.get(dtb_start..dtb_end).ok_or(Error::BufferTooSmall(Some(dtb_end)))?;

        Ok(DtTableEntry { dtb: dtb_buffer, metadata: entry.metadata })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use fdt::Fdt;
    use libtestutils::AlignedBuffer;

    fn verify_entries<'a>(
        entries: impl Iterator<Item = DtTableEntry<'a>>,
        expected_custom: &[u32],
    ) {
        let mut aligned = AlignedBuffer::new(4096, 8);
        let mut count = 0;
        for (i, entry) in entries.enumerate() {
            aligned[..entry.dtb.len()].copy_from_slice(entry.dtb);

            assert_eq!(entry.metadata.id, i.try_into().unwrap());
            assert_eq!(entry.metadata.rev, 0);
            assert_eq!(entry.metadata.custom(), expected_custom);
            assert_eq!(
                Fdt::new(&aligned[..]).unwrap().get_property_u32("device", c"value").unwrap(),
                i.try_into().unwrap()
            );
            count += 1;
        }
        assert_eq!(count, 4, "Must have exactly 4 entries");
    }

    fn verify_parsed_table(table: &DtTableImage, expected_custom: &[u32]) {
        assert_eq!(table.entries_count(), 4, "Test data dttable image must have 4 dtb entries");
        let entries = (0..table.entries_count()).map(|i| table.nth_entry(i).unwrap());
        verify_entries(entries, expected_custom);
    }

    fn verify_iterator(table: &DtTableImage, expected_custom: &[u32]) {
        assert_eq!(table.entries().count(), 4, "Iterator should yield 4 entries");
        verify_entries(table.entries(), expected_custom);
    }

    #[test]
    fn test_dt_table_v0_is_parsed() {
        let dttable = include_bytes!("../test/data/dttable_v0.img").to_vec();
        let table = DtTableImage::from_bytes(&dttable[..]).unwrap();
        verify_parsed_table(&table, &[0u32, 1, 2, 3]);
    }

    #[test]
    fn test_dt_table_v1_is_parsed() {
        let dttable = include_bytes!("../test/data/dttable_v1.img").to_vec();
        let table = DtTableImage::from_bytes(&dttable[..]).unwrap();
        verify_parsed_table(&table, &[0u32, 1, 2]);
    }

    #[test]
    fn test_dt_table_v2_is_parsed() {
        let dttable = include_bytes!("../test/data/dttable_v2.img").to_vec();
        let table = DtTableImage::from_bytes(&dttable[..]).unwrap();
        verify_parsed_table(&table, &[0u32, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    }

    #[test]
    fn test_dt_table_v0_is_parsed_iterator() {
        let dttable = include_bytes!("../test/data/dttable_v0.img").to_vec();
        let table = DtTableImage::from_bytes(&dttable[..]).unwrap();
        verify_iterator(&table, &[0u32, 1, 2, 3]);
    }

    #[test]
    fn test_dt_table_v1_is_parsed_iterator() {
        let dttable = include_bytes!("../test/data/dttable_v1.img").to_vec();
        let table = DtTableImage::from_bytes(&dttable[..]).unwrap();
        verify_iterator(&table, &[0u32, 1, 2]);
    }

    #[test]
    fn test_dt_table_v2_is_parsed_iterator() {
        let dttable = include_bytes!("../test/data/dttable_v2.img").to_vec();
        let table = DtTableImage::from_bytes(&dttable[..]).unwrap();
        verify_iterator(&table, &[0u32, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    }

    #[test]
    fn test_failed_to_parse_corrupted_dt_table() {
        let dttable = include_bytes!("../test/data/corrupted_dttable.img").to_vec();

        assert!(
            DtTableImage::from_bytes(&dttable[..]).is_err(),
            "Must fail when trying to parse corrupted dt table image"
        );
    }
}
