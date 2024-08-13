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
use libdttable_bindgen::{dt_table_entry, dt_table_header, DT_TABLE_MAGIC};
use liberror::{Error, Result};
use safemath::SafeNum;
use zerocopy::{AsBytes, FromBytes, FromZeroes, LayoutVerified};

/// Rust wrapper for the dt table header
#[repr(transparent)]
#[derive(Debug, Copy, Clone, AsBytes, FromBytes, FromZeroes, PartialEq)]
struct DtTableHeader(dt_table_header);

impl DtTableHeader {
    /// Get magic handling the bytes order
    fn magic(self) -> u32 {
        u32::from_be(self.0.magic)
    }

    /// Get dt_entry_count handling the bytes order
    fn dt_entry_count(self) -> u32 {
        u32::from_be(self.0.dt_entry_count)
    }

    /// Get dt_entry_size handling the bytes order
    fn dt_entry_size(self) -> u32 {
        u32::from_be(self.0.dt_entry_size)
    }

    /// Get dt_entries_offset handling the bytes order
    fn dt_entries_offset(self) -> u32 {
        u32::from_be(self.0.dt_entries_offset)
    }
}

/// Rust wrapper for the dt table entry
#[repr(transparent)]
#[derive(Debug, Copy, Clone, AsBytes, FromBytes, FromZeroes, PartialEq)]
struct DtTableHeaderEntry(dt_table_entry);

impl DtTableHeaderEntry {
    /// Get id handling the bytes order
    fn id(self) -> u32 {
        u32::from_be(self.0.id)
    }

    /// Get rev handling the bytes order
    fn rev(self) -> u32 {
        u32::from_be(self.0.rev)
    }

    /// Get dt_size handling the bytes order
    fn dt_size(self) -> u32 {
        u32::from_be(self.0.dt_size)
    }

    /// Get dt_offset handling the bytes order
    fn dt_offset(self) -> u32 {
        u32::from_be(self.0.dt_offset)
    }
}

/// Device tree blob obtained from multidt table image
pub struct DtTableEntry<'a> {
    /// id field from corresponding entry header
    pub id: u32,
    /// rev field from corresponding entry header
    pub rev: u32,
    /// dtb payload extracted from image
    pub dtb: &'a [u8],
}

/// Represents entier multidt table image
pub struct DtTableImage<'a> {
    buffer: &'a [u8],
    header: LayoutVerified<&'a [u8], DtTableHeader>,
    entries: LayoutVerified<&'a [u8], [DtTableHeaderEntry]>,
}

impl<'a> DtTableImage<'a> {
    /// Verify and parse passed buffer following multidt table structure
    pub fn from_bytes(buffer: &'a [u8]) -> Result<DtTableImage<'a>> {
        let (header_layout, _) = LayoutVerified::new_from_prefix(buffer)
            .ok_or(Error::BufferTooSmall(Some(size_of::<DtTableHeader>())))?;

        let header: &DtTableHeader = &header_layout;
        if header.magic() != DT_TABLE_MAGIC {
            return Err(Error::BadMagic);
        }

        let entries_offset: SafeNum = header.dt_entries_offset().into();
        let entry_size: SafeNum = header.dt_entry_size().into();
        let entries_count: SafeNum = header.dt_entry_count().into();

        let entries_start = entries_offset.try_into()?;
        let entries_end = (entries_offset + entry_size * entries_count).try_into()?;

        let entries_buffer = buffer
            .get(entries_start..entries_end)
            .ok_or(Error::BufferTooSmall(Some(entries_end)))?;
        let entries_layout =
            LayoutVerified::new_slice(entries_buffer).ok_or(Error::InvalidInput)?;

        Ok(DtTableImage { buffer: buffer, header: header_layout, entries: entries_layout })
    }

    /// Get amount of presented dt entries in the multidt table image
    pub fn entries_count(&self) -> u32 {
        self.header.dt_entry_count()
    }

    /// Get nth dtb buffer with multidt table structure metadata
    pub fn nth_entry(&self, n: usize) -> Result<DtTableEntry<'a>> {
        let entry = self.entries.get(n).ok_or(Error::BadIndex(n))?;

        let dtb_offset: SafeNum = entry.dt_offset().into();
        let dtb_size: SafeNum = entry.dt_size().into();

        let dtb_start: usize = dtb_offset.try_into()?;
        let dtb_end: usize = (dtb_offset + dtb_size).try_into()?;

        let dtb_buffer =
            self.buffer.get(dtb_start..dtb_end).ok_or(Error::BufferTooSmall(Some(dtb_end)))?;

        Ok(DtTableEntry { id: entry.id(), rev: entry.rev(), dtb: dtb_buffer })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use fdt::Fdt;

    #[test]
    fn test_dt_table_is_parsed() {
        let dttable = include_bytes!("../test/dttable.img").to_vec();
        let table = DtTableImage::from_bytes(&dttable[..]).unwrap();

        assert_eq!(table.entries_count(), 2, "Test data dttable image must have 2 dtb entries");

        let first_entry = table.nth_entry(0).unwrap();
        let second_entry = table.nth_entry(1).unwrap();

        assert_eq!(first_entry.id, 1, "First dttable entry id is incorrect");
        assert_eq!(first_entry.rev, 0, "First dttable entry rev is incorrect");
        assert_eq!(second_entry.id, 2, "Second dttable entry id is incorrect");
        assert_eq!(second_entry.rev, 0, "Second dttable entry rev is incorrect");

        // verify fdt headers are properly parsed
        let _ = Fdt::new(first_entry.dtb).unwrap();
        let _ = Fdt::new(second_entry.dtb).unwrap();
    }

    #[test]
    fn test_failed_to_parse_corrupted_dt_table() {
        let dttable = include_bytes!("../test/corrupted_dttable.img").to_vec();

        assert!(
            DtTableImage::from_bytes(&dttable[..]).is_err(),
            "Must fail when trying to parse corrupted dt table image"
        );
    }
}
