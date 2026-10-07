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

//! This file provides some utilities built on EFI APIs.

use crate::{EfiEntry, Event, EventType};
use core::{str::from_utf8, time::Duration};
use efi_types::{EfiGuid, EFI_TIMER_DELAY_TIMER_RELATIVE};
use fdt::FdtHeader;
use gbl_async::yield_now;
use liberror::Result;

/// `Timeout` provide APIs for checking timeout.
pub struct Timeout<'a> {
    efi_entry: &'a EfiEntry,
    timer: Event<'a, 'static>,
}

impl<'a> Timeout<'a> {
    /// Creates a new instance and starts the timeout timer.
    pub fn new(efi_entry: &'a EfiEntry, timeout: Duration) -> Result<Self> {
        let bs = efi_entry.system_table().boot_services();
        let timer = bs.create_event(EventType::Timer)?;
        bs.set_timer(&timer, EFI_TIMER_DELAY_TIMER_RELATIVE, timeout)?;
        Ok(Self { efi_entry, timer })
    }

    /// Checks if it has timeout.
    pub fn check(&self) -> Result<bool> {
        Ok(self.efi_entry.system_table().boot_services().check_event(&self.timer)?)
    }

    /// Resets the timeout.
    pub fn reset(&self, timeout: Duration) -> Result<()> {
        let bs = self.efi_entry.system_table().boot_services();
        bs.set_timer(&self.timer, EFI_TIMER_DELAY_TIMER_RELATIVE, timeout)?;
        Ok(())
    }
}

/// Waits for a given amount of time.
pub async fn wait(efi_entry: &EfiEntry, duration: Duration) -> Result<()> {
    // EFI boot service has a `stall` API. But it's not async.
    let timeout = Timeout::new(efi_entry, duration)?;
    while !timeout.check()? {
        yield_now().await;
    }
    Ok(())
}

/// Parses the firmware API level from a byte slice.
pub fn parse_fw_api_level(data: &[u8]) -> Result<u64> {
    Ok(from_utf8(data)?.trim_end_matches('\0').trim().parse()?)
}

/// Find a configuration table by GUID.
pub fn find_configuration_table(entry: &EfiEntry, guid: EfiGuid) -> Option<*const u8> {
    let systab = entry.system_table();
    systab
        .configuration_table()
        .and_then(|v| v.iter().find(|v| v.vendor_guid == guid))
        .map(|v| v.vendor_table as *const u8)
}

// TODO(b/486979232): Find better places for these GUID constants.
pub(crate) const EFI_DTB_TABLE_GUID: EfiGuid =
    EfiGuid::new(0xb1b621d5, 0xf19c, 0x41a5, [0x83, 0x0b, 0xd9, 0x15, 0x2c, 0x69, 0xaa, 0xe0]);
pub(crate) const EFI_ACPI_TABLE_GUID: EfiGuid =
    EfiGuid::new(0x8868e871, 0xe4f1, 0x11d3, [0xbc, 0x22, 0x00, 0x80, 0xc7, 0x3c, 0x88, 0x81]);

/// Find FDT from EFI configuration table.
pub fn find_fdt_configuration_table(entry: &EfiEntry) -> Option<(&FdtHeader, &[u8])> {
    if let Some(config_tables) = entry.system_table().configuration_table() {
        for table in config_tables {
            if table.vendor_guid == EFI_DTB_TABLE_GUID {
                // SAFETY: By UEFI spec, the vendor_table points to a valid FDT.
                return unsafe { FdtHeader::from_raw(table.vendor_table as *const _).ok() };
            }
        }
    }
    None
}

/// Find ACPI table from EFI configuration table.
pub fn find_acpi_configuration_table(entry: &EfiEntry) -> Option<*const u8> {
    find_configuration_table(entry, EFI_ACPI_TABLE_GUID)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parse_fw_api_level() {
        assert_eq!(parse_fw_api_level(b"202404\0\0\0").unwrap(), 202404);
        assert_eq!(parse_fw_api_level(b"202404\0").unwrap(), 202404);
        assert_eq!(parse_fw_api_level(b"202404").unwrap(), 202404);
        assert_eq!(parse_fw_api_level(b" 202404 \0").unwrap(), 202404);
        assert!(parse_fw_api_level(b"invalid\0").is_err());
        assert!(parse_fw_api_level(b"2024AA").is_err());
        assert!(parse_fw_api_level(b"").is_err());
        assert!(parse_fw_api_level(b"\0").is_err());
        assert!(parse_fw_api_level(b"202404\0 ").is_err());
    }
}
