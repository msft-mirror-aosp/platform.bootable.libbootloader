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

use crate::error::Result;
use core::ffi::CStr;
use efi::{
    protocol::{
        device_path::{DevicePathProtocol, DevicePathText, DevicePathToTextProtocol},
        loaded_image::LoadedImageProtocol,
        simple_text_input::SimpleTextInputProtocol,
    },
    utils::Timeout,
    DeviceHandle, EfiEntry,
};
use efi_types::EfiGuid;
use fdt::FdtHeader;
use liberror::Error;
use safemath::SafeNum;

pub const EFI_DTB_TABLE_GUID: EfiGuid =
    EfiGuid::new(0xb1b621d5, 0xf19c, 0x41a5, [0x83, 0x0b, 0xd9, 0x15, 0x2c, 0x69, 0xaa, 0xe0]);

/// Gets a subslice of the given slice with aligned address according to `alignment`
pub fn aligned_subslice(
    bytes: &mut [u8],
    alignment: usize,
) -> core::result::Result<&mut [u8], Error> {
    let addr = bytes.as_ptr() as usize;
    let aligned_start = SafeNum::from(addr).round_up(alignment) - addr;
    Ok(&mut bytes[aligned_start.try_into()?..])
}

/// Helper function to get the `DevicePathText` from a `DeviceHandle`.
pub fn get_device_path<'a>(
    entry: &'a EfiEntry,
    handle: DeviceHandle,
) -> Result<DevicePathText<'a>> {
    let bs = entry.system_table().boot_services();
    let path = bs.open_protocol::<DevicePathProtocol>(handle)?;
    let path_to_text = bs.find_first_and_open::<DevicePathToTextProtocol>()?;
    Ok(path_to_text.convert_device_path_to_text(&path, false, false)?)
}

/// Helper function to get the loaded image path.
pub fn loaded_image_path(entry: &EfiEntry) -> Result<DevicePathText> {
    get_device_path(
        entry,
        entry
            .system_table()
            .boot_services()
            .open_protocol::<LoadedImageProtocol>(entry.image_handle())?
            .device_handle()?,
    )
}

/// Find FDT from EFI configuration table.
pub fn get_efi_fdt<'a>(entry: &'a EfiEntry) -> Option<(&FdtHeader, &[u8])> {
    if let Some(config_tables) = entry.system_table().configuration_table() {
        for table in config_tables {
            if table.vendor_guid == EFI_DTB_TABLE_GUID {
                // SAFETY: Buffer provided by EFI configuration table.
                return unsafe { FdtHeader::from_raw(table.vendor_table as *const _).ok() };
            }
        }
    }
    None
}

#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
pub fn efi_to_e820_mem_type(efi_mem_type: u32) -> u32 {
    match efi_mem_type {
        efi_types::EFI_MEMORY_TYPE_LOADER_CODE
        | efi_types::EFI_MEMORY_TYPE_LOADER_DATA
        | efi_types::EFI_MEMORY_TYPE_BOOT_SERVICES_CODE
        | efi_types::EFI_MEMORY_TYPE_BOOT_SERVICES_DATA
        | efi_types::EFI_MEMORY_TYPE_CONVENTIONAL_MEMORY => boot::x86::E820_ADDRESS_TYPE_RAM,
        efi_types::EFI_MEMORY_TYPE_RUNTIME_SERVICES_CODE
        | efi_types::EFI_MEMORY_TYPE_RUNTIME_SERVICES_DATA
        | efi_types::EFI_MEMORY_TYPE_MEMORY_MAPPED_IO
        | efi_types::EFI_MEMORY_TYPE_MEMORY_MAPPED_IOPORT_SPACE
        | efi_types::EFI_MEMORY_TYPE_PAL_CODE
        | efi_types::EFI_MEMORY_TYPE_RESERVED_MEMORY_TYPE => boot::x86::E820_ADDRESS_TYPE_RESERVED,
        efi_types::EFI_MEMORY_TYPE_UNUSABLE_MEMORY => boot::x86::E820_ADDRESS_TYPE_UNUSABLE,
        efi_types::EFI_MEMORY_TYPE_ACPIRECLAIM_MEMORY => boot::x86::E820_ADDRESS_TYPE_ACPI,
        efi_types::EFI_MEMORY_TYPE_ACPIMEMORY_NVS => boot::x86::E820_ADDRESS_TYPE_NVS,
        efi_types::EFI_MEMORY_TYPE_PERSISTENT_MEMORY => boot::x86::E820_ADDRESS_TYPE_PMEM,
        v => panic!("Unmapped EFI memory type {v}"),
    }
}

/// A helper to convert a bytes slice containing a null-terminated string to `str`
pub fn cstr_bytes_to_str(data: &[u8]) -> core::result::Result<&str, Error> {
    Ok(CStr::from_bytes_until_nul(data)?.to_str()?)
}

/// Repetitively runs a closure until it signals completion or timeout.
///
/// * If `f` returns `Ok(R)`, an `Ok(Some(R))` is returned immediately.
/// * If `f` has been repetitively called and returning `Err(false)` for `timeout_ms`,  an
///   `Ok(None)` is returned. This is the time out case.
/// * If `f` returns `Err(true)` the timeout is reset.
pub fn loop_with_timeout<F, R>(efi_entry: &EfiEntry, timeout_ms: u64, mut f: F) -> Result<Option<R>>
where
    F: FnMut() -> core::result::Result<R, bool>,
{
    let timeout = Timeout::new(efi_entry, timeout_ms)?;
    while !timeout.check()? {
        match f() {
            Ok(v) => return Ok(Some(v)),
            Err(true) => timeout.reset(timeout_ms)?,
            _ => {}
        }
    }
    Ok(None)
}

/// Waits for a key stroke value from simple text input.
///
/// Returns `Ok(true)` if the expected key stroke is read, `Ok(false)` if timeout, `Err` otherwise.
pub fn wait_key_stroke(efi_entry: &EfiEntry, expected: char, timeout_ms: u64) -> Result<bool> {
    let input = efi_entry
        .system_table()
        .boot_services()
        .find_first_and_open::<SimpleTextInputProtocol>()?;
    loop_with_timeout(efi_entry, timeout_ms, || -> core::result::Result<Result<bool>, bool> {
        match input.read_key_stroke() {
            Ok(Some(key)) => match char::decode_utf16([key.unicode_char]).next().unwrap() {
                Ok(ch) if ch == expected => Ok(Ok(true)),
                _ => Err(false),
            },
            Ok(None) => Err(false),
            Err(e) => Ok(Err(e.into())),
        }
    })?
    .unwrap_or(Ok(false))
}
