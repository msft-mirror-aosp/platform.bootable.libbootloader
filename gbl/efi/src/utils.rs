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

use crate::error::{EfiAppError, Result};
use core::ffi::CStr;
use efi::{
    defs::{EfiGuid, EFI_TIMER_DELAY_TIMER_RELATIVE},
    protocol::{
        device_path::{DevicePathProtocol, DevicePathText, DevicePathToTextProtocol},
        loaded_image::LoadedImageProtocol,
        simple_text_input::SimpleTextInputProtocol,
    },
    DeviceHandle, EfiEntry, Event, EventType,
};
use fdt::FdtHeader;

pub const EFI_DTB_TABLE_GUID: EfiGuid =
    EfiGuid::new(0xb1b621d5, 0xf19c, 0x41a5, [0x83, 0x0b, 0xd9, 0x15, 0x2c, 0x69, 0xaa, 0xe0]);

/// Checks and converts an integer into usize
pub fn to_usize<T: TryInto<usize>>(val: T) -> Result<usize> {
    Ok(val.try_into().map_err(|_| EfiAppError::ArithmeticOverflow)?)
}

/// Rounds up a usize convertible number.
pub fn usize_roundup<L: TryInto<usize>, R: TryInto<usize>>(lhs: L, rhs: R) -> Result<usize> {
    // (lhs + rhs - 1) / rhs * rhs
    let lhs = to_usize(lhs)?;
    let rhs = to_usize(rhs)?;
    let compute = || lhs.checked_add(rhs.checked_sub(1)?)?.checked_div(rhs)?.checked_mul(rhs);
    Ok(compute().ok_or_else(|| EfiAppError::ArithmeticOverflow)?)
}

/// Adds two usize convertible numbers and checks overflow.
pub fn usize_add<L: TryInto<usize>, R: TryInto<usize>>(lhs: L, rhs: R) -> Result<usize> {
    Ok(to_usize(lhs)?.checked_add(to_usize(rhs)?).ok_or_else(|| EfiAppError::ArithmeticOverflow)?)
}

/// Gets a subslice of the given slice with aligned address according to `alignment`
pub fn aligned_subslice(bytes: &mut [u8], alignment: usize) -> Result<&mut [u8]> {
    let addr = bytes.as_ptr() as usize;
    Ok(&mut bytes[usize_roundup(addr, alignment)? - addr..])
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
        efi::defs::EFI_MEMORY_TYPE_LOADER_CODE
        | efi::defs::EFI_MEMORY_TYPE_LOADER_DATA
        | efi::defs::EFI_MEMORY_TYPE_BOOT_SERVICES_CODE
        | efi::defs::EFI_MEMORY_TYPE_BOOT_SERVICES_DATA
        | efi::defs::EFI_MEMORY_TYPE_CONVENTIONAL_MEMORY => boot::x86::E820_ADDRESS_TYPE_RAM,
        efi::defs::EFI_MEMORY_TYPE_RUNTIME_SERVICES_CODE
        | efi::defs::EFI_MEMORY_TYPE_RUNTIME_SERVICES_DATA
        | efi::defs::EFI_MEMORY_TYPE_MEMORY_MAPPED_IO
        | efi::defs::EFI_MEMORY_TYPE_MEMORY_MAPPED_IOPORT_SPACE
        | efi::defs::EFI_MEMORY_TYPE_PAL_CODE
        | efi::defs::EFI_MEMORY_TYPE_RESERVED_MEMORY_TYPE => boot::x86::E820_ADDRESS_TYPE_RESERVED,
        efi::defs::EFI_MEMORY_TYPE_UNUSABLE_MEMORY => boot::x86::E820_ADDRESS_TYPE_UNUSABLE,
        efi::defs::EFI_MEMORY_TYPE_ACPIRECLAIM_MEMORY => boot::x86::E820_ADDRESS_TYPE_ACPI,
        efi::defs::EFI_MEMORY_TYPE_ACPIMEMORY_NVS => boot::x86::E820_ADDRESS_TYPE_NVS,
        efi::defs::EFI_MEMORY_TYPE_PERSISTENT_MEMORY => boot::x86::E820_ADDRESS_TYPE_PMEM,
        v => panic!("Unmapped EFI memory type {v}"),
    }
}

/// A helper to convert a bytes slice containing a null-terminated string to `str`
pub fn cstr_bytes_to_str(data: &[u8]) -> Result<&str> {
    Ok(CStr::from_bytes_until_nul(data)
        .map_err(|_| EfiAppError::InvalidString)?
        .to_str()
        .map_err(|_| EfiAppError::InvalidString)?)
}

/// Converts 1 ms to number of 100 nano seconds
pub fn ms_to_100ns(ms: u64) -> Result<u64> {
    Ok(ms.checked_mul(1000 * 10).ok_or(EfiAppError::ArithmeticOverflow)?)
}

/// `Timeout` provide APIs for checking timeout.
pub struct Timeout<'a> {
    efi_entry: &'a EfiEntry,
    timer: Event<'a, 'static>,
}

impl<'a> Timeout<'a> {
    /// Creates a new instance and starts the timeout timer.
    pub fn new(efi_entry: &'a EfiEntry, timeout_ms: u64) -> Result<Self> {
        let bs = efi_entry.system_table().boot_services();
        let timer = bs.create_event(EventType::Timer, None)?;
        bs.set_timer(&timer, EFI_TIMER_DELAY_TIMER_RELATIVE, ms_to_100ns(timeout_ms)?)?;
        Ok(Self { efi_entry, timer })
    }

    /// Checks if it has timeout.
    pub fn check(&self) -> Result<bool> {
        Ok(self.efi_entry.system_table().boot_services().check_event(&self.timer)?)
    }

    /// Resets the timeout.
    pub fn reset(&self, timeout_ms: u64) -> Result<()> {
        let bs = self.efi_entry.system_table().boot_services();
        bs.set_timer(&self.timer, EFI_TIMER_DELAY_TIMER_RELATIVE, ms_to_100ns(timeout_ms)?)?;
        Ok(())
    }
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
