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

//! Rust wrapper for `EFI_DEVICE_PATH_PROTOCOL`.

use crate::defs::{
    EfiDevicePathProtocol, EfiDevicePathToTextProtocol, EfiGuid, EFI_STATUS_NOT_FOUND,
};
use crate::protocol::{Protocol, ProtocolInfo};
use crate::{EfiEntry, EfiError, EfiResult};
use core::fmt::Display;

/// `EFI_DEVICE_PATH_PROTOCOL`
pub struct DevicePathProtocol;

impl ProtocolInfo for DevicePathProtocol {
    type InterfaceType = EfiDevicePathProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0x09576e91, 0x6d3f, 0x11d2, [0x8e, 0x39, 0x00, 0xa0, 0xc9, 0x69, 0x72, 0x3b]);
}

/// `EFI_DEVICE_PATH_TO_TEXT_PROTOCOL`
pub struct DevicePathToTextProtocol;

impl ProtocolInfo for DevicePathToTextProtocol {
    type InterfaceType = EfiDevicePathToTextProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0x8b843e20, 0x8132, 0x4852, [0x90, 0xcc, 0x55, 0x1a, 0x4e, 0x4a, 0x7f, 0x1c]);
}

impl<'a> Protocol<'a, DevicePathToTextProtocol> {
    /// Wrapper of `EFI_DEVICE_PATH_TO_TEXT_PROTOCOL.ConvertDevicePathToText()`
    pub fn convert_device_path_to_text(
        &self,
        device_path: &Protocol<DevicePathProtocol>,
        display_only: bool,
        allow_shortcuts: bool,
    ) -> EfiResult<DevicePathText<'a>> {
        let f = self
            .interface()?
            .convert_device_path_to_text
            .as_ref()
            .ok_or_else::<EfiError, _>(|| EFI_STATUS_NOT_FOUND.into())?;
        // SAFETY:
        // `self.interface()?` guarantees `self.interface` is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is input parameter and will not be retained. It outlives the call.
        let res = unsafe { f(device_path.interface_ptr(), display_only, allow_shortcuts) };
        Ok(DevicePathText::new(res, self.efi_entry))
    }
}

/// `DevicePathText` is a wrapper for the return type of
/// EFI_DEVICE_PATH_TO_TEXT_PROTOCOL.ConvertDevicePathToText().
pub struct DevicePathText<'a> {
    text: Option<&'a [u16]>,
    efi_entry: &'a EfiEntry,
}

impl<'a> DevicePathText<'a> {
    pub(crate) fn new(text: *mut u16, efi_entry: &'a EfiEntry) -> Self {
        if text.is_null() {
            return Self { text: None, efi_entry: efi_entry };
        }

        let mut len: usize = 0;
        // SAFETY: UEFI text is NULL terminated.
        while unsafe { *text.add(len) } != 0 {
            len += 1;
        }
        Self {
            // SAFETY: Pointer is confirmed non-null with known length at this point.
            text: Some(unsafe { core::slice::from_raw_parts(text, len) }),
            efi_entry: efi_entry,
        }
    }

    /// Get the text as a u16 slice.
    pub fn text(&self) -> Option<&[u16]> {
        self.text
    }
}

impl Display for DevicePathText<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if let Some(text) = self.text {
            for c in char::decode_utf16(text.into_iter().map(|v| *v)) {
                match c.unwrap_or(char::REPLACEMENT_CHARACTER) {
                    '\0' => break,
                    ch => write!(f, "{}", ch)?,
                };
            }
        }
        Ok(())
    }
}

impl Drop for DevicePathText<'_> {
    fn drop(&mut self) {
        if let Some(text) = self.text {
            self.efi_entry
                .system_table()
                .boot_services()
                .free_pool(text.as_ptr() as *mut _)
                .unwrap();
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::*;
    use core::ptr::null_mut;

    #[test]
    fn test_device_path_text_drop() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let mut data: [u16; 4] = [1, 2, 3, 0];
            {
                let path = DevicePathText::new(data.as_mut_ptr(), &efi_entry);
                assert_eq!(path.text().unwrap().to_vec(), vec![1, 2, 3]);
            }
            efi_call_traces().with(|traces| {
                assert_eq!(
                    traces.borrow_mut().free_pool_trace.inputs,
                    [data.as_mut_ptr() as *mut _]
                );
            });
        })
    }

    #[test]
    fn test_device_path_text_null() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            {
                assert_eq!(DevicePathText::new(null_mut(), &efi_entry).text(), None);
            }
            efi_call_traces().with(|traces| {
                assert_eq!(traces.borrow_mut().free_pool_trace.inputs.len(), 0);
            });
        })
    }
}
