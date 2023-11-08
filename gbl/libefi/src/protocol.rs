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

use core::fmt::{Display, Write};
use core::ptr::null_mut;

use crate::defs::*;
use crate::{map_efi_err, DeviceHandle, EfiEntry, EfiError, EfiResult};

/// ProtocolInfo provides GUID info and the EFI data structure type for a protocol.
pub trait ProtocolInfo {
    /// Data structure type of the interface.
    type InterfaceType;
    /// GUID of the protocol.
    const GUID: EfiGuid;
}

/// A generic type for representing an EFI protcol.
pub struct Protocol<'a, T: ProtocolInfo> {
    // The handle to the device offering the protocol. It's needed for closing the protocol.
    device: DeviceHandle,
    // The interface protocol itself.
    interface: *mut T::InterfaceType,
    // The `EfiEntry` data
    efi_entry: &'a EfiEntry,
}

/// A base implementation for Protocol<T>.
/// Protocol<T> will have additional implementation based on type `T`.
impl<'a, T: ProtocolInfo> Protocol<'a, T> {
    /// Create a new instance with the given device handle, interface pointer and `EfiEntry` data.
    pub(crate) fn new(
        device: DeviceHandle,
        interface: *mut T::InterfaceType,
        efi_entry: &'a EfiEntry,
    ) -> Self {
        Self { device, interface, efi_entry }
    }

    /// Returns the EFI data structure for the protocol interface.
    pub fn interface(&self) -> EfiResult<&T::InterfaceType> {
        // SAFETY: EFI protocol interface data structure.
        unsafe { self.interface.as_ref() }.ok_or_else(|| EFI_STATUS_INVALID_PARAMETER.into())
    }

    /// Returns the mutable pointer of the interface. Invisible from outside. Application should
    /// not have any need to alter the content of interface data.
    pub(crate) fn interface_ptr(&self) -> *mut T::InterfaceType {
        self.interface
    }
}

impl<T: ProtocolInfo> Drop for Protocol<'_, T> {
    fn drop(&mut self) {
        // If the device handle is not specified when creating the Protocol<T>, treat the
        // handle as a static permanent reference and don't close it. An example is
        // `EFI_SYSTEM_TABLE.ConOut`.
        if self.device.0 != null_mut() {
            self.efi_entry.system_table().boot_services().close_protocol::<T>(self.device).unwrap();
        }
    }
}

impl EfiGuid {
    pub const fn new(data1: u32, data2: u16, data3: u16, data4: [u8; 8usize]) -> Self {
        EfiGuid { data1, data2, data3, data4 }
    }
}

#[macro_export]
macro_rules! efi_call {
    ( $method:expr, $($x:expr),* ) => {
        {
            let res: EfiResult<()> = match $method {
                None => Err(EFI_STATUS_NOT_FOUND.into()),
                Some(f) => map_efi_err(f($($x,)*))
            };
            res
        }
    };
}

// Following are protocol specific implementations for Protocol<T>.
// TODO(300168989): Consdier splitting each protocol into separate file as we add more protocols.

/// EFI_BLOCK_IO_PROTOCOL
pub struct BlockIoProtocol;

impl ProtocolInfo for BlockIoProtocol {
    type InterfaceType = EfiBlockIoProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0x964e5b21, 0x6459, 0x11d2, [0x8e, 0x39, 0x00, 0xa0, 0xc9, 0x69, 0x72, 0x3b]);
}

// Protocol interface wrappers.
impl Protocol<'_, BlockIoProtocol> {
    /// Wrapper of `EFI_BLOCK_IO_PROTOCOL.read_blocks()`
    pub fn read_blocks(&self, lba: u64, buffer: &mut [u8]) -> EfiResult<()> {
        // SAFETY: EFI protocol method call.
        unsafe {
            efi_call!(
                self.interface()?.read_blocks,
                self.interface,
                self.media()?.media_id,
                lba,
                buffer.len(),
                buffer.as_mut_ptr() as *mut _
            )
        }
    }

    /// Wrapper of `EFI_BLOCK_IO_PROTOCOL.write_blocks()`
    pub fn write_blocks(&self, lba: u64, buffer: &[u8]) -> EfiResult<()> {
        // SAFETY: EFI protocol method call.
        unsafe {
            efi_call!(
                self.interface()?.write_blocks,
                self.interface,
                self.media()?.media_id,
                lba,
                buffer.len(),
                buffer.as_ptr() as *const _
            )
        }
    }

    /// Wrapper of `EFI_BLOCK_IO_PROTOCOL.flush_blocks()`
    pub fn flush_blocks(&self) -> EfiResult<()> {
        // SAFETY: EFI protocol method call.
        unsafe { efi_call!(self.interface()?.flush_blocks, self.interface) }
    }

    /// Wrapper of `EFI_BLOCK_IO_PROTOCOL.reset()`
    pub fn reset(&self, extended_verification: bool) -> EfiResult<()> {
        // SAFETY: EFI protocol method call.
        unsafe { efi_call!(self.interface()?.reset, self.interface, extended_verification) }
    }

    /// Get a reference to EFI_BLOCK_IO_PROTOCOL.Media structure.
    pub fn media(&self) -> EfiResult<&EfiBlockIoMedia> {
        let ptr = self.interface()?.media;
        // SFETY: Pointers to EFI data structure.
        unsafe { ptr.as_ref() }.ok_or_else(|| EFI_STATUS_INVALID_PARAMETER.into())
    }
}

/// EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL
pub struct SimpleTextOutputProtocol;

impl ProtocolInfo for SimpleTextOutputProtocol {
    type InterfaceType = EfiSimpleTextOutputProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0x387477c2, 0x69c7, 0x11d2, [0x8e, 0x39, 0x00, 0xa0, 0xc9, 0x69, 0x72, 0x3b]);
}

impl Protocol<'_, SimpleTextOutputProtocol> {
    /// Wrapper of `EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL.OutputString()`
    pub fn output_string(&self, msg: *mut char16_t) -> EfiResult<()> {
        // SAFETY: EFI protocol method call.
        unsafe { efi_call!(self.interface()?.output_string, self.interface, msg) }
    }
}

/// Implement formatted write for `EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL`, so that we can print by
/// writing to it. i.e.:
///
/// ```
/// let protocol: Protocol<SimpleTextOutputProtocol> = ...;
/// write!(protocol, "Value = {}\n", 1234);
/// ```
impl Write for Protocol<'_, SimpleTextOutputProtocol> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for ch in s.chars() {
            // 2 is enough for encode_utf16(). Add an additional one as NULL.
            let mut buffer = [0u16; 3];
            let char16_msg = ch.encode_utf16(&mut buffer[..]);
            self.output_string(char16_msg.as_mut_ptr()).map_err(|_| core::fmt::Error {})?;
        }
        Ok(())
    }
}

// A convenient convert to forward error when using write!() on
// Protocol<SimpleTextOutputProtocol>.
impl From<core::fmt::Error> for EfiError {
    fn from(_: core::fmt::Error) -> EfiError {
        EFI_STATUS_UNSUPPORTED.into()
    }
}

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
        // SAFETY: EFI protocol method call.
        let res = unsafe { f(device_path.interface_ptr(), display_only, allow_shortcuts) };
        Ok(DevicePathText::new(res, self.efi_entry))
    }
}

// `DevicePathText` is a wrapper for the return type of
// EFI_DEVICE_PATH_TO_TEXT_PROTOCOL.ConvertDevicePathToText().
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

/// EFI_LOADED_IMAGE_PROTOCOL
pub struct LoadedImageProtocol;

impl ProtocolInfo for LoadedImageProtocol {
    type InterfaceType = EfiLoadedImageProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0x5b1b31a1, 0x9562, 0x11d2, [0x8e, 0x3f, 0x00, 0xa0, 0xc9, 0x69, 0x72, 0x3b]);
}

impl<'a> Protocol<'a, LoadedImageProtocol> {
    pub fn device_handle(&self) -> EfiResult<DeviceHandle> {
        Ok(DeviceHandle(self.interface()?.device_handle))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::*;

    #[test]
    fn test_dont_close_protocol_without_device_handle() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            {
                Protocol::<BlockIoProtocol>::new(DeviceHandle(null_mut()), 2 as *mut _, &efi_entry);
            }
            efi_call_traces().with(|traces| {
                assert_eq!(traces.borrow_mut().close_protocol_trace.inputs.len(), 0);
            });
        })
    }

    #[test]
    fn test_device_path_text_drop() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let mut data: [u16; 4] = [1, 2, 3, 0];
            {
                let path = DevicePathText::new(data.as_mut_ptr(), &efi_entry);
                assert_eq!(path.text.unwrap().to_vec(), vec![1, 2, 3]);
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
