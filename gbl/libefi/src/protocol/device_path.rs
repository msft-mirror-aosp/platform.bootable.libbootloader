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

use crate::protocol::{MaybeVersioned, Protocol, ProtocolInfo, Requirement};
use crate::{efi_println, EfiEntry};
use core::ffi::CStr;
use core::fmt::Display;
use core::marker::PhantomData;
use core::mem::size_of;
use efi_types::{
    protocol::BridgeToRust, EfiDevicePathProtocol, EfiDevicePathToTextProtocol, EfiGuid,
    Identified, EFI_DEVICE_PATH_TO_TEXT_PROTOCOL_GUID_U64_0,
    EFI_DEVICE_PATH_TO_TEXT_PROTOCOL_GUID_U64_1, EFI_DEVICE_PATH_TYPE_END_OF_HARDWARE_DEVICE_PATH,
    EFI_DEVICE_PATH_TYPE_MEDIA_DEVICE_PATH,
    EFI_END_OF_HARDWARE_DEVICE_PATH_SUB_TYPE_END_ENTIRE_DEVICE_PATH,
    EFI_MEDIA_DEVICE_PATH_SUB_TYPE_VENDOR, GBL_VENDOR_MEDIA_DEVICE_PATH_GUID_U64_0,
    GBL_VENDOR_MEDIA_DEVICE_PATH_GUID_U64_1,
};
use liberror::{Error, Result};
use static_assertions::{const_assert, const_assert_eq};
use zerocopy::byteorder::little_endian;
use zerocopy::FromBytes;

impl MaybeVersioned for EfiDevicePathProtocol {}

/// `EFI_DEVICE_PATH_PROTOCOL`
pub struct DevicePathProtocol;

impl ProtocolInfo for DevicePathProtocol {
    type InterfaceType = EfiDevicePathProtocol;
    const GUID: EfiGuid = EfiDevicePathProtocol::GUID;
    const REQUIREMENT: Requirement = Requirement::Optional;
}

const GBL_VENDOR_MEDIA_DEVICE_PATH_GUID: EfiGuid = EfiGuid::from_u64s(
    GBL_VENDOR_MEDIA_DEVICE_PATH_GUID_U64_0,
    GBL_VENDOR_MEDIA_DEVICE_PATH_GUID_U64_1,
);

/// Iterates a series of `EfiDevicePathProtocol`
struct EfiDevicePathNodeIter<'a>(
    *const EfiDevicePathProtocol,
    PhantomData<&'a EfiDevicePathProtocol>,
);

impl<'a> EfiDevicePathNodeIter<'a> {
    /// # Safety
    /// The pointer must point to the start of a series of Device Path nodes and the series must be
    /// terminated by an End of Hardware Device Path node (sub-type End Entire Device Path).
    unsafe fn new(ptr: *const EfiDevicePathProtocol) -> Self {
        EfiDevicePathNodeIter(ptr, PhantomData)
    }
}

impl<'a> Iterator for EfiDevicePathNodeIter<'a> {
    type Item = (&'a EfiDevicePathProtocol, &'a [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY: `self.0` points to a valid `EfiDevicePathProtocol` object.
        let header = unsafe { self.0.as_ref()? };
        if header.type_ == EFI_DEVICE_PATH_TYPE_END_OF_HARDWARE_DEVICE_PATH
            && header.sub_type == EFI_END_OF_HARDWARE_DEVICE_PATH_SUB_TYPE_END_ENTIRE_DEVICE_PATH
        {
            return None;
        }
        let length = little_endian::U16::from_bytes(header.length).get() as usize;
        // SAFETY: Buffer was established by UEFI firmware. Buffer outlives the call.
        let aux = unsafe { core::slice::from_raw_parts(self.0 as *const u8, length) };
        let aux = aux.get(size_of::<EfiDevicePathProtocol>()..)?;
        // SAFETY: UEFI spec requires `EfiDevicePathProtocol` to be byte-packed and shifting by
        // `length` bytes would point to the next `EfiDevicePathProtocol` object.
        unsafe { self.0 = self.0.byte_add(length) };
        Some((header, aux))
    }
}

impl<'a> Protocol<'a, DevicePathProtocol> {
    /// Get the GBL vendor-defined media device path.
    ///
    /// # Returns
    /// * `Ok(Some)` the GBL vendor-defined media device path.
    /// * `Ok(None)` if not found.
    /// * `Err(Error::InvalidInput)` if failed to parse EFI data.
    pub fn gbl_vendor_media_device_path(&self) -> Result<Option<&'a CStr>> {
        // SAFETY: UEFI firmware requires that `self.interface_ptr()` is non-null and points to a
        // series of Device Path nodes that ends with an End of Hardware Device Path node.
        for (header, aux) in unsafe { EfiDevicePathNodeIter::new(self.interface_ptr()) } {
            if header.type_ == EFI_DEVICE_PATH_TYPE_MEDIA_DEVICE_PATH
                && header.sub_type == EFI_MEDIA_DEVICE_PATH_SUB_TYPE_VENDOR
            {
                // Mustn't use ref_from_prefix() because `aux` could be unaligned to `EfiGuid` size.
                match EfiGuid::read_from_prefix(aux) {
                    Err(e) => {
                        efi_println!(
                            self.efi_entry(),
                            "Failed to parse vendor-defined media device path GUID: {e:?}"
                        );
                        return Err(Error::InvalidInput);
                    }
                    Ok((GBL_VENDOR_MEDIA_DEVICE_PATH_GUID, data)) => {
                        return Ok(Some(core::ffi::CStr::from_bytes_until_nul(data)?));
                    }
                    Ok(_) => {}
                };
            }
        }
        Ok(None)
    }
}

/// Linux Initrd Vendor Media Path.
pub struct InitrdDevicePathProtocol;

/// Device Path Protocol for the Linux EFI initrd vendor media path.
#[repr(C, packed)]
pub struct EfiInitrdDevicePathProtocol {
    vendor: EfiDevicePathProtocol,
    guid: EfiGuid,
    end: EfiDevicePathProtocol,
}

impl EfiInitrdDevicePathProtocol {
    /// GUID for the Linux EFI Initrd vendor media device path node.
    const LINUX_EFI_INITRD_MEDIA_GUID: EfiGuid =
        EfiGuid::new(0x5568e427, 0x68fc, 0x4f3d, [0xac, 0x74, 0xca, 0x55, 0x52, 0x31, 0xcc, 0x68]);

    /// Creates a new instance.
    pub const fn new() -> Self {
        Self {
            vendor: EfiDevicePathProtocol {
                type_: EFI_DEVICE_PATH_TYPE_MEDIA_DEVICE_PATH,
                sub_type: EFI_MEDIA_DEVICE_PATH_SUB_TYPE_VENDOR,
                length: ((size_of::<EfiDevicePathProtocol>() + size_of::<EfiGuid>()) as u16)
                    .to_le_bytes(),
            },
            guid: Self::LINUX_EFI_INITRD_MEDIA_GUID,
            end: EfiDevicePathProtocol {
                type_: EFI_DEVICE_PATH_TYPE_END_OF_HARDWARE_DEVICE_PATH,
                sub_type: EFI_END_OF_HARDWARE_DEVICE_PATH_SUB_TYPE_END_ENTIRE_DEVICE_PATH,
                length: (size_of::<EfiDevicePathProtocol>() as u16).to_le_bytes(),
            },
        }
    }
}

// NOTE: Cannot use `const_assert_eq` here because PartialEq is not const-aware for slices.
const_assert!(matches!(EfiInitrdDevicePathProtocol::new().vendor.length, [20, 0]));
const_assert!(matches!(EfiInitrdDevicePathProtocol::new().end.length, [4, 0]));
const_assert_eq!(size_of::<EfiInitrdDevicePathProtocol>(), 24);

impl Identified for EfiInitrdDevicePathProtocol {
    const GUID: EfiGuid = EfiDevicePathProtocol::GUID;
}

impl MaybeVersioned for EfiInitrdDevicePathProtocol {}

impl ProtocolInfo for InitrdDevicePathProtocol {
    type InterfaceType = EfiInitrdDevicePathProtocol;
    const GUID: EfiGuid = EfiInitrdDevicePathProtocol::GUID;
    const REQUIREMENT: Requirement = Requirement::Optional;
}

// SAFETY: EfiInitrdDevicePathProtocol has only one valid value, which is returned by `Self::new()`.
unsafe impl BridgeToRust<InitrdDevicePathProtocol> for EfiInitrdDevicePathProtocol {
    unsafe fn create_bridge(_rust_impl: &InitrdDevicePathProtocol) -> Self {
        Self::new()
    }
}

impl MaybeVersioned for EfiDevicePathToTextProtocol {}

/// `EFI_DEVICE_PATH_TO_TEXT_PROTOCOL`
pub struct DevicePathToTextProtocol;

impl ProtocolInfo for DevicePathToTextProtocol {
    type InterfaceType = EfiDevicePathToTextProtocol;

    const GUID: EfiGuid = EfiGuid::from_u64s(
        EFI_DEVICE_PATH_TO_TEXT_PROTOCOL_GUID_U64_0,
        EFI_DEVICE_PATH_TO_TEXT_PROTOCOL_GUID_U64_1,
    );

    const REQUIREMENT: Requirement = Requirement::Optional;
}

impl<'a> Protocol<'a, DevicePathToTextProtocol> {
    /// Wrapper of `EFI_DEVICE_PATH_TO_TEXT_PROTOCOL.ConvertDevicePathToText()`
    pub fn convert_device_path_to_text(
        &self,
        device_path: &Protocol<DevicePathProtocol>,
        display_only: bool,
        allow_shortcuts: bool,
    ) -> Result<DevicePathText<'a>> {
        let f = self.interface().convert_device_path_to_text.as_ref().ok_or(Error::NotFound)?;
        // SAFETY:
        // `self.interface_ptr()` is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface_ptr()` is an input parameter and will not be retained.
        // It outlives the call.
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
        if text.is_null() || !text.is_aligned() {
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
    use zerocopy::IntoBytes;

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

    #[test]
    fn test_device_path_node_iter() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let dp1_data = [1, 2];
            let dp1 = EfiDevicePathProtocol {
                type_: 0x00,
                sub_type: 0x00,
                length: little_endian::U16::new((4 + dp1_data.len()) as u16).to_bytes(),
            };
            let dp2_data = [1, 2, 3, 4, 5];
            let dp2 = EfiDevicePathProtocol {
                type_: 0x01,
                sub_type: 0x01,
                length: little_endian::U16::new((4 + dp2_data.len()) as u16).to_bytes(),
            };
            let dp3_data =
                [GBL_VENDOR_MEDIA_DEVICE_PATH_GUID.as_bytes(), c"device_name".to_bytes_with_nul()]
                    .concat();
            let dp3 = EfiDevicePathProtocol {
                type_: EFI_DEVICE_PATH_TYPE_MEDIA_DEVICE_PATH,
                sub_type: EFI_MEDIA_DEVICE_PATH_SUB_TYPE_VENDOR,
                length: little_endian::U16::new((4 + dp3_data.len()) as u16).to_bytes(),
            };
            let dp_end = EfiDevicePathProtocol {
                type_: EFI_DEVICE_PATH_TYPE_END_OF_HARDWARE_DEVICE_PATH,
                sub_type: EFI_END_OF_HARDWARE_DEVICE_PATH_SUB_TYPE_END_ENTIRE_DEVICE_PATH,
                length: little_endian::U16::new(4).to_bytes(),
            };

            let mut buf = [
                vec![dp1.as_bytes(), &dp1_data],
                vec![dp2.as_bytes(), &dp2_data],
                vec![dp3.as_bytes(), &dp3_data],
                vec![dp_end.as_bytes()],
            ]
            .concat()
            .concat();
            let protocol = unsafe {
                let efi_protocol = buf.as_mut_ptr() as *mut EfiDevicePathProtocol;
                generate_protocol::<DevicePathProtocol>(&efi_entry, efi_protocol.as_mut().unwrap())
            };

            assert_eq!(size_of::<EfiDevicePathProtocol>(), 4);
            assert_eq!(size_of::<EfiGuid>(), 16);
            assert_eq!(
                unsafe { EfiDevicePathNodeIter::new(protocol.interface_ptr()) }.collect::<Vec<_>>(),
                vec![
                    (&dp1, dp1_data.as_ref()),
                    (&dp2, dp2_data.as_ref()),
                    (&dp3, dp3_data.as_ref()),
                ]
            );
        })
    }

    #[test]
    fn test_gbl_vendor_media_device_path() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let dp1_data = [1, 2];
            let dp1 = EfiDevicePathProtocol {
                type_: 0x00,
                sub_type: 0x00,
                length: little_endian::U16::new((4 + dp1_data.len()) as u16).to_bytes(),
            };
            let dp2_data = [1, 2, 3, 4, 5];
            let dp2 = EfiDevicePathProtocol {
                type_: 0x01,
                sub_type: 0x01,
                length: little_endian::U16::new((4 + dp2_data.len()) as u16).to_bytes(),
            };
            let dp3_data =
                [GBL_VENDOR_MEDIA_DEVICE_PATH_GUID.as_bytes(), c"device_name".to_bytes_with_nul()]
                    .concat();
            let dp3 = EfiDevicePathProtocol {
                type_: EFI_DEVICE_PATH_TYPE_MEDIA_DEVICE_PATH,
                sub_type: EFI_MEDIA_DEVICE_PATH_SUB_TYPE_VENDOR,
                length: little_endian::U16::new((4 + dp3_data.len()) as u16).to_bytes(),
            };
            let dp_end = EfiDevicePathProtocol {
                type_: EFI_DEVICE_PATH_TYPE_END_OF_HARDWARE_DEVICE_PATH,
                sub_type: EFI_END_OF_HARDWARE_DEVICE_PATH_SUB_TYPE_END_ENTIRE_DEVICE_PATH,
                length: little_endian::U16::new(4).to_bytes(),
            };

            let mut buf = [
                vec![dp1.as_bytes(), &dp1_data],
                vec![dp2.as_bytes(), &dp2_data],
                vec![dp3.as_bytes(), &dp3_data],
                vec![dp_end.as_bytes()],
            ]
            .concat()
            .concat();
            let protocol = unsafe {
                let efi_protocol = buf.as_mut_ptr() as *mut EfiDevicePathProtocol;
                generate_protocol::<DevicePathProtocol>(&efi_entry, efi_protocol.as_mut().unwrap())
            };

            assert_eq!(protocol.gbl_vendor_media_device_path(), Ok(Some(c"device_name")));
        })
    }

    #[test]
    fn test_gbl_vendor_media_device_path_unsupported() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let dp1 = EfiDevicePathProtocol {
                type_: 0x00,
                sub_type: 0x00,
                length: little_endian::U16::new(4).to_bytes(),
            };
            let dp_end = EfiDevicePathProtocol {
                type_: EFI_DEVICE_PATH_TYPE_END_OF_HARDWARE_DEVICE_PATH,
                sub_type: EFI_END_OF_HARDWARE_DEVICE_PATH_SUB_TYPE_END_ENTIRE_DEVICE_PATH,
                length: little_endian::U16::new(4).to_bytes(),
            };

            let mut buf = [dp1.as_bytes(), dp_end.as_bytes()].concat();
            let protocol = unsafe {
                let efi_protocol = buf.as_mut_ptr() as *mut EfiDevicePathProtocol;
                generate_protocol::<DevicePathProtocol>(&efi_entry, efi_protocol.as_mut().unwrap())
            };

            assert_eq!(protocol.gbl_vendor_media_device_path(), Ok(None));
        })
    }
}
