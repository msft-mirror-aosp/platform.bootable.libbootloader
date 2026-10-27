// Copyright 2025, The Android Open Source Project
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

//! Rust wrapper for `GBL_EFI_AVF_PROTOCOL`.

use crate::efi_call;
use crate::{
    protocol::{Protocol, ProtocolInfo, Requirement},
    versioned_protocol,
};
use efi_types::{EfiGuid, GblEfiAvfProtocol, Identified, GBL_EFI_AVF_PROTOCOL_REVISION};
use liberror::{Error, Result};

/// `GBL_EFI_AVF_PROTOCOL` implementation.
pub struct GblAvfProtocol;

versioned_protocol!(GblAvfProtocol, GBL_EFI_AVF_PROTOCOL_REVISION);

impl ProtocolInfo for GblAvfProtocol {
    type InterfaceType = GblEfiAvfProtocol;

    const GUID: EfiGuid = GblEfiAvfProtocol::GUID;

    const REQUIREMENT: Requirement = Requirement::Optional;

    const METRICS_TAG: Option<&'static str> = Some("gbl_avf");
}

// Protocol interface wrappers.
impl Protocol<'_, GblAvfProtocol> {
    /// Wraps `GBL_EFI_AVF_PROTOCOL.read_vendor_dice_handover()`.
    pub fn read_vendor_dice_handover(&self, handover_buffer: &mut [u8]) -> Result<usize> {
        if handover_buffer.is_empty() {
            return Err(Error::InvalidInput);
        }

        let mut used_size = handover_buffer.len();
        // SAFETY:
        // * `self.interface_ptr()` points to a valid object established by `Protocol::new()`.
        // * `handover_buffer` is non-null buffer available for write, used only within the call.
        // * `used_size` is non-null usize buffer available for write, used only within the call.
        unsafe {
            efi_call!(
                @bufsize used_size,
                self.interface().read_vendor_dice_handover,
                self.interface_ptr(),
                &mut used_size,
                handover_buffer.as_mut_ptr() as _,
            )?;
        }

        Ok(used_size)
    }

    /// Wraps `GBL_EFI_AVF_PROTOCOL.read_secretkeeper_public_key()`.
    pub fn read_secretkeeper_public_key(&self, key_buffer: &mut [u8]) -> Result<usize> {
        if key_buffer.is_empty() {
            return Err(Error::InvalidInput);
        }

        let mut used_size = key_buffer.len();
        // SAFETY:
        // * `self.interface_ptr()` points to a valid object established by `Protocol::new()`.
        // * `key_buffer` is non-null buffer available for write, used only within the call.
        // * `used_size` is non-null usize buffer available for write, used only within the call.
        unsafe {
            efi_call!(
                @bufsize used_size,
                self.interface().read_secretkeeper_public_key,
                self.interface_ptr(),
                &mut used_size,
                key_buffer.as_mut_ptr() as _,
            )?;
        }

        Ok(used_size)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::test::run_test_with_mock_protocol;
    use efi_types::{
        EfiStatus, EFI_STATUS_BUFFER_TOO_SMALL, EFI_STATUS_INVALID_PARAMETER, EFI_STATUS_SUCCESS,
    };
    use std::slice;

    #[test]
    fn read_vendor_dice_handover_no_op() {
        unsafe extern "efiapi" fn c_return_success(
            _: *mut GblEfiAvfProtocol,
            size: *mut usize,
            _: *mut u8,
        ) -> EfiStatus {
            // SAFETY:
            // * `size` is a valid pointer to writtable usize buffer.
            unsafe {
                *size = 0;
            }
            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiAvfProtocol {
            read_vendor_dice_handover: Some(c_return_success),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |avf_protocol| {
            let mut handover_buffer = [0x0; 128];
            assert_eq!(avf_protocol.read_vendor_dice_handover(&mut handover_buffer), Ok(0));
        });
    }

    #[test]
    fn read_vendor_dice_handover_provided() {
        const EXPECTED_HANDOVER: &[u8] = b"handover";

        unsafe extern "efiapi" fn c_return_success(
            _: *mut GblEfiAvfProtocol,
            size: *mut usize,
            handover: *mut u8,
        ) -> EfiStatus {
            // SAFETY:
            // * `handover` is a valid writtable buffer with enough space for test data.
            // * `size` is a valid pointer to writtable usize buffer.
            let handover_buffer = unsafe {
                *size = EXPECTED_HANDOVER.len();
                slice::from_raw_parts_mut(handover, *size)
            };
            handover_buffer.copy_from_slice(EXPECTED_HANDOVER);

            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiAvfProtocol {
            read_vendor_dice_handover: Some(c_return_success),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |avf_protocol| {
            let mut handover_buffer = [0x0; 128];
            assert_eq!(
                avf_protocol.read_vendor_dice_handover(&mut handover_buffer),
                Ok(EXPECTED_HANDOVER.len())
            );
            assert_eq!(&handover_buffer[..EXPECTED_HANDOVER.len()], &EXPECTED_HANDOVER[..]);
        });
    }

    #[test]
    fn read_vendor_dice_handover_error() {
        unsafe extern "efiapi" fn c_error(
            _: *mut GblEfiAvfProtocol,
            _: *mut usize,
            _: *mut u8,
        ) -> EfiStatus {
            EFI_STATUS_INVALID_PARAMETER
        }

        let c_interface =
            GblEfiAvfProtocol { read_vendor_dice_handover: Some(c_error), ..Default::default() };

        run_test_with_mock_protocol(c_interface, |avf_protocol| {
            let mut handover_buffer = [0u8; 128];

            assert_eq!(
                avf_protocol.read_vendor_dice_handover(&mut handover_buffer),
                Err(Error::InvalidInput),
            );
        });
    }

    #[test]
    fn read_vendor_dice_handover_buffer_too_small() {
        const EXPECTED_REQUIRED_SIZE: usize = 256;

        unsafe extern "efiapi" fn c_buffer_too_small(
            _: *mut GblEfiAvfProtocol,
            size: *mut usize,
            _: *mut u8,
        ) -> EfiStatus {
            // SAFETY:
            // * `size` is a valid, writable pointer supplied by the caller.
            unsafe {
                *size = EXPECTED_REQUIRED_SIZE;
            }
            EFI_STATUS_BUFFER_TOO_SMALL
        }

        let c_interface = GblEfiAvfProtocol {
            read_vendor_dice_handover: Some(c_buffer_too_small),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |avf_protocol| {
            let mut handover_buffer = [0u8; 128];

            assert_eq!(
                avf_protocol.read_vendor_dice_handover(&mut handover_buffer),
                Err(Error::BufferTooSmall(Some(EXPECTED_REQUIRED_SIZE))),
            );
        });
    }

    #[test]
    fn read_secretkeeper_public_key_no_op() {
        unsafe extern "efiapi" fn c_return_success(
            _: *mut GblEfiAvfProtocol,
            size: *mut usize,
            _: *mut u8,
        ) -> EfiStatus {
            // SAFETY:
            // * `size` is a valid, writable pointer supplied by the caller.
            unsafe { *size = 0 };
            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiAvfProtocol {
            read_secretkeeper_public_key: Some(c_return_success),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |avf_protocol| {
            let mut key_buffer = [0u8; 128];
            assert_eq!(avf_protocol.read_secretkeeper_public_key(&mut key_buffer), Ok(0));
        });
    }

    #[test]
    fn read_secretkeeper_public_key_provided() {
        const EXPECTED_KEY: &[u8] = b"publickey";

        unsafe extern "efiapi" fn c_return_success(
            _: *mut GblEfiAvfProtocol,
            size: *mut usize,
            key: *mut u8,
        ) -> EfiStatus {
            // SAFETY:
            // * `key` is a valid writtable buffer with enough space for test data.
            // * `size` is a valid pointer to writtable usize buffer.
            let key_buf = unsafe {
                *size = EXPECTED_KEY.len();
                core::slice::from_raw_parts_mut(key, *size)
            };
            key_buf.copy_from_slice(EXPECTED_KEY);

            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiAvfProtocol {
            read_secretkeeper_public_key: Some(c_return_success),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |avf_protocol| {
            let mut key_buffer = [0u8; 128];
            assert_eq!(
                avf_protocol.read_secretkeeper_public_key(&mut key_buffer),
                Ok(EXPECTED_KEY.len())
            );
            assert_eq!(&key_buffer[..EXPECTED_KEY.len()], EXPECTED_KEY);
        });
    }

    #[test]
    fn read_secretkeeper_public_key_error() {
        unsafe extern "efiapi" fn c_error(
            _: *mut GblEfiAvfProtocol,
            _: *mut usize,
            _: *mut u8,
        ) -> EfiStatus {
            EFI_STATUS_INVALID_PARAMETER
        }

        let c_interface =
            GblEfiAvfProtocol { read_secretkeeper_public_key: Some(c_error), ..Default::default() };

        run_test_with_mock_protocol(c_interface, |avf_protocol| {
            let mut key_buffer = [0u8; 128];
            assert_eq!(
                avf_protocol.read_secretkeeper_public_key(&mut key_buffer),
                Err(Error::InvalidInput)
            );
        });
    }

    #[test]
    fn read_secretkeeper_public_key_buffer_too_small() {
        const EXPECTED_REQUIRED_SIZE: usize = 256;

        unsafe extern "efiapi" fn c_buffer_too_small(
            _: *mut GblEfiAvfProtocol,
            size: *mut usize,
            _: *mut u8,
        ) -> EfiStatus {
            // SAFETY:
            // * `size` is a valid, writable pointer supplied by the caller.
            unsafe { *size = EXPECTED_REQUIRED_SIZE };
            EFI_STATUS_BUFFER_TOO_SMALL
        }

        let c_interface = GblEfiAvfProtocol {
            read_secretkeeper_public_key: Some(c_buffer_too_small),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |avf_protocol| {
            let mut key_buffer = [0u8; 128];
            assert_eq!(
                avf_protocol.read_secretkeeper_public_key(&mut key_buffer),
                Err(Error::BufferTooSmall(Some(EXPECTED_REQUIRED_SIZE)))
            );
        });
    }
}
