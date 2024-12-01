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

//! Rust wrapper for `GBL_EFI_AVB_PROTOCOL`.

use crate::efi_call;
use crate::protocol::{Protocol, ProtocolInfo};
use core::ptr::null;
use efi_types::{
    EfiGuid, GblEfiAvbKeyValidationStatus, GblEfiAvbProtocol, GblEfiAvbVerificationResult,
};
use liberror::Result;

/// `GBL_EFI_AVB_PROTOCOL` implementation.
pub struct GblAvbProtocol;

impl ProtocolInfo for GblAvbProtocol {
    type InterfaceType = GblEfiAvbProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0x6bc66b9a, 0xd5c9, 0x4c02, [0x9d, 0xa9, 0x50, 0xaf, 0x19, 0x8d, 0x91, 0x2c]);
}

// Protocol interface wrappers.
impl Protocol<'_, GblAvbProtocol> {
    /// Wraps `GBL_EFI_AVB_PROTOCOL.validate_vbmeta_public_key()`.
    pub fn validate_vbmeta_public_key(
        &self,
        public_key: &[u8],
        public_key_metadata: Option<&[u8]>,
    ) -> Result<GblEfiAvbKeyValidationStatus> {
        let mut validation_status: GblEfiAvbKeyValidationStatus =
            efi_types::GBL_EFI_AVB_KEY_VALIDATION_STATUS_INVALID;

        // SAFETY:
        // * `self.interface()?` guarantees self.interface is non-null and points to a valid object
        //   established by `Protocol::new()`
        // * `public_key` pointer is not-null and used only within the call
        // * `public_key_metadata` pointer (can be null), used only within the call
        // * `validation_status` non-null pointer available to write
        unsafe {
            efi_call!(
                self.interface()?.validate_vbmeta_public_key,
                self.interface,
                public_key.as_ptr() as *const _,
                public_key.len(),
                public_key_metadata.map_or(null(), |m| m.as_ptr() as *const _),
                public_key_metadata.map_or(0, |m| m.len()),
                &mut validation_status,
            )?
        }

        Ok(validation_status)
    }

    /// Wraps `GBL_EFI_AVB_PROTOCOL.read_is_device_unlocked()`.
    pub fn read_is_device_unlocked(&self) -> Result<bool> {
        let mut is_unlocked: bool = false;

        // SAFETY:
        // * `self.interface()?` guarantees `self.interface` is non-null and points to a valid
        // object established by `Protocol::new()`.
        // * `is_unlocked` is a non-null pointer to a `bool` available for write.
        unsafe {
            efi_call!(self.interface()?.read_is_device_unlocked, self.interface, &mut is_unlocked)?
        }

        Ok(is_unlocked)
    }

    /// Wraps `GBL_EFI_AVB_PROTOCOL.read_rollback_index()`.
    pub fn read_rollback_index(&self, index_location: usize) -> Result<u64> {
        let mut rollback_index: u64 = 0;

        // SAFETY:
        // * `self.interface()?` guarantees `self.interface` is non-null and points to a valid
        //   object established by `Protocol::new()`.
        // * `rollback_index` is a valid pointer to a `u64` available for write.
        unsafe {
            efi_call!(
                self.interface()?.read_rollback_index,
                self.interface,
                index_location,
                &mut rollback_index,
            )?
        }

        Ok(rollback_index)
    }

    /// Wraps `GBL_EFI_AVB_PROTOCOL.write_rollback_index()`.
    pub fn write_rollback_index(&self, index_location: usize, rollback_index: u64) -> Result<()> {
        // SAFETY:
        // * `self.interface()?` guarantees `self.interface` is non-null and points to a valid
        //   object established by `Protocol::new()`.
        unsafe {
            efi_call!(
                self.interface()?.write_rollback_index,
                self.interface,
                index_location,
                rollback_index,
            )?
        }

        Ok(())
    }

    /// Wraps `GBL_EFI_AVB_PROTOCOL.handle_verification_result()`.
    pub fn handle_verification_result(
        &self,
        verification_result: &GblEfiAvbVerificationResult,
    ) -> Result<()> {
        // SAFETY:
        // * `self.interface()?` guarantees self.interface is non-null and points to a valid object
        //   established by `Protocol::new()`.
        // * `verification_result` pointer is not-null and used only within the call.
        unsafe {
            efi_call!(
                self.interface()?.handle_verification_result,
                self.interface,
                verification_result as *const _
            )
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::run_test_with_mock_protocol;
    use efi_types::{EfiStatus, EFI_STATUS_INVALID_PARAMETER, EFI_STATUS_SUCCESS};
    use std::slice;

    #[test]
    fn validate_vbmeta_public_key_status_provided() {
        const EXPECTED_PUBLIC_KEY: &[u8] = b"test_key";
        const EXPECTED_STATUS: GblEfiAvbKeyValidationStatus =
            efi_types::GBL_EFI_AVB_KEY_VALIDATION_STATUS_VALID_CUSTOM_KEY;

        // C callback implementation that returns an error
        unsafe extern "C" fn c_return_error(
            _: *mut GblEfiAvbProtocol,
            public_key_ptr: *const u8,
            public_key_len: usize,
            _metadata_ptr: *const u8,
            _metadata_len: usize,
            validation_status_ptr: *mut GblEfiAvbKeyValidationStatus,
        ) -> EfiStatus {
            // SAFETY:
            // * `public_key_ptr` is a non-null pointer to the buffer at least `public_key_len`
            // size.
            let public_key_buffer =
                unsafe { slice::from_raw_parts(public_key_ptr, public_key_len) };

            assert_eq!(public_key_buffer, EXPECTED_PUBLIC_KEY);

            // SAFETY:
            // * `validation_status_ptr` is a non-null pointer to GblEfiAvbKeyValidationStatus
            // available to write.
            unsafe { *validation_status_ptr = EXPECTED_STATUS };

            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiAvbProtocol {
            validate_vbmeta_public_key: Some(c_return_error),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |avb_protocol| {
            assert_eq!(
                avb_protocol.validate_vbmeta_public_key(EXPECTED_PUBLIC_KEY, None),
                Ok(EXPECTED_STATUS)
            );
        });
    }

    #[test]
    fn validate_vbmeta_public_key_error_handled() {
        // C callback implementation that returns an error
        unsafe extern "C" fn c_return_error(
            _: *mut GblEfiAvbProtocol,
            _public_key_ptr: *const u8,
            _public_key_len: usize,
            _metadata_ptr: *const u8,
            _metadata_len: usize,
            _validation_status_ptr: *mut GblEfiAvbKeyValidationStatus,
        ) -> EfiStatus {
            EFI_STATUS_INVALID_PARAMETER
        }

        let c_interface = GblEfiAvbProtocol {
            validate_vbmeta_public_key: Some(c_return_error),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |avb_protocol| {
            assert!(avb_protocol.validate_vbmeta_public_key(b"test_key", None).is_err());
        });
    }

    #[test]
    fn handle_verification_result_data_provided() {
        const COLOR: u32 = efi_types::GBL_EFI_AVB_BOOT_STATE_COLOR_RED;

        // C callback implementation that returns success.
        unsafe extern "C" fn c_return_success(
            _: *mut GblEfiAvbProtocol,
            result: *const GblEfiAvbVerificationResult,
        ) -> EfiStatus {
            // SAFETY:
            // * `result` is non-null.
            assert_eq!(unsafe { (*result).color }, COLOR);
            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiAvbProtocol {
            handle_verification_result: Some(c_return_success),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |avb_protocol| {
            let verification_result =
                GblEfiAvbVerificationResult { color: COLOR, ..Default::default() };

            assert!(avb_protocol.handle_verification_result(&verification_result).is_ok());
        });
    }

    #[test]
    fn handle_verification_result_error() {
        // C callback implementation that returns an error.
        unsafe extern "C" fn c_return_error(
            _: *mut GblEfiAvbProtocol,
            _: *const GblEfiAvbVerificationResult,
        ) -> EfiStatus {
            EFI_STATUS_INVALID_PARAMETER
        }

        let c_interface = GblEfiAvbProtocol {
            handle_verification_result: Some(c_return_error),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |avb_protocol| {
            let verification_result = GblEfiAvbVerificationResult::default();

            assert!(avb_protocol.handle_verification_result(&verification_result).is_err());
        });
    }

    #[test]
    fn read_is_device_unlocked_returns_true() {
        /// C callback implementation that sets is_unlocked to true.
        ///
        /// # Safety:
        /// Caller must guaranteed that `is_unlocked_ptr` points to a valid bool variable available
        /// for write.
        unsafe extern "C" fn c_return_true(
            _: *mut GblEfiAvbProtocol,
            is_unlocked_ptr: *mut bool,
        ) -> EfiStatus {
            // SAFETY: By safety requirement of this function, is_unlocked_ptr is a valid pointer.
            unsafe { *is_unlocked_ptr = true };
            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiAvbProtocol {
            read_is_device_unlocked: Some(c_return_true),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |avb_protocol| {
            assert_eq!(avb_protocol.read_is_device_unlocked(), Ok(true));
        });
    }

    #[test]
    fn read_is_device_unlocked_returns_false() {
        /// C callback implementation that sets is_unlocked to false.
        ///
        /// # Safety:
        /// Caller must guaranteed that `is_unlocked_ptr` points to a valid bool variable available
        /// for write.
        unsafe extern "C" fn c_return_false(
            _: *mut GblEfiAvbProtocol,
            is_unlocked_ptr: *mut bool,
        ) -> EfiStatus {
            // SAFETY: By safety requirement of this function, is_unlocked_ptr is a valid pointer.
            unsafe { *is_unlocked_ptr = false };
            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiAvbProtocol {
            read_is_device_unlocked: Some(c_return_false),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |avb_protocol| {
            assert_eq!(avb_protocol.read_is_device_unlocked(), Ok(false));
        });
    }

    #[test]
    fn read_is_device_unlocked_error_handled() {
        /// C callback implementation that returns an error.
        unsafe extern "C" fn c_return_error(_: *mut GblEfiAvbProtocol, _: *mut bool) -> EfiStatus {
            EFI_STATUS_INVALID_PARAMETER
        }

        let c_interface = GblEfiAvbProtocol {
            read_is_device_unlocked: Some(c_return_error),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |avb_protocol| {
            assert!(avb_protocol.read_is_device_unlocked().is_err());
        });
    }

    #[test]
    fn read_rollback_index_returns_value() {
        const EXPECTED_INDEX_LOCATION: usize = 1;
        const EXPECTED_ROLLBACK_INDEX: u64 = 42;

        /// C callback implementation that sets rollback_index to EXPECTED_ROLLBACK_INDEX.
        ///
        /// # Safety:
        /// Caller must guaranteed that `rollback_index_ptr` points to a valid u64 variable
        /// available for write.
        unsafe extern "C" fn c_return_value(
            _: *mut GblEfiAvbProtocol,
            index_location: usize,
            rollback_index_ptr: *mut u64,
        ) -> EfiStatus {
            assert_eq!(index_location, EXPECTED_INDEX_LOCATION);

            // SAFETY: By safety requirement of this function, `rollback_index_ptr` is a valid
            // pointer.
            unsafe { *rollback_index_ptr = EXPECTED_ROLLBACK_INDEX };
            EFI_STATUS_SUCCESS
        }

        let c_interface =
            GblEfiAvbProtocol { read_rollback_index: Some(c_return_value), ..Default::default() };

        run_test_with_mock_protocol(c_interface, |avb_protocol| {
            assert_eq!(
                avb_protocol.read_rollback_index(EXPECTED_INDEX_LOCATION),
                Ok(EXPECTED_ROLLBACK_INDEX)
            );
        });
    }

    #[test]
    fn read_rollback_index_error_handled() {
        /// C callback implementation that returns an error.
        unsafe extern "C" fn c_return_error(
            _: *mut GblEfiAvbProtocol,
            _: usize,
            _: *mut u64,
        ) -> EfiStatus {
            EFI_STATUS_INVALID_PARAMETER
        }

        let c_interface =
            GblEfiAvbProtocol { read_rollback_index: Some(c_return_error), ..Default::default() };

        run_test_with_mock_protocol(c_interface, |avb_protocol| {
            assert!(avb_protocol.read_rollback_index(0).is_err());
        });
    }

    #[test]
    fn write_rollback_index_success() {
        const EXPECTED_INDEX_LOCATION: usize = 1;
        const EXPECTED_ROLLBACK_INDEX: u64 = 42;

        /// C callback implementation that checks the passed parameters and returns success.
        unsafe extern "C" fn c_return_success(
            _: *mut GblEfiAvbProtocol,
            index_location: usize,
            rollback_index: u64,
        ) -> EfiStatus {
            assert_eq!(index_location, EXPECTED_INDEX_LOCATION);
            assert_eq!(rollback_index, EXPECTED_ROLLBACK_INDEX);
            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiAvbProtocol {
            write_rollback_index: Some(c_return_success),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |avb_protocol| {
            assert!(avb_protocol
                .write_rollback_index(EXPECTED_INDEX_LOCATION, EXPECTED_ROLLBACK_INDEX)
                .is_ok());
        });
    }

    #[test]
    fn write_rollback_index_error_handled() {
        /// C callback implementation that returns an error.
        unsafe extern "C" fn c_return_error(
            _: *mut GblEfiAvbProtocol,
            _: usize,
            _: u64,
        ) -> EfiStatus {
            EFI_STATUS_INVALID_PARAMETER
        }

        let c_interface =
            GblEfiAvbProtocol { write_rollback_index: Some(c_return_error), ..Default::default() };

        run_test_with_mock_protocol(c_interface, |avb_protocol| {
            assert!(avb_protocol.write_rollback_index(0, 0).is_err());
        });
    }
}
