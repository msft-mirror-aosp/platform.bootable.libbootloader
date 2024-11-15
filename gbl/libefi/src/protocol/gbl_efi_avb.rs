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
use efi_types::{EfiGuid, GblEfiAvbProtocol, GblEfiAvbVerificationResult};
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
}
