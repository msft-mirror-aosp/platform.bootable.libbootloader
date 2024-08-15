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

//! Rust wrapper for `GBL_EFI_OS_CONFIGURATION_PROTOCOL`.

use crate::efi_call;
use crate::protocol::{Protocol, ProtocolInfo};
use efi_types::{EfiGuid, GblEfiOsConfigurationProtocol};
use liberror::Result;

/// `GBL_EFI_OS_CONFIGURATION_PROTOCOL` implementation.
pub struct GblOsConfigurationProtocol;

impl ProtocolInfo for GblOsConfigurationProtocol {
    type InterfaceType = GblEfiOsConfigurationProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0xdda0d135, 0xaa5b, 0x42ff, [0x85, 0xac, 0xe3, 0xad, 0x6e, 0xfb, 0x46, 0x19]);
}

// Protocol interface wrappers.
impl Protocol<'_, GblOsConfigurationProtocol> {
    /// Wraps `GBL_EFI_OS_CONFIGURATION_PROTOCOL.FixupKernelCommandline()`
    pub fn fixup_kernel_commandline(&self, data: &mut [u8]) -> Result<usize> {
        let mut buffer_size = data.len();
        // SAFETY:
        // * `self.interface()?` guarantees self.interface is non-null and points to a valid object
        //   established by `Protocol::new()`.
        // * all arguments are only borrowed for the call and will not be retained.
        unsafe {
            efi_call!(
                @bufsize buffer_size,
                self.interface()?.fixup_kernel_commandline,
                self.interface,
                data.as_mut_ptr(),
                &mut buffer_size
            )?;
        }

        Ok(buffer_size)
    }

    /// Wraps `GBL_EFI_OS_CONFIGURATION_PROTOCOL.FixupBootconfig()`
    pub fn fixup_bootconfig(&self, data: &mut [u8]) -> Result<usize> {
        let mut buffer_size = data.len();
        // SAFETY:
        // * `self.interface()?` guarantees self.interface is non-null and points to a valid object
        //   established by `Protocol::new()`.
        // * all arguments are only borrowed for the call and will not be retained.
        unsafe {
            efi_call!(
                @bufsize buffer_size,
                self.interface()?.fixup_bootconfig,
                self.interface,
                data.as_mut_ptr(),
                &mut buffer_size
            )?;
        }

        // TODO(b/354021403): figure out how to report EFI_BUFFER_TOO_SMALL buffer size. For now
        // we just drop the updated `buffer_size`.

        Ok(buffer_size)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::test::run_test_with_mock_protocol;
    use efi_types::{EfiStatus, EFI_STATUS_INVALID_PARAMETER, EFI_STATUS_SUCCESS};
    use liberror::Error;
    use std::{
        ffi::{CStr, CString},
        slice,
    };

    #[test]
    fn fixup_kernel_commandline_no_op() {
        // No-op C callback implementation.
        unsafe extern "C" fn c_return_success(
            _: *mut GblEfiOsConfigurationProtocol,
            _: *mut u8,
            _: *mut usize,
        ) -> EfiStatus {
            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiOsConfigurationProtocol {
            fixup_kernel_commandline: Some(c_return_success),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            let mut commandline = CString::new("foo=bar baz").unwrap().into_bytes_with_nul();
            assert!(os_config_protocol.fixup_kernel_commandline(&mut commandline[..]).is_ok());
        });
    }

    #[test]
    fn fixup_kernel_commandline_add_arg() {
        // C callback implementation to add " 123" to the given command line.
        unsafe extern "C" fn c_add_123(
            _: *mut GblEfiOsConfigurationProtocol,
            data: *mut u8,
            buffer_size: *mut usize,
        ) -> EfiStatus {
            // SAFETY:
            // * we pass a valid `data` buffer of length `buffer_size`
            // * this function has exclusive access to the buffer while it's executing
            let commandline =
                unsafe { slice::from_raw_parts_mut(data, *buffer_size.as_ref().unwrap()) };

            let nul_pos = commandline.iter().position(|c| *c == b'\0').unwrap();
            commandline[nul_pos..nul_pos + 5].copy_from_slice(b" 123\0");

            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiOsConfigurationProtocol {
            fixup_kernel_commandline: Some(c_add_123),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            let mut commandline = CString::new("foo=bar baz").unwrap().into_bytes_with_nul();
            // Add 4 extra bytes to the command line buffer so the C callback can add its data.
            commandline.extend_from_slice(b"\0\0\0\0");
            assert_eq!(
                os_config_protocol.fixup_kernel_commandline(&mut commandline[..]),
                Ok(commandline.len()),
            );
            assert_eq!(
                CStr::from_bytes_until_nul(&commandline[..]).unwrap(),
                CString::new("foo=bar baz 123").unwrap().as_c_str()
            );
        });
    }

    #[test]
    fn fixup_kernel_commandline_error() {
        // C callback implementation to return an error.
        unsafe extern "C" fn c_error(
            _: *mut GblEfiOsConfigurationProtocol,
            _: *mut u8,
            _: *mut usize,
        ) -> EfiStatus {
            EFI_STATUS_INVALID_PARAMETER
        }

        let c_interface = GblEfiOsConfigurationProtocol {
            fixup_kernel_commandline: Some(c_error),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            assert_eq!(
                os_config_protocol.fixup_kernel_commandline(&mut []),
                Err(Error::InvalidInput),
            );
        });
    }

    #[test]
    fn fixup_bootconfig_no_op() {
        // No-op C callback implementation.
        unsafe extern "C" fn c_return_success(
            _: *mut GblEfiOsConfigurationProtocol,
            _: *mut u8,
            _: *mut usize,
        ) -> EfiStatus {
            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiOsConfigurationProtocol {
            fixup_bootconfig: Some(c_return_success),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            let mut bootconfig = CString::new("foo=bar\nbaz").unwrap().into_bytes_with_nul();
            assert!(os_config_protocol.fixup_bootconfig(&mut bootconfig[..]).is_ok());
        });
    }

    #[test]
    fn fixup_fixup_bootconfig_add_arg() {
        // C callback implementation to add "\n123" to the given bootconfig.
        unsafe extern "C" fn c_add_123(
            _: *mut GblEfiOsConfigurationProtocol,
            data: *mut u8,
            buffer_size: *mut usize,
        ) -> EfiStatus {
            // SAFETY:
            // * we pass a valid `data` buffer of length `buffer_size`
            // * this function has exclusive access to the buffer while it's executing
            let bootconfig =
                unsafe { slice::from_raw_parts_mut(data, *buffer_size.as_ref().unwrap()) };

            let nul_pos = bootconfig.iter().position(|c| *c == b'\0').unwrap();
            bootconfig[nul_pos..nul_pos + 5].copy_from_slice(b"\n123\0");

            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiOsConfigurationProtocol {
            fixup_bootconfig: Some(c_add_123),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            let mut bootconfig = CString::new("foo=bar\nbaz").unwrap().into_bytes_with_nul();
            // Add 4 extra bytes to the command line buffer so the C callback can add its data.
            bootconfig.extend_from_slice(b"\0\0\0\0");
            assert_eq!(
                os_config_protocol.fixup_bootconfig(&mut bootconfig[..]),
                Ok(bootconfig.len()),
            );
            assert_eq!(
                CStr::from_bytes_until_nul(&bootconfig[..]).unwrap(),
                CString::new("foo=bar\nbaz\n123").unwrap().as_c_str()
            );
        });
    }

    #[test]
    fn fixup_bootconfig_error() {
        // C callback implementation to return an error.
        unsafe extern "C" fn c_error(
            _: *mut GblEfiOsConfigurationProtocol,
            _: *mut u8,
            _: *mut usize,
        ) -> EfiStatus {
            EFI_STATUS_INVALID_PARAMETER
        }

        let c_interface =
            GblEfiOsConfigurationProtocol { fixup_bootconfig: Some(c_error), ..Default::default() };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            assert_eq!(os_config_protocol.fixup_bootconfig(&mut []), Err(Error::InvalidInput),);
        });
    }
}
