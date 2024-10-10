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
use core::ffi::CStr;
use efi_types::{EfiGuid, GblEfiOsConfigurationProtocol};
use liberror::{Error, Result};

/// `GBL_EFI_OS_CONFIGURATION_PROTOCOL` implementation.
pub struct GblOsConfigurationProtocol;

impl ProtocolInfo for GblOsConfigurationProtocol {
    type InterfaceType = GblEfiOsConfigurationProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0xdda0d135, 0xaa5b, 0x42ff, [0x85, 0xac, 0xe3, 0xad, 0x6e, 0xfb, 0x46, 0x19]);
}

// Protocol interface wrappers.
impl Protocol<'_, GblOsConfigurationProtocol> {
    /// Wraps `GBL_EFI_OS_CONFIGURATION_PROTOCOL.fixup_kernel_commandline()`.
    pub fn fixup_kernel_commandline(&self, commandline: &CStr, fixup: &mut [u8]) -> Result<()> {
        if fixup.is_empty() {
            return Err(Error::InvalidInput);
        }

        let mut fixup_size = fixup.len();
        fixup[0] = 0;
        // SAFETY:
        // * `self.interface()?` guarantees self.interface is non-null and points to a valid object
        //   established by `Protocol::new()`.
        // * `commandline` is a valid pointer to null-terminated string used only within the call.
        // * `fixup` is non-null buffer available for write, used only within the call.
        // * `fixup_size` is non-null buffer available for write, used only within the call.
        unsafe {
            efi_call!(
                @bufsize fixup_size,
                self.interface()?.fixup_kernel_commandline,
                self.interface,
                commandline.as_ptr() as _,
                fixup.as_mut_ptr(),
                &mut fixup_size
            )?;
        }

        Ok(())
    }

    /// Wraps `GBL_EFI_OS_CONFIGURATION_PROTOCOL.fixup_bootconfig()`.
    pub fn fixup_bootconfig(&self, bootconfig: &[u8], fixup: &mut [u8]) -> Result<usize> {
        if fixup.is_empty() {
            return Err(Error::InvalidInput);
        }

        let mut fixup_size = fixup.len();
        // SAFETY:
        // * `self.interface()?` guarantees self.interface is non-null and points to a valid object
        //   established by `Protocol::new()`.
        // * `bootconfig` is non-null buffer used only within the call.
        // * `fixup` is non-null buffer available for write, used only within the call.
        // * `fixup_size` is non-null usize buffer available for write, used only within the call.
        unsafe {
            efi_call!(
                @bufsize fixup_size,
                self.interface()?.fixup_bootconfig,
                self.interface,
                bootconfig.as_ptr(),
                bootconfig.len(),
                fixup.as_mut_ptr(),
                &mut fixup_size
            )?;
        }

        Ok(fixup_size)
    }

    /// Wraps `GBL_EFI_OS_CONFIGURATION_PROTOCOL.fixup_device_tree()`.
    pub fn fixup_device_tree(&self, device_tree: &mut [u8]) -> Result<()> {
        let mut buffer_size = device_tree.len();

        // SAFETY:
        // * `self.interface()?` guarantees self.interface is non-null and points to a valid object
        //   established by `Protocol::new()`.
        // * `device_tree` is non-null buffer available for write, used only within the call.
        // * `buffer_size` is non-null usize buffer available for write, used only within the call.
        unsafe {
            efi_call!(
                @bufsize buffer_size,
                self.interface()?.fixup_device_tree,
                self.interface,
                device_tree.as_mut_ptr() as _,
                &mut buffer_size
            )?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::test::run_test_with_mock_protocol;
    use efi_types::{
        EfiStatus, EFI_STATUS_BUFFER_TOO_SMALL, EFI_STATUS_INVALID_PARAMETER, EFI_STATUS_SUCCESS,
    };
    use std::{ffi::c_void, ffi::CStr, slice};

    #[test]
    fn fixup_kernel_commandline_no_op() {
        // No-op C callback implementation.
        unsafe extern "C" fn c_return_success(
            _: *mut GblEfiOsConfigurationProtocol,
            _: *const u8,
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
            let mut fixup_buffer = [0x0; 128];
            let commandline = c"foo=bar baz";

            assert!(os_config_protocol
                .fixup_kernel_commandline(commandline, &mut fixup_buffer)
                .is_ok());
            assert_eq!(
                CStr::from_bytes_until_nul(&fixup_buffer[..]).unwrap().to_str().unwrap(),
                ""
            );
        });
    }

    #[test]
    fn fixup_kernel_commandline_provided() {
        const EXPECTED_COMMANDLINE: &CStr = c"a=b";
        const EXPECTED_FIXUP: &[u8] = b"hello=world\0";
        const EXPECTED_FIXUP_STR: &str = "hello=world";

        // C callback implementation to add "hello=world" to the given command line.
        unsafe extern "C" fn c_add_hello_world(
            _: *mut GblEfiOsConfigurationProtocol,
            command_line: *const u8,
            fixup: *mut u8,
            _: *mut usize,
        ) -> EfiStatus {
            assert_eq!(
                // SAFETY:
                // * `command_line` is valid pointer to null terminated string.
                unsafe { CStr::from_ptr(command_line as _) },
                EXPECTED_COMMANDLINE
            );

            // SAFETY:
            // * `fixup` is valid writtable buffer with enough space for test data.
            let fixup_buffer = unsafe { slice::from_raw_parts_mut(fixup, EXPECTED_FIXUP.len()) };
            fixup_buffer.copy_from_slice(EXPECTED_FIXUP);

            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiOsConfigurationProtocol {
            fixup_kernel_commandline: Some(c_add_hello_world),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            let mut fixup_buffer = [0x0; 128];

            assert!(os_config_protocol
                .fixup_kernel_commandline(EXPECTED_COMMANDLINE, &mut fixup_buffer)
                .is_ok());
            assert_eq!(
                CStr::from_bytes_until_nul(&fixup_buffer[..]).unwrap().to_str().unwrap(),
                EXPECTED_FIXUP_STR,
            );
        });
    }

    #[test]
    fn fixup_kernel_commandline_error() {
        // C callback implementation to return an error.
        unsafe extern "C" fn c_error(
            _: *mut GblEfiOsConfigurationProtocol,
            _: *const u8,
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
            let mut fixup_buffer = [0x0; 128];
            let commandline = c"foo=bar baz";

            assert_eq!(
                os_config_protocol.fixup_kernel_commandline(commandline, &mut fixup_buffer),
                Err(Error::InvalidInput),
            );
        });
    }

    #[test]
    fn fixup_kernel_commandline_buffer_too_small() {
        const EXPECTED_REQUESTED_FIXUP_SIZE: usize = 256;
        // C callback implementation to return an error.
        unsafe extern "C" fn c_error(
            _: *mut GblEfiOsConfigurationProtocol,
            _: *const u8,
            _: *mut u8,
            fixup_size: *mut usize,
        ) -> EfiStatus {
            // SAFETY:
            // * `fixup_size` is a valid pointer to writtable usize buffer.
            unsafe {
                *fixup_size = EXPECTED_REQUESTED_FIXUP_SIZE;
            }
            EFI_STATUS_BUFFER_TOO_SMALL
        }

        let c_interface = GblEfiOsConfigurationProtocol {
            fixup_kernel_commandline: Some(c_error),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            let mut fixup_buffer = [0x0; 128];
            let commandline = c"foo=bar baz";

            assert_eq!(
                os_config_protocol.fixup_kernel_commandline(commandline, &mut fixup_buffer),
                Err(Error::BufferTooSmall(Some(EXPECTED_REQUESTED_FIXUP_SIZE))),
            );
        });
    }

    #[test]
    fn fixup_bootconfig_no_op() {
        // No-op C callback implementation.
        unsafe extern "C" fn c_return_success(
            _: *mut GblEfiOsConfigurationProtocol,
            _: *const u8,
            _: usize,
            _: *mut u8,
            fixup_size: *mut usize,
        ) -> EfiStatus {
            // SAFETY:
            // * `fixup_size` is a valid pointer to writtable usize buffer.
            unsafe {
                *fixup_size = 0;
            }
            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiOsConfigurationProtocol {
            fixup_bootconfig: Some(c_return_success),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            let mut fixup_buffer = [0x0; 128];
            let bootconfig = c"foo=bar\nbaz".to_bytes_with_nul();

            assert_eq!(
                os_config_protocol.fixup_bootconfig(&bootconfig[..], &mut fixup_buffer),
                Ok(0)
            );
        });
    }

    #[test]
    fn fixup_bootconfig_provided() {
        // no trailer for simplicity
        const EXPECTED_BOOTCONFIG: &[u8] = b"a=b\nc=d\n";
        const EXPECTED_LEN: usize = 4;
        const EXPECTED_FIXUP: &[u8] = b"e=f\n";

        // C callback implementation to add "e=f" to the given bootconfig.
        unsafe extern "C" fn c_add_ef(
            _: *mut GblEfiOsConfigurationProtocol,
            bootconfig: *const u8,
            bootconfig_size: usize,
            fixup: *mut u8,
            fixup_size: *mut usize,
        ) -> EfiStatus {
            // SAFETY:
            // * `bootconfig` is a valid pointer to the buffer at least `bootconfig_size` size.
            let bootconfig_buffer = unsafe { slice::from_raw_parts(bootconfig, bootconfig_size) };

            assert_eq!(bootconfig_buffer, EXPECTED_BOOTCONFIG);

            // SAFETY:
            // * `fixup` is a valid writtable buffer with enough space for test data.
            // * `fixup_size` is a valid pointer to writtable usize buffer.
            let fixup_buffer = unsafe {
                *fixup_size = EXPECTED_FIXUP.len();
                slice::from_raw_parts_mut(fixup, *fixup_size)
            };
            fixup_buffer.copy_from_slice(EXPECTED_FIXUP);

            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiOsConfigurationProtocol {
            fixup_bootconfig: Some(c_add_ef),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            let mut fixup_buffer = [0x0; 128];

            assert_eq!(
                os_config_protocol.fixup_bootconfig(&EXPECTED_BOOTCONFIG[..], &mut fixup_buffer),
                Ok(EXPECTED_LEN),
            );
            assert_eq!(&fixup_buffer[..EXPECTED_LEN], &EXPECTED_FIXUP[..],);
        });
    }

    #[test]
    fn fixup_bootconfig_error() {
        // C callback implementation to return an error.
        unsafe extern "C" fn c_error(
            _: *mut GblEfiOsConfigurationProtocol,
            _: *const u8,
            _: usize,
            _: *mut u8,
            _: *mut usize,
        ) -> EfiStatus {
            EFI_STATUS_INVALID_PARAMETER
        }

        let c_interface =
            GblEfiOsConfigurationProtocol { fixup_bootconfig: Some(c_error), ..Default::default() };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            let mut fixup_buffer = [0x0; 128];
            let bootconfig = c"foo=bar\nbaz".to_bytes_with_nul();

            assert_eq!(
                os_config_protocol.fixup_bootconfig(&bootconfig[..], &mut fixup_buffer),
                Err(Error::InvalidInput)
            );
        });
    }

    #[test]
    fn fixup_bootconfig_fixup_buffer_too_small() {
        const EXPECTED_REQUESTED_FIXUP_SIZE: usize = 256;
        // C callback implementation to return an error.
        unsafe extern "C" fn c_error(
            _: *mut GblEfiOsConfigurationProtocol,
            _: *const u8,
            _: usize,
            _: *mut u8,
            fixup_size: *mut usize,
        ) -> EfiStatus {
            // SAFETY:
            // * `fixup_size` is a valid pointer to writtable usize buffer.
            unsafe {
                *fixup_size = EXPECTED_REQUESTED_FIXUP_SIZE;
            }
            EFI_STATUS_BUFFER_TOO_SMALL
        }

        let c_interface =
            GblEfiOsConfigurationProtocol { fixup_bootconfig: Some(c_error), ..Default::default() };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            let mut fixup_buffer = [0x0; 128];
            let bootconfig = c"foo=bar\nbaz".to_bytes_with_nul();

            assert_eq!(
                os_config_protocol.fixup_bootconfig(&bootconfig[..], &mut fixup_buffer),
                Err(Error::BufferTooSmall(Some(EXPECTED_REQUESTED_FIXUP_SIZE))),
            );
        });
    }

    #[test]
    fn fixup_device_tree_updated() {
        // Don't check actual FDT content for simplicity.
        const DEVICE_TREE_BUFFER: &[u8] = b"this_is_device_tree";
        const UPDATED_DEVICE_TREE_BUFFER: &[u8] = b"this_is_device_trie";

        // C callback implementation to modify provided FDT to UPDATED_DEVICE_TREE_BUFFER.
        unsafe extern "C" fn c_modify(
            _: *mut GblEfiOsConfigurationProtocol,
            device_tree: *mut c_void,
            buffer_size: *mut usize,
        ) -> EfiStatus {
            // SAFETY:
            // * `device_tree` is a valid pointer to the writtable buffer at least `buffer_size`
            // size.
            // * `buffer_size` is a valid pointer to usize.
            let fdt_buffer =
                unsafe { slice::from_raw_parts_mut(device_tree as *mut u8, *buffer_size) };
            assert_eq!(fdt_buffer, DEVICE_TREE_BUFFER);

            fdt_buffer.copy_from_slice(UPDATED_DEVICE_TREE_BUFFER);

            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiOsConfigurationProtocol {
            fixup_device_tree: Some(c_modify),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            let mut fdt_buffer: Vec<u8> = DEVICE_TREE_BUFFER.to_vec();

            assert!(os_config_protocol.fixup_device_tree(&mut fdt_buffer[..]).is_ok());
            assert_eq!(&fdt_buffer[..], UPDATED_DEVICE_TREE_BUFFER);
        });
    }

    #[test]
    fn fixup_device_tree_fixup_buffer_too_small() {
        const EXPECTED_REQUESTED_FIXUP_SIZE: usize = 256;
        // C callback implementation to return an error.
        unsafe extern "C" fn c_error(
            _: *mut GblEfiOsConfigurationProtocol,
            _: *mut c_void,
            buffer_size: *mut usize,
        ) -> EfiStatus {
            // SAFETY:
            // * `buffer_size` is a valid pointer to writtable usize buffer.
            unsafe {
                *buffer_size = EXPECTED_REQUESTED_FIXUP_SIZE;
            }
            EFI_STATUS_BUFFER_TOO_SMALL
        }

        let c_interface = GblEfiOsConfigurationProtocol {
            fixup_device_tree: Some(c_error),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            let mut fdt_buffer = [0u8; 128];

            assert_eq!(
                os_config_protocol.fixup_device_tree(&mut fdt_buffer[..]),
                Err(Error::BufferTooSmall(Some(EXPECTED_REQUESTED_FIXUP_SIZE))),
            );
        });
    }
}
