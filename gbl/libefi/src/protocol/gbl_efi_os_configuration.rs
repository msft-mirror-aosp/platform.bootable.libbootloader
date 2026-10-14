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
use crate::{
    protocol::{Protocol, ProtocolInfo, Requirement},
    versioned_protocol,
};
use core::{ffi::CStr, ptr::null};
use efi_types::{
    EfiGuid, GblEfiOsConfigurationProtocol, GblEfiVerifiedDeviceTree,
    GBL_EFI_OS_CONFIGURATION_PROTOCOL_GUID_U64_0, GBL_EFI_OS_CONFIGURATION_PROTOCOL_GUID_U64_1,
    GBL_EFI_OS_CONFIGURATION_PROTOCOL_REVISION,
};
use liberror::{Error, Result};

/// `GBL_EFI_OS_CONFIGURATION_PROTOCOL` implementation.
pub struct GblOsConfigurationProtocol;

versioned_protocol!(GblOsConfigurationProtocol, GBL_EFI_OS_CONFIGURATION_PROTOCOL_REVISION);

/// The first protocol revision providing `fixup_kernel_commandline()`.
pub const FIXUP_KERNEL_COMMANDLINE_REVISION: Revision = Revision { major: 1, minor: 1 };

impl ProtocolInfo for GblOsConfigurationProtocol {
    type InterfaceType = GblEfiOsConfigurationProtocol;

    const GUID: EfiGuid = EfiGuid::from_u64s(
        GBL_EFI_OS_CONFIGURATION_PROTOCOL_GUID_U64_0,
        GBL_EFI_OS_CONFIGURATION_PROTOCOL_GUID_U64_1,
    );

    const REQUIREMENT: Requirement = Requirement::Optional;

    const METRICS_TAG: Option<&'static str> = Some("gbl_os_config");
}

// Protocol interface wrappers.
impl Protocol<'_, GblOsConfigurationProtocol> {
    /// Wraps `GBL_EFI_OS_CONFIGURATION_PROTOCOL.fixup_bootconfig()`.
    pub fn fixup_bootconfig(&self, bootconfig: &[u8], fixup: &mut [u8]) -> Result<usize> {
        if fixup.is_empty() {
            return Err(Error::InvalidInput);
        }

        let mut fixup_size = fixup.len();
        // SAFETY:
        // * `self.interface_ptr()` points to a valid object established by `Protocol::new()`.
        // * `bootconfig` is non-null buffer used only within the call.
        // * `fixup_size` is non-null usize buffer available for write, used only within the call.
        // * `fixup` is non-null buffer available for write, used only within the call.
        unsafe {
            efi_call!(
                @bufsize fixup_size,
                self.interface().fixup_bootconfig,
                self.interface_ptr(),
                bootconfig.len(),
                bootconfig.as_ptr(),
                &mut fixup_size,
                fixup.as_mut_ptr(),
            )?;
        }

        Ok(fixup_size)
    }

    /// Wraps `GBL_EFI_OS_CONFIGURATION_PROTOCOL.select_device_trees()`.
    pub fn select_device_trees(&self, components: &mut [GblEfiVerifiedDeviceTree]) -> Result<()> {
        // SAFETY:
        // * `self.interface_ptr()` points to a valid object established by `Protocol::new()`.
        // * `components_len` is non-null usize buffer, used only within the call.
        // * `components` is non-null buffer available for write, used only within the call.
        unsafe {
            efi_call!(
                self.interface().select_device_trees,
                self.interface_ptr(),
                components.len(),
                components.as_mut_ptr() as _,
            )?;
        }

        Ok(())
    }

    /// Wraps `GBL_EFI_OS_CONFIGURATION_PROTOCOL.select_fit_configuration()`.
    pub fn select_fit_configuration(&self, fit: &[u8], metadata: &[u8]) -> Result<usize> {
        if fit.is_empty() {
            return Err(Error::InvalidInput);
        }

        let mut selected_configuration = 0;
        // SAFETY:
        // * `self.interface_ptr()` points to a valid object established by `Protocol::new()`.
        // * `fit` is a non-null buffer.
        // * `metadata` can be a null buffer, used only within the call.
        // * `selected_configuration` is non-null usize buffer available for write, used only
        //   within the call.
        unsafe {
            efi_call!(
                self.interface().select_fit_configuration,
                self.interface_ptr(),
                fit.len(),
                fit.as_ptr(),
                metadata.len(),
                // TODO(b/385690995): Migrate metadata argument to Option once mock issue is
                // resolved.
                if metadata.is_empty() { null() } else { metadata.as_ptr() },
                &mut selected_configuration
            )?;
        }

        Ok(selected_configuration)
    }

    /// Wraps `GBL_EFI_OS_CONFIGURATION_PROTOCOL.fixup_kernel_commandline()`.
    ///
    /// Returns `Error::Unsupported` if the protocol revision predates the method.
    pub fn fixup_kernel_commandline(&self, commandline: &CStr, fixup: &mut [u8]) -> Result<usize> {
        if self.revision() < FIXUP_KERNEL_COMMANDLINE_REVISION {
            return Err(Error::Unsupported);
        }

        let mut fixup_size = fixup.len();
        // SAFETY:
        // * `self.interface_ptr()` points to a valid object established by `Protocol::new()`.
        // * `fixup_kernel_commandline` is guaranteed to exist as the revision is checked above.
        // * `commandline` is a valid null-terminated string used only within the call.
        // * `fixup_size` is non-null usize buffer available for write, used only within the call.
        // * `fixup` is non-null buffer available for write, used only within the call.
        unsafe {
            efi_call!(
                @bufsize fixup_size,
                self.interface().fixup_kernel_commandline,
                self.interface_ptr(),
                commandline.count_bytes(),
                commandline.as_ptr() as _,
                &mut fixup_size,
                fixup.as_mut_ptr(),
            )?;
        }

        Ok(fixup_size)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::test::run_test_with_mock_protocol;
    use efi_types::{
        EfiStatus, EFI_STATUS_BUFFER_TOO_SMALL, EFI_STATUS_INVALID_PARAMETER, EFI_STATUS_SUCCESS,
        EFI_STATUS_UNSUPPORTED,
    };
    use std::slice;

    #[test]
    fn fixup_bootconfig_no_op() {
        // No-op C callback implementation.
        unsafe extern "efiapi" fn c_return_success(
            _: *mut GblEfiOsConfigurationProtocol,
            _: usize,
            _: *const u8,
            fixup_size: *mut usize,
            _: *mut u8,
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
        unsafe extern "efiapi" fn c_add_ef(
            _: *mut GblEfiOsConfigurationProtocol,
            bootconfig_size: usize,
            bootconfig: *const u8,
            fixup_size: *mut usize,
            fixup: *mut u8,
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
        unsafe extern "efiapi" fn c_error(
            _: *mut GblEfiOsConfigurationProtocol,
            _: usize,
            _: *const u8,
            _: *mut usize,
            _: *mut u8,
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
        unsafe extern "efiapi" fn c_error(
            _: *mut GblEfiOsConfigurationProtocol,
            _: usize,
            _: *const u8,
            fixup_size: *mut usize,
            _: *mut u8,
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
    fn fixup_kernel_commandline_provided() {
        const EXPECTED_COMMANDLINE: &CStr = c"a=b c";
        const EXPECTED_FIXUP: &[u8] = b"d=e";

        // C callback implementation to add "d=e" to the given command line.
        unsafe extern "efiapi" fn c_add_de(
            _: *mut GblEfiOsConfigurationProtocol,
            commandline_size: usize,
            commandline: *const u8,
            fixup_size: *mut usize,
            fixup: *mut u8,
        ) -> EfiStatus {
            // SAFETY:
            // * `commandline` is a valid pointer to a null-terminated string.
            let commandline = unsafe { CStr::from_ptr(commandline as _) };
            assert_eq!(commandline, EXPECTED_COMMANDLINE);
            assert_eq!(commandline_size, EXPECTED_COMMANDLINE.count_bytes());

            // SAFETY:
            // * `fixup` is a valid writable buffer with enough space for test data.
            // * `fixup_size` is a valid pointer to writable usize buffer.
            let fixup_buffer = unsafe {
                *fixup_size = EXPECTED_FIXUP.len();
                slice::from_raw_parts_mut(fixup, *fixup_size)
            };
            fixup_buffer.copy_from_slice(EXPECTED_FIXUP);

            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiOsConfigurationProtocol {
            revision: GBL_EFI_OS_CONFIGURATION_PROTOCOL_REVISION,
            fixup_kernel_commandline: Some(c_add_de),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            let mut fixup_buffer = [0x0; 128];

            assert_eq!(
                os_config_protocol
                    .fixup_kernel_commandline(EXPECTED_COMMANDLINE, &mut fixup_buffer),
                Ok(EXPECTED_FIXUP.len()),
            );
            assert_eq!(&fixup_buffer[..EXPECTED_FIXUP.len()], EXPECTED_FIXUP);
        });
    }

    #[test]
    fn fixup_kernel_commandline_error() {
        // C callback implementation to return an error.
        unsafe extern "efiapi" fn c_error(
            _: *mut GblEfiOsConfigurationProtocol,
            _: usize,
            _: *const u8,
            _: *mut usize,
            _: *mut u8,
        ) -> EfiStatus {
            EFI_STATUS_INVALID_PARAMETER
        }

        let c_interface = GblEfiOsConfigurationProtocol {
            revision: GBL_EFI_OS_CONFIGURATION_PROTOCOL_REVISION,
            fixup_kernel_commandline: Some(c_error),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            let mut fixup_buffer = [0x0; 128];

            assert_eq!(
                os_config_protocol.fixup_kernel_commandline(c"foo=bar baz", &mut fixup_buffer),
                Err(Error::InvalidInput)
            );
        });
    }

    #[test]
    fn fixup_kernel_commandline_fixup_buffer_too_small() {
        const EXPECTED_REQUESTED_FIXUP_SIZE: usize = 256;
        // C callback implementation to return an error.
        unsafe extern "efiapi" fn c_error(
            _: *mut GblEfiOsConfigurationProtocol,
            _: usize,
            _: *const u8,
            fixup_size: *mut usize,
            _: *mut u8,
        ) -> EfiStatus {
            // SAFETY:
            // * `fixup_size` is a valid pointer to writable usize buffer.
            unsafe {
                *fixup_size = EXPECTED_REQUESTED_FIXUP_SIZE;
            }
            EFI_STATUS_BUFFER_TOO_SMALL
        }

        let c_interface = GblEfiOsConfigurationProtocol {
            revision: GBL_EFI_OS_CONFIGURATION_PROTOCOL_REVISION,
            fixup_kernel_commandline: Some(c_error),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            let mut fixup_buffer = [0x0; 128];

            assert_eq!(
                os_config_protocol.fixup_kernel_commandline(c"foo=bar baz", &mut fixup_buffer),
                Err(Error::BufferTooSmall(Some(EXPECTED_REQUESTED_FIXUP_SIZE))),
            );
        });
    }

    #[test]
    fn fixup_kernel_commandline_revision_1_0() {
        // C callback implementation that must not be called.
        unsafe extern "efiapi" fn c_unreachable(
            _: *mut GblEfiOsConfigurationProtocol,
            _: usize,
            _: *const u8,
            _: *mut usize,
            _: *mut u8,
        ) -> EfiStatus {
            unreachable!()
        }

        let c_interface = GblEfiOsConfigurationProtocol {
            revision: 0x0001_0000,
            fixup_kernel_commandline: Some(c_unreachable),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            let mut fixup_buffer = [0x0; 128];

            assert_eq!(
                os_config_protocol.fixup_kernel_commandline(c"foo=bar baz", &mut fixup_buffer),
                Err(Error::Unsupported),
            );
        });
    }

    #[test]
    fn select_device_trees_selected() {
        // C callback implementation to select first component.
        unsafe extern "efiapi" fn c_select_first(
            _: *mut GblEfiOsConfigurationProtocol,
            num: usize,
            device_trees: *mut GblEfiVerifiedDeviceTree,
        ) -> EfiStatus {
            assert_eq!(num, 1);

            // SAFETY:
            // * device_trees is non-null buffer available for write.
            unsafe {
                (*device_trees).selected = true;
            }

            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiOsConfigurationProtocol {
            select_device_trees: Some(c_select_first),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            let device_trees = &mut [GblEfiVerifiedDeviceTree::default()];

            assert!(os_config_protocol.select_device_trees(device_trees).is_ok());
            assert!(device_trees[0].selected);
        });
    }

    #[test]
    fn select_fit_configuration_selected() {
        const FIT_BUFFER: &[u8] = &[0x00, 0x01, 0x02, 0x03];
        const EXPECTED_SELECTED_CONFIGURATION_OFFSET: usize = 0x20;

        // C callback implementation to select fixed configuration.
        unsafe extern "efiapi" fn c_select_fixed_configuration(
            _: *mut GblEfiOsConfigurationProtocol,
            fit_size: usize,
            fit: *const u8,
            metadata_size: usize,
            metadata: *const u8,
            selected_configuration_offset: *mut usize,
        ) -> EfiStatus {
            assert_eq!(fit_size, FIT_BUFFER.len());
            assert!(!fit.is_null());

            assert_eq!(metadata_size, 0);
            assert!(metadata.is_null());

            // SAFETY: `fit` points to a valid buffer of `fit_size` length.
            let received_fit = unsafe { std::slice::from_raw_parts(fit, fit_size) };
            assert_eq!(received_fit, FIT_BUFFER);

            // SAFETY:
            // * `selected_configuration_offset` is a valid pointer to writtable usize buffer.
            unsafe {
                *selected_configuration_offset = EXPECTED_SELECTED_CONFIGURATION_OFFSET;
            }

            EFI_STATUS_SUCCESS
        }

        let c_interface = GblEfiOsConfigurationProtocol {
            select_fit_configuration: Some(c_select_fixed_configuration),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            const METADATA: &[u8] = &[];

            let selected_configuration =
                os_config_protocol.select_fit_configuration(FIT_BUFFER, METADATA).unwrap();
            assert_eq!(selected_configuration, EXPECTED_SELECTED_CONFIGURATION_OFFSET);
        });
    }

    #[test]
    fn select_fit_configuration_unsupported() {
        const FIT_BUFFER: &[u8] = &[0x00, 0x01, 0x02, 0x03];

        // C callback implementation to return an error.
        unsafe extern "efiapi" fn c_select_fit_unsupported(
            _: *mut GblEfiOsConfigurationProtocol,
            _: usize,
            _: *const u8,
            _: usize,
            _: *const u8,
            _: *mut usize,
        ) -> EfiStatus {
            EFI_STATUS_UNSUPPORTED
        }

        let c_interface = GblEfiOsConfigurationProtocol {
            select_fit_configuration: Some(c_select_fit_unsupported),
            ..Default::default()
        };

        run_test_with_mock_protocol(c_interface, |os_config_protocol| {
            const METADATA: &[u8] = &[];

            let selected_configuration =
                os_config_protocol.select_fit_configuration(FIT_BUFFER, METADATA);
            assert_eq!(selected_configuration, Err(Error::Unsupported));
        });
    }
}
