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

//! Mock protocols.
//!
//! The structure of these sub-modules must match the libefi structure so that the code can refer
//! to either one using the same path.

use crate::{DeviceHandle, MOCK_EFI};
use core::ffi::CStr;
use core::fmt::Write;
use efi::protocol::gbl_efi_image_loading::EfiImageBuffer;
use efi_types::{
    EfiInputKey, GblEfiAvbKeyValidationStatus, GblEfiAvbVerificationResult, GblEfiImageInfo,
    GblEfiPartitionName, GblEfiVerifiedDeviceTree,
};
use liberror::Result;
use mockall::mock;

/// Mock device_path module.
pub mod device_path {
    use super::*;

    mock! {
        /// Mock [efi::DevicePathProtocol].
        pub DevicePathProtocol {}
    }
    /// Map to the libefi name so code under test can just use one name.
    pub type DevicePathProtocol = MockDevicePathProtocol;

    mock! {
        /// Mock [efi::DevicePathToTextProtocol].
        pub DevicePathToTextProtocol {
            /// Returns a [MockDevicePathText].
            ///
            /// Lifetimes are a little difficult to mock perfectly, so here we can only allow a
            /// `'static` return value.
            pub fn convert_device_path_to_text(
                &self,
                device_path: &MockDevicePathProtocol,
                display_only: bool,
                allow_shortcuts: bool,
            ) -> Result<MockDevicePathText<'static>>;
        }
    }
    /// Map to the libefi name so code under test can just use one name.
    pub type DevicePathToTextProtocol = MockDevicePathToTextProtocol;

    mock! {
        /// Mock [efi::DevicePathText].
        pub DevicePathText<'a> {
            /// Returns the text, which is data-only so isn't mocked.
            pub fn text(&self) -> Option<&'a [u16]>;
        }
    }
    /// Map to the libefi name so code under test can just use one name.
    pub type DevicePathText<'a> = MockDevicePathText<'a>;
}

/// Mock loaded_image protocol.
pub mod loaded_image {
    use super::*;

    mock! {
        /// Mock [efi::LoadedImageProtocol].
        pub LoadedImageProtocol {
            /// Returns a real [efi::DeviceHandle], which is data-only so isn't mocked.
            pub fn device_handle(&self) -> Result<DeviceHandle>;
        }
    }
    /// Map to the libefi name so code under test can just use one name.
    pub type LoadedImageProtocol = MockLoadedImageProtocol;
}

/// Mock simple_text_input module.
pub mod simple_text_input {
    use super::*;

    mock! {
        /// Mock [efi::SimpleTextInputProtocol].
        pub SimpleTextInputProtocol {
            /// Returns an [EfiInputKey], which is data-only so isn't mocked.
            pub fn read_key_stroke(&self) -> Result<Option<EfiInputKey>>;
        }
    }
    /// Map to the libefi name so code under test can just use one name.
    pub type SimpleTextInputProtocol = MockSimpleTextInputProtocol;
}

/// Mock simple_text_output module.
pub mod simple_text_output {
    use super::*;

    mock! {
        /// Mock [efi::SimpleTextOutputProtocol].
        pub SimpleTextOutputProtocol {}

        impl Write for SimpleTextOutputProtocol {
            fn write_str(&mut self, s: &str) -> core::fmt::Result;
        }
    }
    /// Map to the libefi name so code under test can just use one name.
    pub type SimpleTextOutputProtocol = MockSimpleTextOutputProtocol;

    /// Returns a [MockSimpleTextOutputProtocol] that forwards all calls to `MOCK_EFI`.
    pub fn passthrough_con_out() -> MockSimpleTextOutputProtocol {
        let mut con_out = MockSimpleTextOutputProtocol::default();
        con_out.expect_write_str().returning(|s| {
            MOCK_EFI.with_borrow_mut(|efi| efi.as_mut().unwrap().con_out.write_str(s))
        });
        con_out
    }

    /// While this mock itself isn't necessarily thread-local, passing through to the thread-local
    /// state is our primary use case, so we just disallow [Send] entirely.
    impl !Send for MockSimpleTextOutputProtocol {}
}

/// Mock image_loading protocol.
pub mod gbl_efi_image_loading {
    use super::*;

    mock! {
        /// Mock [efi::ImageLoadingProtocol].
        pub GblImageLoadingProtocol {
            /// Returns [EfiImageBuffer] matching `gbl_image_info`
            pub fn get_buffer(&self, gbl_image_info: &GblEfiImageInfo) -> Result<EfiImageBuffer>;

            /// Returns number of partitions to be provided via `get_verify_partitions()`, and thus
            /// expected size of `partition_name` slice.
            pub fn get_verify_partitions_count(&self) -> Result<usize>;

            /// Returns number of partition names written to `partition_name` slice.
            pub fn get_verify_partitions(
                &self,
                partition_names: &mut [GblEfiPartitionName]
            ) -> Result<usize>;
        }
    }

    /// Map to the libefi name so code under test can just use one name.
    pub type GblImageLoadingProtocol = MockGblImageLoadingProtocol;
}

/// Mock os_configuration protocol.
pub mod gbl_efi_os_configuration {
    use super::*;

    mock! {
        /// Mock [efi::OsConfigurationProtocol].
        pub GblOsConfigurationProtocol {
            /// Wraps `GBL_EFI_OS_CONFIGURATION_PROTOCOL.fixup_kernel_commandline()`
            pub fn fixup_kernel_commandline(
                &self,
                commandline: &CStr,
                fixup: &[u8],
            ) -> Result<()>;

            /// Wraps `GBL_EFI_OS_CONFIGURATION_PROTOCOL.fixup_bootconfig()`
            pub fn fixup_bootconfig(
                &self,
                bootconfig: &[u8],
                fixup: &mut [u8],
            ) -> Result<usize>;

            /// Wraps `GBL_EFI_OS_CONFIGURATION_PROTOCOL.select_device_trees()`
            pub fn select_device_trees(
                &self,
                components: &mut [GblEfiVerifiedDeviceTree],
            ) -> Result<()>;
        }
    }

    /// Map to the libefi name so code under test can just use one name.
    pub type GblOsConfigurationProtocol = MockGblOsConfigurationProtocol;
}

/// Mock dt_fixup protocol.
pub mod dt_fixup {
    use super::*;

    mock! {
        /// Mock [efi::DtFixupProtocol].
        pub DtFixupProtocol {
            /// Wraps `EFI_DT_FIXUP_PROTOCOL.fixup()`
            pub fn fixup(&self, device_tree: &mut [u8]) -> Result<()>;
        }
    }

    /// Map to the libefi name so code under test can just use one name.
    pub type DtFixupProtocol = MockDtFixupProtocol;
}

/// Mock avb protocol.
pub mod gbl_efi_avb {
    use super::*;

    /// Mock implementation of `GBL_EFI_AVB_PROTOCOL`.
    /// We use a custom mock implementation instead of relying on `mockall` due to its limitations
    /// regarding argument lifetimes. Specifically, in this case, `mockall` requires the
    /// `validate_vbmeta_public_key.public_key_metadata` argument to have a `'static` lifetime,
    /// which is not practical for our use case.
    #[derive(Clone, Default)]
    pub struct GblAvbProtocol {
        /// Expected return value from `validate_vbmeta_public_key`.
        pub validate_vbmeta_public_key_result: Option<Result<GblEfiAvbKeyValidationStatus>>,
        /// Expected return value from `read_is_device_unlocked`.
        pub read_is_device_unlocked_result: Option<Result<bool>>,
        /// Expected return value from `read_rollback_index`.
        pub read_rollback_index_result: Option<Result<u64>>,
        /// Expected return value from `write_rollback_index`.
        pub write_rollback_index_result: Option<Result<()>>,
        /// Expected return value from `read_persistent_value`.
        pub read_persistent_value_result: Option<Result<usize>>,
        /// Expected return value from `write_persistent_value`.
        pub write_persistent_value_result: Option<Result<()>>,
    }

    impl GblAvbProtocol {
        /// Wraps `GBL_EFI_AVB_PROTOCOL.validate_vbmeta_public_key()`.
        pub fn validate_vbmeta_public_key(
            &self,
            _public_key: &[u8],
            _public_key_metadata: Option<&[u8]>,
        ) -> Result<GblEfiAvbKeyValidationStatus> {
            self.validate_vbmeta_public_key_result.unwrap()
        }

        /// Wraps `GBL_EFI_AVB_PROTOCOL.read_is_device_unlocked()`.
        pub fn read_is_device_unlocked(&self) -> Result<bool> {
            self.read_is_device_unlocked_result.unwrap()
        }

        /// Wraps `GBL_EFI_AVB_PROTOCOL.read_rollback_index()`.
        pub fn read_rollback_index(&self, _index_location: usize) -> Result<u64> {
            self.read_rollback_index_result.unwrap()
        }

        /// Wraps `GBL_EFI_AVB_PROTOCOL.write_rollback_index()`.
        pub fn write_rollback_index(
            &self,
            _index_location: usize,
            _rollback_index: u64,
        ) -> Result<()> {
            self.write_rollback_index_result.unwrap()
        }

        /// Wraps `GBL_EFI_AVB_PROTOCOL.read_persistent_value()`.
        pub fn read_persistent_value(&self, _name: &CStr, _value: &mut [u8]) -> Result<usize> {
            self.read_persistent_value_result.unwrap()
        }

        /// Wraps `GBL_EFI_AVB_PROTOCOL.write_persistent_value()`.
        pub fn write_persistent_value(&self, _name: &CStr, _value: Option<&[u8]>) -> Result<()> {
            self.write_persistent_value_result.unwrap()
        }

        /// Wraps `GBL_EFI_AVB_PROTOCOL.handle_verification_result()`.
        pub fn handle_verification_result(
            &self,
            _verification_result: &GblEfiAvbVerificationResult,
        ) -> Result<()> {
            unimplemented!();
        }
    }
}

/// Mock gbl_efi_fastboot protocol.
pub mod gbl_efi_fastboot {
    use super::*;

    mock! {
        /// Mock [efi::protocol::gbl_efi_fastboot::Var].
        pub Var {
            /// Get name, arguments and corresponding value.
            pub fn get<'s>(&self, out: &mut [u8])
                -> Result<(&'static str, [&'static str; 1], &'static str)>;
        }
    }

    mock! {
        /// Mock [efi::GblFastbootProtocol].
        pub GblFastbootProtocol {
            /// Protocol<'_, GblFastbootProtocol>::get_var.
            pub fn get_var<'a>(
                &self,
                name: &str,
                args: core::str::Split<'a, char>,
                buffer: &mut [u8],
            ) -> Result<usize>;

            /// Returns an iterator over backend fastboot variables.
            pub fn var_iter(&self) -> Result<&'static [Var]> ;
        }
    }

    /// Map to the libefi name so code under test can just use one name.
    pub type Var = MockVar;

    /// Map to the libefi name so code under test can just use one name.
    pub type GblFastbootProtocol = MockGblFastbootProtocol;
}
