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
use core::fmt::Write;
use efi::protocol::image_loading::ImageBuffer;
use efi_types::{EfiInputKey, GblImageInfo, GblPartitionName};
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
pub mod image_loading {
    use super::*;

    mock! {
        /// Mock [efi::ImageLoadingProtocol].
        pub GblImageLoadingProtocol {
            /// Returns [ImageBuffer] matching `gbl_image_info`
            pub fn get_buffer<'a>(&self, gbl_image_info: &GblImageInfo) -> Result<ImageBuffer<'a>>;

            /// Returns number of partitions to be provided via `get_verify_partitions()`, and thus
            /// expected size of `partition_name` slice.
            pub fn get_verify_partitions_count(&self) -> Result<usize>;

            /// Returns number of partition names written to `partition_name` slice.
            pub fn get_verify_partitions(
                &self,
                partition_names: &mut [GblPartitionName]
            ) -> Result<usize>;
        }
    }

    /// Map to the libefi name so code under test can just use one name.
    pub type GblImageLoadingProtocol = MockGblImageLoadingProtocol;
}
