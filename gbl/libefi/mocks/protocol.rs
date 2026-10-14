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
use alloc::vec::Vec;
use arrayvec::ArrayVec;
use core::{ffi::CStr, fmt::Write};
pub use efi::protocol::{Revision, Versioned};
use efi_types::{
    EfiInputKey, EfiTimestampProperties, GblEfiAvbDeviceStatus, GblEfiAvbKeyValidationStatus,
    GblEfiAvbLockState, GblEfiAvbLockType, GblEfiAvbVerificationResult,
    GblEfiFastbootCommandExecResult, GblEfiFastbootMessageType, GblEfiVerifiedDeviceTree,
};
use liberror::{Error, Result};
use libgbl::gbl_avb::SpecializedPartition;
use mockall::mock;

/// Mock `Protocol` type.
pub type Protocol<'a, T> = T;

/// Constructs a mock pre-set to the given [`Versioned::revision`].
pub trait WithRevision: Default {
    /// Returns a default mock with [`Versioned::revision`] overridden to `revision`.
    fn with_revision(revision: Revision) -> Self;
}

/// Wraps a protocol mock to add an overridable [`Versioned::revision`].
/// [`Deref`](core::ops::Deref)s to the inner mock so `.expect_*()` calls flow through.
#[derive(Clone)]
pub struct VersionedMock<T, const MAJOR: u16 = 1, const MINOR: u16 = 0> {
    /// Revision reported by [`Versioned::revision`].
    pub revision: Revision,
    inner: T,
}

impl<T: Default, const MAJOR: u16, const MINOR: u16> Default for VersionedMock<T, MAJOR, MINOR> {
    fn default() -> Self {
        Self { revision: Revision { major: MAJOR, minor: MINOR }, inner: T::default() }
    }
}

impl<T, const MAJOR: u16, const MINOR: u16> core::ops::Deref for VersionedMock<T, MAJOR, MINOR> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.inner
    }
}

impl<T, const MAJOR: u16, const MINOR: u16> core::ops::DerefMut for VersionedMock<T, MAJOR, MINOR> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.inner
    }
}

impl<T, const MAJOR: u16, const MINOR: u16> Versioned for VersionedMock<T, MAJOR, MINOR> {
    const REVISION: Revision = Revision { major: MAJOR, minor: MINOR };

    fn revision(&self) -> Revision {
        self.revision
    }
}

impl<T: Default, const MAJOR: u16, const MINOR: u16> WithRevision
    for VersionedMock<T, MAJOR, MINOR>
{
    fn with_revision(revision: Revision) -> Self {
        Self { revision, inner: T::default() }
    }
}

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
            pub fn device_handle(&self) -> DeviceHandle;

            /// Returns a [DevicePathProtocol] for the loaded image file.
            pub fn file_path(&self) -> Result<device_path::DevicePathProtocol>;

            /// Returns the image base address.
            pub fn image_base(&self) -> usize;
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

/// Mock RNG protocol
pub mod random_number_generator {
    use super::*;

    /// Requested random number generator algorithm.
    ///
    /// Re-definition of: libefi/src/protocol/random_number_generator.rs
    pub enum RngAlgorithm {
        /// No specific algorithm is required. Up to implementation to decide.
        Default,
        /// Entropy directly from the source, without it going through some deterministic
        /// random bit generator.
        Raw,
    }

    mock! {
        /// Mock [efi::RandomNumberGeneratorProtocol]
        pub RandomNumberGeneratorProtocol {
            /// Returns `buffer.len()` of random data.
            pub fn get_rng_bytes(&self, algorithm: RngAlgorithm, buffer: &[u8]) -> Result<()>;
        }
    }

    /// Map to the libefi name so code under test can just use one name.
    pub type RandomNumberGeneratorProtocol = MockRandomNumberGeneratorProtocol;
}

/// Mock timestamp protocol
pub mod timestamp {
    use super::*;

    mock! {
        /// Mock [efi::TimestampProtocol]
        pub TimestampProtocol {
            /// Returns the current timestamp.
            pub fn get_timestamp(&self)->Result<u64>;

            /// Returns properties of the timestamp protocol.
            pub fn get_properties(&self)->Result<EfiTimestampProperties>;
        }
    }

    /// Map to the libefi name so code under test can just use one name.
    pub type TimestampProtocol = MockTimestampProtocol;
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
                fixup: &mut [u8],
            ) -> Result<usize>;

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

            /// Wraps `GBL_EFI_OS_CONFIGURATION_PROTOCOL.select_fit_configuration()`
            pub fn select_fit_configuration(
                &self,
                fit: &[u8],
                metadata: &[u8],
            ) -> Result<usize>;
        }
    }

    /// Map to the libefi name so code under test can just use one name.
    pub type GblOsConfigurationProtocol = VersionedMock<MockGblOsConfigurationProtocol>;
}

/// Mock dt_fixup protocol.
pub mod dt_fixup {
    use super::*;

    mock! {
        /// Mock [efi::DtFixupProtocol].
        pub DtFixupProtocol {
            /// Wraps `EFI_DT_FIXUP_PROTOCOL.revision`.
            pub fn revision(&self) -> Revision;

            /// Wraps `EFI_DT_FIXUP_PROTOCOL.fixup()`
            pub fn fixup(&self, device_tree: &mut [u8]) -> Result<()>;
        }
    }

    impl Versioned for MockDtFixupProtocol {
        const REVISION: efi::protocol::Revision = Revision { major: 1, minor: 0 };

        fn revision(&self) -> Revision {
            self.revision()
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
    pub struct MockGblAvbProtocol {
        /// Expected return value from `read_partition_attributes`.
        pub read_partition_attributes_result: Option<Result<Vec<SpecializedPartition>>>,
        /// Expected return value from `read_device_status`
        pub read_device_status_result: Option<Result<GblEfiAvbDeviceStatus>>,
        /// Expected return value from `validate_vbmeta_public_key`.
        pub validate_vbmeta_public_key_result: Option<Result<GblEfiAvbKeyValidationStatus>>,
        /// Expected return value from `read_rollback_index`.
        pub read_rollback_index_result: Option<Result<u64>>,
        /// Expected return value from `write_rollback_index`.
        pub write_rollback_index_result: Option<Result<()>>,
        /// Expected return value from `read_persistent_value`.
        pub read_persistent_value_result: Option<Result<usize>>,
        /// Expected return value from `write_persistent_value`.
        pub write_persistent_value_result: Option<Result<()>>,
        /// Expected return value from `handle_verification_result`.
        pub handle_verification_result_result: Option<Result<()>>,
        /// Expected return value from `write_lock_state`.
        pub write_lock_state_result: Option<Result<()>>,
        /// Expected return value from `factory_data_reset`.
        pub factory_data_reset_result: Option<Result<()>>,
    }

    impl MockGblAvbProtocol {
        /// Wraps `GBL_EFI_AVB_PROTOCOL.read_partition_attributes()`.
        pub fn read_partition_attributes<const N: usize>(
            &self,
        ) -> Result<ArrayVec<SpecializedPartition, N>> {
            match &self.read_partition_attributes_result {
                Some(Ok(parts)) => Ok(parts.iter().cloned().collect()),
                Some(Err(e)) => Err(*e),
                None => Err(Error::Unsupported),
            }
        }

        /// Wraps `GBL_EFI_AVB_PROTOCOL.read_device_status()`.
        pub fn read_device_status(&self) -> Result<GblEfiAvbDeviceStatus> {
            self.read_device_status_result.unwrap()
        }

        /// Wraps `GBL_EFI_AVB_PROTOCOL.validate_vbmeta_public_key()`.
        pub fn validate_vbmeta_public_key(
            &self,
            _public_key: &[u8],
            _public_key_metadata: Option<&[u8]>,
        ) -> Result<GblEfiAvbKeyValidationStatus> {
            self.validate_vbmeta_public_key_result.unwrap()
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
            self.handle_verification_result_result.unwrap()
        }

        /// Wraps `GBL_EFI_AVB_PROTOCOL.write_lock_state()`.
        pub fn write_lock_state(
            &self,
            _type: GblEfiAvbLockType,
            _state: GblEfiAvbLockState,
        ) -> Result<()> {
            self.write_lock_state_result.unwrap()
        }

        /// Wraps `GBL_EFI_AVB_PROTOCOL.FactoryDataReset()`.
        pub fn factory_data_reset(&self) -> Result<()> {
            self.factory_data_reset_result.unwrap()
        }
    }

    /// Map to the libefi name so code under test can just use one name.
    pub type GblAvbProtocol = VersionedMock<MockGblAvbProtocol>;
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

    /// Mock [efi::GblFastbootProtocol].
    #[derive(Default)]
    pub struct MockGblFastbootProtocol {}

    impl MockGblFastbootProtocol {
        /// Protocol<'_, GblFastbootProtocol>::get_var.
        pub fn get_var<'a>(
            &self,
            _: &CStr,
            _: impl Iterator<Item = &'a CStr> + Clone,
            _: &mut [u8],
        ) -> Result<usize> {
            unimplemented!()
        }

        /// Protocol<'_, GblFastbootProtocol>::get_var_all.
        pub fn get_var_all(&self, _: impl FnMut(&[&CStr], &CStr)) -> Result<()> {
            unimplemented!()
        }

        /// Protocol<'_, GblFastbootProtocol>::get_staged.
        pub fn get_staged(&self, _: &mut [u8]) -> Result<(usize, usize)> {
            unimplemented!()
        }

        /// Protocol<'_, GblFastbootProtocol>::command_exec()`
        pub fn command_exec<'a>(
            &self,
            _: impl Iterator<Item = &'a CStr> + Clone,
            _: &mut [u8],
            _: usize,
            _: impl FnMut(GblEfiFastbootMessageType, &str) -> Result<()>,
        ) -> Result<GblEfiFastbootCommandExecResult> {
            unimplemented!()
        }

        /// Protocol<'_, GblFastbootProtocol>::get_partition_type()`
        pub fn get_partition_type(&self, _: &CStr, _: &mut [u8]) -> Result<usize> {
            unimplemented!()
        }
    }

    /// Map to the libefi name so code under test can just use one name.
    pub type Var = MockVar;
    /// Map to the libefi name so code under test can just use one name.
    pub type GblFastbootProtocol = VersionedMock<MockGblFastbootProtocol>;
}

/// Mock gbl_efi_boot_control
pub mod gbl_efi_boot_control {
    use super::*;
    use efi::protocol::gbl_efi_boot_control::GblSlot;
    use efi_types::{GblEfiLoadedOs, GblEfiOneShotBootMode};

    mock! {
        /// Mock of [GblBootControlProtocol]
        pub GblBootControlProtocol {
            /// Mock of GblBootControlProtocol::get_slot_count.
            pub fn get_slot_count(&self) -> Result<u8>;

            /// Mock of GblBootControlProtocol::get_slot_info.
            pub fn get_slot_info(&self, idx: u8) -> Result<GblSlot>;

            /// Mock of GblBootControlProtocol::get_current_slot.
            pub fn get_current_slot(&self) -> Result<GblSlot>;

            /// Mock of GblBootControlProtocol::set_active_slot.
            pub fn set_active_slot(&self, idx: u8) -> Result<()>;

            /// Mock of GblBootControlProtocol::get_one_shot_boot_mode.
            pub fn get_one_shot_boot_mode(&self) -> Result<GblEfiOneShotBootMode>;

            /// Mock of GblBootControlProtocol::handle_loaded_os.
            pub fn handle_loaded_os(
                &self,
                os: &GblEfiLoadedOs
            ) -> Result<()>;
        }
    }

    /// Map to the libefi name so code under test can just use one name.
    pub type GblBootControlProtocol = VersionedMock<MockGblBootControlProtocol>;
}

/// Mock gbl_efi_boot_memory
pub mod gbl_efi_boot_memory {
    use super::*;
    use crate::EfiEntry;
    use core::ops::{Deref, DerefMut};
    use efi_types::GblEfiBootBufferType;

    /// Mock GblVendorReservedMemory
    pub struct GblVendorReservedMemory;

    impl GblVendorReservedMemory {
        /// Mock is_preloaded
        pub fn is_preloaded(&self) -> bool {
            unimplemented!()
        }

        /// Mock leak
        pub fn leak(self) -> &'static mut [u8] {
            unimplemented!()
        }
    }

    impl Deref for GblVendorReservedMemory {
        type Target = [u8];

        fn deref(&self) -> &Self::Target {
            &[][..]
        }
    }

    impl DerefMut for GblVendorReservedMemory {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut [][..]
        }
    }

    /// Mock `gbl_get_partition_buffer`.
    pub fn gbl_get_partition_buffer(_: &EfiEntry, _: &str) -> Result<GblVendorReservedMemory> {
        unimplemented!()
    }

    /// Mock `gbl_sync_partition_buffer`.
    pub fn gbl_sync_partition_buffer(_: &EfiEntry, _: bool) -> Result<()> {
        unimplemented!()
    }

    /// Gets the boot buffer of the given type.
    pub fn gbl_get_boot_buffer(
        _: &EfiEntry,
        _: GblEfiBootBufferType,
        _: usize,
    ) -> Result<GblVendorReservedMemory> {
        unimplemented!();
    }

    /// Mock `gbl_clear_boot_buffer`.
    pub fn gbl_clear_boot_buffer(_: &EfiEntry, _: GblEfiBootBufferType) -> Result<()> {
        unimplemented!();
    }
}

/// Mock avf protocol.
pub mod gbl_efi_avf {
    use super::*;

    mock! {
        /// Mock [efi::AvfProtocol].
        pub GblAvfProtocol {
            /// Wraps `GBL_EFI_AVF_PROTOCOL.read_vendor_dice_handover()`.
            pub fn read_vendor_dice_handover(&self, handover_buffer: &mut [u8]) -> Result<usize>;

            /// Wraps `GBL_EFI_AVF_PROTOCOL.read_secretkeeper_public_key()`.
            pub fn read_secretkeeper_public_key(&self, key_buffer: &mut [u8]) -> Result<usize>;
        }
    }

    /// Map to the libefi name so code under test can just use one name.
    pub type GblAvfProtocol = VersionedMock<MockGblAvfProtocol>;
}
