// Copyright 2026, The Android Open Source Project
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

//! Rust trait for
//! [`GBL_EFI_BOOT_CONTROL_PROTOCOL`](https://android.googlesource.com/platform/bootable/libbootloader/+/refs/heads/gbl-mainline/gbl/docs/gbl_efi_boot_control_protocol.md).

use crate::{
    defs::{
        EfiGuid, EfiStatus, GblEfiBootControlProtocol, GblEfiLoadedOs, GblEfiOneShotBootMode,
        GblEfiSlotInfo,
    },
    protocol::{check_required_params, BridgeToRust, Provider},
    status::{EfiError, EfiResult},
    Identified,
};

/// Protocol Rust API for `GBL_EFI_BOOT_CONTROL_PROTOCOL`.
#[cfg_attr(feature = "mocks", mockall::automock)]
pub trait GblEfiBootControl {
    /// Returns the protocol revision that the implementation is providing.
    fn revision(&self) -> u64;

    /// Returns the number of boot slots.
    fn get_slot_count(&self) -> EfiResult<u8>;

    /// Returns information about a slot by index.
    fn get_slot_info(&self, index: u8) -> EfiResult<GblEfiSlotInfo>;

    /// Returns information about the currently booted slot.
    fn get_current_slot(&self) -> EfiResult<GblEfiSlotInfo>;

    /// Sets the active slot by index.
    fn set_active_slot(&self, index: u8) -> EfiResult<()>;

    /// Gets the hardware-triggered one-shot boot mode.
    fn get_one_shot_boot_mode(&self) -> EfiResult<GblEfiOneShotBootMode>;

    /// Handles loaded OS images.
    fn handle_loaded_os(&self, os: &GblEfiLoadedOs) -> EfiResult<()>;
}

impl Identified for GblEfiBootControlProtocol {
    const GUID: EfiGuid = EfiGuid::from_u64s(
        crate::defs::GBL_EFI_BOOT_CONTROL_PROTOCOL_GUID_U64_0,
        crate::defs::GBL_EFI_BOOT_CONTROL_PROTOCOL_GUID_U64_1,
    );
}

// SAFETY:
// * our wrapper functions adhere to the protocol spec
unsafe impl<R: GblEfiBootControl> BridgeToRust<R> for GblEfiBootControlProtocol {
    unsafe fn create_bridge(rust_impl: &R) -> Self {
        Self {
            revision: rust_impl.revision(),
            get_slot_count: Some(Provider::<_, R>::get_slot_count),
            get_slot_info: Some(Provider::<_, R>::get_slot_info),
            get_current_slot: Some(Provider::<_, R>::get_current_slot),
            set_active_slot: Some(Provider::<_, R>::set_active_slot),
            get_one_shot_boot_mode: Some(Provider::<_, R>::get_one_shot_boot_mode),
            handle_loaded_os: Some(Provider::<_, R>::handle_loaded_os),
        }
    }
}

impl<R: GblEfiBootControl> Provider<'_, GblEfiBootControlProtocol, R> {
    /// Implementation of `GBL_EFI_BOOT_CONTROL_PROTOCOL.GetSlotCount`.
    ///
    /// # Safety
    ///
    /// * Caller must guarantee that `interface` is a valid pointer to a
    ///   `GblEfiBootControlProtocol` struct inside a `Self` struct.
    /// * Caller must guarantee that `slot_count` points to a valid `u8` parameter.
    unsafe extern "efiapi" fn get_slot_count(
        interface: *mut GblEfiBootControlProtocol,
        slot_count: *mut u8,
    ) -> EfiStatus {
        // SAFETY: By safety contract, `interface` is a valid pointer to a
        // `GblEfiBootControlProtocol` struct inside a `Self` struct. Since it comes as the
        // first field, `interface` is also a valid pointer to the `Self` struct.
        let rust_impl = unsafe { Self::to_rust(interface) };
        (|| {
            check_required_params(&[&slot_count])?;
            // SAFETY: `slot_count` was checked non-null and aligned above, and by safety contract
            // is valid for writes.
            rust_impl.get_slot_count().inspect(|count| unsafe { slot_count.write(*count) })
        })()
        .into()
    }

    /// Implementation of `GBL_EFI_BOOT_CONTROL_PROTOCOL.GetSlotInfo`.
    ///
    /// # Safety
    ///
    /// * Caller must guarantee that `interface` is a valid pointer to a
    ///   `GblEfiBootControlProtocol` struct inside a `Self` struct.
    /// * Caller must guarantee that `info` points to a valid `GblEfiSlotInfo` parameter.
    unsafe extern "efiapi" fn get_slot_info(
        interface: *mut GblEfiBootControlProtocol,
        index: u8,
        info: *mut GblEfiSlotInfo,
    ) -> EfiStatus {
        // SAFETY: By safety contract, `interface` is a valid pointer to a
        // `GblEfiBootControlProtocol` struct inside a `Self` struct. Since it comes as the
        // first field, `interface` is also a valid pointer to the `Self` struct.
        let rust_impl = unsafe { Self::to_rust(interface) };
        (|| {
            check_required_params(&[&info])?;
            // SAFETY: `info` was checked non-null and aligned above, and by safety contract is
            // valid for writes.
            rust_impl.get_slot_info(index).inspect(|slot_info| unsafe { info.write(*slot_info) })
        })()
        .into()
    }

    /// Implementation of `GBL_EFI_BOOT_CONTROL_PROTOCOL.GetCurrentSlot`.
    ///
    /// # Safety
    ///
    /// * Caller must guarantee that `interface` is a valid pointer to a
    ///   `GblEfiBootControlProtocol` struct inside a `Self` struct.
    /// * Caller must guarantee that `info` points to a valid `GblEfiSlotInfo` parameter.
    unsafe extern "efiapi" fn get_current_slot(
        interface: *mut GblEfiBootControlProtocol,
        info: *mut GblEfiSlotInfo,
    ) -> EfiStatus {
        // SAFETY: By safety contract, `interface` is a valid pointer to a
        // `GblEfiBootControlProtocol` struct inside a `Self` struct. Since it comes as the
        // first field, `interface` is also a valid pointer to the `Self` struct.
        let rust_impl = unsafe { Self::to_rust(interface) };
        (|| {
            check_required_params(&[&info])?;
            // SAFETY: `info` was checked non-null and aligned above, and by safety contract is
            // valid for writes.
            rust_impl.get_current_slot().inspect(|slot_info| unsafe { info.write(*slot_info) })
        })()
        .into()
    }

    /// Implementation of `GBL_EFI_BOOT_CONTROL_PROTOCOL.SetActiveSlot`.
    ///
    /// # Safety
    ///
    /// * Caller must guarantee that `interface` is a valid pointer to a
    ///   `GblEfiBootControlProtocol` struct inside a `Self` struct.
    unsafe extern "efiapi" fn set_active_slot(
        interface: *mut GblEfiBootControlProtocol,
        index: u8,
    ) -> EfiStatus {
        // SAFETY: By safety contract, `interface` is a valid pointer to a
        // `GblEfiBootControlProtocol` struct inside a `Self` struct. Since it comes as the
        // first field, `interface` is also a valid pointer to the `Self` struct.
        let rust_impl = unsafe { Self::to_rust(interface) };
        rust_impl.set_active_slot(index).into()
    }

    /// Implementation of `GBL_EFI_BOOT_CONTROL_PROTOCOL.GetOneShotBootMode`.
    ///
    /// # Safety
    ///
    /// * Caller must guarantee that `interface` is a valid pointer to a
    ///   `GblEfiBootControlProtocol` struct inside a `Self` struct.
    /// * Caller must guarantee that `mode` points to a valid `GblEfiOneShotBootMode` parameter.
    unsafe extern "efiapi" fn get_one_shot_boot_mode(
        interface: *mut GblEfiBootControlProtocol,
        mode: *mut GblEfiOneShotBootMode,
    ) -> EfiStatus {
        // SAFETY: By safety contract, `interface` is a valid pointer to a
        // `GblEfiBootControlProtocol` struct inside a `Self` struct. Since it comes as the
        // first field, `interface` is also a valid pointer to the `Self` struct.
        let rust_impl = unsafe { Self::to_rust(interface) };
        (|| {
            check_required_params(&[&mode])?;
            // SAFETY: `mode` was checked non-null and aligned above, and by safety contract is
            // valid for writes.
            rust_impl
                .get_one_shot_boot_mode()
                .inspect(|boot_mode| unsafe { mode.write(*boot_mode) })
        })()
        .into()
    }

    /// Implementation of `GBL_EFI_BOOT_CONTROL_PROTOCOL.HandleLoadedOs`.
    ///
    /// # Safety
    ///
    /// * Caller must guarantee that `interface` is a valid pointer to a
    ///   `GblEfiBootControlProtocol` struct inside a `Self` struct.
    /// * Caller must guarantee that `os` points to a valid `GblEfiLoadedOs` parameter.
    unsafe extern "efiapi" fn handle_loaded_os(
        interface: *mut GblEfiBootControlProtocol,
        os: *const GblEfiLoadedOs,
    ) -> EfiStatus {
        // SAFETY: By safety contract, `interface` is a valid pointer to a
        // `GblEfiBootControlProtocol` struct inside a `Self` struct. Since it comes as the
        // first field, `interface` is also a valid pointer to the `Self` struct.
        let rust_impl = unsafe { Self::to_rust(interface) };
        (|| {
            // SAFETY: By safety contract, `os` points to a valid parameter.
            let os = unsafe { os.as_ref().ok_or(EfiError::InvalidParameter)? };
            rust_impl.handle_loaded_os(os)
        })()
        .into()
    }
}
