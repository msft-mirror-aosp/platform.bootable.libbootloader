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

//! Rust wrapper for `GBL_EFI_SLOT_PROTOCOL`.
extern crate libgbl;

use crate::efi_call;
use crate::protocol::{Protocol, ProtocolInfo};
use efi_types::{
    EfiGuid, GblEfiABSlotProtocol, GblEfiBootReason, GblEfiSlotInfo, GblEfiSlotMetadataBlock,
    GblEfiUnbootableReason, GBL_EFI_UNBOOTABLE_REASON_GBL_EFI_NO_MORE_TRIES as NO_MORE_TRIES,
    GBL_EFI_UNBOOTABLE_REASON_GBL_EFI_SYSTEM_UPDATE as SYSTEM_UPDATE,
    GBL_EFI_UNBOOTABLE_REASON_GBL_EFI_USER_REQUESTED as USER_REQUESTED,
    GBL_EFI_UNBOOTABLE_REASON_GBL_EFI_VERIFICATION_FAILURE as VERIFICATION_FAILURE,
};
use liberror::{Error, Result};

use libgbl::slots::{Bootability, Slot, UnbootableReason};

/// Wraps `GBL_EFI_SLOT_PROTOCOL`.
pub struct GblSlotProtocol;

impl ProtocolInfo for GblSlotProtocol {
    type InterfaceType = GblEfiABSlotProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0x9a7a7db4, 0x614b, 0x4a08, [0x3d, 0xf9, 0x00, 0x6f, 0x49, 0xb0, 0xd8, 0x0c]);
}

fn from_efi_unbootable_reason(reason: GblEfiUnbootableReason) -> UnbootableReason {
    match reason {
        NO_MORE_TRIES => UnbootableReason::NoMoreTries,
        SYSTEM_UPDATE => UnbootableReason::SystemUpdate,
        USER_REQUESTED => UnbootableReason::UserRequested,
        VERIFICATION_FAILURE => UnbootableReason::VerificationFailure,
        _ => UnbootableReason::Unknown,
    }
}

/// Newtype around GblEfiSlotInfo to bypass orphan rule.
pub struct GblSlot(pub(crate) GblEfiSlotInfo);

impl From<GblEfiSlotInfo> for GblSlot {
    fn from(slot: GblEfiSlotInfo) -> Self {
        Self(slot)
    }
}

impl TryFrom<GblSlot> for libgbl::slots::Slot {
    type Error = liberror::Error;
    fn try_from(info: GblSlot) -> Result<Self> {
        let info = info.0;
        Ok(Slot {
            suffix: info.suffix.try_into()?,
            priority: info.priority.into(),
            bootability: match (info.successful, info.tries) {
                (s, _) if s != 0 => Bootability::Successful,
                (0, t) if t > 0 => Bootability::Retriable(info.tries.into()),
                _ => Bootability::Unbootable(from_efi_unbootable_reason(info.unbootable_reason)),
            },
        })
    }
}

impl<'a> Protocol<'a, GblSlotProtocol> {
    /// Wrapper of `GBL_EFI_SLOT_PROTOCOL.load_boot_data()`
    pub fn load_boot_data(&self) -> Result<GblEfiSlotMetadataBlock> {
        let mut block: GblEfiSlotMetadataBlock = Default::default();
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is an input parameter and will not be retained. It outlives the call.
        // `block` is an output parameter and will not be retained. It outlives the call.
        unsafe { efi_call!(self.interface()?.load_boot_data, self.interface, &mut block)? }
        Ok(block)
    }

    /// Wrapper of `GBL_EFI_SLOT_PROTOCOL.get_slot_info()`
    pub fn get_slot_info(&self, idx: u8) -> Result<GblSlot> {
        let mut info: GblEfiSlotInfo = Default::default();
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is an input parameter and will not be retained. It outlives the call.
        // `info` is an output parameter and will not be retained. It outlives the call.
        unsafe { efi_call!(self.interface()?.get_slot_info, self.interface, idx, &mut info,)? }
        Ok(info.into())
    }

    /// Wrapper of `GBL_EFI_SLOT_PROTOCOL.get_current_slot()`
    pub fn get_current_slot(&self) -> Result<GblSlot> {
        let mut info: GblEfiSlotInfo = Default::default();
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is an input parameter and will not be retained. It outlives the call.
        // `info` is an output parameter and will not be retained. It outlives the call.
        unsafe { efi_call!(self.interface()?.get_current_slot, self.interface, &mut info)? };
        Ok(info.into())
    }

    /// Wrapper of `GBL_EFI_SLOT_PROTOCOL.GetNextSlot()`
    pub fn get_next_slot(&self, mark_boot_attempt: bool) -> Result<GblSlot> {
        let mut info = GblEfiSlotInfo::default();
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface`, `info` are input/output parameter and will not be retained. It
        // outlives the call.
        unsafe {
            efi_call!(
                self.interface()?.get_next_slot,
                self.interface,
                mark_boot_attempt,
                &mut info as _
            )?;
        }
        Ok(GblSlot::from(info))
    }

    /// Wrapper of `GBL_EFI_SLOT_PROTOCOL.set_active_slot()`
    pub fn set_active_slot(&self, idx: u8) -> Result<()> {
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is an input parameter and will not be retained. It outlives the call.
        unsafe { efi_call!(self.interface()?.set_active_slot, self.interface, idx) }
    }

    /// Wrapper of `GBL_EFI_SLOT_PROTOCOL.set_slot_unbootable()`
    pub fn set_slot_unbootable(&self, idx: u8, reason: GblEfiUnbootableReason) -> Result<()> {
        let reason: u32 = reason.try_into().or(Err(Error::InvalidInput))?;
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is an input parameter and will not be retained. It outlives the call.
        unsafe { efi_call!(self.interface()?.set_slot_unbootable, self.interface, idx, reason) }
    }

    /// Wrapper of `GBL_EFI_SLOT_PROTOCOL.reinitialize()`
    pub fn reinitialize(&self) -> Result<()> {
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is an input parameter and will not be retained. It outlives the call.
        unsafe { efi_call!(self.interface()?.reinitialize, self.interface) }
    }

    /// Wrapper of `GBL_EFI_SLOT_PROTOCOL.get_boot_reason()`
    pub fn get_boot_reason(&self, subreason: &mut [u8]) -> Result<(GblEfiBootReason, usize)> {
        let mut reason: u32 = 0;
        let mut subreason_size = subreason.len();
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is an input parameter and will not be retained. It outlives the call.
        // `reason` is an output parameter. It is not retained, and it outlives the call.
        // `subreason_size` is an in-out parameter. It is not retained, and it outlives the call.
        // `subreason` remains valid during the call.
        unsafe {
            efi_call!(
                @bufsize subreason_size,
                self.interface()?.get_boot_reason,
                self.interface,
                &mut reason,
                &mut subreason_size,
                subreason.as_mut_ptr(),
            )?
        }

        let reason: GblEfiBootReason = reason.try_into().or(Err(Error::InvalidInput))?;
        Ok((reason, subreason_size))
    }

    /// Wrapper of `GBL_EFI_SLOT_PROTOCOL.set_boot_reason()`
    pub fn set_boot_reason(&self, reason: GblEfiBootReason, subreason: &[u8]) -> Result<()> {
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is an input parameter and will not be retained. It outlives the call.
        // `subreason` is not modified or retained. It outlives the call.
        unsafe {
            efi_call!(
                self.interface()?.set_boot_reason,
                self.interface,
                reason.try_into().or(Err(Error::InvalidInput))?,
                subreason.len(),
                subreason.as_ptr(),
            )
        }
    }

    /// Wrapper of `GBL_EFI_SLOT_PROTOCOL.flush()`
    pub fn flush(&self) -> Result<()> {
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is an input parameter and will not be retained. It outlives the call.
        unsafe { efi_call!(self.interface()?.flush, self.interface) }
    }

    /// Wrapper of `GBL_EFI_SLOT_PROTOCOL.version`
    pub fn version(&self) -> Result<u32> {
        Ok(self.interface()?.version)
    }
}
