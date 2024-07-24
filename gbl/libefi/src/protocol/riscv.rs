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

//! Rust wrapper for `RISCV_EFI_BOOT_PROTOCOL`.

use crate::defs::{EfiGuid, EfiRiscvBootProtocol, EFI_STATUS_NOT_FOUND};
use crate::protocol::{Protocol, ProtocolInfo};
use crate::{efi_call, map_efi_err, EfiResult};

/// RISCV_EFI_BOOT_PROTOCOL
pub struct RiscvBootProtocol;

impl ProtocolInfo for RiscvBootProtocol {
    type InterfaceType = EfiRiscvBootProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0xccd15fec, 0x6f73, 0x4eec, [0x83, 0x95, 0x3e, 0x69, 0xe4, 0xb9, 0x40, 0xbf]);
}

impl<'a> Protocol<'a, RiscvBootProtocol> {
    /// Wraps `RISCV_EFI_BOOT_PROTOCOL.GetBootHartId()`.
    pub fn get_boot_hartid(&self) -> EfiResult<usize> {
        let mut boot_hart_id: usize = 0;
        // SAFETY:
        // `self.interface()?` guarantees `self.interface` is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is input parameter and will not be retained. It outlives the call.
        // `&mut boot_hart_id` is output parameter and will not be retained. It outlives the call.
        unsafe {
            efi_call!(self.interface()?.get_boot_hartid, self.interface, &mut boot_hart_id)?;
        }
        Ok(boot_hart_id)
    }

    /// Wraps `RISCV_EFI_BOOT_PROTOCOL.Revision`.
    pub fn revision(&self) -> EfiResult<u64> {
        Ok(self.interface()?.revision)
    }
}
