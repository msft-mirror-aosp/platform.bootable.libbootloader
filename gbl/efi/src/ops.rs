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

//! Implements [Gbl::Ops] for the EFI environment.

use crate::{error::GblEfiError, utils::wait_key_stroke};

use core::fmt::Write;
use efi::{efi_print, efi_println, EfiEntry};
use libgbl::{
    slots::{BootToken, Cursor},
    BootImages, GblOps, GblOpsError, Result as GblResult,
};
use zbi::ZbiContainer;

pub struct Ops<'a> {
    pub efi_entry: &'a EfiEntry,
}

// TODO(b/355217848): figure out a better way to propagate the error type we actually want;
// filtering our EFI errors through `GblOpsError` loses information.
impl From<GblEfiError> for GblOpsError {
    fn from(_: GblEfiError) -> GblOpsError {
        GblOpsError(Some("EFI error during GBL callback"))
    }
}

impl GblOps for Ops<'_> {
    fn console_out(&mut self) -> Option<&mut dyn Write> {
        unimplemented!();
    }

    fn should_stop_in_fastboot(&mut self) -> Result<bool, GblOpsError> {
        // TODO(b/349829690): also query GblSlotProtocol.get_boot_reason() for board-specific
        // fastboot triggers.
        efi_println!(self.efi_entry, "Press Backspace to enter fastboot");
        let found = wait_key_stroke(self.efi_entry, '\x08', 2000);
        if matches!(found, Ok(true)) {
            efi_println!(self.efi_entry, "Backspace pressed, entering fastboot");
        }
        Ok(found?)
    }

    fn preboot(&mut self, _: BootImages) -> Result<(), GblOpsError> {
        unimplemented!();
    }

    async fn read_from_partition(
        &mut self,
        _: &str,
        _: u64,
        _: &mut [u8],
    ) -> Result<(), GblOpsError> {
        unimplemented!();
    }

    async fn write_to_partition(
        &mut self,
        _: &str,
        _: u64,
        _: &mut [u8],
    ) -> Result<(), GblOpsError> {
        unimplemented!();
    }

    fn partition_size(&mut self, _: &str) -> Result<Option<u64>, GblOpsError> {
        unimplemented!();
    }

    fn zircon_add_device_zbi_items(
        &mut self,
        _: &mut ZbiContainer<&mut [u8]>,
    ) -> Result<(), GblOpsError> {
        unimplemented!();
    }

    fn do_fastboot<B: gbl_storage::AsBlockDevice>(&self, _: &mut Cursor<B>) -> GblResult<()> {
        unimplemented!();
    }

    fn load_slot_interface<'a, B: gbl_storage::AsBlockDevice>(
        &'a mut self,
        _: &'a mut B,
        _: BootToken,
    ) -> GblResult<Cursor<'a, B>> {
        unimplemented!();
    }
}
