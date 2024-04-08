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

use crate::defs::{
    EfiGuid, EfiInputKey, EfiSimpleTextInputProtocol, EFI_STATUS_NOT_FOUND, EFI_STATUS_NOT_READY,
};
use crate::protocol::{Protocol, ProtocolInfo};
use crate::{efi_call, map_efi_err, EfiResult};

/// EFI_SIMPLE_TEXT_INPUT_PROTOCOL
pub struct SimpleTextInputProtocol;

impl ProtocolInfo for SimpleTextInputProtocol {
    type InterfaceType = EfiSimpleTextInputProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0x387477c1, 0x69c7, 0x11d2, [0x8e, 0x39, 0x00, 0xa0, 0xc9, 0x69, 0x72, 0x3b]);
}

impl Protocol<'_, SimpleTextInputProtocol> {
    /// Wrapper of `EFI_SIMPLE_TEXT_INPUT_PROTOCOL.reset()`
    pub fn reset(&self, extendend_verification: bool) -> EfiResult<()> {
        // SAFETY:
        // `self.interface()?` guarantees `self.interface` is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is input parameter and will not be retained. It outlives the call.
        unsafe { efi_call!(self.interface()?.reset, self.interface, extendend_verification) }
    }

    /// Wrapper of `EFI_SIMPLE_TEXT_INPUT_PROTOCOL.read_key_stroke()`
    ///
    /// Returns `Ok(Some(EfiInputKey))` if there is a key stroke, Ok(None) if no key stroke is
    /// pressed.
    pub fn read_key_stroke(&self) -> EfiResult<Option<EfiInputKey>> {
        let mut key: EfiInputKey = Default::default();
        // SAFETY:
        // `self.interface()?` guarantees `self.interface` is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is input parameter and will not be retained. It outlives the call.
        // `key` is an output argument. It outlives the call and will not be taken.
        match unsafe { efi_call!(self.interface()?.read_key_stroke, self.interface, &mut key) } {
            Ok(()) => Ok(Some(key)),
            Err(e) if e.is_efi_err(EFI_STATUS_NOT_READY) => Ok(None),
            Err(e) => Err(e),
        }
    }
}
