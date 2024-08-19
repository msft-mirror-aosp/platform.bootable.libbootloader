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

//! Rust wrapper for `EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL`.

use crate::efi_call;
use crate::protocol::{Protocol, ProtocolInfo};
use core::fmt::Write;
use efi_types::{char16_t, EfiGuid, EfiSimpleTextOutputProtocol};
use liberror::Result;

/// EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL
pub struct SimpleTextOutputProtocol;

impl ProtocolInfo for SimpleTextOutputProtocol {
    type InterfaceType = EfiSimpleTextOutputProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0x387477c2, 0x69c7, 0x11d2, [0x8e, 0x39, 0x00, 0xa0, 0xc9, 0x69, 0x72, 0x3b]);
}

impl Protocol<'_, SimpleTextOutputProtocol> {
    /// Wrapper of `EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL.OutputString()`
    pub fn output_string(&self, msg: *mut char16_t) -> Result<()> {
        // SAFETY:
        // `self.interface()?` guarantees `self.interface` is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is input parameter and will not be retained. It outlives the call.
        unsafe { efi_call!(self.interface()?.output_string, self.interface, msg) }
    }
}

/// Implement formatted write for `EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL`, so that we can print by
/// writing to it. i.e.:
///
/// ```
/// let protocol: Protocol<SimpleTextOutputProtocol> = ...;
/// write!(protocol, "Value = {}\n", 1234);
/// ```
impl Write for Protocol<'_, SimpleTextOutputProtocol> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for ch in s.chars() {
            // 2 is enough for encode_utf16(). Add an additional one as NULL.
            let mut buffer = [0u16; 3];
            let char16_msg = ch.encode_utf16(&mut buffer[..]);
            self.output_string(char16_msg.as_mut_ptr()).map_err(|_| core::fmt::Error {})?;
        }
        Ok(())
    }
}
