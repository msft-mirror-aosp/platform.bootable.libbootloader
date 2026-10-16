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
use crate::protocol::{MaybeVersioned, Protocol, ProtocolInfo};
use core::fmt::{Error, Write};
use efi_types::{
    EfiGuid, EfiSimpleTextOutputProtocol, EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL_GUID_U64_0,
    EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL_GUID_U64_1,
};
use liberror::Result;

impl MaybeVersioned for EfiSimpleTextOutputProtocol {}

/// EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL
pub struct SimpleTextOutputProtocol;

impl ProtocolInfo for SimpleTextOutputProtocol {
    type InterfaceType = EfiSimpleTextOutputProtocol;

    const GUID: EfiGuid = EfiGuid::from_u64s(
        EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL_GUID_U64_0,
        EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL_GUID_U64_1,
    );
}

impl Protocol<'_, SimpleTextOutputProtocol> {
    /// Wrapper of `EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL.Reset()`
    pub fn reset(&self, extended: bool) -> Result<()> {
        // SAFETY:
        // `self.interface()` is non-null and points to a valid object.
        // `self.interface_ptr()` is an input parameter and is not retained. It outlives the call.
        unsafe { efi_call!(self.interface().reset, self.interface_ptr(), extended) }
    }

    /// Wrapper of `EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL.OutputString()`
    pub fn output_string(&self, msg: &mut [u16]) -> Result<()> {
        if !msg.contains(&0) {
            return Err(liberror::Error::InvalidInput);
        }
        // SAFETY:
        // `self.interface_ptr()` guarantees `self.interface_ptr()` is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface_ptr()` is input parameter and will not be retained. It outlives the call.
        // `msg` is null-terminated, for input only, and will not be retained.
        unsafe { efi_call!(self.interface().output_string, self.interface_ptr(), msg.as_mut_ptr()) }
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
        let mut prev: char = '\0';
        for ch in s.chars() {
            // 2 is enough for encode_utf16(). Add an additional one as NULL.
            let mut buffer = [0u16; 3];
            let _ = ch.encode_utf16(&mut buffer[..2]);
            if ch == '\n' && prev != '\r' {
                self.output_string(&mut [b'\r' as _, 0u16]).map_err(|_| Error {})?;
            }
            // Pass all of `buffer` so the NUL terminator is inside the slice.
            self.output_string(&mut buffer[..]).map_err(|_| Error {})?;
            prev = ch;
        }
        Ok(())
    }
}
