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

//! Rust wrapper for `EFI_BLOCK_IO_PROTOCOL`.

use crate::efi_call;
use crate::protocol::{Protocol, ProtocolInfo};
use efi_types::{EfiBlockIoMedia, EfiBlockIoProtocol, EfiGuid};
use liberror::{Error, Result};

/// EFI_BLOCK_IO_PROTOCOL
pub struct BlockIoProtocol;

impl ProtocolInfo for BlockIoProtocol {
    type InterfaceType = EfiBlockIoProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0x964e5b21, 0x6459, 0x11d2, [0x8e, 0x39, 0x00, 0xa0, 0xc9, 0x69, 0x72, 0x3b]);
}

// Protocol interface wrappers.
impl Protocol<'_, BlockIoProtocol> {
    /// Wrapper of `EFI_BLOCK_IO_PROTOCOL.read_blocks()`
    pub fn read_blocks(&self, lba: u64, buffer: &mut [u8]) -> Result<()> {
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is input parameter and will not be retained. It outlives the call.
        // `buffer` remains valid during the call.
        unsafe {
            efi_call!(
                self.interface()?.read_blocks,
                self.interface,
                self.media()?.media_id,
                lba,
                buffer.len(),
                buffer.as_mut_ptr() as *mut _
            )
        }
    }

    /// Wrapper of `EFI_BLOCK_IO_PROTOCOL.write_blocks()`
    pub fn write_blocks(&self, lba: u64, buffer: &mut [u8]) -> Result<()> {
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is input parameter and will not be retained. It outlives the call.
        // `buffer` remains valid during the call.
        unsafe {
            efi_call!(
                self.interface()?.write_blocks,
                self.interface,
                self.media()?.media_id,
                lba,
                buffer.len(),
                buffer.as_mut_ptr() as _
            )
        }
    }

    /// Wrapper of `EFI_BLOCK_IO_PROTOCOL.flush_blocks()`
    pub fn flush_blocks(&self) -> Result<()> {
        // SAFETY:
        // `self.interface()?` guarantees `self.interface` is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is input parameter and will not be retained. It outlives the call.
        unsafe { efi_call!(self.interface()?.flush_blocks, self.interface) }
    }

    /// Wrapper of `EFI_BLOCK_IO_PROTOCOL.reset()`
    pub fn reset(&self, extended_verification: bool) -> Result<()> {
        // SAFETY:
        // `self.interface()?` guarantees `self.interface` is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is input parameter and will not be retained. It outlives the call.
        unsafe { efi_call!(self.interface()?.reset, self.interface, extended_verification) }
    }

    /// Get a copy to the EFI_BLOCK_IO_PROTOCOL.Media structure.
    pub fn media(&self) -> Result<EfiBlockIoMedia> {
        let ptr = self.interface()?.media;
        // SFETY: Pointers to EFI data structure.
        Ok(*unsafe { ptr.as_ref() }.ok_or(Error::InvalidInput)?)
    }
}
