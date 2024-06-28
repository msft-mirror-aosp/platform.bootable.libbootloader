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

//! Rust wrapper for `EFI_LOADED_IMAGE_PROTOCOL`.

use crate::defs::{EfiGuid, EfiLoadedImageProtocol};
use crate::protocol::{Protocol, ProtocolInfo};
use crate::{DeviceHandle, EfiResult};

/// EFI_LOADED_IMAGE_PROTOCOL
pub struct LoadedImageProtocol;

impl ProtocolInfo for LoadedImageProtocol {
    type InterfaceType = EfiLoadedImageProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0x5b1b31a1, 0x9562, 0x11d2, [0x8e, 0x3f, 0x00, 0xa0, 0xc9, 0x69, 0x72, 0x3b]);
}

impl<'a> Protocol<'a, LoadedImageProtocol> {
    /// Wraps `EFI_LOADED_IMAGE_PROTOCOL.DeviceHandle`.
    pub fn device_handle(&self) -> EfiResult<DeviceHandle> {
        Ok(DeviceHandle(self.interface()?.device_handle))
    }
}
