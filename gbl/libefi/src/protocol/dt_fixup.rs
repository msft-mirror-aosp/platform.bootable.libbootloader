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

//! Rust wrapper for `EFI_DT_FIXUP_PROTOCOL`.

use crate::efi_call;
use crate::protocol::{Protocol, ProtocolInfo};
use efi_types::{EfiDtFixupProtocol, EfiGuid, EFI_DT_APPLY_FIXUPS};
use liberror::Result;

/// `EFI_DT_FIXUP_PROTOCOL` implementation.
pub struct DtFixupProtocol;

impl ProtocolInfo for DtFixupProtocol {
    type InterfaceType = EfiDtFixupProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0xe617d64c, 0xfe08, 0x46da, [0xf4, 0xdc, 0xbb, 0xd5, 0x87, 0x0c, 0x73, 0x00]);
}

// Protocol interface wrappers.
impl Protocol<'_, DtFixupProtocol> {
    /// Wraps `EFI_DT_FIXUP_PROTOCOL.fixup()`.
    pub fn fixup(&self, device_tree: &mut [u8]) -> Result<()> {
        let mut buffer_size = device_tree.len();

        // SAFETY:
        // * `self.interface()?` guarantees self.interface is non-null and points to a valid object
        //   established by `Protocol::new()`.
        // * `device_tree` is non-null buffer available for write, used only within the call.
        // * `buffer_size` is non-null usize buffer available for write, used only within the call.
        unsafe {
            efi_call!(
                @bufsize buffer_size,
                self.interface()?.fixup,
                self.interface,
                device_tree.as_mut_ptr() as _,
                &mut buffer_size,
                EFI_DT_APPLY_FIXUPS
            )?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::test::run_test_with_mock_protocol;
    use efi_types::{EfiStatus, EFI_STATUS_BUFFER_TOO_SMALL, EFI_STATUS_SUCCESS};
    use liberror::Error;
    use std::{ffi::c_void, slice};

    #[test]
    fn fixup_device_tree_updated() {
        // Don't check actual FDT content for simplicity.
        const DEVICE_TREE_BUFFER: &[u8] = b"this_is_device_tree";
        const UPDATED_DEVICE_TREE_BUFFER: &[u8] = b"this_is_device_trie";

        // C callback implementation to modify provided FDT to UPDATED_DEVICE_TREE_BUFFER.
        unsafe extern "C" fn c_modify(
            _: *mut EfiDtFixupProtocol,
            device_tree: *mut c_void,
            buffer_size: *mut usize,
            flags: u32,
        ) -> EfiStatus {
            assert_eq!(flags, EFI_DT_APPLY_FIXUPS);
            // SAFETY:
            // * `device_tree` is a valid pointer to the writtable buffer at least `buffer_size`
            // size.
            // * `buffer_size` is a valid pointer to usize.
            let fdt_buffer =
                unsafe { slice::from_raw_parts_mut(device_tree as *mut u8, *buffer_size) };
            assert_eq!(fdt_buffer, DEVICE_TREE_BUFFER);

            fdt_buffer.copy_from_slice(UPDATED_DEVICE_TREE_BUFFER);

            EFI_STATUS_SUCCESS
        }

        let c_interface = EfiDtFixupProtocol { fixup: Some(c_modify), ..Default::default() };

        run_test_with_mock_protocol(c_interface, |dt_fixup_protocol| {
            let mut fdt_buffer: Vec<u8> = DEVICE_TREE_BUFFER.to_vec();

            assert!(dt_fixup_protocol.fixup(&mut fdt_buffer[..]).is_ok());
            assert_eq!(&fdt_buffer[..], UPDATED_DEVICE_TREE_BUFFER);
        });
    }

    #[test]
    fn fixup_device_tree_fixup_buffer_too_small() {
        const EXPECTED_REQUESTED_FIXUP_SIZE: usize = 256;
        // C callback implementation to return an error.
        unsafe extern "C" fn c_error(
            _: *mut EfiDtFixupProtocol,
            _: *mut c_void,
            buffer_size: *mut usize,
            _: u32,
        ) -> EfiStatus {
            // SAFETY:
            // * `buffer_size` is a valid pointer to writtable usize buffer.
            unsafe {
                *buffer_size = EXPECTED_REQUESTED_FIXUP_SIZE;
            }
            EFI_STATUS_BUFFER_TOO_SMALL
        }

        let c_interface = EfiDtFixupProtocol { fixup: Some(c_error), ..Default::default() };

        run_test_with_mock_protocol(c_interface, |dt_fixup_protocol| {
            let mut fdt_buffer = [0u8; 128];

            assert_eq!(
                dt_fixup_protocol.fixup(&mut fdt_buffer[..]),
                Err(Error::BufferTooSmall(Some(EXPECTED_REQUESTED_FIXUP_SIZE))),
            );
        });
    }
}
