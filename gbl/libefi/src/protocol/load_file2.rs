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

//! Rust implementation of `EFI_LOAD_FILE2_PROTOCOL` for loading Linux initrd.

use crate::{
    efi_try_print,
    protocol::{MaybeVersioned, ProtocolInfo, Requirement},
};
use core::{mem::MaybeUninit, ptr::copy_nonoverlapping};
use efi_types::{
    protocol::load_file2::LoadFile2,
    status::{EfiError, EfiResult},
    EfiDevicePathProtocol, EfiGuid, EfiLoadFile2Protocol, Identified,
};

impl MaybeVersioned for EfiLoadFile2Protocol {}

/// `EFI_LOAD_FILE2_PROTOCOL`
pub struct LoadFile2Protocol;

impl ProtocolInfo for LoadFile2Protocol {
    type InterfaceType = EfiLoadFile2Protocol;
    const GUID: EfiGuid = EfiLoadFile2Protocol::GUID;
    const REQUIREMENT: Requirement = Requirement::Optional;
}

/// An `EFI_LOAD_FILE2_PROTOCOL` that loads the Linux initrd from memory.
pub struct InitrdLoadFile2Protocol<'a>(pub &'a [u8]);

impl<'a> LoadFile2 for InitrdLoadFile2Protocol<'a> {
    fn load_file(
        &self,
        _file_path: Option<&EfiDevicePathProtocol>,
        buffer: Option<&mut [MaybeUninit<u8>]>,
    ) -> EfiResult<usize> {
        let len = self.0.len();
        match buffer {
            Some(buf) if buf.len() >= len => {
                // SAFETY:
                // * `self.0` points to a valid slice for reads of `len` bytes.
                // * `buf` points to valid slice for writes of `len` bytes.
                // * `u8` has no alignment requirements.
                // * src and dst does not overlap within `len` bytes.
                unsafe {
                    copy_nonoverlapping(self.0.as_ptr(), buf.as_mut_ptr() as *mut u8, len);
                }
                efi_try_print!("InitrdLoadFile2: successfully copied {len} bytes\r\n");
                Ok(len)
            }
            // A null buffer is the caller asking how large the initrd is, not a
            // failure. The Linux stub issues exactly this call first and treats
            // any status other than EFI_BUFFER_TOO_SMALL as EFI_LOAD_ERROR
            // (efi_load_initrd_dev_path in
            // drivers/firmware/efi/libstub/efi-stub-helper.c), so this branch
            // is the contract rather than a fault.
            None => {
                efi_try_print!("InitrdLoadFile2: reporting initrd size {len}\r\n");
                Err(EfiError::BufferTooSmall(len))
            }
            Some(buf) => {
                efi_try_print!(
                    "InitrdLoadFile2: buffer too small (required: {len}, provided: {})\r\n",
                    buf.len()
                );
                Err(EfiError::BufferTooSmall(len))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_RAMDISK: &[u8] = b"mock_initrd_ramdisk_payload_for_testing";

    /// Drops any console output from an earlier test on this thread.
    fn reset_console_out() {
        crate::test::efi_call_traces().with(|t| *t.borrow_mut() = Default::default());
    }

    /// Returns what has been written to the console since the last reset.
    fn console_out() -> String {
        crate::test::efi_call_traces().with(|t| t.borrow().console_out_trace.as_single_string())
    }

    #[test]
    fn test_initrd_load_file2_null_buffer_returns_buffer_too_small() {
        let loader = InitrdLoadFile2Protocol(TEST_RAMDISK);
        reset_console_out();

        let res = loader.load_file(None, None);

        assert_eq!(res, Err(EfiError::BufferTooSmall(TEST_RAMDISK.len())));
        assert!(console_out().contains("reporting initrd size"));
    }

    #[test]
    fn test_initrd_load_file2_insufficient_buffer_returns_buffer_too_small() {
        let loader = InitrdLoadFile2Protocol(TEST_RAMDISK);
        let mut buffer = vec![MaybeUninit::<u8>::uninit(); TEST_RAMDISK.len() - 1];
        reset_console_out();

        let res = loader.load_file(None, Some(&mut buffer));

        assert_eq!(res, Err(EfiError::BufferTooSmall(TEST_RAMDISK.len())));
        assert!(console_out().contains("buffer too small"));
    }

    #[test]
    fn test_initrd_load_file2_exact_buffer_size_success() {
        let loader = InitrdLoadFile2Protocol(TEST_RAMDISK);
        let mut buffer = vec![0u8; TEST_RAMDISK.len()];

        // SAFETY: `InitrdLoadFile2Protocol::load_file` only writes initialized bytes into the
        // slice and never writes `MaybeUninit::uninit()`.
        let res = loader.load_file(
            None,
            Some(unsafe {
                core::slice::from_raw_parts_mut(
                    buffer.as_mut_ptr() as *mut MaybeUninit<u8>,
                    buffer.len(),
                )
            }),
        );

        assert_eq!(res, Ok(TEST_RAMDISK.len()));
        assert_eq!(&buffer[..], TEST_RAMDISK);
    }

    #[test]
    fn test_initrd_load_file2_larger_buffer_size_success() {
        let loader = InitrdLoadFile2Protocol(TEST_RAMDISK);
        let mut buffer = vec![0u8; TEST_RAMDISK.len() + 16];

        // SAFETY: `InitrdLoadFile2Protocol::load_file` only writes initialized bytes into the
        // slice and never writes `MaybeUninit::uninit()`.
        let res = loader.load_file(
            None,
            Some(unsafe {
                core::slice::from_raw_parts_mut(
                    buffer.as_mut_ptr() as *mut MaybeUninit<u8>,
                    buffer.len(),
                )
            }),
        );

        assert_eq!(res, Ok(TEST_RAMDISK.len()));
        assert_eq!(&buffer[..TEST_RAMDISK.len()], TEST_RAMDISK);
    }
}
