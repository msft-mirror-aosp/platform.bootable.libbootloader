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

//! Implementation of the `GblEfiFastbootProtocol` for qemu tests.

#![cfg_attr(not(test), no_std)]

use core::ffi::CStr;
use efi_types::{
    defs::{
        GblEfiFastbootCommandExecResult, GblEfiFastbootMessageType,
        GBL_EFI_FASTBOOT_COMMAND_EXEC_RESULT_CUSTOM_IMPL,
        GBL_EFI_FASTBOOT_COMMAND_EXEC_RESULT_DEFAULT_IMPL, GBL_EFI_FASTBOOT_MESSAGE_TYPE_FAIL,
        GBL_EFI_FASTBOOT_MESSAGE_TYPE_OKAY, GBL_EFI_FASTBOOT_PROTOCOL_REVISION,
    },
    protocol::gbl_efi_fastboot::GblEfiFastboot,
    status::{EfiError, EfiResult},
};

/// Test implementation of `GblEfiFastboot`.
pub struct GblEfiFastbootImpl;

impl GblEfiFastboot for GblEfiFastbootImpl {
    fn revision(&self) -> u64 {
        GBL_EFI_FASTBOOT_PROTOCOL_REVISION
    }

    fn serial_number(&self) -> EfiResult<&str> {
        Ok("test_serial_num")
    }

    fn get_var<'a>(
        &self,
        _args: impl Iterator<Item = &'a str>,
        _buffer: &mut [u8],
    ) -> EfiResult<usize> {
        // TODO(b/578052235): Implement and test get_var
        Err(EfiError::NotFound)
    }

    fn get_var_all(&self, _cb: &mut dyn FnMut(&[&CStr], &CStr) -> EfiResult<()>) -> EfiResult<()> {
        // TODO(b/578052235): Implement and test get_var_all
        Ok(())
    }

    fn get_staged(&self, _buffer: &mut [u8]) -> EfiResult<(usize, usize)> {
        // TODO(b/578052235): Implement and test get_staged
        Err(EfiError::Unsupported)
    }

    fn command_exec<'a>(
        &self,
        mut args: impl Iterator<Item = &'a str>,
        _download_buffer: &mut [u8],
        _download_buffer_used: usize,
        sender: &mut dyn FnMut(GblEfiFastbootMessageType, &str) -> EfiResult<()>,
    ) -> EfiResult<GblEfiFastbootCommandExecResult> {
        let first_arg = args.next().ok_or(EfiError::InvalidParameter)?;
        if let Some(mut args_iter) = match_oem_cmd(first_arg, "readenv") {
            // oem readenv <var>
            let var_name = args_iter.next().ok_or(EfiError::InvalidParameter)?;
            return readenv(var_name, sender);
        } else if first_arg == "readenv" {
            // readenv:<var>
            let var_name = args.next().ok_or(EfiError::InvalidParameter)?;
            return readenv(var_name, sender);
        }
        Ok(GBL_EFI_FASTBOOT_COMMAND_EXEC_RESULT_DEFAULT_IMPL)
    }

    fn get_partition_type(&self, _part_name: &CStr, _part_type: &mut [u8]) -> EfiResult<usize> {
        Err(EfiError::NotFound)
    }
}

/// Helper function to match OEM command and extract arguments.
fn match_oem_cmd<'a>(cmd: &'a str, target: &str) -> Option<impl Iterator<Item = &'a str>> {
    // For tests, we require oem command args are separated by spaces.
    let mut args = cmd.split(' ');
    match (args.next()?, args.next()?) {
        ("oem", t) if t == target => Some(args),
        _ => None,
    }
}

/// Helper function for `readenv` command.
fn readenv(
    var: &str,
    sender: &mut dyn FnMut(GblEfiFastbootMessageType, &str) -> EfiResult<()>,
) -> EfiResult<GblEfiFastbootCommandExecResult> {
    let mut buf = [0u8; 64];
    match semihosting::getenv(Some(var), &mut buf) {
        Ok(val) => sender(GBL_EFI_FASTBOOT_MESSAGE_TYPE_OKAY, val)?,
        Err(_) => sender(GBL_EFI_FASTBOOT_MESSAGE_TYPE_FAIL, "Variable not found")?,
    }
    Ok(GBL_EFI_FASTBOOT_COMMAND_EXEC_RESULT_CUSTOM_IMPL)
}
