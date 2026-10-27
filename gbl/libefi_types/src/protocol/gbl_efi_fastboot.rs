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

//! Rust trait for
//! [`GBL_EFI_FASTBOOT_PROTOCOL`](https://android.googlesource.com/platform/bootable/libbootloader/+/refs/heads/gbl-mainline/gbl/docs/gbl_efi_fastboot_protocol.md).

use alloc::vec::Vec;
use core::{
    ffi::{c_void, CStr},
    ptr::NonNull,
};

use crate::{
    defs::{
        EfiGuid, EfiStatus, FastbootMessageSender, GblEfiFastbootCommandExecResult,
        GblEfiFastbootMessageType, GblEfiFastbootProtocol, GetVarAllCallback,
        GBL_EFI_FASTBOOT_SERIAL_NUMBER_MAX_LEN_UTF8,
    },
    protocol::{
        check_required_params, slice_from_raw_parts, slice_from_raw_parts_mut, BridgeToRust,
        Provider,
    },
    status::{EfiError, EfiResult},
    Identified,
};

/// Protocol Rust API for `GBL_EFI_FASTBOOT_PROTOCOL`.
pub trait GblEfiFastboot {
    /// Returns the protocol revision that the implementation is providing.
    fn revision(&self) -> u64;

    /// Returns the serial number.
    fn serial_number(&self) -> EfiResult<&str>;

    /// Implementation of `GBL_EFI_FASTBOOT_PROTOCOL.GetVar`.
    fn get_var<'a>(
        &self,
        args: impl Iterator<Item = &'a str>,
        buffer: &mut [u8],
    ) -> EfiResult<usize>;

    /// Implementation of `GBL_EFI_FASTBOOT_PROTOCOL.GetVarAll`.
    fn get_var_all(&self, cb: &mut dyn FnMut(&[&CStr], &CStr) -> EfiResult<()>) -> EfiResult<()>;

    /// Implementation of `GBL_EFI_FASTBOOT_PROTOCOL.GetStaged`.
    fn get_staged(&self, buffer: &mut [u8]) -> EfiResult<(usize, usize)>;

    /// Implementation of `GBL_EFI_FASTBOOT_PROTOCOL.CommandExec`.
    fn command_exec<'a>(
        &self,
        args: impl Iterator<Item = &'a str>,
        download_buffer: &mut [u8],
        download_buffer_used: usize,
        sender: &mut dyn FnMut(GblEfiFastbootMessageType, &str) -> EfiResult<()>,
    ) -> EfiResult<GblEfiFastbootCommandExecResult>;

    /// Implementation of `GBL_EFI_FASTBOOT_PROTOCOL.GetPartitionType`.
    fn get_partition_type(&self, part_name: &CStr, part_type: &mut [u8]) -> EfiResult<usize>;
}

impl Identified for GblEfiFastbootProtocol {
    const GUID: EfiGuid = EfiGuid::from_u64s(
        crate::defs::GBL_EFI_FASTBOOT_PROTOCOL_GUID_U64_0,
        crate::defs::GBL_EFI_FASTBOOT_PROTOCOL_GUID_U64_1,
    );
}

// SAFETY:
// * our wrapper functions adhere to the protocol spec
unsafe impl<R: GblEfiFastboot> BridgeToRust<R> for GblEfiFastbootProtocol {
    unsafe fn create_bridge(rust_impl: &R) -> Self {
        let mut serial_number = [0; GBL_EFI_FASTBOOT_SERIAL_NUMBER_MAX_LEN_UTF8 as usize];
        if let Ok(sn) = rust_impl.serial_number() {
            let sn_bytes = sn.as_bytes();
            let len = sn_bytes.len().min(serial_number.len() - 1);
            serial_number[..len].copy_from_slice(&sn_bytes[..len]);
        }
        Self {
            revision: rust_impl.revision(),
            serial_number,
            get_var: Some(Provider::<_, R>::get_var),
            get_var_all: Some(Provider::<_, R>::get_var_all),
            get_staged: Some(Provider::<_, R>::get_staged),
            command_exec: Some(Provider::<_, R>::command_exec),
            get_partition_type: Some(Provider::<_, R>::get_partition_type),
        }
    }
}

impl<R: GblEfiFastboot> Provider<'_, GblEfiFastbootProtocol, R> {
    /// Implementation of `GBL_EFI_FASTBOOT_PROTOCOL.GetVar`.
    ///
    /// # Safety
    ///
    /// * Caller must guarantee that `interface` is a valid pointer to a
    ///   `GblEfiFastbootProtocol` struct inside a `Self` struct.
    /// * Caller must guarantee that `args` points to an array of `num_args` C Strings.
    /// * Caller must guarantee that `buffer_size` points to a valid usize parameter.
    /// * Caller must guarantee that `buffer` points to a buffer of at least `buffer_size` bytes.
    unsafe extern "efiapi" fn get_var(
        interface: *mut GblEfiFastbootProtocol,
        num_args: usize,
        args: *const *const u8,
        buffer_size: *mut usize,
        buffer: *mut u8,
    ) -> EfiStatus {
        // SAFETY: By safety contract, `interface` is a valid pointer to a
        // `GblEfiFastbootProtocol` struct inside a `Self` struct. Since it comes as the
        // first field, `interface` is also a valid pointer to the `Self` struct.
        let rust_impl = unsafe { Self::to_rust(interface) };
        (|| {
            // SAFETY: By safety contract, `buffer_size` points to a valid `usize`, and `buffer` is
            // valid for reads and writes of `*buffer_size` bytes that nothing else accesses for the
            // duration of this call. Neither reference outlives the call.
            let (buffer, out_size) = unsafe {
                let out_size = buffer_size.as_mut().ok_or(EfiError::InvalidParameter)?;
                (slice_from_raw_parts_mut(buffer, *out_size)?, out_size)
            };
            // SAFETY: By safety contract, `args` is valid for reads of `num_args` pointers, each to
            // a null-terminated string, none of which are modified for the duration of this call.
            let args = unsafe {
                let ptrs = slice_from_raw_parts(args, num_args)?
                    .iter()
                    .map(|&v| NonNull::new(v as *mut _));
                if ptrs.clone().any(|v| v.is_none()) {
                    return Err(EfiError::InvalidParameter);
                }
                ptrs.map(|v| CStr::from_ptr(v.unwrap().as_ptr()).to_str().unwrap())
            };

            match rust_impl.get_var(args, buffer) {
                rep @ Ok(size) | rep @ Err(EfiError::BufferTooSmall(size)) => {
                    *out_size = size;
                    rep
                }
                v => v,
            }
        })()
        .into()
    }

    /// Implementation of `GBL_EFI_FASTBOOT_PROTOCOL.GetVarAll`.
    ///
    /// # Safety
    ///
    /// * Caller must guarantee that `interface` is a valid pointer to a
    ///   `GblEfiFastbootProtocol` struct inside a `Self` struct.
    /// * Caller must guarantee that `cb` is a valid callback function pointer and `context`
    ///   is a valid context data pointer for the callback.
    unsafe extern "efiapi" fn get_var_all(
        interface: *mut GblEfiFastbootProtocol,
        context: *mut c_void,
        cb: GetVarAllCallback,
    ) -> EfiStatus {
        // SAFETY: By safety contract, `interface` is a valid pointer to a
        // `GblEfiFastbootProtocol` struct inside a `Self` struct. Since it comes as the
        // first field, `interface` is also a valid pointer to the `Self` struct.
        let rust_impl = unsafe { Self::to_rust(interface) };
        (|| {
            let cb = cb.ok_or(EfiError::InvalidParameter)?;
            rust_impl.get_var_all(&mut |args, val| {
                let c_args: Vec<*const u8> = args.iter().map(|s| s.as_ptr() as *const u8).collect();
                // SAFETY: `cb` is a valid callback pointer by contract and context is a matching
                // context data pointer.
                unsafe {
                    cb(context, c_args.len(), c_args.as_ptr() as _, val.as_ptr() as _);
                }
                Ok(())
            })
        })()
        .into()
    }

    /// Implementation of `GBL_EFI_FASTBOOT_PROTOCOL.GetStaged`.
    ///
    /// # Safety
    ///
    /// * Caller must guarantee that `interface` is a valid pointer to a
    ///   `GblEfiFastbootProtocol` struct inside a `Self` struct.
    /// * Caller must guarantee that `buffer_size` points to a valid usize parameter.
    /// * Caller must guarantee that `buffer_remains` points to a valid usize parameter.
    /// * Caller must guarantee that `buffer` points to a buffer of at least `buffer_size` bytes.
    unsafe extern "efiapi" fn get_staged(
        interface: *mut GblEfiFastbootProtocol,
        buffer_size: *mut usize,
        buffer_remains: *mut usize,
        buffer: *mut u8,
    ) -> EfiStatus {
        // SAFETY: By safety contract, `interface` is a valid pointer to a
        // `GblEfiFastbootProtocol` struct inside a `Self` struct. Since it comes as the
        // first field, `interface` is also a valid pointer to the `Self` struct.
        let rust_impl = unsafe { Self::to_rust(interface) };
        (|| {
            // SAFETY: By safety contract, `buffer_size` and `buffer_remains` point to valid
            // `usize`s, and `buffer` is valid for reads and writes of `*buffer_size` bytes that
            // nothing else accesses for the duration of this call. None of the references outlive
            // the call. Read `*out_size` through `out_size` rather than `buffer_size` so
            // `out_size`'s Stacked Borrows `Unique` tag is not invalidated.
            let (out_size, buffer_remains, buffer) = unsafe {
                let out_size = buffer_size.as_mut().ok_or(EfiError::InvalidParameter)?;
                let buffer_remains = buffer_remains.as_mut().ok_or(EfiError::InvalidParameter)?;
                let buf = slice_from_raw_parts_mut(buffer, *out_size)?;
                (out_size, buffer_remains, buf)
            };
            let (written, remains) = rust_impl.get_staged(buffer)?;
            *out_size = written;
            *buffer_remains = remains;
            Ok(())
        })()
        .into()
    }

    /// Implementation of `GBL_EFI_FASTBOOT_PROTOCOL.CommandExec`.
    ///
    /// # Safety
    ///
    /// * Caller must guarantee that `interface` is a valid pointer to a
    ///   `GblEfiFastbootProtocol` struct inside a `Self` struct.
    /// * Caller must guarantee that `args` points to an array of `num_args` C strings.
    /// * Caller must guarantee that `download_buffer` points to a buffer of at least
    ///   `download_buffer_size` bytes.
    /// * Caller must guarantee that `implementation` points to a valid
    ///   GblEfiFastbootCommandExecResult.
    /// * Caller must guarantee that `sender` is a valid message sender callback and `context`
    ///   is a valid context data pointer for the callback.
    unsafe extern "efiapi" fn command_exec(
        interface: *mut GblEfiFastbootProtocol,
        num_args: usize,
        args: *const *const u8,
        download_buffer_size: usize,
        download_buffer_used_size: usize,
        download_buffer: *mut u8,
        implementation: *mut GblEfiFastbootCommandExecResult,
        sender: FastbootMessageSender,
        context: *mut c_void,
    ) -> EfiStatus {
        // SAFETY: By safety contract, `interface` is a valid pointer to a
        // `GblEfiFastbootProtocol` struct inside a `Self` struct. Since it comes as the
        // first field, `interface` is also a valid pointer to the `Self` struct.
        let rust_impl = unsafe { Self::to_rust(interface) };
        (|| {
            check_required_params(&[&implementation])?;
            // SAFETY: By safety contract, `args` is valid for reads of `num_args` pointers, each to
            // a null-terminated string, none of which are modified for the duration of this call.
            let args = unsafe {
                let ptrs = slice_from_raw_parts(args, num_args)?
                    .iter()
                    .map(|&v| NonNull::new(v as *mut _));
                if ptrs.clone().any(|v| v.is_none()) {
                    return Err(EfiError::InvalidParameter);
                }
                ptrs.map(|v| CStr::from_ptr(v.unwrap().as_ptr()).to_str().unwrap())
            };
            // SAFETY: By safety contract, `download_buffer` is valid for reads and writes of
            // `download_buffer_size` bytes that nothing else accesses for the duration of this
            // call, and the slice does not outlive the call.
            let download_buffer =
                unsafe { slice_from_raw_parts_mut(download_buffer, download_buffer_size)? };

            let sender_cb = sender.ok_or(EfiError::InvalidParameter)?;
            let exec_res = rust_impl.command_exec(
                args,
                download_buffer,
                download_buffer_used_size,
                &mut |msg_type, msg| {
                    let msg_bytes = msg.as_bytes();
                    // SAFETY: By safety contract, `sender_cb` is a valid callback pointer and
                    // `context` is a valid context data pointer for the callback.
                    let status = unsafe {
                        sender_cb(context, msg_type, msg_bytes.len(), msg_bytes.as_ptr() as _)
                    };
                    EfiResult::from(status)
                },
            )?;
            // SAFETY: `implementation` was checked non-null and aligned above, and by safety
            // contract is valid for writes.
            unsafe { implementation.write(exec_res) };
            Ok(())
        })()
        .into()
    }

    /// Implementation of `GBL_EFI_FASTBOOT_PROTOCOL.GetPartitionType`.
    ///
    /// # Safety
    ///
    /// * Caller must guarantee that `interface` is a valid pointer to a
    ///   `GblEfiFastbootProtocol` struct inside a `Self` struct.
    /// * Caller must guarantee that `part_name` points to a valid null-terminated C string.
    /// * Caller must guarantee that `part_type_len` points to a valid usize parameter.
    /// * Caller must guarantee that `part_type` points to a buffer of at least `part_type_len`
    ///   bytes.
    unsafe extern "efiapi" fn get_partition_type(
        interface: *mut GblEfiFastbootProtocol,
        part_name: *const u8,
        part_type_len: *mut usize,
        part_type: *mut u8,
    ) -> EfiStatus {
        // SAFETY: By safety contract, `interface` is a valid pointer to a
        // `GblEfiFastbootProtocol` struct inside a `Self` struct. Since it comes as the
        // first field, `interface` is also a valid pointer to the `Self` struct.
        let rust_impl = unsafe { Self::to_rust(interface) };
        (|| {
            check_required_params(&[&part_name])?;
            // SAFETY: By safety contract, `part_name` points to a valid null-terminated C string.
            let part_name = unsafe { CStr::from_ptr(part_name as *const _) };
            // SAFETY: By safety contract, `part_type_len` points to a valid `usize`, and
            // `part_type` is valid for reads and writes of `*part_type_len` bytes that nothing
            // else accesses for the duration of this call. Neither reference outlives the call.
            let (part_type_buf, out_len) = unsafe {
                let out_len = part_type_len.as_mut().ok_or(EfiError::InvalidParameter)?;
                (slice_from_raw_parts_mut(part_type, *out_len)?, out_len)
            };
            match rust_impl.get_partition_type(part_name, part_type_buf) {
                rep @ Ok(size) | rep @ Err(EfiError::BufferTooSmall(size)) => {
                    *out_len = size;
                    rep
                }
                v => v,
            }
        })()
        .into()
    }
}
