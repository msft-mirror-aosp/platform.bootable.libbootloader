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

//! Rust wrapper for `EFI_BLOCK_IO2_PROTOCOL`.

use crate::{
    efi_call,
    protocol::{MaybeVersioned, Protocol, ProtocolInfo, Requirement},
    EfiEntry, EventNotify, EventType, Tpl,
};
use bytes::buf::UninitSlice;
use core::{
    ptr::null_mut,
    sync::atomic::{AtomicBool, Ordering},
};
use efi_types::{
    EfiBlockIo2Protocol, EfiBlockIo2Token, EfiBlockIoMedia, EfiGuid,
    EFI_BLOCK_IO2_PROTOCOL_GUID_U64_0, EFI_BLOCK_IO2_PROTOCOL_GUID_U64_1, EFI_STATUS_NOT_READY,
};
use gbl_async::{assert_return, yield_now};
use liberror::{efi_status_to_result, Result};

impl MaybeVersioned for EfiBlockIo2Protocol {}

/// EFI_BLOCK_IO2_PROTOCOL
pub struct BlockIo2Protocol;

impl ProtocolInfo for BlockIo2Protocol {
    type InterfaceType = EfiBlockIo2Protocol;

    const GUID: EfiGuid =
        EfiGuid::from_u64s(EFI_BLOCK_IO2_PROTOCOL_GUID_U64_0, EFI_BLOCK_IO2_PROTOCOL_GUID_U64_1);

    const REQUIREMENT: Requirement = Requirement::Optional;
}

/// Helper for waiting an AtomicBool to become true while regularly calling EFI CheckEvent().
pub(crate) async fn wait_completion(entry: &EfiEntry, complete: &AtomicBool) {
    // Disable tracing when waiting for IO.
    let _guard = trace::TraceGuard::new(false);
    while !complete.load(Ordering::Acquire) {
        let bs = entry.system_table().boot_services();
        // UEFI implementation such as that of u-boot has no real interrupt. It relies on UEFI
        // app regularly calling into UEFI API to have a chance to process timer and other
        // events. Therefore here we make a call to CheckEvent() with a NULL event pointer. For
        // UEFI platforms that do have interrupt, we assume this is a noop with little to no
        // overhead. It should always return EFI_INVALID_PARAMETER according to UEFI spec.
        //
        // SAFETY:
        // * efi_call checks that `check_event` is a valid function pointer before calling.
        // * All parameters are valid and no memory is retained.
        let _ = unsafe { efi_call!(bs.boot_services.check_event, null_mut()) };
        yield_now().await;
    }
}

// Protocol interface wrappers.
impl Protocol<'_, BlockIo2Protocol> {
    /// Wraps `EfiBlockIo2Protocol.read_blocks_ex`.
    pub async fn read_blocks_ex<'a>(
        &self,
        lba: u64,
        buffer: impl Into<&'a mut UninitSlice>,
    ) -> Result<()> {
        let bs = self.efi_entry().system_table().boot_services();
        let complete = AtomicBool::new(false);
        let mut notify_fn = &mut |_| complete.store(true, Ordering::Release);
        let mut notify = EventNotify::new(Tpl::Callback, &mut notify_fn);
        // SAFETY: the notification callback never allocates, deallocates, or panics.
        let event =
            unsafe { bs.create_event_with_notification(EventType::NotifySignal, &mut notify) }?;
        let mut token =
            EfiBlockIo2Token { event: event.efi_event, transaction_status: EFI_STATUS_NOT_READY };
        let buffer = buffer.into();
        // SAFETY:
        // * `self.interface_ptr()` is an input parameter and will not be retained.
        //   It outlives the call.
        // * `EfiBlockIo2Protocol.read_blocks_ex()` will only initialize the data, never reading
        //    or uininitializing it.
        // * The function waits until `complete` is marked true by the event notification function,
        //   which guarantees that `buffer` and `token` are not being retained by the UEFI firmware
        //   anymore.
        // * `assert_return` asserts that the wait for `complete = true` must complete. Otherwise
        //   it panics. This makes sure that we don't violate aliasing rule due to the top level
        //   Future getting dropped before it can execute to completion.
        unsafe {
            efi_call!(
                self.interface().read_blocks_ex,
                self.interface_ptr(),
                self.media().media_id,
                lba,
                &mut token,
                buffer.len(),
                buffer.as_mut_ptr() as _
            )?;
        }
        assert_return(wait_completion(self.efi_entry(), &complete)).await;
        efi_status_to_result(token.transaction_status)
    }

    /// Wraps `EfiBlockIo2Protocol.write_blocks_ex`.
    pub async fn write_blocks_ex(&self, lba: u64, buffer: &mut [u8]) -> Result<()> {
        let bs = self.efi_entry().system_table().boot_services();
        let complete = AtomicBool::new(false);
        let mut notify_fn = &mut |_| complete.store(true, Ordering::Release);
        let mut notify = EventNotify::new(Tpl::Callback, &mut notify_fn);
        // SAFETY: the notification callback never allocates, deallocates, or panics.
        let event =
            unsafe { bs.create_event_with_notification(EventType::NotifySignal, &mut notify) }?;
        let mut token =
            EfiBlockIo2Token { event: event.efi_event, transaction_status: EFI_STATUS_NOT_READY };
        // SAFETY: See safety comment for `Self::read_blocks_ex()`.
        unsafe {
            efi_call!(
                self.interface().write_blocks_ex,
                self.interface_ptr(),
                self.media().media_id,
                lba,
                &mut token,
                buffer.len(),
                buffer.as_mut_ptr() as _
            )?;
        }
        assert_return(wait_completion(self.efi_entry(), &complete)).await;
        efi_status_to_result(token.transaction_status)
    }

    /// Wraps `EFI_BLOCK_IO2_PROTOCOL.flush_blocks_ex()`
    pub async fn flush_blocks_ex(&self) -> Result<()> {
        let bs = self.efi_entry().system_table().boot_services();
        let complete = AtomicBool::new(false);
        let mut notify_fn = &mut |_| complete.store(true, Ordering::Release);
        let mut notify = EventNotify::new(Tpl::Callback, &mut notify_fn);
        // SAFETY: the notification callback never allocates, deallocates, or panics.
        let event =
            unsafe { bs.create_event_with_notification(EventType::NotifySignal, &mut notify) }?;
        let mut token =
            EfiBlockIo2Token { event: event.efi_event, transaction_status: EFI_STATUS_NOT_READY };
        // SAFETY: See safety comment for `Self::read_blocks_ex()`.
        unsafe { efi_call!(self.interface().flush_blocks_ex, self.interface_ptr(), &mut token) }?;
        assert_return(wait_completion(self.efi_entry(), &complete)).await;
        efi_status_to_result(token.transaction_status)
    }

    /// Wraps `EFI_BLOCK_IO2_PROTOCOL.reset()`
    pub fn reset(&self, extended_verification: bool) -> Result<()> {
        // SAFETY:
        // * See safety comment for `Self::read_blocks_ex()`.
        // * The operation is synchronous, no need to call wait_io_completion().
        unsafe { efi_call!(self.interface().reset, self.interface_ptr(), extended_verification) }
    }

    /// Gets a copy of the `EFI_BLOCK_IO2_PROTOCOL.Media` structure.
    pub fn media(&self) -> EfiBlockIoMedia {
        // SAFETY: Pointers to EFI data structure.
        unsafe { *self.interface().media }
    }
}
