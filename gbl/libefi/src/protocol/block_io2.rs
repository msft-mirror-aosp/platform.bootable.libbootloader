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
    protocol::{Protocol, ProtocolInfo},
    Event, EventNotify, EventType, Tpl,
};
use efi_types::{
    EfiBlockIo2Protocol, EfiBlockIo2Token, EfiBlockIoMedia, EfiGuid, EFI_STATUS_NOT_READY,
};
use gbl_async::{assert_return, yield_now};
use liberror::{efi_status_to_result, Error, Result};

/// EFI_BLOCK_IO2_PROTOCOL
pub struct BlockIo2Protocol;

impl ProtocolInfo for BlockIo2Protocol {
    type InterfaceType = EfiBlockIo2Protocol;

    const GUID: EfiGuid =
        EfiGuid::new(0xa77b2472, 0xe282, 0x4e9f, [0xa2, 0x45, 0xc2, 0xc0, 0xe2, 0x7b, 0xbc, 0xc1]);
}

// Protocol interface wrappers.
impl Protocol<'_, BlockIo2Protocol> {
    /// Syncs a non-blocking operation by waiting for the corresponding EFI event to be signaled.
    async fn wait_io_completion(&self, event: &Event<'_, '_>) -> Result<()> {
        let bs = self.efi_entry().system_table().boot_services();
        loop {
            match bs.check_event(&event) {
                Err(e) => {
                    // If we fail to check event/status, force reset the device to release any
                    // retained user buffer. The reset cannot fail.
                    self.reset(true).unwrap();
                    return Err(e);
                }
                Ok(true) => return Ok(()),
                _ => yield_now().await,
            }
        }
    }

    /// Wraps `EfiBlockIo2Protocol.read_blocks_ex`.
    pub async fn read_blocks_ex(&self, lba: u64, buffer: &mut [u8]) -> Result<()> {
        let bs = self.efi_entry().system_table().boot_services();
        // UEFI spec requires that NOTIFY_WAIT event be always created with a callback.
        let mut notify_fn = &mut |_| ();
        let mut notify = EventNotify::new(Tpl::Callback, &mut notify_fn);
        // SAFETY: the notification callback never allocates, deallocates, or panics.
        let event =
            unsafe { bs.create_event_with_notification(EventType::NotifyWait, &mut notify) }?;
        let mut token =
            EfiBlockIo2Token { event: event.efi_event, transaction_status: EFI_STATUS_NOT_READY };
        // SAFETY:
        // * `self.interface()?` guarantees self.interface is non-null and points to a valid object
        //    established by `Protocol::new()`.
        // * `self.interface` is input parameter and will not be retained. It outlives the call.
        // * `Self::wait_io_completion()` is called immediately after. It makes sure the IO is
        //   either completed successfully or is reset if `check_event` fails. Thus it's
        //   guaranteed that after `Self::wait_io_completion()` returns, `buffer` and `token` are
        //   not being retained by the UEFI firmware anymore.
        // * `assert_return` asserts that `wait_io_completion` returns eventually. Otherwise it
        //   panics if the top level Future gets dropped before it returns.
        unsafe {
            efi_call!(
                self.interface()?.read_blocks_ex,
                self.interface,
                self.media()?.media_id,
                lba,
                &mut token,
                buffer.len(),
                buffer.as_mut_ptr() as _
            )?;
        }
        assert_return(self.wait_io_completion(&event)).await?;
        efi_status_to_result(token.transaction_status)
    }

    /// Wraps `EfiBlockIo2Protocol.write_blocks_ex`.
    pub async fn write_blocks_ex(&self, lba: u64, buffer: &mut [u8]) -> Result<()> {
        let bs = self.efi_entry().system_table().boot_services();
        let mut notify_fn = &mut |_| ();
        let mut notify = EventNotify::new(Tpl::Callback, &mut notify_fn);
        // SAFETY: the notification callback never allocates, deallocates, or panics.
        let event =
            unsafe { bs.create_event_with_notification(EventType::NotifyWait, &mut notify) }?;
        let mut token =
            EfiBlockIo2Token { event: event.efi_event, transaction_status: EFI_STATUS_NOT_READY };
        // SAFETY: See safety comment for `Self::read_blocks_ex()`.
        unsafe {
            efi_call!(
                self.interface()?.write_blocks_ex,
                self.interface,
                self.media()?.media_id,
                lba,
                &mut token,
                buffer.len(),
                buffer.as_mut_ptr() as _
            )?;
        }
        assert_return(self.wait_io_completion(&event)).await?;
        efi_status_to_result(token.transaction_status)
    }

    /// Wraps `EFI_BLOCK_IO2_PROTOCOL.flush_blocks_ex()`
    pub async fn flush_blocks_ex(&self) -> Result<()> {
        let bs = self.efi_entry().system_table().boot_services();
        let mut notify_fn = &mut |_| ();
        let mut notify = EventNotify::new(Tpl::Callback, &mut notify_fn);
        // SAFETY: the notification callback never allocates, deallocates, or panics.
        let event =
            unsafe { bs.create_event_with_notification(EventType::NotifyWait, &mut notify) }?;
        let mut token =
            EfiBlockIo2Token { event: event.efi_event, transaction_status: EFI_STATUS_NOT_READY };
        // SAFETY: See safety comment for `Self::read_blocks_ex()`.
        unsafe { efi_call!(self.interface()?.flush_blocks_ex, self.interface, &mut token) }?;
        assert_return(self.wait_io_completion(&event)).await?;
        efi_status_to_result(token.transaction_status)
    }

    /// Wraps `EFI_BLOCK_IO2_PROTOCOL.reset()`
    pub fn reset(&self, extended_verification: bool) -> Result<()> {
        // SAFETY:
        // * See safety comment for `Self::read_blocks_ex()`.
        // * The operation is synchronous, no need to call wait_io_completion().
        unsafe { efi_call!(self.interface()?.reset, self.interface, extended_verification) }
    }

    /// Gets a copy of the `EFI_BLOCK_IO2_PROTOCOL.Media` structure.
    pub fn media(&self) -> Result<EfiBlockIoMedia> {
        let ptr = self.interface()?.media;
        // SAFETY: Pointers to EFI data structure.
        Ok(*unsafe { ptr.as_ref() }.ok_or(Error::InvalidInput)?)
    }
}
