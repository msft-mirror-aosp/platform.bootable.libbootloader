// Copyright 2025, The Android Open Source Project
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

//! Rust wrapper for `EFI_ERASE_BLOCK_PROTOCOL`.

use crate::{
    efi_call, efi_println,
    protocol::{block_io2::wait_completion, Protocol, ProtocolInfo},
    versioned_protocol, EventNotify, EventType, Tpl,
};
use core::sync::atomic::{AtomicBool, Ordering};
use efi_types::{
    EfiEraseBlockProtocol, EfiEraseBlockToken, EfiGuid, EFI_ERASE_BLOCK_PROTOCOL_GUID_U64_0,
    EFI_ERASE_BLOCK_PROTOCOL_GUID_U64_1, EFI_ERASE_BLOCK_PROTOCOL_REVISION, EFI_STATUS_NOT_READY,
};
use gbl_async::assert_return;
use liberror::{efi_status_to_result, Result};

versioned_protocol!(EraseBlockProtocol, EFI_ERASE_BLOCK_PROTOCOL_REVISION);

/// EFI_ERASE_BLOCK_PROTOCOL
pub struct EraseBlockProtocol;

impl ProtocolInfo for EraseBlockProtocol {
    type InterfaceType = EfiEraseBlockProtocol;

    const GUID: EfiGuid = EfiGuid::from_u64s(
        EFI_ERASE_BLOCK_PROTOCOL_GUID_U64_0,
        EFI_ERASE_BLOCK_PROTOCOL_GUID_U64_1,
    );
}

// Protocol interface wrappers.
impl Protocol<'_, EraseBlockProtocol> {
    /// Returns `EFI_ERASE_BLOCK_PROTOCOL.erase_length_granularity`
    pub fn erase_length_granularity(&self) -> u32 {
        self.interface().erase_length_granularity
    }

    /// Wrapper of `EFI_ERASE_BLOCK_PROTOCOL.erase_blocks`
    pub async fn erase_blocks(&self, media_id: u32, lba: u64, size: usize) -> Result<()> {
        if let Err(e) = self.erase_blocks_nonblocking(media_id, lba, size).await {
            // The UEFI spec is unclear about what error should be returned if the protocol did not
            // support non-blocking mode, so just retry if any error is encountered.
            efi_println!(
                self.efi_entry(),
                "Nonblocking erase_blocks failed with: {e}\nRetry with blocking mode."
            );
            self.erase_blocks_blocking(media_id, lba, size)
        } else {
            Ok(())
        }
    }

    fn erase_blocks_blocking(&self, media_id: u32, lba: u64, size: usize) -> Result<()> {
        // SAFETY:
        // * `self.interface_ptr()` points to a valid object established by `Protocol::new()`.
        // * `self.interface_ptr()` is an input parameter and will not be retained.
        //   It outlives the call.
        // * Blocking I/O is performed if `event` is NULL, so `token` are not being retained by the
        //   UEFI firmware.
        unsafe {
            efi_call!(
                self.interface().erase_blocks,
                self.interface_ptr(),
                media_id,
                lba,
                &mut EfiEraseBlockToken {
                    event: core::ptr::null_mut(),
                    transaction_status: EFI_STATUS_NOT_READY,
                },
                size
            )
        }
    }

    async fn erase_blocks_nonblocking(&self, media_id: u32, lba: u64, size: usize) -> Result<()> {
        let bs = self.efi_entry().system_table().boot_services();
        let complete = AtomicBool::new(false);
        let mut notify_fn = &mut |_| complete.store(true, Ordering::Release);
        let mut notify = EventNotify::new(Tpl::Callback, &mut notify_fn);
        // SAFETY: the notification callback never allocates, deallocates, or panics.
        let event =
            unsafe { bs.create_event_with_notification(EventType::NotifySignal, &mut notify) }?;
        let mut token =
            EfiEraseBlockToken { event: event.efi_event, transaction_status: EFI_STATUS_NOT_READY };
        // SAFETY:
        // * `self.interface_ptr()` points to a valid object established by `Protocol::new()`.
        // * `self.interface_ptr()` is an input parameter and will not be retained.
        //   It outlives the call.
        // * The function waits until `complete` is marked true by the event notification function,
        //   which guarantees that `token` are not being retained by the UEFI firmware anymore.
        // * `assert_return` asserts that the wait for `complete = true` must complete. Otherwise
        //   it panics. This makes sure that we don't violate aliasing rule due to the top level
        //   Future getting dropped before it can execute to completion.
        unsafe {
            efi_call!(
                self.interface().erase_blocks,
                self.interface_ptr(),
                media_id,
                lba,
                &mut token,
                size
            )?;
        }
        assert_return(wait_completion(self.efi_entry(), &complete)).await;
        efi_status_to_result(token.transaction_status)
    }
}
