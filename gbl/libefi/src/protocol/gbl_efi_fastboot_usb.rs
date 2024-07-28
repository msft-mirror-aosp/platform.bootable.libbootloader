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

//! Rust wrapper for `GBL_EFI_FASTBOOT_USB_PROTOCOL`.

use crate::{
    defs::{
        EfiGuid, GblEfiFastbootUsbProtocol, EFI_STATUS_NOT_FOUND, EFI_STATUS_NOT_READY,
        EFI_STATUS_TIMEOUT,
    },
    protocol::{Protocol, ProtocolInfo},
    utils::with_timeout,
    {efi_call, map_efi_err, EfiResult, Event},
};
use gbl_async::yield_now;

/// GBL_EFI_FASTBOOT_USB_PROTOCOL
pub struct GblFastbootUsbProtocol;

impl ProtocolInfo for GblFastbootUsbProtocol {
    type InterfaceType = GblEfiFastbootUsbProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0x6281a893, 0xac23, 0x4ca7, [0xb2, 0x81, 0x34, 0x0e, 0xf8, 0x16, 0x89, 0x55]);
}

// Protocol interface wrappers.
impl Protocol<'_, GblFastbootUsbProtocol> {
    /// Wrapper of `GBL_EFI_FASTBOOT_USB_PROTOCOL.fastboot_usb_interface_start()`
    pub fn fastboot_usb_interface_start(&self) -> EfiResult<usize> {
        let mut max_packet_size = 0;
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` and `max_packet_size` are input/output parameters, outlive the call and
        // will not be retained.
        unsafe {
            efi_call!(
                self.interface()?.fastboot_usb_interface_start,
                self.interface,
                &mut max_packet_size,
            )?;
        }
        Ok(max_packet_size)
    }

    /// Wrapper of `GBL_EFI_FASTBOOT_USB_PROTOCOL.fastboot_usb_interface_stop()`
    pub fn fastboot_usb_interface_stop(&self) -> EfiResult<()> {
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is input parameter, outlives the call, and will not be retained.
        unsafe { efi_call!(self.interface()?.fastboot_usb_interface_stop, self.interface,) }
    }

    /// Wrapper of `GBL_EFI_FASTBOOT_USB_PROTOCOL.fastboot_usb_receive()`
    pub fn fastboot_usb_receive(&self, out: &mut [u8], out_size: &mut usize) -> EfiResult<()> {
        *out_size = out.len();
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface`, `out_size` and `buffer` are input/output parameters, outlive the call
        // and will not be retained.
        unsafe {
            efi_call!(
                self.interface()?.fastboot_usb_receive,
                self.interface,
                out_size,
                out.as_mut_ptr() as _,
            )
        }
    }

    /// Wrapper of `GBL_EFI_FASTBOOT_USB_PROTOCOL.fastboot_usb_send()`
    pub fn fastboot_usb_send(&self, data: &[u8], out_size: &mut usize) -> EfiResult<()> {
        *out_size = data.len();
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface`, `out_size` and `buffer` are input/output parameters, outlive the call
        // and will not be retained.
        unsafe {
            efi_call!(
                self.interface()?.fastboot_usb_send,
                self.interface,
                out_size,
                data.as_ptr() as _,
            )
        }
    }

    /// Returns the `GBL_EFI_FASTBOOT_USB_PROTOCOL.wait_for_send_completion` EFI event.
    pub fn wait_for_send_completion(&self) -> EfiResult<Event> {
        Ok(Event::new_unowned(self.interface()?.wait_for_send_completion))
    }

    /// Receives the next packet from the USB.
    pub async fn receive_packet(&self, out: &mut [u8]) -> EfiResult<usize> {
        loop {
            let mut out_size = 0;
            match self.fastboot_usb_receive(out, &mut out_size) {
                Ok(()) => return Ok(out_size),
                Err(e) if e.is_efi_err(EFI_STATUS_NOT_READY) => yield_now().await,
                Err(e) => return Err(e),
            }
        }
    }

    /// A helper to wait for the send event to signal.
    async fn wait_send(&self) -> EfiResult<()> {
        let bs = self.efi_entry().system_table().boot_services();
        while !bs.check_event(&self.wait_for_send_completion()?)? {
            yield_now().await;
        }
        Ok(())
    }

    /// Sends a packet over the USB.
    pub async fn send_packet(&self, data: &[u8], timeout_ms: u64) -> EfiResult<()> {
        let mut out_size = 0;
        self.fastboot_usb_send(data, &mut out_size)?;
        match with_timeout(self.efi_entry(), self.wait_send(), timeout_ms).await? {
            None => Err(EFI_STATUS_TIMEOUT.into()),
            Some(_) => Ok(()),
        }
    }
}
