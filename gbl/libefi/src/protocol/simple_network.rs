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

use crate::defs::{
    EfiGuid, EfiMacAddress, EfiSimpleNetworkMode, EfiSimpleNetworkProtocol, EFI_STATUS_NOT_FOUND,
};
use crate::protocol::{Protocol, ProtocolInfo};
use crate::{efi_call, map_efi_err, EfiResult};
use core::ffi::c_void;
use core::ptr::null_mut;

/// EFI_SIMPLE_NETWORK_PROTOCOL
pub struct SimpleNetworkProtocol;

impl ProtocolInfo for SimpleNetworkProtocol {
    type InterfaceType = EfiSimpleNetworkProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0xa19832b9, 0xac25, 0x11d3, [0x9a, 0x2d, 0x00, 0x90, 0x27, 0x3f, 0xc1, 0x4d]);
}

impl<'a> Protocol<'a, SimpleNetworkProtocol> {
    /// Wrapper of `EFI_SIMPLE_NETWORK.Start()`
    pub fn start(&self) -> EfiResult<()> {
        // SAFETY:
        // `self.interface()?` guarantees to return a valid object pointer as established by
        // `Protocol::new()`.
        // `self.interface` outlives the call and will not be retained.
        unsafe { efi_call!(self.interface()?.start, self.interface) }
    }

    /// Wrapper of `EFI_SIMPLE_NETWORK.Stop()`
    pub fn stop(&self) -> EfiResult<()> {
        // SAFETY: See safety reasoning of `start()`.
        unsafe { efi_call!(self.interface()?.stop, self.interface) }
    }

    /// Wrapper of `EFI_SIMPLE_NETWORK.Initialize()`
    pub fn initialize(&self, extra_rx_buf_size: usize, extra_tx_buf_size: usize) -> EfiResult<()> {
        // SAFETY: See safety reasoning of `start()`.
        unsafe {
            efi_call!(
                self.interface()?.initialize,
                self.interface,
                extra_rx_buf_size,
                extra_tx_buf_size
            )
        }
    }

    /// Wrapper of `EFI_SIMPLE_NETWORK.Reset()`
    pub fn reset(&self, extended_verification: bool) -> EfiResult<()> {
        // SAFETY: See safety reasoning of `start()`.
        unsafe { efi_call!(self.interface()?.reset, self.interface, extended_verification) }
    }

    /// Wrapper of `EFI_SIMPLE_NETWORK.Shutdown()`
    pub fn shutdown(&self) -> EfiResult<()> {
        // SAFETY: See safety reasoning of `start()`.
        unsafe { efi_call!(self.interface()?.shutdown, self.interface) }
    }

    /// Wrapper of `EFI_SIMPLE_NETWORK.GetStatus()`
    pub fn get_status(
        &self,
        interrupt_status: Option<&mut u32>,
        recycle_buffer: Option<&mut *mut c_void>,
    ) -> EfiResult<()> {
        // SAFETY:
        // See safety reasoning of `start()`.
        // Pointers to `interrupt_status`, `recycled_buffer` are valid during the call and for
        // writing output values only.
        unsafe {
            efi_call!(
                self.interface()?.get_status,
                self.interface,
                option_ref_mut_to_pointer(interrupt_status),
                option_ref_mut_to_pointer(recycle_buffer)
            )?;
        }
        Ok(())
    }

    /// Wrapper of `EFI_SIMPLE_NETWORK.Transmit()`
    ///
    /// # Safety
    ///
    /// * `buf` needs to be a valid buffer.
    /// * There should not be any existing references to memory pointed by `buf`.
    /// * Because `buf` is internally retained by the network. `buf` should remain valid and not
    ///   dereferenced until either 1) the buffer address re-appears in `recycled_buffer` from
    ///   `Self::get_status()` or 2) Self::Shutdown() is called and returns either Ok(()) or
    ///   EFI_STATUS_NOT_STARTED.
    pub unsafe fn transmit(
        &self,
        header_size: usize,
        buf: *mut [u8],
        mut src: EfiMacAddress,
        mut dest: EfiMacAddress,
        mut protocol: u16,
    ) -> EfiResult<()> {
        let buf = buf.as_mut().unwrap();
        // SAFETY:
        // See safety reasoning of `start()`.
        // All pointers passed are valid, outlive the call and are not retained by the call.
        unsafe {
            efi_call!(
                self.interface()?.transmit,
                self.interface,
                header_size,
                buf.len(),
                buf.as_mut_ptr() as *mut _,
                &mut src,
                &mut dest,
                &mut protocol
            )
        }
    }

    /// Wrapper of `EFI_SIMPLE_NETWORK.Receive()`.
    pub fn receive(
        &self,
        header_size: Option<&mut usize>,
        buf_size: Option<&mut usize>,
        buf: &mut [u8],
        src: Option<&mut EfiMacAddress>,
        dest: Option<&mut EfiMacAddress>,
        protocol: Option<&mut u16>,
    ) -> EfiResult<()> {
        // SAFETY:
        // See safety reasoning of `start()`.
        // All pointers passed are valid, outlive the call and are not retained by the call.
        unsafe {
            efi_call!(
                self.interface()?.receive,
                self.interface,
                option_ref_mut_to_pointer(header_size),
                option_ref_mut_to_pointer(buf_size),
                buf.as_mut_ptr() as *mut _,
                option_ref_mut_to_pointer(src),
                option_ref_mut_to_pointer(dest),
                option_ref_mut_to_pointer(protocol)
            )?;
        }
        Ok(())
    }

    /// Returns `EFI_SIMPLE_NETWORK.Mode` structure
    pub fn mode(&self) -> EfiResult<EfiSimpleNetworkMode> {
        // SAFETY: Non-null pointer from UEFI interface points to valid object.
        unsafe { self.interface()?.mode.as_ref() }.ok_or(EFI_STATUS_NOT_FOUND.into()).copied()
    }
}

/// A helper to convert an `Option<&mut T>` to `*mut T`. None maps to NULL.
fn option_ref_mut_to_pointer<T>(option: Option<&mut T>) -> *mut T {
    option.map(|t| t as *mut _).unwrap_or(null_mut())
}
