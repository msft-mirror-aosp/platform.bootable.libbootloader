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
//! [`GBL_EFI_FASTBOOT_TRANSPORT_PROTOCOL`](https://android.googlesource.com/platform/bootable/libbootloader/+/refs/heads/gbl-mainline/gbl/docs/gbl_efi_fastboot_transport_protocol.md).

use core::ffi::{c_void, CStr};

use crate::{
    defs::{EfiGuid, EfiStatus, GblEfiFastbootRxMode, GblEfiFastbootTransportProtocol},
    protocol::{slice_from_raw_parts, slice_from_raw_parts_mut, BridgeToRust, Provider},
    status::{EfiError, EfiResult},
    Identified,
};

/// Protocol Rust API for `GBL_EFI_FASTBOOT_TRANSPORT_PROTOCOL`.
pub trait GblEfiFastbootTransport {
    /// Returns the protocol revision that the implementation is providing.
    fn revision(&self) -> u64;

    /// Returns a description of the fastboot transport.
    fn description(&self) -> &'static CStr;

    /// Starts the transport channel.
    fn start(&self) -> EfiResult<()>;

    /// Stops the transport interface.
    fn stop(&self) -> EfiResult<()>;

    /// Receives data from the transport channel.
    fn receive(&self, buffer: &mut [u8], mode: GblEfiFastbootRxMode) -> EfiResult<usize>;

    /// Sends data to the transport channel.
    fn send(&self, buffer: &[u8]) -> EfiResult<usize>;

    /// Waits until all pending TX transfers are completed.
    fn flush(&self) -> EfiResult<()>;
}

impl Identified for GblEfiFastbootTransportProtocol {
    const GUID: EfiGuid = EfiGuid::from_u64s(
        crate::defs::GBL_EFI_FASTBOOT_TRANSPORT_PROTOCOL_GUID_U64_0,
        crate::defs::GBL_EFI_FASTBOOT_TRANSPORT_PROTOCOL_GUID_U64_1,
    );
}

// SAFETY:
// * our wrapper functions adhere to the protocol spec
unsafe impl<R: GblEfiFastbootTransport> BridgeToRust<R> for GblEfiFastbootTransportProtocol {
    unsafe fn create_bridge(rust_impl: &R) -> Self {
        Self {
            revision: rust_impl.revision(),
            description: rust_impl.description().as_ptr() as _,
            start: Some(Provider::<_, R>::start),
            stop: Some(Provider::<_, R>::stop),
            receive: Some(Provider::<_, R>::receive),
            send: Some(Provider::<_, R>::send),
            flush: Some(Provider::<_, R>::flush),
        }
    }
}

impl<R: GblEfiFastbootTransport> Provider<'_, GblEfiFastbootTransportProtocol, R> {
    /// Implementation of `GBL_EFI_FASTBOOT_TRANSPORT_PROTOCOL.Start`.
    ///
    /// # Safety
    ///
    /// * Caller must guarantee that `interface` is a valid pointer to a
    ///   `GblEfiFastbootTransportProtocol` struct inside a `Self` struct.
    unsafe extern "efiapi" fn start(interface: *mut GblEfiFastbootTransportProtocol) -> EfiStatus {
        // SAFETY: By safety contract, `interface` is a valid pointer to a
        // `GblEfiFastbootTransportProtocol` struct inside a `Self` struct. Since it comes as the
        // first field, `interface` is also a valid pointer to the `Self` struct.
        let rust_impl = unsafe { Self::to_rust(interface) };
        rust_impl.start().into()
    }

    /// Implementation of `GBL_EFI_FASTBOOT_TRANSPORT_PROTOCOL.Stop`.
    ///
    /// # Safety
    ///
    /// * Caller must guarantee that `interface` is a valid pointer to a
    ///   `GblEfiFastbootTransportProtocol` struct inside a `Self` struct.
    unsafe extern "efiapi" fn stop(interface: *mut GblEfiFastbootTransportProtocol) -> EfiStatus {
        // SAFETY: By safety contract, `interface` is a valid pointer to a
        // `GblEfiFastbootTransportProtocol` struct inside a `Self` struct. Since it comes as the
        // first field, `interface` is also a valid pointer to the `Self` struct.
        let rust_impl = unsafe { Self::to_rust(interface) };
        rust_impl.stop().into()
    }

    /// Implementation of `GBL_EFI_FASTBOOT_TRANSPORT_PROTOCOL.Receive`.
    ///
    /// # Safety
    ///
    /// * Caller must guarantee that `interface` is a valid pointer to a
    ///   `GblEfiFastbootTransportProtocol` struct inside a `Self` struct.
    /// * Caller must guarantee that `buffer_size` points to a valid usize parameter.
    /// * Caller must guarantee that `buffer` points to a buffer of at least `buffer_size` bytes.
    unsafe extern "efiapi" fn receive(
        interface: *mut GblEfiFastbootTransportProtocol,
        buffer_size: *mut usize,
        buffer: *mut c_void,
        mode: GblEfiFastbootRxMode,
    ) -> EfiStatus {
        // SAFETY: By safety contract, `interface` is a valid pointer to a
        // `GblEfiFastbootTransportProtocol` struct inside a `Self` struct. Since it comes as the
        // first field, `interface` is also a valid pointer to the `Self` struct.
        let rust_impl = unsafe { Self::to_rust(interface) };
        (|| {
            // SAFETY: By safety contract, `buffer_size` points to a valid `usize`, and `buffer` is
            // valid for reads and writes of `*buffer_size` bytes that nothing else accesses for the
            // duration of this call. Neither reference outlives the call. Casting `buffer` rather
            // than going through `&mut c_void` keeps provenance over the whole buffer.
            let (buffer, buffer_size) = unsafe {
                let buffer_size = buffer_size.as_mut().ok_or(EfiError::InvalidParameter)?;
                (slice_from_raw_parts_mut(buffer.cast::<u8>(), *buffer_size)?, buffer_size)
            };
            match rust_impl.receive(buffer, mode) {
                rep @ Ok(v) | rep @ Err(EfiError::BufferTooSmall(v)) => {
                    *buffer_size = v;
                    rep
                }
                v => v,
            }
        })()
        .into()
    }

    /// Implementation of `GBL_EFI_FASTBOOT_TRANSPORT_PROTOCOL.Send`.
    ///
    /// # Safety
    ///
    /// * Caller must guarantee that `interface` is a valid pointer to a
    ///   `GblEfiFastbootTransportProtocol` struct inside a `Self` struct.
    /// * Caller must guarantee that `buffer_size` points to a valid usize parameter.
    /// * Caller must guarantee that `buffer` points to a buffer of at least `buffer_size` bytes.
    unsafe extern "efiapi" fn send(
        interface: *mut GblEfiFastbootTransportProtocol,
        buffer_size: *mut usize,
        buffer: *const c_void,
    ) -> EfiStatus {
        // SAFETY: By safety contract, `interface` is a valid pointer to a
        // `GblEfiFastbootTransportProtocol` struct inside a `Self` struct. Since it comes as the
        // first field, `interface` is also a valid pointer to the `Self` struct.
        let rust_impl = unsafe { Self::to_rust(interface) };
        (|| {
            // SAFETY: By safety contract, `buffer_size` points to a valid `usize`, and `buffer` is
            // valid for reads of `*buffer_size` initialized bytes that are not modified for the
            // duration of this call. Neither reference outlives the call. Casting `buffer` rather
            // than going through `&c_void` keeps provenance over the whole buffer.
            let (buffer, buffer_size) = unsafe {
                let buffer_size = buffer_size.as_mut().ok_or(EfiError::InvalidParameter)?;
                (slice_from_raw_parts(buffer.cast::<u8>(), *buffer_size)?, buffer_size)
            };
            rust_impl.send(buffer).inspect(|size| *buffer_size = *size)
        })()
        .into()
    }

    /// Implementation of `GBL_EFI_FASTBOOT_TRANSPORT_PROTOCOL.Flush`.
    ///
    /// # Safety
    ///
    /// * Caller must guarantee that `interface` is a valid pointer to a
    ///   `GblEfiFastbootTransportProtocol` struct inside a `Self` struct.
    unsafe extern "efiapi" fn flush(interface: *mut GblEfiFastbootTransportProtocol) -> EfiStatus {
        // SAFETY: By safety contract, `interface` is a valid pointer to a
        // `GblEfiFastbootTransportProtocol` struct inside a `Self` struct. Since it comes as the
        // first field, `interface` is also a valid pointer to the `Self` struct.
        let rust_impl = unsafe { Self::to_rust(interface) };
        rust_impl.flush().into()
    }
}
