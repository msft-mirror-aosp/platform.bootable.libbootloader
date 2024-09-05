// Copyright 2023, The Android Open Source Project
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

//! EFI protocol wrappers to provide Rust-safe APIs for usage.

use core::ptr::null_mut;

use crate::{DeviceHandle, EfiEntry};
use efi_types::*;

pub mod block_io;
pub mod block_io2;
pub mod device_path;
pub mod gbl_efi_ab_slot;
pub mod gbl_efi_fastboot;
pub mod gbl_efi_fastboot_usb;
pub mod gbl_efi_os_configuration;
pub mod image_loading;
pub mod loaded_image;
pub mod riscv;
pub mod simple_network;
pub mod simple_text_input;
pub mod simple_text_output;

use liberror::{Error, Result};

/// ProtocolInfo provides GUID info and the EFI data structure type for a protocol.
pub trait ProtocolInfo {
    /// Data structure type of the interface.
    type InterfaceType;
    /// GUID of the protocol.
    const GUID: EfiGuid;
}

/// A generic type for representing an EFI protcol.
pub struct Protocol<'a, T: ProtocolInfo> {
    // The handle to the device offering the protocol. It's needed for closing the protocol.
    device: DeviceHandle,
    // The interface protocol itself.
    interface: *mut T::InterfaceType,
    // The `EfiEntry` data
    efi_entry: &'a EfiEntry,
}

/// A base implementation for Protocol<T>.
/// Protocol<T> will have additional implementation based on type `T`.
impl<'a, T: ProtocolInfo> Protocol<'a, T> {
    /// Create a new instance with the given device handle, interface pointer and `EfiEntry` data.
    ///
    /// # Safety
    ///
    /// Caller needs to ensure that
    ///
    /// * `interface` points to a valid object of type T::InterfaceType.
    ///
    /// * Object pointed to by `interface` must live as long as the create `Protocol` or 'a.
    pub(crate) unsafe fn new(
        device: DeviceHandle,
        interface: *mut T::InterfaceType,
        efi_entry: &'a EfiEntry,
    ) -> Self {
        Self { device, interface, efi_entry }
    }

    /// Returns the EFI data structure for the protocol interface.
    pub fn interface(&self) -> Result<&T::InterfaceType> {
        // SAFETY: EFI protocol interface data structure.
        unsafe { self.interface.as_ref() }.ok_or(Error::InvalidInput)
    }

    /// Returns the reference to EFI entry.
    pub fn efi_entry(&self) -> &'a EfiEntry {
        self.efi_entry
    }

    /// Returns the mutable pointer of the interface. Invisible from outside. Application should
    /// not have any need to alter the content of interface data.
    pub(crate) fn interface_ptr(&self) -> *mut T::InterfaceType {
        self.interface
    }
}

impl<T: ProtocolInfo> Drop for Protocol<'_, T> {
    fn drop(&mut self) {
        // If the device handle is not specified when creating the Protocol<T>, treat the
        // handle as a static permanent reference and don't close it. An example is
        // `EFI_SYSTEM_TABLE.ConOut`.
        if self.device.0 != null_mut() {
            // Currently we open all protocols using flags BY_HANDLE_PROTOCOL. The flag allows a
            // protocol to be opened for multiple copies, which is needed if a UEFI protocol
            // implementation also require access for other protocols. But if any one of them is
            // closed, all other opened copies will be affected. Therefore for now we don't close
            // the protocol on drop. In the future when we start using other flags such as
            // EXCLUSIVE, we should perform protocol close based on the open flags.

            // self.efi_entry.system_table().boot_services().close_protocol::<T>(self.device).unwrap();
        }
    }
}

/// Macro to perform an EFI protocol function call.
///
/// In the first variant, the first argument is the function pointer,
/// and the following arguments are passed through as protocol args.
///
/// With our [Protocol] struct, usage generally looks something like:
///
/// ```
/// efi_call!(
///   self.interface()?.protocol_function_name,
///   self.interface,
///   arg1,
///   arg2,
///   ...
/// )
/// ```
/// Most efi_call! invocations should use the first variant.
///
/// With the second variant, the first argument is an expression that references
/// a buffer in-out size parameter.
/// This is part of a pattern used by some protocol methods
/// that take an output buffer and an in-out buffer size:
/// if the method returns EFI_STATUS_BUFFER_TOO_SMALL,
/// the size is mutated to contain the minimum required buffer size.
/// The caller can then allocate a larger buffer and reattempt the method call.
///
/// Usage generally looks something like:
/// ```
/// efi_call!(
///   @bufsize arg2,
///   self.interface()?.protocol_function_name,
///   self.interface,
///   arg1,
///   &mut arg2,
///   ...
/// )
/// ```
#[macro_export]
macro_rules! efi_call {
    ( $method:expr, $($x:expr),*$(,)? ) => {
        {
            use liberror::{Error, Result, efi_status_to_result};
            let res: Result<()> = match $method {
                None => Err(Error::NotFound),
                Some(f) => efi_status_to_result(f($($x,)*)),
            };
            res
        }
    };
    ( @bufsize $size:expr, $method:expr, $($x:expr),*$(,)? ) => {
        {
            use liberror::{Error, Result, efi_status_to_result};
            use efi_types::EFI_STATUS_BUFFER_TOO_SMALL;
            let res: Result<()> = match $method {
                None => Err(Error::NotFound),
                Some(f) => {
                    match f($($x,)*) {
                        EFI_STATUS_BUFFER_TOO_SMALL => Err(Error::BufferTooSmall(Some($size))),
                        r => efi_status_to_result(r),
                    }
                },
            };
            res
        }
    };
}

// Following are protocol specific implementations for Protocol<T>.
// TODO(300168989): Consdier splitting each protocol into separate file as we add more protocols.

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::*;

    #[test]
    fn test_dont_close_protocol_without_device_handle() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let mut block_io: EfiBlockIoProtocol = Default::default();
            // SAFETY: `block_io` is a EfiBlockIoProtocol and out lives the created Protocol.
            unsafe {
                Protocol::<block_io::BlockIoProtocol>::new(
                    DeviceHandle(null_mut()),
                    &mut block_io as *mut _,
                    &efi_entry,
                );
            }
            efi_call_traces().with(|traces| {
                assert_eq!(traces.borrow_mut().close_protocol_trace.inputs.len(), 0);
            });
        })
    }
}
