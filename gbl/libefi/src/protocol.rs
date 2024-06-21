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

use core::ptr::null_mut;

use crate::defs::*;
use crate::{DeviceHandle, EfiEntry, EfiResult};

pub mod ab_slot;
pub mod android_boot;
pub mod block_io;
pub mod device_path;
pub mod loaded_image;
pub mod riscv;
pub mod simple_network;
pub mod simple_text_input;
pub mod simple_text_output;

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
    pub fn interface(&self) -> EfiResult<&T::InterfaceType> {
        // SAFETY: EFI protocol interface data structure.
        unsafe { self.interface.as_ref() }.ok_or_else(|| EFI_STATUS_INVALID_PARAMETER.into())
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
            self.efi_entry.system_table().boot_services().close_protocol::<T>(self.device).unwrap();
        }
    }
}

impl EfiGuid {
    pub const fn new(data1: u32, data2: u16, data3: u16, data4: [u8; 8usize]) -> Self {
        EfiGuid { data1, data2, data3, data4 }
    }
}

#[macro_export]
macro_rules! efi_call {
    ( $method:expr, $($x:expr),*$(,)? ) => {
        {
            let res: EfiResult<()> = match $method {
                None => Err(EFI_STATUS_NOT_FOUND.into()),
                Some(f) => map_efi_err(f($($x,)*))
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
