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

use crate::{efi_println, record_protocol, DeviceHandle, EfiEntry};
use core::{
    ops::{Deref, DerefMut},
    ptr::NonNull,
};
use efi_types::{defs::EfiGuid, protocol::Client, Identified};

pub mod block_io;
pub mod block_io2;
pub mod device_path;
pub mod dt_fixup;
pub mod erase_block;
pub mod gbl_efi_avb;
pub mod gbl_efi_avf;
pub mod gbl_efi_boot_control;
pub mod gbl_efi_boot_memory;
pub mod gbl_efi_debug;
pub mod gbl_efi_fastboot;
pub mod gbl_efi_fastboot_transport;
pub mod gbl_efi_os_configuration;
pub mod load_file2;
pub mod loaded_image;
pub mod random_number_generator;
pub mod riscv;
pub mod simple_network;
pub mod simple_text_input;
pub mod simple_text_output;
pub mod timestamp;

pub(super) mod hash2;
pub(crate) mod service_binding;

/// Describes whether a Protocol is required or optional.
pub enum Requirement {
    /// The protocol is a mandatory requirement for supporting GBL.
    Mandatory,
    /// The protocol is an optional requirement for supporting GBL.
    Optional,
}

/// Type safe definition for protocol revision.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Revision {
    /// The major revision of the protocol as defined in the header.
    /// The major version must match EXACTLY for compatibility.
    /// If the major version is 0, the protocol is not yet stable
    /// and breaking changes may occur.
    pub major: u16,
    /// The minor revision of the protocol as defined by the header.
    ///
    /// If the minor version is higher than the defined constant,
    /// this is a transparent, backwards compatible difference.
    ///
    /// If the minor version is lower than expected,
    /// the size of the protocol struct may be smaller than the GBL visible type
    /// or fields may be in a reserved and undefined state.
    pub minor: u16,
}

impl Revision {
    /// Generate a revision from a raw u32.
    pub const fn from_u32(r: u32) -> Self {
        Self { major: ((r >> 16) & 0xFFFF) as u16, minor: (r & 0xFFFF) as u16 }
    }
}

impl core::fmt::Display for Revision {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}.{}", self.major, self.minor)
    }
}

impl From<u64> for Revision {
    fn from(value: u64) -> Self {
        // For now, discard the most significant bytes..
        Self::from_u32(value as u32)
    }
}

impl From<u32> for Revision {
    fn from(value: u32) -> Self {
        Self::from_u32(value)
    }
}

/// Bindgen-derived protocol structures MUST implement `MaybeVersioned`.
/// If the protocol is actually versioned it should provide override definitions
/// for `REVISION` and `revision`.
///
/// This is necessary due to limitations in specializing trait implementations.
pub trait MaybeVersioned {
    /// Revision of struct as defined by header file.
    const REVISION: Option<Revision> = None;

    /// Actual revision of runtime protocol.
    fn revision(&self) -> Option<Revision> {
        None
    }
}

/// Interface for defining the compile time expected version of a protocol
/// and the actual runtime version of the protocol when opened.
///
/// Implement for Protocol<T> if you want to check the minor version in order to
/// gate access to fields or method.
///
/// E.g.
///
/// ```
/// struct MyProtocol;
/// impl ProtocolInfo for MyProtocol {
///     type InterfaceType = EfiMyProtocol;
///
///     const GUID: EfiGuid = ...;
/// }
///
/// impl MaybeVersioned for EfiMyProtocol {
///     const REVISION: Option<Revision> = Some(Revision::from_u32(EFI_MY_PROTOCOL_REVISION as u32));
///
///     fn revision(&self) -> Option<Revision> {
///         Some(self.revision.into())
///     }
/// }
///
/// impl Versioned for Protocol<'_, MyProtocol> {
///     const REVISION: Some(Revision::from_u32(EFI_MY_PROTOCOL_REVISION as u32));
///
///     fn revision(&self) -> Revision {
///         self.interface().revision.into()
///     }
/// }
/// ```
///
/// This is verbose, and it is easy to make mistakes, so the `versioned_protocol!` macro
/// is defined to assist with the boilerplate.
///
/// The two traits `MaybeVersioned` and `Versioned` are necessary due to limitations
/// in specializing trait implementations.
pub trait Versioned {
    /// The revision of the struct definition as seen by GBL.
    /// Should be derived from the header that defines the protocol struct
    /// and provided by bindgen.
    const REVISION: Revision;

    /// Accesses the revision field of the protocol structure.
    fn revision(&self) -> Revision;
}

/// Convenience macro for describing versioned protocols.
///
/// Extended example:
///
/// ```
/// // libefi_types/defs/protocols/efi_my_proto.h
/// #include <gbl_protocol_utils.h>
///
/// static const uint64_t EFI_MY_PROTOCOL_REVISION = GBL_PROTOCOL_REVISION(2, 3);
///
/// typedef struct {
///     uint64_t revision;
///     ...
/// } EfiMyProtocol;
/// ```
///
/// ```
/// // libefi/src/protocol/my_protocol.rs
///
/// use crate::{versioned_protocol, ProtocolInfo};
/// use efi_types::{EfiMyProtocol, EFI_MY_PROTOCOL_REVISION};
///
/// struct MyProtocol;
///
/// impl ProtocolInfo for MyProtocol {
///     type InterfaceType = EfiMyProtocol;
///     ...
/// }
///
/// versioned_protocol!(MyProtocol, EFI_MY_PROTOCOL_REVISION);
///
/// fn check_protocol<P>(p: &Protocol<'_, P>)
///   where Protocol<'_, P>: Versioned {
///     if p.revision() != P::REVISION {
///         efi_println!(p.efi_entry(), "Version mismatch: expected {}, got {}",
///                      P::REVISION, p.revision());
///     }
/// }
/// ```
#[macro_export]
macro_rules! versioned_protocol {
    ($protocol_struct:tt, $revision:expr) => {
        versioned_protocol!($protocol_struct, $revision, revision);
    };
    ($protocol_struct:tt, $revision:expr, $field_name:ident) => {
        use crate::protocol::{MaybeVersioned, Revision, Versioned};

        impl MaybeVersioned for <$protocol_struct as ProtocolInfo>::InterfaceType {
            const REVISION: Option<Revision> = Some(Revision::from_u32($revision as u32));

            fn revision(&self) -> Option<Revision> {
                Some(self.$field_name.into())
            }
        }

        impl Versioned for Protocol<'_, $protocol_struct> {
            const REVISION: Revision = Revision::from_u32($revision as u32);

            fn revision(&self) -> Revision {
                self.interface().$field_name.into()
            }
        }
    };
}

/// ProtocolInfo provides GUID info and the EFI data structure type for a protocol.
pub trait ProtocolInfo {
    /// Data structure type of the interface.
    type InterfaceType: MaybeVersioned;
    /// GUID of the protocol.
    const GUID: EfiGuid;
    /// Whether the protocol is mandatory or optional.
    const REQUIREMENT: Requirement = Requirement::Mandatory;
    /// An optional tag to identify this protocol in metrics.
    const METRICS_TAG: Option<&'static str> = None;
}

/// Temporary trait to abstract over protocols using [ProtocolInfo] vs [Client].
/// Once we use [Client] everywhere this can go away.
///
/// Note: `CInterface` must always be `Versioned` because of the
/// [ProtocolInfo] vs [Client] split and because of limitations
/// in impl specialization.
pub trait ProtocolImpl {
    /// The raw C struct type.
    type CInterface: MaybeVersioned;
    /// The underlying implementation type.
    type ImplType;
    /// The protocol GUID.
    const GUID: EfiGuid;
    /// Whether the protocol is mandatory or optional.
    const REQUIREMENT: Requirement = Requirement::Mandatory;
    /// An optional tag to identify this protocol in metrics.
    const METRICS_TAG: Option<&'static str> = None;

    /// Creates the corresponding `ImplType` from a raw C struct.
    ///
    /// # Safety
    ///
    /// * `c_interface` must point to a valid `CInterface` object
    /// * `c_interface` must outlive the returned `ImplType`
    /// * ownership of `c_interface` must be passed in, and must not be used
    ///   again except through the returned `ImplType`
    unsafe fn new_impl(c_interface: NonNull<Self::CInterface>) -> Self::ImplType;
}

/// For [ProtocolInfo], the implementation type is a raw C struct pointer.
impl<T: ProtocolInfo> ProtocolImpl for T {
    type CInterface = T::InterfaceType;
    type ImplType = NonNull<T::InterfaceType>;
    const GUID: EfiGuid = T::GUID;
    const REQUIREMENT: Requirement = T::REQUIREMENT;
    const METRICS_TAG: Option<&'static str> = T::METRICS_TAG;

    unsafe fn new_impl(c_interface: NonNull<Self::CInterface>) -> Self::ImplType {
        // Just pass the c_interface pointer through, we use it directly.
        c_interface
    }
}

/// For [Client], the implementation is a [Client] itself.
impl<T: Identified + MaybeVersioned> ProtocolImpl for Client<T> {
    type CInterface = T;
    type ImplType = Self;
    const GUID: EfiGuid = T::GUID;
    const METRICS_TAG: Option<&'static str> = None;

    unsafe fn new_impl(c_interface: NonNull<Self::CInterface>) -> Self::ImplType {
        // SAFETY: by function safety,
        // * `c_interface` is a valid `CInterface`
        // * `c_interface` will outlive the returned `ImplType`
        // * we have exclusive ownership of `c_interface`, which we transfer
        //   into `Client` without retaining a copy
        unsafe { Client::new(c_interface) }
    }
}

/// A generic type for representing an EFI protocol.
#[derive(Debug)]
pub struct Protocol<'a, T: ProtocolImpl> {
    // The handle to the device offering the protocol.
    device: DeviceHandle,
    // The protocol implementation.
    interface: T::ImplType,
    // The `EfiEntry` data
    efi_entry: &'a EfiEntry,
}

/// Common functions for Protocol<T> with either raw or [Client] backend.
///
/// Protocol<T> may have additional implementation based on type `T`.
impl<'a, T: ProtocolImpl> Protocol<'a, T> {
    /// Create a new instance with the given device handle, interface pointer and `EfiEntry` data.
    ///
    /// # Safety
    ///
    /// * `c_interface` must point to a valid `T::CInterface` object
    /// * `c_interface` must outlive the returned `Protocol`
    /// * ownership of `c_interface` must be passed in, and must not be used
    ///   again except through the returned `Protocol`
    pub(crate) unsafe fn new(
        device: DeviceHandle,
        c_interface: NonNull<T::CInterface>,
        efi_entry: &'a EfiEntry,
    ) -> Self {
        // Safety: By precondition, `c_interface` must point to a valid `T::CInterface`.
        let interface_revision = unsafe { c_interface.as_ref() }.revision();

        // TODO(b/445016017): If a protocol is first opened *after* bootconfig has already been
        // finalized and metrics serialized, then the protocol version would not be recorded in the
        // final metrics. Revisit if this becomes a problem in the future.
        if let (Some(tag), Some(revision)) = (T::METRICS_TAG, interface_revision) {
            record_protocol(tag, revision);
        }
        if let Some(expected) = T::CInterface::REVISION {
            if let Some(actual) = interface_revision {
                if actual.major != expected.major {
                    efi_println!(
                        efi_entry,
                        "Opening Protocol<{}>: expected major version {}, got {}",
                        core::any::type_name::<T>(),
                        expected.major,
                        actual.major
                    );
                } else if actual.minor < expected.minor {
                    efi_println!(
                        efi_entry,
                        "Opening Protocol<{}>: expected minor version {}, got {}",
                        core::any::type_name::<T>(),
                        expected.minor,
                        actual.minor
                    );
                }
            } else {
                efi_println!(
                    efi_entry,
                    "Opening Protocol<{}>: cannot check revision",
                    core::any::type_name::<T>()
                );
            }
        }

        // SAFETY: by function safety,
        // * `c_interface` is a valid `T::CInterface`
        // * `c_interface` will outlive the returned `Protocol`
        // * we have exclusive ownership of `c_interface`, which we transfer
        //   into `T::new_impl` without retaining a copy
        let interface = unsafe { T::new_impl(c_interface) };
        Self { device, interface, efi_entry }
    }

    /// Returns the reference to EFI entry.
    pub fn efi_entry(&self) -> &'a EfiEntry {
        self.efi_entry
    }
}

/// Additional functions for Protocol<T> with a raw pointer implementation.
impl<'a, T: ProtocolInfo> Protocol<'a, T> {
    /// Returns the EFI data structure for the protocol interface.
    pub fn interface(&self) -> &T::InterfaceType {
        // SAFETY: EFI protocol interface data structure.
        unsafe { self.interface.as_ref() }
    }

    /// Returns the mutable pointer of the interface. Invisible from outside. Application should
    /// not have any need to alter the content of interface data.
    pub(crate) fn interface_ptr(&self) -> *mut T::InterfaceType {
        self.interface.as_ptr()
    }
}

/// Protocol<T> with a [Client] implementation can deref to [Client] to call
/// its protocol APIs.
impl<'a, T: Identified + MaybeVersioned> Deref for Protocol<'a, Client<T>> {
    type Target = Client<T>;

    fn deref(&self) -> &Self::Target {
        &self.interface
    }
}

/// Protocol<T> with a [Client] implementation can deref to [Client] to call
/// its protocol APIs.
impl<'a, T: Identified + MaybeVersioned> DerefMut for Protocol<'a, Client<T>> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.interface
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
///   self.interface().protocol_function_name,
///   self.interface_ptr(),
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
///   self.interface().protocol_function_name,
///   self.interface_ptr(),
///   arg1,
///   &mut arg2,
///   ...
/// )
/// ```
///
/// This macro is expanded at ~100 call sites, so any code added to it is duplicated at each of
/// them. Keep it minimal and put new logic in out-of-line helpers such as `efi_method_not_found()`.
#[macro_export]
macro_rules! efi_call {
    ( $method:expr $(, $x:expr)* $(,)? ) => {
        {
            use liberror::{Result, efi_status_to_result};
            let res: Result<()> = match $method {
                None => Err($crate::protocol::efi_method_not_found(stringify!($method))),
                Some(f) => efi_status_to_result(f($($x,)*)),
            };
            res
        }
    };
    ( @bufsize $size:expr, $method:expr $(, $x:expr)* $(,)? ) => {
        {
            use efi_types::{EFI_STATUS_BUFFER_TOO_SMALL, EFI_STATUS_SUCCESS};
            use liberror::{Error, Result, efi_status_to_result};
            use libutils::method_basename;
            let res: Result<()> = match $method {
                None => Err($crate::protocol::efi_method_not_found(stringify!($method))),
                Some(f) => {
                    let capacity = $size;
                    match f($($x,)*) {
                        EFI_STATUS_SUCCESS => {
                            // Safety check that the implementation didn't accidentally overflow
                            // the provided buffer. If they did, memory is likely corrupted and
                            // we cannot recover, so panicking is the best option.
                            assert!($size <= capacity,
                                    "Error: buffer overflow detected in protocol call '{}'",
                                    method_basename(stringify!($method)));
                            Ok(())
                        }
                        EFI_STATUS_BUFFER_TOO_SMALL => Err(Error::BufferTooSmall(Some($size))),
                        r => efi_status_to_result(r),
                    }
                },
            };
            res
        }
    };
}

/// Cold path of [efi_call!] when the protocol method pointer is NULL.
///
/// Prints `Protocol method not found at <file>:<line>:<column>: <method basename>`, where the
/// location is the [efi_call!] invocation, and returns `Error::NotFound`. Not a public API.
#[doc(hidden)]
#[cold]
#[inline(never)]
#[track_caller]
pub fn efi_method_not_found(method: &str) -> liberror::Error {
    // Must be read outside `efi_try_print!`, which may wrap its arguments in a closure.
    let caller = core::panic::Location::caller();
    crate::efi_try_print!(
        "Protocol method not found at {}: {}\r\n",
        caller,
        libutils::method_basename(method)
    );
    liberror::Error::NotFound
}

#[cfg(test)]
mod test {
    use super::*;
    use efi_types::{
        EfiStatus, GblEfiAvbProtocol, EFI_STATUS_BUFFER_TOO_SMALL, EFI_STATUS_DEVICE_ERROR,
        EFI_STATUS_SUCCESS,
    };
    use gbl_efi_avb::GblAvbProtocol;
    use liberror::Error;

    #[test]
    fn efi_call_success() {
        fn test_func(a: u32, b: &str) -> EfiStatus {
            assert_eq!(a, 100);
            assert_eq!(b, "foo");
            EFI_STATUS_SUCCESS
        }

        assert_eq!(efi_call!(Some(test_func), 100, "foo"), Ok(()));
    }

    #[test]
    fn efi_call_error() {
        fn test_func() -> EfiStatus {
            EFI_STATUS_DEVICE_ERROR
        }

        assert_eq!(efi_call!(Some(test_func)), Err(Error::DeviceError));
    }

    #[test]
    fn efi_call_method_not_found() {
        let test_func: Option<fn() -> EfiStatus> = None;

        assert_eq!(efi_call!(test_func), Err(Error::NotFound));
    }

    #[test]
    fn efi_call_bufsize_valid() {
        fn test_func(bufsize: &mut usize) -> EfiStatus {
            assert_eq!(*bufsize, 10);
            *bufsize = 5;
            EFI_STATUS_SUCCESS
        }

        let mut size = 10;
        assert_eq!(efi_call!(@bufsize size, Some(test_func), &mut size), Ok(()));
        assert_eq!(size, 5);
    }

    #[test]
    fn efi_call_bufsize_max() {
        fn test_func(_: &mut usize) -> EfiStatus {
            // Leave bufsize at the maximum allowed value to make sure our <= logic is right.
            EFI_STATUS_SUCCESS
        }

        let mut size = 10;
        assert_eq!(efi_call!(@bufsize size, Some(test_func), &mut size), Ok(()));
        assert_eq!(size, 10);
    }

    #[test]
    fn efi_call_bufsize_too_small_error() {
        fn test_func(bufsize: &mut usize) -> EfiStatus {
            *bufsize = 20;
            EFI_STATUS_BUFFER_TOO_SMALL
        }

        let mut size = 10;
        assert_eq!(
            efi_call!(@bufsize size, Some(test_func), &mut size),
            Err(Error::BufferTooSmall(Some(20)))
        );
    }

    #[test]
    #[should_panic]
    fn efi_call_bufsize_overflow_panic() {
        fn test_func(bufsize: &mut usize) -> EfiStatus {
            // Make it look like we overflowed the buffer but then incorrectly returned SUCCESS.
            *bufsize += 1;
            EFI_STATUS_SUCCESS
        }

        let mut size = 10;
        // This should panic.
        let _ = efi_call!(@bufsize size, Some(test_func), &mut size);
    }

    #[test]
    fn efi_call_bufsize_method_not_found() {
        let test_func: Option<fn(&mut usize) -> EfiStatus> = None;

        let mut size = 10;
        assert_eq!(efi_call!(@bufsize size, test_func, &mut size), Err(Error::NotFound));
    }

    #[test]
    fn test_protocol_new_records_version() {
        let c_interface = GblEfiAvbProtocol { revision: 0x0001_0000, ..Default::default() };

        crate::test::run_test_with_mock_protocol::<GblAvbProtocol>(c_interface, |_| {
            assert_eq!(
                crate::opened_protocols().as_slice(),
                [(
                    <GblAvbProtocol as ProtocolInfo>::METRICS_TAG.unwrap(),
                    Revision { major: 1, minor: 0 }
                )]
            );
        });
    }
}
