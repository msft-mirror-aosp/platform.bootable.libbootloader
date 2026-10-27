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

//! Rust UEFI protocols.
//!
//! This module provides Rust traits for protocols used by GBL. The protocol
//! APIs are designed to mirror the underlying UEFI protocol definitions, but
//! modified to be more idiomatic Rust, for example:
//!
//! * buffers are slices rather than (pointer, length) pairs
//! * output params are converted to return values instead when feasible
//! * return values are `Result`s rather than raw status enum
//!
//! These protocol traits are usable both on the client side (UEFI application)
//! and the provider side (UEFI firmware). GBL will use the client-side APIs,
//! but devices are not required to use the provider-side APIs, they are just
//! offered as an option to make it easier to build GBL-compatible UEFI firmware
//! in Rust.
//!
//! ```text
//!        GBL           Protocol API           Rust backend (optional)
//!  ---------------------------------------------------------------------
//!                                           Rust protocol provider
//!                                <----------
//!                        C struct
//!               <--------
//!    Rust client
//!
//!    Make Rust calls
//!               -------->
//!                        C struct
//!                                ---------->
//!                                           Rust provider implementation
//! ```
//!
//! This library does not provide a full UEFI firmware implementation, it only
//! aims to wrap protocol pointers. How those pointers get into and out of the
//! UEFI stack is up to the particular implementation.
//!
//! # Client usage
//!
//! Protocol clients such as GBL will get the protocol C pointer from UEFI,
//! then wrap them in a [Client] object, which exposes protocol functionality
//! via safe Rust APIs.
//!
//! # Provider usage
//!
//! Protocol providers such as the UEFI firmware or a driver will implement
//! the protocol Rust backend, then pass it into a [Provider], which exposes
//! a raw C pointer to register with the UEFI stack. Calls on this C pointer
//! will route back into the Rust backend implementation.
//!
//! Additionally there is a [BridgeToRust] trait that [Provider] requires, which
//! properly initializes the C struct to pass calls back into the Rust backend.
//! This will be provided for protocols supported by this library, but can also
//! be implemented manually for new protocols or if users want to define a
//! different Rust API to wrap an existing protocol.
//!
//! # Ownership
//!
//! In UEFI, protocols can be opened by multiple clients. For Rust, this means
//! that we must use non-mutable references to avoid violating single-owner
//! mutability requirements. If a protocol backend needs to modify state, it
//! must use interior mutability to safely do so.
//!
//! For [Client]s, this means that the protocol methods all take a const
//! `&self`, but may still change internal state. For example, Block I/O
//! Protocol calls to read/write may end up modifying the associated `Media`
//! state. Ensuring safe shared access is normally the responsibility of the
//! protocol backend, whether implemented in Rust or C, though there are a
//! few exceptions. See [Client] docs for details.
//!
//! For this library's [Provider] backend, the [Provider] documentation has
//! details on how to safely meet these requirements.

pub mod block_io;
pub mod device_path;
pub mod gbl_efi_avf;
pub mod gbl_efi_boot_control;
pub mod gbl_efi_boot_memory;
pub mod gbl_efi_fastboot;
pub mod gbl_efi_fastboot_transport;
pub mod load_file2;

use crate::{
    status::{EfiError, EfiResult},
    Identified,
};
use core::{cell::UnsafeCell, marker::PhantomPinned, pin::Pin, ptr::NonNull, slice};

/// A UEFI protocol client.
///
/// This wraps the protocol C struct and exposes the Rust API, so that the
/// protocol can be used with as little unsafe code as possible.
///
/// # Ownership and concurrency
///
/// In most cases it's the protocol implementation's responsibility to ensure
/// proper ownership and concurrency protection to protect against data races,
/// but when a protocol struct has a raw pointer to mutable data, the backend
/// can't know when this data is being accessed.
///
/// In these cases, to ensure safe usage the client must protect against data
/// races itself. These functions will be marked `unsafe` with guidance on how
/// to properly access the data; in UEFI environments this generally means
/// raising the TPL to the protocol's maximum supported level according to the
/// [spec](https://uefi.org/specs/UEFI/2.10/07_Services_Boot_Services.html#tpl-restrictions)
/// which ensures no other client can concurrently modify the data.
///
/// # Usage
///
/// 1. Open a protocol to get the C struct
/// 2. Call [Client::new] to wrap the C struct
/// 3. Make calls on the [Client] API
/// 4. Drop the [Client]
/// 5. Close the protocol
#[derive(Debug)]
pub struct Client<C: 'static + Identified>(&'static C);

impl<C: 'static + Identified> Client<C> {
    /// Creates a new protocol client.
    ///
    /// # Arguments
    ///
    /// * `c_interface`: the protocol implementation C pointer.
    ///
    /// # Panics
    ///
    /// If `c_interface` is null.
    ///
    /// # Safety
    ///
    /// * `c_interface` must be a valid object adhering to the UEFI spec
    /// * `c_interface` must outlive the returned [Client]
    ///
    /// In UEFI environments, this means the returned [Client] must be dropped
    /// before calling `CloseProtocol()` or `ExitBootServices()`.
    ///
    /// Additionally, in UEFI the caller must only use the returned [Client]
    /// within the protocol's
    /// [supported TPL range](https://uefi.org/specs/UEFI/2.10/07_Services_Boot_Services.html#tpl-restrictions)
    pub unsafe fn new(c_interface: NonNull<C>) -> Self {
        // SAFETY: function safety requires a valid pointer which outlives us.
        let c_interface = unsafe { c_interface.as_ref() };
        Self(c_interface)
    }

    /// Returns the underlying client struct.
    ///
    /// This method is a safety valve for tests.
    /// Calling it in production code is a code smell.
    pub fn interface(&self) -> &'static C {
        self.0
    }
}

/// A UEFI protocol provider.
///
/// This wraps the Rust API and exposes the protocol C struct, so that calls on
/// the struct route back to the Rust implementation.
///
/// # Ownership and concurrency
///
/// In UEFI, protocols can be opened by multiple clients, so we use interior
/// mutability techniques if any state needs to be changed in a protocol call.
///
/// UEFI also supports limited concurrency in the form of
/// [task priority levels (TPLs)](https://uefi.org/specs/UEFI/2.10/07_Services_Boot_Services.html#event-timer-and-task-priority-services).
/// Higher priority levels will interrupt lower levels, which leads to a few
/// complications:
///
/// * There is no priority inversion support, which means something like a
///   standard mutex will not work here; if lower-priority code holds a mutex
///   when higher-priority code tries to grab it, the system will deadlock
///
/// * Rust `Cell`-type classes are not thread-safe, so could cause data races
///   and undefined behavior if used directly from multiple TPLs
///
/// Each protocol has unique requirements, but a general approach might look
/// like:
///
/// ```
/// use core::cell::Cell;
/// use efi_types::status::{EfiError, EfiResult};
///
/// // A simple protocol API.
/// trait FooProtocol {
///     // Saves the given `arg` in the protocol state.
///     fn save_state(&self, arg: u32) -> EfiResult<()>;
/// }
///
/// // The protocol provider backend.
/// struct FooProvider {
///     state: Cell<u32>
/// }
///
/// // We need some way to raise and restore TPL. Up to the implementation
/// // what this looks like; see `TplScope` for a helper that automatically
/// // restores the TPL on drop.
/// fn raise_tpl(level: usize) {}
/// fn restore_tpl() {}
///
/// // The maximum allowed TPL for this protocol.
/// const MAX_FOO_PROTOCOL_TPL: usize = 8;
///
/// impl FooProtocol for FooProvider {
///     fn save_state(&self, arg: u32) -> EfiResult<()> {
///         // 1. Perform any non-state-dependent operations first outside of the
///         //    critical section, e.g. argument validation.
///         if (arg > 100) {
///             return Err(EfiError::InvalidParameter);
///         }
///
///         // 2. Enter the critical section by raising the TPL to the maximum
///         //    supported level for this protocol.
///         //
///         //    Depending on the firmware implementation, you may also need
///         //    additional guards here, e.g. if there is threading internally
///         //    this may also need to lock a mutex, but the TPL should be
///         //    updated first to prevent deadlock.
///         raise_tpl(MAX_FOO_PROTOCOL_TPL);
///
///         // 3. Now it's safe to get mutability on the `Cell`.
///         self.state.set(arg);
///
///         // 4. Restore the TPL to leave the critical section.
///         restore_tpl();
///
///         Ok(())
///     }
/// }
/// ```
///
/// # Usage
///
/// 1. Implement a Rust protocol trait
/// 2. Call [Provider::new] to wrap the Rust implementation
/// 3. Call [Provider::to_ptr] to get the C struct
/// 4. Register the C struct with the UEFI protocol database
#[repr(C)]
pub struct Provider<'a, C: Identified, R> {
    // This must come first, so that with `repr(C)` we can cast between this
    // `c_interface` pointer and the overall `Provider` pointer.
    c_interface: UnsafeCell<C>,
    rust_impl: &'a R,
    // Clients use our `c_interface` pointer directly, so pinning is critical
    // to ensure those pointers stay valid.
    _pin: PhantomPinned,
}

impl<'a, C: 'a + Identified + BridgeToRust<R>, R> Provider<'a, C, R> {
    /// Creates a new [Provider] backed by the given Rust implementation.
    pub fn new(rust_impl: &'a R) -> Self {
        // SAFETY: we hold a borrow of `rust_impl` so we know it will not be
        // moved or destroyed while we exist.
        let c_interface = unsafe { C::create_bridge(rust_impl) };
        Self { c_interface: UnsafeCell::new(c_interface), rust_impl, _pin: PhantomPinned }
    }
}

impl<'a, C: 'a + Identified, R> Provider<'a, C, R> {
    /// Returns the raw UEFI C interface pointer backed by this provider.
    ///
    /// # Arguments
    ///
    /// * `self`: a pinned reference to `self`. The pin is critical for safe
    ///           functionality so that the pointer given to clients stays
    ///           valid and can be used to route calls back into `self`.
    ///
    /// # Returns
    ///
    /// A pointer which can be registered with the UEFI protocol database and
    /// handed out to clients. When clients make C calls on this struct, it
    /// will automatically route back into the Rust backing implementation.
    ///
    /// The returned pointer is mutable because the UEFI C interface requires
    /// it, but protocol pointers are shared and clients are not allowed to
    /// write to them directly which we represent in Rust as a const ref with
    /// interior mutability.
    ///
    /// # Safety
    ///
    /// `self` must outlive the returned pointer.
    ///
    /// Any client calling into the returned pointer must also adhere to the
    /// protocol definitions and requirements, such as:
    ///
    /// * not writing directly to the pointer (shared non-mutable)
    /// * only using the pointer within the supported TPL range
    ///
    /// This library's [Client] classes enforce proper usage, but other clients,
    /// particulary those written in C, could cause undefined behavior if they
    /// violate the protocol requirements.
    pub fn to_ptr(self: Pin<&Self>) -> NonNull<C> {
        // With `#[repr(C)]` and `UnsafeCell<C>` at offset 0, a pointer to `Self` is also a
        // pointer to `C`, and deriving it from `self.get_ref()` gives it provenance over the whole
        // `Provider` for `to_rust()`.
        NonNull::from(self.get_ref()).cast()
    }

    /// Converts the raw C interface pointer back to our Rust implementation.
    ///
    /// # Safety
    ///
    /// * `this` must be the C interface pointer returned by [to_ptr()]
    ///   * most commonly this condition will be satisfied by using the first
    ///     argument of a UEFI protocol function
    /// * all usage of the returned `Self` must properly protect shared data,
    ///   e.g. via the techniques described in the [Protocol] struct docs
    pub(crate) unsafe fn to_rust(this: *const C) -> &'a R {
        // `repr(C)` lets us cast between the struct and its first item.
        let this = this as *const Self;
        // SAFETY:
        // * function safety requires `this` is the `to_ptr()` pointer
        // * by `to_ptr()` safety docs and implementation, we know `this` points
        //   to a valid non-null `Self` which lives for at least `'a`
        unsafe { this.as_ref() }.unwrap().rust_impl
    }
}

/// Bridges a C protocol interface to a Rust backend implementation.
///
/// This trait gets implemented on the protocol C struct to configure it to
/// forward calls into a Rust provider backend `R`.
///
/// # Safety
///
/// The created C struct must adhere to the UEFI protocol spec - pointers must
/// be valid, function implementations must obey requirements, etc.
///
/// Pointers require particular care, e.g. if the protocol structure contains
/// something like `UINT8* data`. These pointers will be set once upon bridge
/// creation and must remain valid for the lifetime of the bridge.
///
/// The Rust backend will stay valid and unmoved while the bridge exists, so the
/// recommended way to approach this is to put the data inside the Rust struct,
/// something like this:
///
/// ```
/// use efi_types::protocol::BridgeToRust;
///
/// // The C protocol definition.
/// struct FooC {
///   data: *mut u8
/// }
///
/// // The corresponding Rust API.
/// trait FooRust {
///   fn data(&self) -> &[u8];
/// }
///
/// struct FooImpl {
///   // Data lives inside our struct, so as long as the struct can't move
///   // the data won't either.
///   //
///   // Note that this is NOT necessarily the case if `data` was something like
///   // `Vec<u8>` that lives outside the struct - in that case you would have
///   // to ensure the vector never reallocates once the [Provider] is created.
///   data: [u8; 8]
/// }
///
/// impl FooRust for FooImpl {
///   fn data(&self) -> &[u8] {
///     &self.data
///   }
/// }
///
/// // SAFETY: we can assign `rust_impl.data()` to a pointer because `rust_impl`
/// // is guaranteed to stay valid an unmoved while the bridge exists, and the
/// // data lives inside `rust_impl`.
/// unsafe impl BridgeToRust<FooImpl> for FooC {
///   unsafe fn create_bridge(rust_impl: &FooImpl) -> Self {
///     Self { data: rust_impl.data().as_ptr() as *mut _ }
///   }
/// }
/// ```
///
/// Otherwise, it is up to the implementation to ensure that pointers remain
/// valid and safe to convert back to a reference according to
/// https://doc.rust-lang.org/std/ptr/index.html#pointer-to-reference-conversion.
pub unsafe trait BridgeToRust<R> {
    /// Creates the C struct that will forward calls into `rust_impl`.
    ///
    /// # Safety
    ///
    /// This function may create pointers from `self` into `rust_impl`, so to
    /// ensure those pointers stay valid, `rust_impl` must remain valid and
    /// unmoved until `self` is dropped.
    unsafe fn create_bridge(rust_impl: &R) -> Self;
}

/// A raw pointer parameter passed to a protocol provider by a C caller.
pub(crate) trait RawParam {
    /// Returns true if the pointer is non-null and aligned for its pointee type.
    fn is_non_null_and_aligned(&self) -> bool;
}

impl<T> RawParam for *const T {
    fn is_non_null_and_aligned(&self) -> bool {
        !self.is_null() && self.is_aligned()
    }
}

impl<T> RawParam for *mut T {
    fn is_non_null_and_aligned(&self) -> bool {
        !self.is_null() && self.is_aligned()
    }
}

/// Checks that required pointer parameters are non-null and aligned.
///
/// This does not by itself make the pointers safe to use; callers must still
/// ensure they are valid for the intended access, e.g. by the protocol spec.
///
/// # Returns
///
/// `Err(EfiError::InvalidParameter)` if any pointer is null or misaligned.
pub(crate) fn check_required_params(params: &[&dyn RawParam]) -> EfiResult<()> {
    match params.iter().all(|p| p.is_non_null_and_aligned()) {
        true => Ok(()),
        false => Err(EfiError::InvalidParameter),
    }
}

/// Converts a C (pointer, length) buffer into a slice.
///
/// C callers may pass a null or dangling pointer for an empty buffer, which
/// [slice::from_raw_parts] does not allow, so `ptr` is ignored if `len` is 0.
///
/// # Returns
///
/// `Err(EfiError::InvalidParameter)` if `len` is nonzero and `ptr` is null or
/// misaligned.
///
/// # Safety
///
/// If `len` is nonzero, `ptr` must be valid for reads of `len` initialized
/// elements of `T` within a single allocation, `len * size_of::<T>()` must not
/// exceed `isize::MAX`, and the memory must not be mutated for `'a`.
pub unsafe fn slice_from_raw_parts<'a, T>(ptr: *const T, len: usize) -> EfiResult<&'a [T]> {
    match len {
        0 => Ok(&[]),
        _ => {
            check_required_params(&[&ptr])?;
            // SAFETY: `ptr` was checked non-null and aligned above. The caller guarantees the
            // rest of the `slice::from_raw_parts` contract: `ptr` is valid for reads of `len`
            // initialized elements in one allocation, the size fits in `isize`, and the memory
            // is not mutated for `'a`.
            Ok(unsafe { slice::from_raw_parts(ptr, len) })
        }
    }
}

/// Converts a mutable C (pointer, length) buffer into a mutable slice.
///
/// See [slice_from_raw_parts].
///
/// # Safety
///
/// If `len` is nonzero, `ptr` must be valid for reads and writes of `len`
/// initialized elements of `T` within a single allocation,
/// `len * size_of::<T>()` must not exceed `isize::MAX`, and the memory must not
/// be accessed through any other pointer for `'a`.
pub unsafe fn slice_from_raw_parts_mut<'a, T>(ptr: *mut T, len: usize) -> EfiResult<&'a mut [T]> {
    match len {
        0 => Ok(&mut []),
        _ => {
            check_required_params(&[&ptr])?;
            // SAFETY: `ptr` was checked non-null and aligned above. The caller guarantees the
            // rest of the `slice::from_raw_parts_mut` contract: `ptr` is valid for reads and
            // writes of `len` initialized elements in one allocation, the size fits in `isize`,
            // and the memory is not accessed through any other pointer for `'a`.
            Ok(unsafe { slice::from_raw_parts_mut(ptr, len) })
        }
    }
}

#[cfg(test)]
pub(crate) mod test {
    use super::*;
    use crate::{
        defs::{EfiGuid, EfiStatus},
        status::{EfiError, EfiResult},
    };
    use mockall::automock;
    use std::{ffi::c_void, ops::Range, slice};

    /// Returns a buffer pointer ranges.
    ///
    /// The `==` operator on slices only compares contents, but for our UEFI
    /// protocols we often want to be sure that a buffer is passed exactly
    /// through a protocol without any intermediate copies or pointer mixups.
    ///
    /// This also converts to `usize` which makes it easier to use with
    /// mockall expectations.
    pub fn buffer_range<T>(buffer: &[T]) -> Range<usize> {
        let range = buffer.as_ptr_range();
        // Convert to usize because mockall objects require `Send` which
        // raw pointers are not. There are some workarounds but converting
        // here makes usage easier.
        Range { start: range.start as usize, end: range.end as usize }
    }

    #[test]
    fn same_buffer_true() {
        let buffer = [1, 2, 3, 4];
        let buffer_ref = &buffer;
        assert_eq!(buffer_range(&buffer), buffer_range(buffer_ref));
    }

    #[test]
    fn same_buffer_false() {
        let buffer = [1, 2, 3, 4];
        let buffer2 = [1, 2, 3, 4];
        assert_ne!(buffer_range(&buffer), buffer_range(&buffer2));
    }

    /// Fake protocol C interface for testing.
    ///
    /// Declares a few differently-shaped functions and data fields to test that
    /// they can be properly modeled in our library. This can also be used as a
    /// reference for adding new protocols.
    ///
    /// Normally this would be defined in C and bindgen would convert it to
    /// Rust, but here we just define the Rust struct directly for simplicity.
    #[repr(C)]
    struct CInterface {
        /// A raw value.
        pub value: u64,

        /// A pointer to some data that lives outside the struct.
        /// This must be a valid pointer.
        pub external_data: *mut [u8; 8],

        /// A function that sends a const buffer (e.g. to write to disk).
        pub send_buffer: Option<
            unsafe extern "efiapi" fn(
                self_: *mut Self,
                buffer_size: usize,
                buffer: *const c_void,
            ) -> EfiStatus,
        >,

        /// A function that sends a mut buffer (e.g. to read from disk).
        pub send_buffer_mut: Option<
            unsafe extern "efiapi" fn(
                self_: *mut Self,
                buffer_size: usize,
                buffer: *mut c_void,
            ) -> EfiStatus,
        >,
    }

    impl Identified for CInterface {
        const GUID: EfiGuid = EfiGuid::new(0, 1, 2, [3, 4, 5, 6, 7, 8, 9, 10]);
    }

    /// Fake protocol Rust API wrapper.
    ///
    /// The API of the Rust wrapper is up to us, but it should mirror the C API
    /// pretty closely with just some modified argument and return types to use
    /// more idiomatic Rust.
    ///
    /// # Safety
    ///
    /// The reference returned by [external_data] must not be invalidated by any
    /// other protocol methods.
    ///
    /// This is necessary because the C struct holds a pointer to the data. See
    /// [BridgeToRust] safety docs for details on pointers in protocols.
    #[automock]
    unsafe trait RustInterface {
        /// Returns `value`.
        fn value(&self) -> u64;

        /// Returns `external_data` as a const ref.
        // The explicit lifetimes are required for `automock`, if we try to
        // elide them it gives a compile error.
        fn external_data<'a>(&'a self) -> EfiResult<&'a [u8; 8]>;

        /// Rust API for `send_buffer`.
        fn send_buffer(&self, buffer: &[u8]) -> EfiResult<()>;

        /// Rust API for `send_buffer_mut`.
        fn send_buffer_mut(&self, buffer: &mut [u8]) -> EfiResult<()>;
    }

    /// SAFETY:
    /// * our wrapper functions adhere to the protocol spec
    /// * [RustInterface] safety guarantees the [external_data] pointer stays
    ///   valid
    unsafe impl<R: RustInterface> BridgeToRust<R> for CInterface {
        unsafe fn create_bridge(rust_impl: &R) -> Self {
            CInterface {
                value: rust_impl.value(),
                external_data: rust_impl.external_data().unwrap() as *const _ as *mut _,
                send_buffer: Some(Provider::<_, R>::send_buffer_wrapper),
                send_buffer_mut: Some(Provider::<_, R>::send_buffer_mut_wrapper),
            }
        }
    }

    /// Provider wrappers to serve the protocol C -> Rust.
    impl<'a, R: RustInterface> Provider<'a, CInterface, R> {
        unsafe extern "efiapi" fn send_buffer_wrapper(
            this: *mut CInterface,
            buffer_size: usize,
            buffer: *const c_void,
        ) -> EfiStatus {
            // SAFETY: UEFI protocols require `this` is our C interface pointer.
            let rust_impl = unsafe { Self::to_rust(this) };
            // SAFETY: protocol spec requires this be a valid buffer.
            let buffer = unsafe { slice::from_raw_parts(buffer as *const u8, buffer_size) };
            rust_impl.send_buffer(buffer).into()
        }

        unsafe extern "efiapi" fn send_buffer_mut_wrapper(
            this: *mut CInterface,
            buffer_size: usize,
            buffer: *mut c_void,
        ) -> EfiStatus {
            // SAFETY: UEFI protocols require `this` is our C interface pointer.
            let rust_impl = unsafe { Self::to_rust(this) };
            // SAFETY: protocol spec requires this be a valid mutable buffer.
            let buffer = unsafe { slice::from_raw_parts_mut(buffer as *mut u8, buffer_size) };
            rust_impl.send_buffer_mut(buffer).into()
        }
    }

    /// Client wrappers to call into the protocol Rust -> C.
    ///
    /// SAFETY: the [external_data] returned reference is never invalidated.
    unsafe impl RustInterface for Client<CInterface> {
        fn value(&self) -> u64 {
            self.0.value
        }

        fn external_data(&self) -> EfiResult<&[u8; 8]> {
            // SAFETY:
            // * protocol spec guarantees `external_data` pointer is valid
            let data = unsafe { self.0.external_data.as_ref() };
            Ok(data.unwrap())
        }

        fn send_buffer(&self, buffer: &[u8]) -> EfiResult<()> {
            let func = self.0.send_buffer.unwrap();
            // SAFETY:
            // * `self.0` is only borrowed for the duration of the call
            // * `buffer` will only be read up to `buffer.len()` and is only
            //   borrowed for the duration of the call
            unsafe { func(self.0 as *const _ as *mut _, buffer.len(), buffer.as_ptr() as *const _) }
                .into()
        }

        fn send_buffer_mut(&self, buffer: &mut [u8]) -> EfiResult<()> {
            let func = self.0.send_buffer_mut.unwrap();
            // SAFETY:
            // * `self.0` is only borrowed for the duration of the call
            // * `buffer` will only be written up to `buffer.len()` and is
            //   only borrowed for the duration of the call
            unsafe {
                func(self.0 as *const _ as *mut _, buffer.len(), buffer.as_mut_ptr() as *mut _)
            }
            .into()
        }
    }

    const VALUE: u64 = 0xABCD1234;
    const EXTERNAL_DATA: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

    /// Creates a [MockRustInterface] with default expectations set up so that
    /// it can be used as a [Provider].
    fn create_mock() -> MockRustInterface {
        let mut mock = MockRustInterface::new();
        mock.expect_value().return_const(VALUE);
        mock.expect_external_data().return_const(Ok(&EXTERNAL_DATA));
        mock
    }

    /// Connects a [Client] and [Provider] by tunneling through the C interface.
    ///
    /// This properly handles lifetimes and ownership when we control both the
    /// [Client] and [Provider] Rust objects, which lets us omit some `unsafe`
    /// blocks in each test.
    pub(super) struct TestProtocolTunnel<'a, C: 'static + Identified + BridgeToRust<R>, R> {
        // Struct fields are dropped in declaration order
        // (https://doc.rust-lang.org/reference/destructors.html), so `client`
        // must come first so that provider outlives it.
        client: Client<C>,
        // The provider is called through the raw C interface, but the
        // compiler doesn't know this so throws a dead-code error unless
        // we give it the underscore prefix.
        _provider: Pin<Box<Provider<'a, C, R>>>,
    }

    impl<'a, C: Identified + BridgeToRust<R>, R> TestProtocolTunnel<'a, C, R> {
        pub(super) fn new(backend: &'a R) -> Self {
            let provider = Box::pin(Provider::<'a, C, R>::new(backend));
            let c_interface = provider.as_ref().to_ptr();

            // SAFETY:
            // * `c_interface` points to a valid UEFI protocol interface
            //   backed by `provider`
            // * `provider` outlives `client` due to struct declaration order
            let client = unsafe { Client::new(c_interface) };

            Self { client, _provider: provider }
        }

        pub(super) fn client(&self) -> &Client<C> {
            &self.client
        }
    }

    #[test]
    fn value_success() {
        let mock = create_mock();
        let tunnel = TestProtocolTunnel::new(&mock);

        assert_eq!(tunnel.client().value(), VALUE);
    }

    #[test]
    fn external_data_success() {
        let mock = create_mock();
        let tunnel = TestProtocolTunnel::new(&mock);

        assert_eq!(tunnel.client().external_data(), Ok(&EXTERNAL_DATA));
    }

    #[test]
    fn send_buffer_success() {
        let test_buffer: &[u8] = &[0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF];
        let test_buffer_range = buffer_range(test_buffer);

        let mut mock = create_mock();
        mock.expect_send_buffer().returning(move |buffer: &[u8]| {
            // Make sure we got the exact buffer we expected.
            assert_eq!(buffer_range(buffer), test_buffer_range);
            Ok(())
        });
        let tunnel = TestProtocolTunnel::new(&mock);

        assert_eq!(tunnel.client().send_buffer(test_buffer), Ok(()));
    }

    #[test]
    fn send_buffer_failure() {
        let mut mock = create_mock();
        mock.expect_send_buffer().returning(|_| Err(EfiError::NoMedia));
        let tunnel = TestProtocolTunnel::new(&mock);

        assert_eq!(tunnel.client().send_buffer(&[]), Err(EfiError::NoMedia));
    }

    #[test]
    fn send_buffer_mut_success() {
        let test_buffer: &mut [u8] = &mut [1, 2, 3, 4, 5, 6, 7, 8];
        let test_buffer_range = buffer_range(test_buffer);

        let mut mock = create_mock();
        mock.expect_send_buffer_mut().returning(move |buffer: &mut [u8]| {
            // Make sure we got the exact buffer we expected.
            assert_eq!(buffer_range(buffer), test_buffer_range);
            // Zero the bytes.
            buffer.fill(0);
            Ok(())
        });
        let tunnel = TestProtocolTunnel::new(&mock);

        assert_eq!(tunnel.client().send_buffer_mut(test_buffer), Ok(()));
        assert_eq!(test_buffer, &[0, 0, 0, 0, 0, 0, 0, 0]);
    }

    #[test]
    fn send_buffer_mut_failure() {
        let mut mock = create_mock();
        mock.expect_send_buffer_mut().returning(|_| Err(EfiError::NoMedia));
        let tunnel = TestProtocolTunnel::new(&mock);

        assert_eq!(tunnel.client().send_buffer_mut(&mut []), Err(EfiError::NoMedia));
    }
}
