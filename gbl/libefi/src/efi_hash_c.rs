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

//! C-visible wrappers for EFI based hash functions.

use alloc::boxed::Box;

use crate::{
    hash2::{HashAlgorithm, Hasher, Sha256, Sha512},
    with_global_efi_entry,
};
use avb_bindgen::avb_abort;
use core::ptr::{copy_nonoverlapping, null_mut};
use efi_types::protocol::slice_from_raw_parts;
use zerocopy::IntoBytes;

// TODO(b/439659986): store the hasher by value instead of dynamically
// allocating it.

fn efi_sha_init<Algorithm: HashAlgorithm>() -> *mut Hasher<'static, Algorithm> {
    // Safety:
    // * It is the responsibility of initialization code to guarantee that the
    //   global efi entry is valid.
    unsafe { with_global_efi_entry(|e| Hasher::<Algorithm>::new(e).ok()) }
        .ok()
        .flatten()
        .map_or(null_mut(), |h| Box::into_raw(Box::new(h)))
}

/// Safety:
/// * `hasher` points to a valid Hasher<Algorithm> that has been initialized.
/// * `data` is valid to read for `len` bytes.
unsafe fn efi_sha_update<Algorithm: HashAlgorithm>(
    hasher: *mut Hasher<'static, Algorithm>,
    data: *const u8,
    len: usize,
) {
    if hasher.is_null() {
        // Safety:
        // * FFI call
        unsafe { avb_abort() };
    }

    // Safety:
    // * It is a precondition that `data` is valid to read for `len` bytes. `slice_from_raw_parts`
    //   accepts a null `data` when `len` is 0 and rejects it otherwise.
    // * `avb_abort` is an FFI call.
    let slice =
        unsafe { slice_from_raw_parts(data, len) }.unwrap_or_else(|_| unsafe { avb_abort() });
    // Safety:
    // * It is a precondition that `hasher` is a pointer to a valid Hasher<Algorithm>.
    let _ = unsafe { (*hasher).update(slice) };
}

/// Safety:
/// * `hasher_ptr` points to a pointer to a valid Hasher<Algorithm> that has been
/// initialized.
/// * `out` is valid to write for core::mem::size_of::<Algorithm::DigestType>() bytes.
unsafe fn efi_sha_final<Algorithm: HashAlgorithm>(
    hasher_ptr: *mut *mut Hasher<'static, Algorithm>,
    out: *mut u8,
) {
    // Safety:
    // * `*hasher_ptr` is only read after `hasher_ptr` is checked non-null, and it is otherwise
    //   valid per the function contract.
    if hasher_ptr.is_null() || unsafe { (*hasher_ptr).is_null() } || out.is_null() {
        // Safety:
        // * FFI call
        unsafe { avb_abort() };
    }

    // Safety:
    // * It is a precondition that `hasher_ptr` is a valid pointer.
    // * It is a precondition that `out` is valid to write for
    //   core::mem::size_of::<Algorithm::DigestType> bytes.
    // * `digest` and `out` cannot overlap, so the copy is safe.
    unsafe {
        let digest = Box::from_raw(*hasher_ptr).finalize().unwrap();
        *hasher_ptr = null_mut();
        copy_nonoverlapping(digest.as_bytes().as_ptr(), out, core::mem::size_of_val(&digest));
    }
}

/// Allocates and initializes a Hasher<Sha256> and return its pointer.
/// Ownership of the Hasher<Sha256> is passed to the caller.
#[no_mangle]
pub extern "C" fn efi_sha256_init() -> *mut Hasher<'static, Sha256> {
    efi_sha_init::<Sha256>()
}

/// Adds data to the Hasher<Sha256> context.
///
/// Safety:
/// * `hasher` points to a valid Hasher<Sha256> that has been initialized.
/// * `data` is valid to read for `len` bytes.
#[no_mangle]
pub unsafe extern "C" fn efi_sha256_update(
    hasher: *mut Hasher<'static, Sha256>,
    data: *const u8,
    len: usize,
) {
    // Safety:
    // * It is a precondition that `hasher` points to a valid,
    //   initialized Hasher<Sha256>.
    // * It is ia precondition that `data` is valid to read for `len` bytes.
    unsafe { efi_sha_update::<Sha256>(hasher, data, len) }
}
/// Returns the digest from a Hasher<Sha256>.
///
/// Safety:
/// * `hasher_ptr` points to a pointer to a valid Hasher<Sha256> that has been
/// initialized.
/// * `out` is valid to write for 32 bytes.
#[no_mangle]
pub unsafe extern "C" fn efi_sha256_final(
    hasher_ptr: *mut *mut Hasher<'static, Sha256>,
    out: *mut u8,
) {
    // Safety:
    // * It is a precondition that `hasher_ptr` is points to a valid,
    //   initialized Hasher<Sha256> ptr.
    // * It is a precondition that `out` is valid to write for 32 bytes.
    unsafe { efi_sha_final::<Sha256>(hasher_ptr, out) }
}

/// Allocates and initializes a Hasher<Sha512> and return its pointer.
/// Ownership of the Hasher<Sha512> is passed to the caller.
#[no_mangle]
pub extern "C" fn efi_sha512_init() -> *mut Hasher<'static, Sha512> {
    efi_sha_init::<Sha512>()
}

/// Adds data to the Hasher<Sha512> context.
///
/// Safety:
/// * `hasher` points to a valid Hasher<Sha512> that has been initialized.
/// * `data` is valid to read for `len` bytes.
#[no_mangle]
pub unsafe extern "C" fn efi_sha512_update(
    hasher: *mut Hasher<'static, Sha512>,
    data: *const u8,
    len: usize,
) {
    // Safety:
    // * It is a precondition that `hasher` points to a valid,
    //   initialized Hasher<512>.
    // * It is ia precondition that `data` is valid to read for `len` bytes.
    unsafe { efi_sha_update::<Sha512>(hasher, data, len) }
}

/// Returns the digest from a Hasher<Sha512>.
///
/// Safety:
/// * `hasher` points to a pointer to a valid Hasher<Sha512> that has been
/// initialized.
/// * `out` is valid to write for 64 bytes.
#[no_mangle]
pub unsafe extern "C" fn efi_sha512_final(
    hasher_ptr: *mut *mut Hasher<'static, Sha512>,
    out: *mut u8,
) {
    // Safety:
    // * It is a precondition that `hasher_ptr` is points to a valid,
    //   initialized Hasher<Sha256> ptr.
    // * It is a precondition that `out` is valid to write for 32 bytes.
    unsafe { efi_sha_final::<Sha512>(hasher_ptr, out) }
}

#[cfg(test)]
mod test {
    extern crate avb_sysdeps;

    use super::*;
    use crate::{
        hash2::HashAlgorithm,
        protocol::{
            hash2::test::{hash2_call_traces, hash_final, hash_init, hash_update},
            service_binding::test::{
                create_child, destroy_child, reinitialized_service_binding_call_traces,
            },
        },
        test::*,
        DeviceHandle, EfiEntry,
    };
    use efi_types::{EfiHash2Protocol, EfiServiceBindingProtocol, EFI_STATUS_SUCCESS};
    use std::collections::VecDeque;
    use zerocopy::{FromZeros, IntoBytes};

    const DATA: &'static str = "Well if it seems to be real, it' s illusion.";

    struct HashTest<Algorithm: HashAlgorithm> {
        init: extern "C" fn() -> *mut Hasher<'static, Algorithm>,
        update: unsafe extern "C" fn(*mut Hasher<'static, Algorithm>, *const u8, usize),
        r#final: unsafe extern "C" fn(*mut *mut Hasher<'static, Algorithm>, *mut u8),
    }

    fn efi_hash_wrapper_test<Algorithm: HashAlgorithm>(test_struct: HashTest<Algorithm>) {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let handles = [DeviceHandle(1 as *const _)];

            let mut h2_sp = EfiServiceBindingProtocol {
                create_child: Some(create_child),
                destroy_child: Some(destroy_child),
            };

            let mut h2_p = EfiHash2Protocol {
                hash_init: Some(hash_init),
                hash_update: Some(hash_update),
                hash_final: Some(hash_final),
                ..Default::default()
            };

            efi_call_traces().with(|traces| {
                let mut traces = traces.borrow_mut();

                traces.locate_handle_trace.outputs = VecDeque::from([handles.into()]);

                traces.open_protocol_trace.outputs =
                    VecDeque::from([(as_efi_handle(&mut h2_sp), EFI_STATUS_SUCCESS)]);

                let interface = &mut h2_p as *mut _;
                traces.handle_protocol_trace.outputs.push_back(interface as *mut _);
            });

            reinitialized_service_binding_call_traces().with(|traces| {
                let mut traces = traces.borrow_mut();

                traces.create_child_trace.outputs =
                    VecDeque::from([(2 as *const _, EFI_STATUS_SUCCESS)]);
            });

            hash2_call_traces().with(|traces| {
                *traces.borrow_mut() = Default::default();
            });

            // Safety:
            // * `efi_entry` is valid for the duration of this test.
            crate::GLOBAL_EFI_ENTRY
                .with(|e| *e.borrow_mut() = Some(std::ptr::NonNull::from_ref(&efi_entry)));

            let mut hasher = (test_struct.init)();
            let mut digest = Algorithm::DigestType::new_zeroed();
            // Safety:
            // * `hasher` is a valid pointer.
            // * `DATA` is valid to read for `DATA.as_bytes().len()`
            // * `digest` is valid to write for size_of<Algorithm::DigestType>().
            // * It is the caller's responsibility to match the correct
            //   HashAlgorithm type, and init, update, and final values.
            unsafe {
                (test_struct.update)(hasher, DATA.as_bytes().as_ptr(), DATA.as_bytes().len());
                (test_struct.r#final)(
                    std::ptr::from_mut(&mut hasher),
                    digest.as_mut_bytes().as_mut_ptr(),
                );
            }

            hash2_call_traces().with(|traces| {
                let traces = traces.borrow();
                assert_eq!(traces.init.call_count, 1);
                assert_eq!(traces.update.call_count, 1);
                assert_eq!(traces.r#final.call_count, 1);
            });
        });
    }

    #[test]
    fn test_efi_wrapper_sha256() {
        efi_hash_wrapper_test(HashTest::<Sha256> {
            init: efi_sha256_init,
            update: efi_sha256_update,
            r#final: efi_sha256_final,
        })
    }

    #[test]
    fn test_efi_wrapper_sha512() {
        efi_hash_wrapper_test(HashTest::<Sha512> {
            init: efi_sha512_init,
            update: efi_sha512_update,
            r#final: efi_sha512_final,
        })
    }
}
