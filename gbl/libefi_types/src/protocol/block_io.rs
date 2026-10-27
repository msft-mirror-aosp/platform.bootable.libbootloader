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

//! Rust trait for
//! [`EFI_BLOCK_IO_PROTOCOL`](https://uefi.org/specs/UEFI/2.10/13_Protocols_Media_Access.html#block-i-o-protocol).

use crate::{
    defs::{EfiBlockIoMedia, EfiBlockIoProtocol, EfiGuid, EfiStatus, EfiTpl, EFI_TPL_CALLBACK},
    protocol::{slice_from_raw_parts, slice_from_raw_parts_mut, BridgeToRust, Client, Provider},
    status::{EfiError, EfiResult},
    tpl::TplLocked,
    Identified,
};
use core::mem::MaybeUninit;

impl Identified for EfiBlockIoProtocol {
    const GUID: EfiGuid = EfiGuid::from_u64s(
        crate::defs::EFI_BLOCK_IO_PROTOCOL_GUID_U64_0,
        crate::defs::EFI_BLOCK_IO_PROTOCOL_GUID_U64_1,
    );
}

/// Protocol Rust API.
///
/// # Safety
///
/// The implementation must adhere to the UEFI protocol specification.
///
/// ## Concurrency
///
/// Block I/O protocol is supported at `TPL_CALLBACK` and below, which means
/// for UEFI environments the TPL should be raised to at least this level
/// before trying to access any mutable state.
///
/// See [Provider] docs for details on concurrency in UEFI.
///
/// ## [BlockIo::media()]
///
/// The returned reference must not be invalidated by any protocol methods.
/// This is necessary because the C struct holds a pointer to the data.
/// See [BridgeToRust] safety docs for details on pointers in protocols.
///
/// ## [BlockIo::read_blocks()]
///
/// The implementation must guarantee that:
///
/// * the data is never uninitialized (e.g. via [MaybeUninit::uninit()])
/// * if successful, the entire buffer must have been filled
#[cfg_attr(feature = "mocks", mockall::automock)]
pub unsafe trait BlockIo {
    /// Returns the protocol revision that the implementation is providing.
    fn revision(&self) -> u64;

    /// Returns the current media information.
    ///
    /// # Safety
    ///
    /// The protocol spec indicates this data may be modified during calls into
    /// this protocol. To prevent data races with other clients making calls
    /// that might modify this data, the caller must enter a critical section
    /// to lock this data during any access.
    ///
    /// For UEFI environments: raise the TPL to `TPL_CALLBACK` or above.
    unsafe fn media<'a>(&'a self) -> EfiResult<&'a EfiBlockIoMedia>;

    /// Resets the block device.
    fn reset(&self, extended_verification: bool) -> EfiResult<()>;

    /// Reads blocks from the device.
    ///
    /// We use [MaybeUninit] here because UEFI does not guarantee that the
    /// caller has initialized this buffer, and there are cases where GBL
    /// does provide uninitialized data here for efficiency.
    ///
    /// For the client, if this function returns successfully, the buffer has
    /// been initialized.
    ///
    /// For the provider, it is not safe to convert `buffer` directly to a
    /// `&mut [u8]` slice; see [MaybeUninit] docs for details. Expected usage is
    /// to get the raw pointer with [MaybeUninit::as_mut_ptr] and pass that
    /// pointer into the underlying disk I/O mechanisms.
    fn read_blocks(&self, media_id: u32, lba: u64, buffer: &mut [MaybeUninit<u8>])
        -> EfiResult<()>;

    /// Writes blocks to the device.
    fn write_blocks(&self, media_id: u32, lba: u64, buffer: &[u8]) -> EfiResult<()>;

    /// Flushes any buffered blocks to the device.
    fn flush_blocks(&self) -> EfiResult<()>;
}

// SAFETY: UEFI spec says Block I/O protocol supports <= `EFI_TPL_CALLBACK`.
unsafe impl TplLocked for Client<EfiBlockIoProtocol> {
    const MAX_TPL: EfiTpl = EFI_TPL_CALLBACK;
}

/// Client-side implementation.
///
/// SAFETY:
/// * we adhere to the spec since we're just forwarding calls into the
///   protocol struct which itself adheres to the spec
/// * the [media] returned reference is never invalidated since we never modify
///   the pointer and the protocol guarantees it will stay valid
unsafe impl BlockIo for Client<EfiBlockIoProtocol> {
    fn revision(&self) -> u64 {
        self.0.revision
    }

    unsafe fn media(&self) -> EfiResult<&EfiBlockIoMedia> {
        // SAFETY:
        // * protocol spec guarantees `media` pointer is valid
        // * function safety requires the caller lock the protocol so it
        //   cannot be modified
        let media = unsafe { self.0.media.as_ref() }.ok_or(EfiError::NotFound)?;
        Ok(media)
    }

    fn reset(&self, extended_verification: bool) -> EfiResult<()> {
        let func = self.0.reset.ok_or(EfiError::NotFound)?;
        // SAFETY:
        // * `self.0` is only borrowed for the duration of the call
        unsafe { func(self.0 as *const _ as *mut _, extended_verification) }.into()
    }

    fn read_blocks(
        &self,
        media_id: u32,
        lba: u64,
        buffer: &mut [MaybeUninit<u8>],
    ) -> EfiResult<()> {
        let func = self.0.read_blocks.ok_or(EfiError::NotFound)?;
        // SAFETY:
        // * `self.0` is only borrowed for the duration of the call
        // * `buffer` will only be written up to `buffer.len()` and is only
        //   borrowed for the duration of the call
        unsafe {
            func(
                self.0 as *const _ as *mut _,
                media_id,
                lba,
                buffer.len(),
                buffer.as_mut_ptr() as *mut _,
            )
        }
        .into()
    }

    fn write_blocks(&self, media_id: u32, lba: u64, buffer: &[u8]) -> EfiResult<()> {
        let func = self.0.write_blocks.ok_or(EfiError::NotFound)?;
        // SAFETY:
        // * `self.0` is only borrowed for the duration of the call
        // * `buffer` will only be read up to `buffer.len()`, is only borrowed
        //   for the duration of the call, and will not be modified
        unsafe {
            func(
                self.0 as *const _ as *mut _,
                media_id,
                lba,
                buffer.len(),
                buffer.as_ptr() as *mut _,
            )
        }
        .into()
    }

    fn flush_blocks(&self) -> EfiResult<()> {
        let func = self.0.flush_blocks.ok_or(EfiError::NotFound)?;
        // SAFETY:
        // * `self.0` is only borrowed for the duration of the call
        unsafe { func(self.0 as *const _ as *mut _) }.into()
    }
}

// SAFETY:
// * our wrapper functions adhere to the protocol spec
// * [BlockIo] safety guarantees the [BlockIo::media] pointer stays valid
unsafe impl<R: BlockIo> BridgeToRust<R> for EfiBlockIoProtocol {
    unsafe fn create_bridge(rust_impl: &R) -> Self {
        Self {
            revision: rust_impl.revision(),
            // SAFETY: we are only accessing the pointer here which is
            // required by [BlockIo] safety to remain valid and unchanged, so
            // we don't need a critical section.
            media: unsafe { rust_impl.media() }.unwrap() as *const _ as *mut EfiBlockIoMedia,
            reset: Some(Provider::<_, R>::reset_wrapper),
            read_blocks: Some(Provider::<_, R>::read_blocks_wrapper),
            write_blocks: Some(Provider::<_, R>::write_blocks_wrapper),
            flush_blocks: Some(Provider::<_, R>::flush_blocks_wrapper),
        }
    }
}

impl<R: BlockIo> Provider<'_, EfiBlockIoProtocol, R> {
    unsafe extern "efiapi" fn reset_wrapper(
        this: *mut EfiBlockIoProtocol,
        extended_verification: bool,
    ) -> EfiStatus {
        // SAFETY: `this` is the C interface pointer from [Provider::to_ptr()].
        let rust_impl = unsafe { Self::to_rust(this) };
        rust_impl.reset(extended_verification).into()
    }

    unsafe extern "efiapi" fn read_blocks_wrapper(
        this: *mut EfiBlockIoProtocol,
        media_id: u32,
        lba: u64,
        buffer_size: usize,
        buffer: *mut core::ffi::c_void,
    ) -> EfiStatus {
        // SAFETY: `this` is the C interface pointer from [Provider::to_ptr()].
        let rust_impl = unsafe { Self::to_rust(this) };
        (|| {
            // SAFETY: The Block I/O spec requires `buffer` to be valid for writes of `buffer_size`
            // bytes for the duration of this call, and nothing else accesses it until we return.
            // `MaybeUninit<u8>` has no initialization requirement.
            let buffer =
                unsafe { slice_from_raw_parts_mut(buffer as *mut MaybeUninit<u8>, buffer_size)? };
            rust_impl.read_blocks(media_id, lba, buffer)
        })()
        .into()
    }

    unsafe extern "efiapi" fn write_blocks_wrapper(
        this: *mut EfiBlockIoProtocol,
        media_id: u32,
        lba: u64,
        buffer_size: usize,
        buffer: *mut core::ffi::c_void,
    ) -> EfiStatus {
        // SAFETY: `this` is the C interface pointer from [Provider::to_ptr()].
        let rust_impl = unsafe { Self::to_rust(this) };
        (|| {
            // SAFETY: The Block I/O spec requires `buffer` to be valid for reads of `buffer_size`
            // initialized bytes that are not modified for the duration of this call.
            let buffer = unsafe { slice_from_raw_parts(buffer as *const u8, buffer_size)? };
            rust_impl.write_blocks(media_id, lba, buffer)
        })()
        .into()
    }

    unsafe extern "efiapi" fn flush_blocks_wrapper(this: *mut EfiBlockIoProtocol) -> EfiStatus {
        // SAFETY: `this` is the C interface pointer from [Provider::to_ptr()].
        let rust_impl = unsafe { Self::to_rust(this) };
        rust_impl.flush_blocks().into()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::protocol::test::{buffer_range, TestProtocolTunnel};
    use std::{iter::zip, mem::transmute};

    const TEST_REVISION: u64 = 0x1234;

    const TEST_MEDIA: EfiBlockIoMedia = EfiBlockIoMedia {
        media_id: 1,
        removable_media: false,
        media_present: true,
        logical_partition: true,
        read_only: false,
        write_caching: false,
        block_size: 1024,
        io_align: 0,
        last_block: 4096,
        lowest_aligned_lba: 0,
        logical_blocks_per_physical_block: 0,
        optimal_transfer_length_granularity: 0,
    };

    /// Creates a [MockBlockIo] with default expectations set up so that it can
    /// be used as a [Provider].
    fn create_mock() -> MockBlockIo {
        let mut mock = MockBlockIo::new();
        mock.expect_revision().return_const(TEST_REVISION);
        mock.expect_media().return_const(Ok(&TEST_MEDIA));
        mock
    }

    #[test]
    fn register() {
        let mock = create_mock();
        let tunnel = TestProtocolTunnel::new(&mock);

        assert_eq!(tunnel.client().revision(), TEST_REVISION);
        // SAFETY: this is the only client so there is no data race.
        assert_eq!(unsafe { tunnel.client().media() }, Ok(&TEST_MEDIA));
    }

    #[test]
    fn reset_success() {
        const TEST_EXTENDED_VERIFICATION: bool = true;

        let mut mock = create_mock();
        mock.expect_reset().returning(|extended_verification| {
            assert_eq!(extended_verification, TEST_EXTENDED_VERIFICATION);
            Ok(())
        });
        let tunnel = TestProtocolTunnel::new(&mock);

        assert_eq!(tunnel.client().reset(TEST_EXTENDED_VERIFICATION), Ok(()));
    }

    #[test]
    fn reset_failure() {
        let mut mock = create_mock();
        mock.expect_reset().returning(|_| Err(EfiError::NoMedia));
        let tunnel = TestProtocolTunnel::new(&mock);

        assert_eq!(tunnel.client().reset(true), Err(EfiError::NoMedia));
    }

    #[test]
    fn read_blocks_success() {
        const TEST_MEDIA_ID: u32 = 5;
        const TEST_LBA: u64 = 20;
        const TEST_BUFFER: &[u8] = &[1, 2, 3, 4, 5, 6, 7, 8];

        let mut buffer = [MaybeUninit::uninit(); TEST_BUFFER.len()];
        let expected_range = buffer_range(&buffer);

        // Mock read_blocks() to fill the given buffer with `TEST_BUFFER`.
        let mut mock = create_mock();
        mock.expect_read_blocks().returning(
            move |media_id: u32, lba: u64, buffer: &mut [MaybeUninit<u8>]| {
                assert_eq!(media_id, TEST_MEDIA_ID);
                assert_eq!(lba, TEST_LBA);
                // Make sure the right buffer got passed through.
                assert_eq!(buffer_range(buffer), expected_range);
                // Write bytes one-by-one so we don't need unsafe.
                for (source, dest) in zip(TEST_BUFFER, buffer) {
                    dest.write(*source);
                }
                Ok(())
            },
        );
        let tunnel = TestProtocolTunnel::new(&mock);

        assert_eq!(tunnel.client().read_blocks(TEST_MEDIA_ID, TEST_LBA, &mut buffer), Ok(()));
        // SAFETY:
        // * `[MaybeUninit<u8>]` is safe to transmute to `u8` once the data has
        //   been initialized
        // * `read_blocks()` returning successfully means the buffer been fully
        //   initialized
        //
        // TODO: use `MaybeUninit::array_assume_init()` instead of
        // `mem::transmute()` once it has stabilized.
        let buffer = unsafe { transmute::<[MaybeUninit<u8>; 8], [u8; 8]>(buffer) };
        assert_eq!(buffer, TEST_BUFFER);
    }

    #[test]
    fn read_blocks_failure() {
        let mut mock = create_mock();
        mock.expect_read_blocks().returning(|_, _, _| Err(EfiError::NoMedia));
        let tunnel = TestProtocolTunnel::new(&mock);

        assert_eq!(tunnel.client().read_blocks(0, 0, &mut []), Err(EfiError::NoMedia));
    }

    #[test]
    fn write_blocks_success() {
        const TEST_MEDIA_ID: u32 = 5;
        const TEST_LBA: u64 = 20;
        const TEST_BUFFER: &[u8] = &[1, 2, 3, 4, 5, 6, 7, 8];

        // Mock write_blocks() to assert that the given buffer is `TEST_BUFFER`.
        let mut mock = create_mock();
        mock.expect_write_blocks().returning(|media_id: u32, lba: u64, buffer: &[u8]| {
            assert_eq!(media_id, TEST_MEDIA_ID);
            assert_eq!(lba, TEST_LBA);
            // Make sure the right buffer got passed through.
            assert_eq!(buffer_range(buffer), buffer_range(TEST_BUFFER));
            Ok(())
        });
        let tunnel = TestProtocolTunnel::new(&mock);

        assert_eq!(tunnel.client().write_blocks(TEST_MEDIA_ID, TEST_LBA, TEST_BUFFER), Ok(()));
    }

    #[test]
    fn write_blocks_failure() {
        let mut mock = create_mock();
        mock.expect_write_blocks().returning(|_, _, _| Err(EfiError::NoMedia));
        let tunnel = TestProtocolTunnel::new(&mock);

        assert_eq!(tunnel.client().write_blocks(0, 0, &[]), Err(EfiError::NoMedia));
    }

    #[test]
    fn flush_blocks_success() {
        let mut mock = create_mock();
        mock.expect_flush_blocks().returning(|| Ok(()));
        let tunnel = TestProtocolTunnel::new(&mock);

        assert_eq!(tunnel.client().flush_blocks(), Ok(()));
    }

    #[test]
    fn flush_blocks_failure() {
        let mut mock = create_mock();
        mock.expect_flush_blocks().returning(|| Err(EfiError::NoMedia));
        let tunnel = TestProtocolTunnel::new(&mock);

        assert_eq!(tunnel.client().flush_blocks(), Err(EfiError::NoMedia));
    }
}
