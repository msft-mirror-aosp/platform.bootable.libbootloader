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

//! Rust wrapper for `EFI_IMAGE_LOADING_PROTOCOL`.

use crate::efi_call;
use crate::protocol::{Protocol, ProtocolInfo};
use arrayvec::ArrayVec;
use core::mem::{size_of, MaybeUninit};
use efi_types::{
    EfiGuid, GblEfiImageBuffer, GblEfiImageInfo, GblEfiImageLoadingProtocol, GblEfiPartitionName,
    PARTITION_NAME_LEN_U16,
};
use liberror::{Error, Result};
use spin::Mutex;

/// GBL_IMAGE_LOADING_PROTOCOL
pub struct GblImageLoadingProtocol;

impl ProtocolInfo for GblImageLoadingProtocol {
    type InterfaceType = GblEfiImageLoadingProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0xdb84b4fa, 0x53bd, 0x4436, [0x98, 0xa7, 0x4e, 0x02, 0x71, 0x42, 0x8b, 0xa8]);
}

/// Max length of partition name in UTF8 in bytes.
pub const PARTITION_NAME_LEN_U8: usize = size_of::<char>() * PARTITION_NAME_LEN_U16;

const MAX_ARRAY_SIZE: usize = 100;
static RETURNED_BUFFERS: Mutex<ArrayVec<usize, MAX_ARRAY_SIZE>> = Mutex::new(ArrayVec::new_const());

/// Wrapper class for buffer received with [get_buffer] function.
///
/// Helps to keep track of allocated memory and avoid getting same buffer more than once.
#[derive(Debug)]
pub struct EfiImageBuffer {
    buffer: Option<&'static mut [MaybeUninit<u8>]>,
}

impl EfiImageBuffer {
    // SAFETY:
    // `gbl_buffer` must represent valid buffer.
    //
    // # Return
    // Err(EFI_STATUS_INVALID_PARAMETER) - If `gbl_buffer.Memory` == NULL
    // Err(EFI_STATUS_ALREADY_STARTED) - Requested buffer was already returned and is still in use.
    // Err(err) - on error
    // Ok(_) - on success
    unsafe fn new(gbl_buffer: GblEfiImageBuffer) -> Result<EfiImageBuffer> {
        if gbl_buffer.Memory.is_null() {
            return Err(Error::InvalidInput);
        }

        let addr = gbl_buffer.Memory as usize;
        let mut returned_buffers = RETURNED_BUFFERS.lock();
        if returned_buffers.contains(&addr) {
            return Err(Error::AlreadyStarted);
        }
        returned_buffers.push(addr);

        // SAFETY:
        // `gbl_buffer.Memory` is guarantied to be not null
        // This code is relying on EFI protocol implementation to provide valid buffer pointer
        // to memory region of size `gbl_buffer.SizeBytes`.
        Ok(EfiImageBuffer {
            buffer: Some(unsafe {
                core::slice::from_raw_parts_mut(
                    gbl_buffer.Memory as *mut MaybeUninit<u8>,
                    gbl_buffer.SizeBytes,
                )
            }),
        })
    }

    /// Move buffer ownership out of EfiImageBuffer, and consume it.
    pub fn take(mut self) -> &'static mut [MaybeUninit<u8>] {
        self.buffer.take().unwrap()
    }
}

impl Drop for EfiImageBuffer {
    fn drop(&mut self) {
        if self.buffer.is_none() {
            return;
        }

        let mut returned_buffers = RETURNED_BUFFERS.lock();
        if let Some(pos) = returned_buffers
            .iter()
            .position(|&val| val == (*self.buffer.as_ref().unwrap()).as_ptr() as usize)
        {
            returned_buffers.swap_remove(pos);
        }
    }
}

// Protocol interface wrappers.
impl Protocol<'_, GblImageLoadingProtocol> {
    /// Wrapper of `GBL_IMAGE_LOADING_PROTOCOL.get_buffer()`
    ///
    /// # Return
    /// Ok(Some(EfiImageBuffer)) if buffer was successfully provided,
    /// Ok(None) if buffer was not provided
    /// Err(Error::EFI_STATUS_BUFFER_TOO_SMALL) if provided buffer is too small
    /// Err(Error::EFI_STATUS_INVALID_PARAMETER) if received buffer is NULL
    /// Err(Error::EFI_STATUS_ALREADY_STARTED) buffer was already returned and is still in use.
    /// Err(err) if `err` occurred
    pub fn get_buffer(&self, gbl_image_info: &GblEfiImageInfo) -> Result<EfiImageBuffer> {
        let mut gbl_buffer: GblEfiImageBuffer = Default::default();
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` and `gbl_buffer` are input/output parameters, outlive the call and
        // will not be retained.
        // `gbl_buffer` returned by this call must not overlap, and will be checked by
        // `EfiImageBuffer`
        unsafe {
            efi_call!(
                @bufsize gbl_image_info.SizeBytes,
                self.interface()?.get_buffer,
                self.interface,
                gbl_image_info,
                &mut gbl_buffer
            )?;
        }

        if gbl_buffer.SizeBytes < gbl_image_info.SizeBytes {
            return Err(Error::BufferTooSmall(Some(gbl_image_info.SizeBytes)));
        }

        // SAFETY:
        // `gbl_buffer.Memory` must be not null. This checked in `new()` call
        // `gbl_buffer.Size` must be valid size of the buffer.
        // This protocol is relying on EFI protocol implementation to provide valid buffer pointer
        // to memory region of size `gbl_buffer.SizeBytes`.
        let image_buffer = unsafe { EfiImageBuffer::new(gbl_buffer)? };

        Ok(image_buffer)
    }

    /// Wrapper of `GBL_IMAGE_LOADING_PROTOCOL.get_verify_partitions()`
    ///
    /// # Result
    /// Err(BufferTooSmall(Some(size))) - when provided `partition_names` is less than expected
    /// `size`
    /// Err(err) - if error occurred.
    /// Ok(len) - will return number of `GblEfiPartitionName`s copied to `partition_names` slice.
    pub fn get_verify_partitions(
        &self,
        partition_names: &mut [GblEfiPartitionName],
    ) -> Result<usize> {
        let partition_count_in: usize = partition_names.len();
        let mut partition_count: usize = partition_count_in;

        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is input parameter, outlives the call, and will not be retained.
        // `partition_count` must be set to valid length of `partition_names` array after the call.
        // `partition_names` must be valid array of length `partition_count` after the call.
        unsafe {
            efi_call!(
                @bufsize partition_count,
                self.interface()?.get_verify_partitions,
                self.interface,
                &mut partition_count,
                partition_names.as_mut_ptr(),
            )?;
        }

        Ok(partition_count)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        protocol::gbl_efi_image_loading::GblImageLoadingProtocol, test::run_test, DeviceHandle,
        EfiEntry,
    };
    use core::{ffi::c_void, iter::zip, ptr::null_mut};
    use efi_types::{
        EfiStatus, EFI_STATUS_BAD_BUFFER_SIZE, EFI_STATUS_BUFFER_TOO_SMALL,
        EFI_STATUS_INVALID_PARAMETER, EFI_STATUS_SUCCESS,
    };

    const UCS2_STR: [u16; 8] = [0x2603, 0x0073, 0x006e, 0x006f, 0x0077, 0x006d, 0x0061, 0x006e];
    const UTF8_STR: &str = "☃snowman";
    const PARTITIONS_MAX: usize = 128;

    fn get_buffer_utf8() -> [[u8; PARTITION_NAME_LEN_U8]; PARTITIONS_MAX] {
        [[0; PARTITION_NAME_LEN_U8]; PARTITIONS_MAX]
    }

    fn get_printable_utf16() -> Vec<u16> {
        (0x0021..0x007e).collect::<Vec<u16>>()
    }

    fn get_printable_string() -> String {
        String::from_utf8((0x21..0x7e).collect::<Vec<u8>>()).unwrap()
    }

    #[test]
    fn test_partition_name_get_str() {
        let mut buffer = [0u8; 100];
        // empty string
        assert_eq!(GblEfiPartitionName::from([0u16]).get_str(&mut buffer).unwrap(), "");
        assert_eq!(GblEfiPartitionName::from([0u16]).get_str(&mut buffer).unwrap(), "");
        assert_eq!(GblEfiPartitionName::from([0x0000]).get_str(&mut buffer[..0]).unwrap(), "");

        // Special characters
        assert_eq!(GblEfiPartitionName::from(UCS2_STR).get_str(&mut buffer).unwrap(), UTF8_STR);

        // Null character in the middle
        assert_eq!(
            GblEfiPartitionName::from([0x006d, 0x0075, 0x0000, 0x0073, 0x0069, 0x0063])
                .get_str(&mut buffer),
            Ok("mu")
        );

        // Null character at the end
        assert_eq!(
            GblEfiPartitionName::from([0x006d, 0x0075, 0x0073, 0x0069, 0x0063, 0x0000])
                .get_str(&mut buffer),
            Ok("music")
        );

        // exact buffer size
        assert_eq!(
            GblEfiPartitionName::from([0x006d, 0x0075, 0x0073, 0x0069, 0x0063])
                .get_str(&mut buffer[..5]),
            Ok("music")
        );
        assert_eq!(
            GblEfiPartitionName::from([0x006d, 0x0075, 0x0000, 0x0073, 0x0069, 0x0063])
                .get_str(&mut buffer[..2]),
            Ok("mu")
        );
    }

    #[test]
    fn test_partition_name_get_str_small_buffer() {
        let mut buffer = [0u8; 8];
        let partition_name: GblEfiPartitionName = UCS2_STR.into();
        assert_eq!(partition_name.get_str(&mut buffer), Err(10usize));
    }

    fn generate_protocol<'a, P: ProtocolInfo>(
        efi_entry: &'a EfiEntry,
        proto: &'a mut P::InterfaceType,
    ) -> Protocol<'a, P> {
        // SAFETY:
        // proto is a valid pointer and lasts at least as long as efi_entry.
        unsafe { Protocol::<'a, P>::new(DeviceHandle::new(null_mut()), proto, efi_entry) }
    }

    #[test]
    fn test_proto_get_partitions_count() {
        const EXPECTED_PARTITIONS_NUM: usize = 2;
        unsafe extern "C" fn get_verify_partitions(
            _: *mut GblEfiImageLoadingProtocol,
            number_of_partitions: *mut usize,
            _: *mut GblEfiPartitionName,
        ) -> EfiStatus {
            assert!(!number_of_partitions.is_null());
            // SAFETY
            // `number_of_partitions` must be valid pointer to usize
            let number_of_partitions = unsafe { number_of_partitions.as_mut() }.unwrap();

            *number_of_partitions = EXPECTED_PARTITIONS_NUM;
            EFI_STATUS_BUFFER_TOO_SMALL
        }

        run_test(|image_handle, systab_ptr| {
            let mut image_loading = GblEfiImageLoadingProtocol {
                get_verify_partitions: Some(get_verify_partitions),
                ..Default::default()
            };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol =
                generate_protocol::<GblImageLoadingProtocol>(&efi_entry, &mut image_loading);

            let mut partitions: [GblEfiPartitionName; 0] = Default::default();
            assert_eq!(
                protocol.get_verify_partitions(&mut partitions).unwrap_err(),
                Error::BufferTooSmall(Some(EXPECTED_PARTITIONS_NUM))
            );
        });
    }

    #[test]
    fn test_proto_get_partitions_count_error() {
        unsafe extern "C" fn get_verify_partitions(
            _: *mut GblEfiImageLoadingProtocol,
            _: *mut usize,
            _: *mut GblEfiPartitionName,
        ) -> EfiStatus {
            EFI_STATUS_INVALID_PARAMETER
        }

        run_test(|image_handle, systab_ptr| {
            let mut image_loading = GblEfiImageLoadingProtocol {
                get_verify_partitions: Some(get_verify_partitions),
                ..Default::default()
            };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol =
                generate_protocol::<GblImageLoadingProtocol>(&efi_entry, &mut image_loading);

            let mut partitions: [GblEfiPartitionName; 0] = Default::default();
            assert_eq!(
                protocol.get_verify_partitions(&mut partitions).unwrap_err(),
                Error::InvalidInput
            );
        });
    }

    #[test]
    fn test_proto_get_partitions_len_and_value() {
        const EXPECTED_PARTITIONS_NUM: usize = 1;
        unsafe extern "C" fn get_verify_partitions(
            _: *mut GblEfiImageLoadingProtocol,
            number_of_partitions: *mut usize,
            partitions: *mut GblEfiPartitionName,
        ) -> EfiStatus {
            // SAFETY
            // `number_of_partitions` must be valid pointer to usize
            let number_of_partitions = unsafe { number_of_partitions.as_mut() }.unwrap();

            match *number_of_partitions {
                n if n < EXPECTED_PARTITIONS_NUM => {
                    *number_of_partitions = EXPECTED_PARTITIONS_NUM;
                    EFI_STATUS_BUFFER_TOO_SMALL
                }
                _ => {
                    // SAFETY
                    // `partitions` must be valid array of size `number_of_partitions`
                    let partitions = unsafe {
                        core::slice::from_raw_parts_mut(partitions, *number_of_partitions)
                    };
                    *number_of_partitions = 1;
                    partitions[0].StrUtf16[..UCS2_STR.len()].copy_from_slice(&UCS2_STR);
                    EFI_STATUS_SUCCESS
                }
            }
        }

        run_test(|image_handle, systab_ptr| {
            let mut buffer_utf8 = get_buffer_utf8();
            let mut image_loading = GblEfiImageLoadingProtocol {
                get_verify_partitions: Some(get_verify_partitions),
                ..Default::default()
            };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol =
                generate_protocol::<GblImageLoadingProtocol>(&efi_entry, &mut image_loading);
            let mut partitions: [GblEfiPartitionName; 2] = Default::default();

            assert_eq!(
                protocol.get_verify_partitions(&mut partitions[..0]).unwrap_err(),
                Error::BufferTooSmall(Some(EXPECTED_PARTITIONS_NUM))
            );
            let verify_partitions_len = protocol.get_verify_partitions(&mut partitions).unwrap();
            assert_eq!(verify_partitions_len, 1);
            assert_eq!(partitions[0].get_str(&mut buffer_utf8[0]), Ok(UTF8_STR));
        });
    }

    #[test]
    fn test_proto_get_partitions_zero_len() {
        const EXPECTED_PARTITIONS_NUM: usize = 1;
        unsafe extern "C" fn get_verify_partitions(
            _: *mut GblEfiImageLoadingProtocol,
            number_of_partitions: *mut usize,
            _: *mut GblEfiPartitionName,
        ) -> EfiStatus {
            // SAFETY
            // `number_of_partitions` must be valid pointer to usize
            let number_of_partitions = unsafe { number_of_partitions.as_mut() }.unwrap();
            assert_eq!(*number_of_partitions, 0);
            *number_of_partitions = EXPECTED_PARTITIONS_NUM;
            EFI_STATUS_BUFFER_TOO_SMALL
        }

        run_test(|image_handle, systab_ptr| {
            let mut image_loading = GblEfiImageLoadingProtocol {
                get_verify_partitions: Some(get_verify_partitions),
                ..Default::default()
            };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol =
                generate_protocol::<GblImageLoadingProtocol>(&efi_entry, &mut image_loading);
            let mut partitions: [GblEfiPartitionName; 0] = Default::default();

            let verify_partitions_res = protocol.get_verify_partitions(&mut partitions);
            assert_eq!(
                verify_partitions_res.unwrap_err(),
                Error::BufferTooSmall(Some(EXPECTED_PARTITIONS_NUM))
            );
        });
    }

    #[test]
    fn test_proto_get_partitions_less_than_buffer() {
        const EXPECTED_PARTITIONS_NUM: usize = 1;
        unsafe extern "C" fn get_verify_partitions(
            _: *mut GblEfiImageLoadingProtocol,
            number_of_partitions: *mut usize,
            partitions: *mut GblEfiPartitionName,
        ) -> EfiStatus {
            // SAFETY
            // `number_of_partitions` must be valid pointer to usize
            let number_of_partitions = unsafe { number_of_partitions.as_mut() }.unwrap();

            assert!(!partitions.is_null());
            assert!(*number_of_partitions > 0);

            // SAFETY
            // `partitions` must be valid array of size `number_of_partitions`
            let partitions =
                unsafe { core::slice::from_raw_parts_mut(partitions, *number_of_partitions) };
            partitions[0].StrUtf16[..UCS2_STR.len()].copy_from_slice(&UCS2_STR);
            *number_of_partitions = EXPECTED_PARTITIONS_NUM;
            EFI_STATUS_SUCCESS
        }

        run_test(|image_handle, systab_ptr| {
            let mut buffer_utf8 = get_buffer_utf8();
            let mut image_loading = GblEfiImageLoadingProtocol {
                get_verify_partitions: Some(get_verify_partitions),
                ..Default::default()
            };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol =
                generate_protocol::<GblImageLoadingProtocol>(&efi_entry, &mut image_loading);
            let mut partitions: [GblEfiPartitionName; 2] = Default::default();

            let verify_partitions_len = protocol.get_verify_partitions(&mut partitions).unwrap();
            assert_eq!(verify_partitions_len, EXPECTED_PARTITIONS_NUM);
            assert_eq!(partitions[0].get_str(&mut buffer_utf8[0]), Ok(UTF8_STR));
        });
    }

    #[test]
    fn test_proto_get_partitions_name_max() {
        unsafe extern "C" fn get_verify_partitions(
            _: *mut GblEfiImageLoadingProtocol,
            number_of_partitions: *mut usize,
            partitions: *mut GblEfiPartitionName,
        ) -> EfiStatus {
            let printable_utf16 = get_printable_utf16();
            // SAFETY
            // `number_of_partitions` must be valid pointer to usize
            let number_of_partitions = unsafe { number_of_partitions.as_mut() }.unwrap();

            assert!(!partitions.is_null());
            assert!(*number_of_partitions > 0);

            // SAFETY
            // `partitions` must be valid array of size `number_of_partitions`
            let partitions =
                unsafe { core::slice::from_raw_parts_mut(partitions, *number_of_partitions) };

            let partition_names: [GblEfiPartitionName; PARTITIONS_MAX] = (0
                ..PARTITION_NAME_LEN_U16)
                .cycle()
                .take(PARTITIONS_MAX)
                .map(|i| printable_utf16[i..i + PARTITION_NAME_LEN_U16].into())
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();

            *number_of_partitions = partition_names.len();

            for (p_out, p_gen) in zip(partitions.iter_mut(), partition_names.iter()) {
                *p_out = *p_gen;
            }

            EFI_STATUS_SUCCESS
        }

        run_test(|image_handle, systab_ptr| {
            let mut buffer_utf8 = get_buffer_utf8();
            let printable_str = get_printable_string();
            let mut image_loading = GblEfiImageLoadingProtocol {
                get_verify_partitions: Some(get_verify_partitions),
                ..Default::default()
            };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol =
                generate_protocol::<GblImageLoadingProtocol>(&efi_entry, &mut image_loading);
            let mut partitions = [GblEfiPartitionName::default(); PARTITIONS_MAX];
            let expected_strs: Vec<&str> = (0..PARTITION_NAME_LEN_U16)
                .cycle()
                .take(PARTITIONS_MAX)
                .map(|i| &printable_str[i..i + PARTITION_NAME_LEN_U16])
                .collect();

            let verify_partitions_len = protocol.get_verify_partitions(&mut partitions).unwrap();
            assert_eq!(verify_partitions_len, PARTITIONS_MAX);

            assert!(zip(partitions.iter(), expected_strs.iter())
                .all(|(p, expected_str)| { p.get_str(&mut buffer_utf8[0]) == Ok(*expected_str) }));
        });
    }

    #[test]
    fn test_proto_get_partitions() {
        const EXPECTED_PARTITIONS_NUM: usize = 2;
        unsafe extern "C" fn get_verify_partitions(
            _: *mut GblEfiImageLoadingProtocol,
            number_of_partitions: *mut usize,
            partitions: *mut GblEfiPartitionName,
        ) -> EfiStatus {
            // SAFETY
            // `number_of_partitions` must be valid pointer to usize
            let number_of_partitions = unsafe { number_of_partitions.as_mut() }.unwrap();

            assert!(!partitions.is_null());
            assert!(*number_of_partitions > 0);

            // SAFETY
            // `partitions` must be valid array of size `number_of_partitions`
            let partitions =
                unsafe { core::slice::from_raw_parts_mut(partitions, *number_of_partitions) };
            partitions[0].StrUtf16[..UCS2_STR.len()].copy_from_slice(&UCS2_STR);
            partitions[1].StrUtf16[..UCS2_STR.len() - 1].copy_from_slice(&UCS2_STR[1..]);
            *number_of_partitions = EXPECTED_PARTITIONS_NUM;
            EFI_STATUS_SUCCESS
        }

        run_test(|image_handle, systab_ptr| {
            let mut buffer_utf8 = get_buffer_utf8();
            let mut image_loading = GblEfiImageLoadingProtocol {
                get_verify_partitions: Some(get_verify_partitions),
                ..Default::default()
            };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol =
                generate_protocol::<GblImageLoadingProtocol>(&efi_entry, &mut image_loading);
            let mut partitions: [GblEfiPartitionName; EXPECTED_PARTITIONS_NUM] = Default::default();

            let verify_partitions_len = protocol.get_verify_partitions(&mut partitions).unwrap();
            assert_eq!(verify_partitions_len, EXPECTED_PARTITIONS_NUM);

            let mut char_idx = UTF8_STR.char_indices();
            char_idx.next();
            let (next_char_pos, _) = char_idx.next().unwrap();

            assert_eq!(partitions[0].get_str(&mut buffer_utf8[0]), Ok(UTF8_STR));
            assert_eq!(partitions[1].get_str(&mut buffer_utf8[1]), Ok(&UTF8_STR[next_char_pos..]));
        });
    }

    #[test]
    fn test_proto_get_partitions_empty() {
        const EXPECTED_PARTITIONS_NUM: usize = 0;
        unsafe extern "C" fn get_verify_partitions(
            _: *mut GblEfiImageLoadingProtocol,
            number_of_partitions: *mut usize,
            partitions: *mut GblEfiPartitionName,
        ) -> EfiStatus {
            // SAFETY
            // `number_of_partitions` must be valid pointer to usize
            let number_of_partitions = unsafe { number_of_partitions.as_mut() }.unwrap();
            assert!(!partitions.is_null());
            *number_of_partitions = EXPECTED_PARTITIONS_NUM;
            EFI_STATUS_SUCCESS
        }

        run_test(|image_handle, systab_ptr| {
            let mut image_loading = GblEfiImageLoadingProtocol {
                get_verify_partitions: Some(get_verify_partitions),
                ..Default::default()
            };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol =
                generate_protocol::<GblImageLoadingProtocol>(&efi_entry, &mut image_loading);
            let mut partitions: [GblEfiPartitionName; 2] = Default::default();

            let verify_partitions_len = protocol.get_verify_partitions(&mut partitions).unwrap();
            assert_eq!(verify_partitions_len, EXPECTED_PARTITIONS_NUM);
        });
    }

    #[test]
    fn test_proto_get_partitions_error() {
        unsafe extern "C" fn get_verify_partitions(
            _: *mut GblEfiImageLoadingProtocol,
            _: *mut usize,
            _: *mut GblEfiPartitionName,
        ) -> EfiStatus {
            EFI_STATUS_BAD_BUFFER_SIZE
        }

        run_test(|image_handle, systab_ptr| {
            let mut image_loading = GblEfiImageLoadingProtocol {
                get_verify_partitions: Some(get_verify_partitions),
                ..Default::default()
            };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol =
                generate_protocol::<GblImageLoadingProtocol>(&efi_entry, &mut image_loading);
            let mut partitions: [GblEfiPartitionName; 1] = Default::default();

            assert!(protocol.get_verify_partitions(&mut partitions).is_err());
        });
    }

    // Mutex to make sure tests that use `static RETURNED_BUFFERS` do not run in parallel to avoid
    // unexpected results since this is global static that would be shared between tests.
    static GET_BUFFER_MUTEX: Mutex<()> = Mutex::new(());
    #[test]
    fn test_proto_get_buffer_error() {
        unsafe extern "C" fn get_buffer(
            _: *mut GblEfiImageLoadingProtocol,
            _: *const GblEfiImageInfo,
            _: *mut GblEfiImageBuffer,
        ) -> EfiStatus {
            EFI_STATUS_INVALID_PARAMETER
        }

        run_test(|image_handle, systab_ptr| {
            let gbl_image_info: GblEfiImageInfo = Default::default();
            let mut image_loading =
                GblEfiImageLoadingProtocol { get_buffer: Some(get_buffer), ..Default::default() };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol =
                generate_protocol::<GblImageLoadingProtocol>(&efi_entry, &mut image_loading);

            assert!(protocol.get_buffer(&gbl_image_info).is_err());
        });
    }

    #[test]
    fn test_proto_get_buffer_not_provided() {
        unsafe extern "C" fn get_buffer(
            _: *mut GblEfiImageLoadingProtocol,
            image_info: *const GblEfiImageInfo,
            buffer: *mut GblEfiImageBuffer,
        ) -> EfiStatus {
            assert!(!image_info.is_null());
            assert!(!buffer.is_null());
            // SAFETY
            // `buffer` must be valid pointer to `GblEfiImageBuffer`
            let buffer = unsafe { buffer.as_mut() }.unwrap();

            buffer.Memory = null_mut();
            buffer.SizeBytes = 10;

            EFI_STATUS_SUCCESS
        }

        run_test(|image_handle, systab_ptr| {
            let gbl_image_info: GblEfiImageInfo = Default::default();
            let mut image_loading =
                GblEfiImageLoadingProtocol { get_buffer: Some(get_buffer), ..Default::default() };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol =
                generate_protocol::<GblImageLoadingProtocol>(&efi_entry, &mut image_loading);

            let res = protocol.get_buffer(&gbl_image_info);
            assert_eq!(res.unwrap_err(), Error::InvalidInput);
        });
    }

    fn get_memory() -> Box<[u8; 100]> {
        Box::new([0; 100])
    }

    #[test]
    fn test_proto_get_buffer_zero_size() {
        unsafe extern "C" fn get_buffer(
            _: *mut GblEfiImageLoadingProtocol,
            image_info: *const GblEfiImageInfo,
            buffer: *mut GblEfiImageBuffer,
        ) -> EfiStatus {
            assert!(!image_info.is_null());
            assert!(!buffer.is_null());
            // SAFETY
            // `buffer` must be valid pointer to `GblEfiImageBuffer`
            let buffer = unsafe { buffer.as_mut() }.unwrap();

            buffer.Memory = Box::leak(get_memory()).as_mut_ptr() as *mut c_void;
            buffer.SizeBytes = 0;

            EFI_STATUS_SUCCESS
        }

        run_test(|image_handle, systab_ptr| {
            let gbl_image_info: GblEfiImageInfo = Default::default();
            let mut image_loading =
                GblEfiImageLoadingProtocol { get_buffer: Some(get_buffer), ..Default::default() };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol =
                generate_protocol::<GblImageLoadingProtocol>(&efi_entry, &mut image_loading);

            let _guard = GET_BUFFER_MUTEX.lock();
            let res = protocol.get_buffer(&gbl_image_info).unwrap();
            assert!(res.buffer.as_ref().unwrap().is_empty());
        });
    }

    #[test]
    fn test_proto_get_buffer_small() {
        unsafe extern "C" fn get_buffer(
            _: *mut GblEfiImageLoadingProtocol,
            image_info: *const GblEfiImageInfo,
            buffer: *mut GblEfiImageBuffer,
        ) -> EfiStatus {
            assert!(!image_info.is_null());
            // SAFETY
            // `image_info` must be valid pointer to `GblEfiImageInfo`
            let image_info = unsafe { image_info.as_ref() }.unwrap();
            assert!(!buffer.is_null());
            // SAFETY
            // `buffer` must be valid pointer to `GblEfiImageBuffer`
            let buffer = unsafe { buffer.as_mut() }.unwrap();

            buffer.Memory = Box::leak(get_memory()).as_mut_ptr() as *mut c_void;
            buffer.SizeBytes = image_info.SizeBytes - 1;

            EFI_STATUS_SUCCESS
        }

        run_test(|image_handle, systab_ptr| {
            let gbl_image_info: GblEfiImageInfo =
                GblEfiImageInfo { ImageType: [0; PARTITION_NAME_LEN_U16], SizeBytes: 10 };
            let mut image_loading =
                GblEfiImageLoadingProtocol { get_buffer: Some(get_buffer), ..Default::default() };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol =
                generate_protocol::<GblImageLoadingProtocol>(&efi_entry, &mut image_loading);

            let _guard = GET_BUFFER_MUTEX.lock();
            let res = protocol.get_buffer(&gbl_image_info);
            assert_eq!(res.unwrap_err(), Error::BufferTooSmall(Some(10)));
        });
    }

    #[test]
    fn test_proto_get_buffer() {
        unsafe extern "C" fn get_buffer(
            _: *mut GblEfiImageLoadingProtocol,
            image_info: *const GblEfiImageInfo,
            buffer: *mut GblEfiImageBuffer,
        ) -> EfiStatus {
            assert!(!image_info.is_null());
            assert!(!buffer.is_null());
            // SAFETY
            // `buffer` must be valid pointer to `GblEfiImageBuffer`
            let buffer = unsafe { buffer.as_mut() }.unwrap();

            let mem = get_memory();
            buffer.SizeBytes = mem.len();
            buffer.Memory = Box::leak(mem).as_mut_ptr() as *mut c_void;

            EFI_STATUS_SUCCESS
        }

        run_test(|image_handle, systab_ptr| {
            let gbl_image_info: GblEfiImageInfo =
                GblEfiImageInfo { ImageType: [0; PARTITION_NAME_LEN_U16], SizeBytes: 100 };
            let mut image_loading =
                GblEfiImageLoadingProtocol { get_buffer: Some(get_buffer), ..Default::default() };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol =
                generate_protocol::<GblImageLoadingProtocol>(&efi_entry, &mut image_loading);

            let _guard = GET_BUFFER_MUTEX.lock();
            let buf = protocol.get_buffer(&gbl_image_info).unwrap();
            assert_ne!(buf.buffer.as_ref().unwrap().as_ptr(), null_mut());
            assert_eq!(buf.buffer.as_ref().unwrap().len(), 100);
        });
    }

    #[test]
    fn test_proto_get_buffer_image_type() {
        const IMAGE_TYPE_STR: &'static str = "test";
        unsafe extern "C" fn get_buffer(
            _: *mut GblEfiImageLoadingProtocol,
            image_info: *const GblEfiImageInfo,
            buffer: *mut GblEfiImageBuffer,
        ) -> EfiStatus {
            assert!(!image_info.is_null());
            // SAFETY
            // `image_info` must be valid pointer to `GblEfiImageInfo`
            let image_info = unsafe { image_info.as_ref() }.unwrap();
            assert!(!buffer.is_null());
            // SAFETY
            // `buffer` must be valid pointer to `GblEfiImageBuffer`
            let buffer = unsafe { buffer.as_mut() }.unwrap();

            let mut buffer_utf8 = [0u8; 100];
            assert_eq!(
                GblEfiPartitionName::from(image_info.ImageType).get_str(&mut buffer_utf8).unwrap(),
                IMAGE_TYPE_STR
            );

            let mem = get_memory();
            buffer.SizeBytes = mem.len();
            buffer.Memory = Box::leak(mem).as_mut_ptr() as *mut c_void;

            EFI_STATUS_SUCCESS
        }

        run_test(|image_handle, systab_ptr| {
            let mut image_type = [0u16; PARTITION_NAME_LEN_U16];
            image_type[..4].copy_from_slice(&IMAGE_TYPE_STR.encode_utf16().collect::<Vec<u16>>());
            let gbl_image_info: GblEfiImageInfo =
                GblEfiImageInfo { ImageType: image_type, SizeBytes: 100 };
            let mut image_loading =
                GblEfiImageLoadingProtocol { get_buffer: Some(get_buffer), ..Default::default() };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol =
                generate_protocol::<GblImageLoadingProtocol>(&efi_entry, &mut image_loading);

            let _guard = GET_BUFFER_MUTEX.lock();
            let res = protocol.get_buffer(&gbl_image_info);
            assert!(res.is_ok());
        });
    }

    #[test]
    fn test_proto_get_buffer_double_call() {
        unsafe extern "C" fn get_buffer(
            _: *mut GblEfiImageLoadingProtocol,
            image_info: *const GblEfiImageInfo,
            buffer: *mut GblEfiImageBuffer,
        ) -> EfiStatus {
            assert!(!image_info.is_null());
            assert!(!buffer.is_null());
            // SAFETY
            // `buffer` must be valid pointer to `GblEfiImageBuffer`
            let buffer = unsafe { buffer.as_mut() }.unwrap();

            let mem = get_memory();
            buffer.SizeBytes = mem.len();
            buffer.Memory = 0x1000 as *mut c_void;

            EFI_STATUS_SUCCESS
        }

        run_test(|image_handle, systab_ptr| {
            let gbl_image_info: GblEfiImageInfo =
                GblEfiImageInfo { ImageType: [0; PARTITION_NAME_LEN_U16], SizeBytes: 100 };
            let mut image_loading =
                GblEfiImageLoadingProtocol { get_buffer: Some(get_buffer), ..Default::default() };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol =
                generate_protocol::<GblImageLoadingProtocol>(&efi_entry, &mut image_loading);

            let _guard = GET_BUFFER_MUTEX.lock();
            let _buf = protocol.get_buffer(&gbl_image_info).unwrap();
            assert_eq!(protocol.get_buffer(&gbl_image_info).unwrap_err(), Error::AlreadyStarted);
        });
    }

    #[test]
    fn test_proto_get_buffer_double_call_after_drop() {
        unsafe extern "C" fn get_buffer(
            _: *mut GblEfiImageLoadingProtocol,
            image_info: *const GblEfiImageInfo,
            buffer: *mut GblEfiImageBuffer,
        ) -> EfiStatus {
            assert!(!image_info.is_null());
            assert!(!buffer.is_null());
            // SAFETY
            // `buffer` must be valid pointer to `GblEfiImageBuffer`
            let buffer = unsafe { buffer.as_mut() }.unwrap();

            let mem = get_memory();
            buffer.SizeBytes = mem.len();
            buffer.Memory = 0x2000 as *mut c_void;

            EFI_STATUS_SUCCESS
        }

        run_test(|image_handle, systab_ptr| {
            let gbl_image_info: GblEfiImageInfo =
                GblEfiImageInfo { ImageType: [0; PARTITION_NAME_LEN_U16], SizeBytes: 100 };
            let mut image_loading =
                GblEfiImageLoadingProtocol { get_buffer: Some(get_buffer), ..Default::default() };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol =
                generate_protocol::<GblImageLoadingProtocol>(&efi_entry, &mut image_loading);

            let _guard = GET_BUFFER_MUTEX.lock();
            protocol.get_buffer(&gbl_image_info).unwrap();
            protocol.get_buffer(&gbl_image_info).unwrap();
        });
    }

    #[test]
    #[should_panic]
    fn test_proto_get_buffer_too_many_times() {
        unsafe extern "C" fn get_buffer(
            _: *mut GblEfiImageLoadingProtocol,
            image_info: *const GblEfiImageInfo,
            buffer: *mut GblEfiImageBuffer,
        ) -> EfiStatus {
            assert!(!image_info.is_null());
            assert!(!buffer.is_null());
            // SAFETY
            // `buffer` must be valid pointer to `GblEfiImageBuffer`
            let buffer = unsafe { buffer.as_mut() }.unwrap();

            let mem = get_memory();
            buffer.SizeBytes = mem.len();
            // Make sure to return different memory
            buffer.Memory = Box::leak(get_memory()).as_mut_ptr() as *mut c_void;

            EFI_STATUS_SUCCESS
        }

        run_test(|image_handle, systab_ptr| {
            let gbl_image_info: GblEfiImageInfo =
                GblEfiImageInfo { ImageType: [0; PARTITION_NAME_LEN_U16], SizeBytes: 100 };
            let mut image_loading =
                GblEfiImageLoadingProtocol { get_buffer: Some(get_buffer), ..Default::default() };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol =
                generate_protocol::<GblImageLoadingProtocol>(&efi_entry, &mut image_loading);

            let _guard = GET_BUFFER_MUTEX.lock();
            let mut keep_alive: Vec<EfiImageBuffer> = vec![];
            for _ in 1..=MAX_ARRAY_SIZE + 1 {
                keep_alive.push(protocol.get_buffer(&gbl_image_info).unwrap());
            }
        });
    }

    #[test]
    fn test_efi_image_buffer() {
        let mut v = vec![0u8; 1];
        let gbl_buffer =
            GblEfiImageBuffer { Memory: v.as_mut_ptr() as *mut c_void, SizeBytes: v.len() };

        let _guard = GET_BUFFER_MUTEX.lock();
        // SAFETY:
        // 'gbl_buffer` represents valid buffer created by vector.
        let res = unsafe { EfiImageBuffer::new(gbl_buffer) };
        assert!(res.is_ok());
    }

    #[test]
    fn test_efi_image_buffer_null() {
        let gbl_buffer = GblEfiImageBuffer { Memory: null_mut(), SizeBytes: 1 };

        let _guard = GET_BUFFER_MUTEX.lock();
        // SAFETY:
        // 'gbl_buffer` contains Memory == NULL, which is valid input value. And we expect Error as
        // a result
        let res = unsafe { EfiImageBuffer::new(gbl_buffer) };
        assert_eq!(res.unwrap_err(), Error::InvalidInput);
    }

    #[test]
    fn test_efi_image_buffer_same_buffer() {
        let mut v = vec![0u8; 1];
        let gbl_buffer =
            GblEfiImageBuffer { Memory: v.as_mut_ptr() as *mut c_void, SizeBytes: v.len() };

        let _guard = GET_BUFFER_MUTEX.lock();
        // SAFETY:
        // 'gbl_buffer` represents valid buffer created by vector.
        let res1 = unsafe { EfiImageBuffer::new(gbl_buffer) };
        assert!(res1.is_ok());

        // Since we keep `res1`, second return of same buffer should fail
        // SAFETY:
        // 'gbl_buffer` represents valid buffer created by vector.
        let res2 = unsafe { EfiImageBuffer::new(gbl_buffer) };
        assert_eq!(res2.unwrap_err(), Error::AlreadyStarted);
    }

    #[test]
    fn test_efi_image_buffer_same_buffer_after_drop() {
        let mut v = vec![0u8; 1];
        let gbl_buffer =
            GblEfiImageBuffer { Memory: v.as_mut_ptr() as *mut c_void, SizeBytes: v.len() };

        let _guard = GET_BUFFER_MUTEX.lock();
        // SAFETY:
        // 'gbl_buffer` represents valid buffer created by vector.
        let res1 = unsafe { EfiImageBuffer::new(gbl_buffer) };
        drop(res1);

        // Since `res1` was dropped same buffer can be returned.
        // SAFETY:
        // 'gbl_buffer` represents valid buffer created by vector.
        let res2 = unsafe { EfiImageBuffer::new(gbl_buffer) };
        assert!(res2.is_ok());
    }

    #[test]
    fn test_efi_image_buffer_take() {
        let mut v = vec![0u8; 1];
        let gbl_buffer =
            GblEfiImageBuffer { Memory: v.as_mut_ptr() as *mut c_void, SizeBytes: v.len() };

        let _guard = GET_BUFFER_MUTEX.lock();
        // SAFETY:
        // 'gbl_buffer` represents valid buffer created by vector.
        let res1 = unsafe { EfiImageBuffer::new(gbl_buffer) }.unwrap();
        let _tmp = res1.take();

        // Since `res1` was taken, we can't reuse same buffer.
        // SAFETY:
        // 'gbl_buffer` represents valid buffer created by vector.
        let res2 = unsafe { EfiImageBuffer::new(gbl_buffer) };
        assert_eq!(res2.unwrap_err(), Error::AlreadyStarted);
    }
}
