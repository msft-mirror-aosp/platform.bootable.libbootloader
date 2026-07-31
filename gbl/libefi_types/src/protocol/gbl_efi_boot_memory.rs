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
//! [`GBL_EFI_BOOT_MEMORY_PROTOCOL`](https://android.googlesource.com/platform/bootable/libbootloader/+/refs/heads/gbl-mainline/gbl/docs/gbl_efi_boot_memory_protocol.md).

use alloc::{borrow::ToOwned, collections::BTreeMap, ffi::CString};
use core::{
    ffi::{c_void, CStr},
    ops::DerefMut,
};
use spin::Mutex;

use crate::{
    defs::{
        EfiGuid, EfiStatus, GblEfiBootBufferType, GblEfiBootMemoryProtocol,
        GblEfiPartitionBufferFlag,
    },
    protocol::{BridgeToRust, Provider},
    status::{EfiError, EfiResult},
    Identified,
};

/// Partition buffer
pub struct PartitionBuffer {
    /// Size of the buffer.
    pub size: usize,
    /// Pointer to the buffer.
    pub buffer: *mut c_void,
    /// Flag indicating the type of the buffer.
    pub flag: GblEfiPartitionBufferFlag,
}

/// Protocol Rust API for `GBL_EFI_BOOT_MEMORY_PROTOCOL`.
///
/// # Safety
///
/// * Buffers returned by `get_boot_buffer` should be considered retained by the caller. It
///   should remain valid and not be accessed by the implementing object once returned.
/// * Buffers returned by `get_partition_buffer` should be considered retained by the
///   caller until `sync_partition_buffer` is called. Implementing object should prevent from
///   accessing it before `sync_partition_buffer` is called.
pub unsafe trait GblEfiBootMemory {
    /// Returns the protocol revision that the implementation is providing.
    fn revision(&self) -> u64;

    /// Implementation of `GBL_EFI_BOOT_MEMORY_PROTOCOL.SyncPartitionBuffer`.
    ///
    /// # Args
    ///
    /// * `sync_preloaded`: Whether to sync preloaded partitions.
    ///
    /// # Safety
    ///
    /// Caller must ensures that all buffer previously returned by `get_partition_buffer`
    /// are no longer in use.
    unsafe fn sync_partition_buffer(&self, sync_preloaded: bool) -> EfiResult<()>;

    /// Implementation of `GBL_EFI_BOOT_MEMORY_PROTOCOL.GetPartitionBuffer`.
    ///
    /// # Args
    ///
    /// * `base_name`: The base name of the partition to get the buffer for.
    ///
    /// # Returns
    ///
    /// `Ok(PartitionBuffer)` if the partition buffer was found.
    fn get_partition_buffer(&self, base_name: &CStr) -> EfiResult<PartitionBuffer>;

    /// Implementation of `GBL_EFI_BOOT_MEMORY_PROTOCOL.GetBootBuffer`.
    ///
    /// # Args
    ///
    /// * `buffer_type`: The type of the boot buffer to get.
    ///
    /// # Returns
    ///
    /// `Ok((size, buffer))` if the boot buffer was found.
    fn get_boot_buffer(&self, buffer_type: GblEfiBootBufferType)
        -> EfiResult<(usize, *mut c_void)>;
}

impl Identified for GblEfiBootMemoryProtocol {
    const GUID: EfiGuid =
        EfiGuid::new(0x309f2874, 0xad59, 0x4fd2, [0xaf, 0x5e, 0xce, 0x0f, 0x4a, 0xb4, 0x01, 0xa6]);
}

// SAFETY:
// * our wrapper functions adhere to the protocol spec
unsafe impl<R: GblEfiBootMemory> BridgeToRust<R> for GblEfiBootMemoryProtocol {
    unsafe fn create_bridge(rust_impl: &R) -> Self {
        Self {
            revision: rust_impl.revision(),
            sync_partition_buffer: Some(Provider::<_, R>::sync_partition_buffer),
            get_partition_buffer: Some(Provider::<_, R>::get_partition_buffer),
            get_boot_buffer: Some(Provider::<_, R>::get_boot_buffer),
        }
    }
}

impl<R: GblEfiBootMemory> Provider<'_, GblEfiBootMemoryProtocol, R> {
    unsafe extern "efiapi" fn get_boot_buffer(
        interface: *mut GblEfiBootMemoryProtocol,
        buffer_type: GblEfiBootBufferType,
        out_size: *mut usize,
        out_buffer: *mut *mut c_void,
    ) -> EfiStatus {
        (|| {
            // SAFETY: `interface` is the C interface pointer from [Provider::to_ptr()].
            let rust_impl = unsafe { Self::to_rust(interface) };
            // SAFETY: By UEFI spec, `out_size` and `out_buffer` point to valid
            // output parameters.
            let (Some(out_size), Some(out_buffer)) =
                (unsafe { (out_size.as_mut(), out_buffer.as_mut()) })
            else {
                return Err(EfiError::InvalidParameter);
            };
            let (size, buffer) = rust_impl.get_boot_buffer(buffer_type)?;
            *out_size = size;
            *out_buffer = buffer as _;
            Ok(())
        })()
        .into()
    }

    unsafe extern "efiapi" fn sync_partition_buffer(
        interface: *mut GblEfiBootMemoryProtocol,
        sync_preloaded: bool,
    ) -> EfiStatus {
        // SAFETY: `interface` is the C interface pointer from [Provider::to_ptr()].
        let rust_impl = unsafe { Self::to_rust(interface) };
        // SAFETY: By UEFI spec of this API, caller is not longer using any buffer returned by
        // `get_boot_buffer_registry`.
        unsafe { rust_impl.sync_partition_buffer(sync_preloaded) }.into()
    }

    unsafe extern "efiapi" fn get_partition_buffer(
        interface: *mut GblEfiBootMemoryProtocol,
        base_name: *const u8,
        out_size: *mut usize,
        out_buffer: *mut *mut c_void,
        out_flag: *mut GblEfiPartitionBufferFlag,
    ) -> EfiStatus {
        (|| {
            // SAFETY: `interface` is the C interface pointer from [Provider::to_ptr()].
            let rust_impl = unsafe { Self::to_rust(interface) };
            // SAFETY: By UEFI spec, `base_name` is a pointer to a null-terminated string.
            let base_name = unsafe { CStr::from_ptr(base_name as _) };
            // SAFETY: By UEFI spec, `out_size`, `out_buffer`, and `out_flag` point to valid
            // output parameters.
            let (Some(out_size), Some(out_buffer), Some(out_flag)) =
                (unsafe { (out_size.as_mut(), out_buffer.as_mut(), out_flag.as_mut()) })
            else {
                return Err(EfiError::InvalidParameter);
            };
            let partition_buffer = rust_impl.get_partition_buffer(base_name)?;
            *out_size = partition_buffer.size;
            *out_buffer = partition_buffer.buffer;
            *out_flag = partition_buffer.flag;
            Ok(())
        })()
        .into()
    }
}

/// Boot buffer type for return by GblEfiBootMemorySafe::take_boot_buffer`.
pub enum BootBuffer {
    /// Static boot buffer.
    Static(&'static [u8]),
    /// Boot buffer to be allocated.
    ToAllocate(usize),
}

/// Safe variant of `GblEfiBootMemory`.
pub trait GblEfiBootMemorySafe {
    /// Partition buffer type.
    type PartitionBuffer: DerefMut<Target = [u8]>;

    /// Returns the protocol revision that the implementation is providing.
    fn revision(&self) -> u64;

    /// Syncs partition buffers
    ///
    /// # Args
    ///
    /// * `sync_preloaded`: Whether to sync preloaded partitions.
    fn sync_partition_buffer(&self, sync_preloaded: bool) -> EfiResult<()>;

    /// Returns a partition buffer.
    ///
    /// # Args
    ///
    /// * `base_name`: The base name of the partition to get the buffer for.
    ///
    /// # Returns
    ///
    /// `Ok((PartitionBuffer, flag))` if the partition buffer was found.
    fn get_partition_buffer(
        &self,
        base_name: &CStr,
    ) -> EfiResult<(Self::PartitionBuffer, GblEfiPartitionBufferFlag)>;

    /// Takes the boot buffer.
    ///
    /// # Args
    ///
    /// * `buffer_type`: The type of the boot buffer to get.
    ///
    /// # Returns
    ///
    /// `Ok(BootBuffer)` if the boot buffer was found.
    fn take_boot_buffer(&self, buffer_type: GblEfiBootBufferType) -> EfiResult<BootBuffer>;
}

/// Internally managed GBL EFI boot memory buffers.
pub struct GblEfiBootMemoryManaged<T: GblEfiBootMemorySafe> {
    inner: T,
    partition_buffers: Mutex<BTreeMap<CString, (T::PartitionBuffer, GblEfiPartitionBufferFlag)>>,
    boot_buffers: Mutex<BTreeMap<u32, BootBuffer>>,
}

impl<T: GblEfiBootMemorySafe> GblEfiBootMemoryManaged<T> {
    /// Creates a new wrapper.
    pub const fn new(inner: T) -> Self {
        Self {
            inner,
            partition_buffers: Mutex::new(BTreeMap::new()),
            boot_buffers: Mutex::new(BTreeMap::new()),
        }
    }
}

// SAFETY:
// * The implementation does not access any buffers returned from `get_boot_buffer`.
// * The implementation does not access any buffers returned from `get_partition_buffer` outside of
//   `sync_partition_buffer`.
unsafe impl<T: GblEfiBootMemorySafe> GblEfiBootMemory for GblEfiBootMemoryManaged<T> {
    fn revision(&self) -> u64 {
        self.inner.revision()
    }

    unsafe fn sync_partition_buffer(&self, sync_preloaded: bool) -> EfiResult<()> {
        self.partition_buffers.try_lock().ok_or(EfiError::NotReady)?.clear();
        self.inner.sync_partition_buffer(sync_preloaded)
    }

    fn get_partition_buffer(&self, base_name: &CStr) -> EfiResult<PartitionBuffer> {
        let mut cache = self.partition_buffers.try_lock().ok_or(EfiError::NotReady)?;
        if let Some((buffer, flag)) = cache.get(base_name) {
            return Ok(PartitionBuffer {
                size: buffer.len(),
                buffer: buffer.as_ptr() as *mut c_void,
                flag: *flag,
            });
        }

        let new = self.inner.get_partition_buffer(base_name)?;
        let (buffer, flag) = cache.entry(base_name.to_owned()).or_insert(new);
        Ok(PartitionBuffer {
            size: buffer.len(),
            buffer: buffer.as_mut_ptr() as *mut c_void,
            flag: *flag,
        })
    }

    fn get_boot_buffer(
        &self,
        buffer_type: GblEfiBootBufferType,
    ) -> EfiResult<(usize, *mut c_void)> {
        let mut cache = self.boot_buffers.try_lock().ok_or(EfiError::NotReady)?;
        let buf = match cache.get(&(buffer_type.0)) {
            Some(buffer) => buffer,
            None => {
                let new = self.inner.take_boot_buffer(buffer_type)?;
                cache.entry(buffer_type.0).or_insert(new)
            }
        };
        match buf {
            BootBuffer::Static(buf) => Ok((buf.len(), buf.as_ptr() as *mut c_void)),
            BootBuffer::ToAllocate(size) => Ok((*size, core::ptr::null_mut())),
        }
    }
}
