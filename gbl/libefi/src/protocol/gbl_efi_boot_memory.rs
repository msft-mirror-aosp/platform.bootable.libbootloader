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

//! APIs for getting partition and boot buffers.

use crate::{
    efi_call, efi_println,
    protocol::{Protocol, ProtocolInfo},
    versioned_protocol, EfiEntry,
};
use alloc::{vec, vec::Vec};
use arrayvec::ArrayString;
use core::{
    mem::take,
    ops::{Deref, DerefMut},
    ptr::null_mut,
    slice::from_raw_parts_mut,
};
use efi_types::{
    defs::{
        EfiGuid, GblEfiBootBufferType, GblEfiBootMemoryProtocol, GblEfiPartitionBufferFlag,
        GBL_EFI_BOOT_BUFFER_TYPE_FASTBOOT_DOWNLOAD, GBL_EFI_BOOT_BUFFER_TYPE_FDT,
        GBL_EFI_BOOT_BUFFER_TYPE_GENERAL_LOAD, GBL_EFI_BOOT_BUFFER_TYPE_KERNEL,
        GBL_EFI_BOOT_BUFFER_TYPE_PVMFW_DATA, GBL_EFI_BOOT_BUFFER_TYPE_RAMDISK,
        GBL_EFI_BOOT_MEMORY_PROTOCOL_REVISION, GBL_EFI_PARTITION_BUFFER_FLAG_PRELOADED,
        PARTITION_NAME_LEN_U16,
    },
    Identified,
};
use liberror::{Error, Result};
use spin::{Mutex, Spin};

type MutexGuard<'a, T> = spin::MutexGuard<'a, T, Spin>;

/// Represents a borrowed or heap allocated buffer managed by `BufferPool`.
#[derive(Debug)]
enum Buffer<'b> {
    /// Boot buffer or designated/preloaded partition buffer.
    Borrowed { buffer: &'b mut [u8], is_preloaded_partition: bool },
    /// Heap allocated buffer.
    Allocated { buffer: Vec<u8>, offset: usize, size: usize },
}

impl Default for Buffer<'_> {
    fn default() -> Self {
        Self::Borrowed { buffer: &mut [], is_preloaded_partition: false }
    }
}

impl<'b> Buffer<'b> {
    /// Leaks the wrapped buffer.
    fn leak(self) -> &'b mut [u8] {
        match self {
            Self::Borrowed { buffer, .. } => buffer,
            Self::Allocated { buffer, offset, size } => &mut (buffer.leak())[offset..][..size],
        }
    }
}

/// Buffer type returned by BufferPool.get().
pub struct BufferGuard<'a, 'b>(MutexGuard<'a, Buffer<'b>>);

impl Deref for BufferGuard<'_, '_> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        match self.0.deref() {
            Buffer::Borrowed { buffer, .. } => &buffer[..],
            Buffer::Allocated { buffer, offset, size } => &buffer[*offset..][..*size],
        }
    }
}

impl DerefMut for BufferGuard<'_, '_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self.0.deref_mut() {
            Buffer::Borrowed { buffer, .. } => &mut buffer[..],
            Buffer::Allocated { buffer, offset, size } => &mut buffer[*offset..][..*size],
        }
    }
}

impl<'a, 'b> BufferGuard<'a, 'b> {
    /// Checks if a buffer contains preloaded data.
    pub fn is_preloaded(&self) -> bool {
        matches!(self.0.deref(), Buffer::Borrowed { buffer: _, is_preloaded_partition: true })
    }

    /// Leaks the underlying buffer.
    ///
    /// Note that the MutexGuard of the buffer would be consumed and permanently locked, so the
    /// caller must not try to access the buffer from the BufferPool ever again.
    pub fn leak(self) -> &'b mut [u8] {
        take(MutexGuard::leak(self.0)).leak()
    }
}

/// A wrapper of Mutex that only expose the non-blocking try_lock method.
struct NonBlockingMutex<T>(Mutex<T>);

impl<T> NonBlockingMutex<T> {
    fn try_lock(&self) -> Result<MutexGuard<'_, T>> {
        self.0.try_lock().ok_or(Error::NotReady)
    }
}

/// A simple buffer pool that supports interior mutability.
struct BufferPool<'b, const N: usize> {
    // Stores the names associated with the buffers.
    // It needs to be independently accessible from buffers to support querying when the buffer
    // may be locked.
    names: NonBlockingMutex<[Option<ArrayString<{ PARTITION_NAME_LEN_U16 as usize }>>; N]>,
    // Stores the buffer. Each buffer needs to be independently accessible as caller may acquire
    // multiples of them.
    buffers: [NonBlockingMutex<Buffer<'b>>; N],
}

impl<'b, const N: usize> BufferPool<'b, N> {
    /// Creates a new instance
    const fn new() -> Self {
        Self {
            names: NonBlockingMutex(Mutex::new([const { None }; N])),
            buffers: [const {
                NonBlockingMutex(Mutex::new(Buffer::Borrowed {
                    buffer: &mut [],
                    is_preloaded_partition: false,
                }))
            }; N],
        }
    }

    /// Finds buffer associated with the given `name`, or creates a new entry if not found when
    /// `add` is true.
    fn get(&self, name: &str, add: bool) -> Result<BufferGuard<'_, 'b>> {
        let mut names = self.names.try_lock()?;
        match names.iter().position(|v| v.as_ref().is_some_and(|v| v == name)) {
            Some(idx) => Ok(BufferGuard(self.buffers[idx].try_lock()?)),
            None if add => {
                let idx = names.iter().position(|v| v.is_none()).ok_or(Error::OutOfResources)?;
                names[idx] = Some(ArrayString::from(name).map_err(|_| Error::InvalidInput)?);
                Ok(BufferGuard(self.buffers[idx].try_lock().unwrap())) // Should not be in use.
            }
            _ => Err(Error::NotFound),
        }
    }

    /// Finds and removes an existing buffer from the pool and returns it.
    fn clear(&self, name: &str) -> Result<Buffer<'_>> {
        let mut names = self.names.try_lock()?;
        let idx = names
            .iter()
            .position(|v| v.as_ref().is_some_and(|v| v == name))
            .ok_or(Error::NotFound)?;
        let res = take(self.buffers[idx].try_lock()?.deref_mut());
        names[idx] = None;
        Ok(res)
    }

    /// Clears all registered buffers.
    fn clear_all(&self) -> Result<()> {
        let mut names = self.names.try_lock()?;
        for i in 0..N {
            take(self.buffers[i].try_lock()?.deref_mut());
            names[i] = None;
        }
        Ok(())
    }
}

/// GBL_BOOT_MEMORY_PROTOCOL
pub struct GblBootMemoryProtocol;

versioned_protocol!(GblBootMemoryProtocol, GBL_EFI_BOOT_MEMORY_PROTOCOL_REVISION);

impl ProtocolInfo for GblBootMemoryProtocol {
    type InterfaceType = GblEfiBootMemoryProtocol;

    const GUID: EfiGuid = GblEfiBootMemoryProtocol::GUID;

    const METRICS_TAG: Option<&'static str> = Some("gbl_boot_memory");
}

/// Helper for getting 'GblBootMemoryProtocol'.
#[cfg(not(test))]
fn get_protocol(entry: &EfiEntry) -> Result<Protocol<'_, GblBootMemoryProtocol>> {
    entry.system_table().boot_services().find_first_and_open::<GblBootMemoryProtocol>()
}

/// Placeholder for test build.
#[cfg(test)]
fn get_protocol(_: &EfiEntry) -> Result<Protocol<'static, GblBootMemoryProtocol>> {
    unreachable!()
}

/// Represents a vendor reserved memory.
pub type GblVendorReservedMemory = BufferGuard<'static, 'static>;

/// Specifies operation for `partition_buffer_op`
// We did not put these operations into two separate functions because that would require exposing
// the pool object (`PARTITION_BUFFER_POOL`) to the module level, which might get accidentally
// accessed by other code and violate safety constraint.
enum PartitionBufferOps<'a> {
    /// Query partition buffer.
    Get(&'a str),
    /// Sync partition buffer. The parameter specifies whether to re-sync preloaded partition.
    Sync(bool),
}

/// Internal helper for getting/syncing partition buffers.
fn partition_buffer_op(
    entry: &EfiEntry,
    op: PartitionBufferOps<'_>,
) -> Result<Option<GblVendorReservedMemory>> {
    // 64 is randomly chosen. Changed if a tighter bound is found.
    //
    // TODO(b/578053116): Ideally this should shared the same constant as the maximum avb verify
    // partitions from libgbl. But doing that currently causes dependency cycle. Alterantively,
    // investigate letting caller determine the pool size.
    const POOL_SIZE: usize = 64;
    // The global pool is defined within this function to prevent it from being accidentally
    // accessed by code outside of this function.
    static PARTITION_BUFFER_POOL: BufferPool<'static, POOL_SIZE> = BufferPool::new();
    let protocol = get_protocol(entry)?;
    match op {
        PartitionBufferOps::Get(part) => {
            // Checks if the memory is already registered in the pool.
            match PARTITION_BUFFER_POOL.get(part, false) {
                Err(Error::NotFound) => {}
                Err(e) => return Err(e),
                Ok(v) => return Ok(Some(v)),
            };

            let (mut addr, mut sz, mut flags) = (null_mut(), 0, GblEfiPartitionBufferFlag(0));
            let mut part_cstr = ArrayString::<{ (PARTITION_NAME_LEN_U16 + 1) as usize }>::new();
            part_cstr.try_push_str(part).map_err(|_| Error::InvalidInput)?;
            part_cstr.try_push('\0').map_err(|_| Error::InvalidInput)?;
            // SAFETY:
            // * `protocol.interface()?` guarantees protocol.interface is non-null and points to a
            //   valid object established by `Protocol::new()`.
            // * `addr`, `size` and `flags` point to valid data and are output parameters. They
            //   outlive the call and will not be retained.
            unsafe {
                efi_call!(
                    protocol.interface().get_partition_buffer,
                    protocol.interface_ptr(),
                    part_cstr.as_ptr() as _,
                    &mut sz,
                    &mut addr,
                    &mut flags,
                )?;
            }

            let mut add = PARTITION_BUFFER_POOL.get(part, true)?;
            let is_preloaded_partition = (flags & GBL_EFI_PARTITION_BUFFER_FLAG_PRELOADED).0 != 0;
            if addr.is_null() {
                efi_println!(entry, "NULL partition buffer pointer is not allowed");
                return Err(Error::InvalidInput);
            }
            // SAFETY:
            // * Protocol spec requires that the returned buffer must remain valid for read/write
            //   between calls of `sync_partition_buffer()` and be exclusively accessed by GBL.
            // * `sync_partition_buffer()` is only called in the `PartitionBufferOps::Sync(v) =>`
            //    branch and after dropping all existing buffer references.
            // * Protocol spec requires that the memory is unique for each `name` id.
            //   `PARTITION_BUFFER_POOL.get(part, true)?;` checks that we have not acquired the same
            //   buffer before.
            *add.0 = Buffer::Borrowed {
                buffer: unsafe { from_raw_parts_mut(addr as _, sz) },
                is_preloaded_partition,
            };
            Ok(Some(add))
        }
        PartitionBufferOps::Sync(v) => {
            // Drops all existing buffer references.
            PARTITION_BUFFER_POOL.clear_all()?;
            // SAFETY:
            // * `protocol.interface()?` guarantees protocol.interface is non-null and points to a
            //   valid object established by `Protocol::new()`.
            // * All existing references in PARTITION_BUFFER_POOL are dropped by
            //   `PARTITION_BUFFER_POOL.clear_all()?;` above.
            unsafe {
                efi_call!(protocol.interface().sync_partition_buffer, protocol.interface_ptr(), v)?
            };
            Ok(None)
        }
    }
}

/// Gets GBL partition buffer for the given partition name
pub fn gbl_get_partition_buffer(entry: &EfiEntry, part: &str) -> Result<GblVendorReservedMemory> {
    partition_buffer_op(entry, PartitionBufferOps::Get(part)).map(|v| v.unwrap())
}

/// Syncs GBL partition buffer.
pub fn gbl_sync_partition_buffer(entry: &EfiEntry, sync_preloaded: bool) -> Result<()> {
    partition_buffer_op(entry, PartitionBufferOps::Sync(sync_preloaded)).map(|_| ())
}

/// Number of boot buffer type. Needs to be kept in sync with number of types for
/// `GblEfiBootBufferType`
const BUFFER_TYPE_NUM: usize = 6;

/// Helper that returns a unique name and the alignment for a GblEfiBootBufferType.
fn boot_buf_info(buf_type: GblEfiBootBufferType) -> (&'static str, usize) {
    match buf_type {
        GBL_EFI_BOOT_BUFFER_TYPE_GENERAL_LOAD => ("general_load", 1),
        GBL_EFI_BOOT_BUFFER_TYPE_KERNEL => ("kernel", 2 * 1024 * 1024),
        GBL_EFI_BOOT_BUFFER_TYPE_RAMDISK => ("ramdisk", 1),
        GBL_EFI_BOOT_BUFFER_TYPE_FDT => ("fdt", 8),
        GBL_EFI_BOOT_BUFFER_TYPE_PVMFW_DATA => ("pvmfw", 4 * 1024),
        GBL_EFI_BOOT_BUFFER_TYPE_FASTBOOT_DOWNLOAD => ("fastboot", 1),
        _ => unreachable!(),
    }
}

/// Specifies operation for `boot_buffer_op`
// We did not put these operations into two separate functions because that would require exposing
// the pool object (`BOOT_BUFFER_POOL`) to the module level, which might get accidentally accessed
// by other code and violate safety constraint.
enum BootBufferOp {
    /// (Buffer type, default alloc size)
    Get(GblEfiBootBufferType, usize),
    /// Releases the buffer.
    Clear(GblEfiBootBufferType),
}

/// Helper function for finding/releasing boot buffers.
fn boot_buffer_op(entry: &EfiEntry, op: BootBufferOp) -> Result<Option<GblVendorReservedMemory>> {
    // The global pool is defined within this function to prevent it from being accidentally
    // accessed by code outside of this function.
    static BOOT_BUFFER_POOL: BufferPool<'static, BUFFER_TYPE_NUM> = BufferPool::new();
    match op {
        BootBufferOp::Get(buf_type, default_alloc) => {
            let (name, align) = boot_buf_info(buf_type);
            // Checks if the memory is already registered in the pool.
            match BOOT_BUFFER_POOL.get(name, false) {
                Err(Error::NotFound) => {}
                Err(e) => return Err(e),
                Ok(v) => return Ok(Some(v)),
            };

            // Finds an empty slot in the pool.
            let mut add = BOOT_BUFFER_POOL.get(name, true)?;
            let (mut addr, mut sz) = (null_mut(), Default::default());

            let res = get_protocol(entry).and_then(|v| {
                // SAFETY:
                // * `v.interface_ptr()` points to a valid object established by `Protocol::new()`.
                // * `addr`, `sz` point to valid data and are output parameters. They outlive the
                //   call and will not be retained.
                unsafe {
                    efi_call!(
                        v.interface().get_boot_buffer,
                        v.interface_ptr(),
                        buf_type,
                        &mut sz,
                        &mut addr,
                    )
                }
            });
            // Pattern matching must use constant variable, otherwise the compiler treats it as
            // binding.
            const NULL_PTR: *mut core::ffi::c_void = core::ptr::null_mut();
            *add.0 = match (res.map(|_| (addr, sz)), default_alloc) {
                // `addr` == 0 or buffer is not found and caller specifies default allocation size.
                (Ok((NULL_PTR, size)), _) | (Err(Error::NotFound), size) if size > 0 => {
                    let buffer = vec![0u8; size + align - 1];
                    let offset = buffer.as_ptr().align_offset(align);
                    efi_println!(
                        entry,
                        "Allocated {size:#x} bytes for {name:?} buffer at {:#x}.",
                        buffer.as_ptr() as usize + offset,
                    );
                    Buffer::Allocated { buffer, offset, size }
                }
                (Ok((addr, sz)), _) => {
                    efi_println!(entry, "Found {name:?} buffer: addr {addr:?}, sz: {sz:#x}.");
                    // SAFETY:
                    // * Protocol spec requires that the returned buffer must be valid for
                    //   read/write, have static lifetime and be exclusively accessed by GBL.
                    // * Protocol spec requires that the memory is unique for each `buf_type` id.
                    //   `PARTITION_BUFFER_POOL.get(part, true)?;` checks that we have not acquired
                    //   the same buffer before.
                    Buffer::Borrowed {
                        buffer: unsafe { from_raw_parts_mut(addr as _, sz) },
                        is_preloaded_partition: false,
                    }
                }
                (Err(e), _) => return Err(e),
            };
            Ok(Some(add))
        }
        BootBufferOp::Clear(v) => {
            let name = boot_buf_info(v).0;
            match BOOT_BUFFER_POOL.clear(name)? {
                Buffer::Allocated { .. } => {
                    efi_println!(entry, "Released allocated buffer for {name:?}.");
                }
                _ => {}
            }
            Ok(None)
        }
    }
}

/// Gets the boot buffer of the given type.
pub fn gbl_get_boot_buffer(
    entry: &EfiEntry,
    buf_type: GblEfiBootBufferType,
    default: usize,
) -> Result<GblVendorReservedMemory> {
    boot_buffer_op(entry, BootBufferOp::Get(buf_type, default)).map(|v| v.unwrap())
}

/// Releases the buffer identified by the given type.
///
/// If the buffer is previously returned by `gbl_get_boot_buffer` and has not dropped,
/// Err(Error::NotReady) is returned.
///
/// If the buffer is allocated by the API, it will be deallocated. Otherwise it's a noop.
pub fn gbl_clear_boot_buffer(entry: &EfiEntry, buf_type: GblEfiBootBufferType) -> Result<()> {
    boot_buffer_op(entry, BootBufferOp::Clear(buf_type)).map(|_| ())
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_get() {
        let mut buf = (0..16).collect::<Vec<_>>();
        let pool = BufferPool::<2>::new();

        // Add allocated buffer.
        assert!(matches!(pool.get("alloc", false), Err(Error::NotFound)));
        *pool.get("alloc", true).unwrap().0 =
            Buffer::Allocated { buffer: vec![0u8; 16], offset: 0, size: 16 };
        assert_eq!(&mut pool.get("alloc", false).unwrap()[..], [0; 16]);

        // Add borrowed buffer
        assert!(matches!(pool.get("borrow", false), Err(Error::NotFound)));
        *pool.get("borrow", true).unwrap().0 =
            Buffer::Borrowed { buffer: &mut buf[..], is_preloaded_partition: false };
        assert_eq!(&mut pool.get("borrow", false).unwrap()[..], (0..16).collect::<Vec<_>>());
        pool.get("borrow", true).unwrap().fill(1);

        drop(pool);
        assert_eq!(buf, [1; 16]);
    }

    #[test]
    fn test_clear() {
        let pool = BufferPool::<2>::new();
        *pool.get("alloc", true).unwrap().0 =
            Buffer::Allocated { buffer: vec![0u8; 16], offset: 0, size: 16 };
        assert_eq!(&mut pool.get("alloc", false).unwrap()[..], [0; 16]);
        pool.clear("alloc").unwrap();
        assert!(matches!(pool.get("alloc", false), Err(Error::NotFound)));
    }

    #[test]
    fn test_get_busy() {
        let pool = BufferPool::<2>::new();
        let _a = pool.get("buf", true).unwrap();
        assert!(matches!(pool.get("buf", false), Err(Error::NotReady)));
        assert!(matches!(pool.get("buf", true), Err(Error::NotReady)));
        assert!(matches!(pool.clear("buf"), Err(Error::NotReady)));
    }

    #[test]
    fn test_get_out_of_resource() {
        let pool = BufferPool::<1>::new();
        pool.get("buf1", true).unwrap();
        assert!(matches!(pool.get("buf2", true), Err(Error::OutOfResources)));
    }
}
