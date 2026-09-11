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

//! The library implements Rust wrappers for a set of UEFI interfaces needed by GBL. It also
//! provides a global allocator and supports auto-release of dynamic UEFI resources such as
//! protocols and UEFI allocated buffers.
//!
//! # Examples
//!
//! The following example covers the basic use pattern of the library. It scans all block devices
//! and prints out the device path, block size and io alignment info for each of them.
//!
//! ```
//! fn main(image: EfiHandle, systab_ptr: *mut EfiSystemTable) -> liberror::Result<()> {
//!     let efi_entry = initialize(image, systab_ptr)?;
//!     let mut con_out = efi_entry.system_table().con_out()?;
//!     let boot_services = efi_entry.system_table().boot_services();
//!     let path_to_text = boot_services.find_first_and_open::<DevicePathToTextProtocol>()?;
//!
//!     write!(con_out, "Scanning block devices...\n")?;
//!
//!     let block_handles = boot_services.locate_handle_buffer_by_protocol::<BlockIoProtocol>()?;
//!
//!     for (i, handle) in block_handles.handles().iter().enumerate() {
//!         let path = boot_services.open_protocol::<DevicePathProtocol>(*handle)?;
//!         write!(con_out, "Block Device #{}: ", i)?;
//!         path_to_text.convert_device_path_to_text(&path, false, false)?.print()?;
//!         write!(con_out, "\n")?;
//!
//!         let block_io_protocol = boot_services.open_protocol::<BlockIoProtocol>(*handle)?;
//!         let media = block_io_protocol.media()?;
//!         write!(con_out, "  block size = {}\n", media.block_size)?;
//!         write!(con_out, "  io alignment = {}\n", media.io_align)?;
//!     }
//!
//!     Ok(())
//! }
//! ```

#![cfg_attr(not(test), no_std)]
#![feature(never_type)]

extern crate alloc;
use alloc::{boxed::Box, vec::Vec};
use arrayvec::ArrayVec;
use core::ptr::NonNull;
use efi_types::{
    protocol::{BridgeToRust, Provider},
    Identified,
};
pub use libutils::arch_timestamp;

/// Address parameter for UEFI page allocation.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum AllocationAddress {
    /// Allocate at any available address.
    Any,
    /// Allocate at a fixed address.
    Fixed(u64),
    /// Allocate at an address no greater than the specified address.
    Max(u64),
}

#[cfg(not(test))]
mod allocation;

#[cfg(test)]
thread_local! {
    static GLOBAL_EFI_ENTRY: std::cell::RefCell<Option<NonNull<EfiEntry>>> = std::cell::RefCell::new(None);
}

/// Escape valve for operations that need the global EfiEntry
/// but cannot be provided with it as a parameter.
///
/// Safety:
/// * It is the responsibility of whatever code initializes the global efi entry
///   to guarantee that it is well formed and valid for as long as any caller might
///   see it, usually 'static or for the duration of the unit test.
pub unsafe fn with_global_efi_entry<F, T>(mut func: F) -> Result<T>
where
    F: FnMut(&'static EfiEntry) -> T,
{
    let entry;
    cfg_if! {
        if #[cfg(test)] {
            entry = GLOBAL_EFI_ENTRY
            // Safety:
            // * It is the responsibility of initialization code to guarantee that
            //   `e_ptr` is valid and live.
                .with(|e| e.borrow().map(|e_ptr| unsafe{ e_ptr.as_ref() }))
                .ok_or(Error::InvalidState)?;
        } else {
            entry = allocation::internal_efi_entry_and_rt().0.ok_or(Error::InvalidState)?;
        }
    }

    Ok(func(entry))
}

#[cfg(all(not(test), not(target_os = "linux")))]
pub mod libc;

#[cfg(not(test))]
pub use allocation::EfiAllocator;

/// C wrappers for EFI based hashing.
pub mod efi_hash_c;
/// EFI backed implementations for profiling framework.
pub mod profiling;
/// Idiomatic wrappers around EFI protocols.
pub mod protocol;
pub mod utils;

use cfg_if::cfg_if;
use core::{
    marker::PhantomData,
    ptr::{null, null_mut},
    slice::from_raw_parts,
    time::Duration,
};
use efi_types::{
    defs::{
        EfiBootService, EfiConfigurationTable, EfiEvent, EfiGuid, EfiHandle,
        EfiMemoryAttributesTableHeader, EfiMemoryDescriptor, EfiMemoryType, EfiResetType,
        EfiRuntimeService, EfiStatus, EfiSystemTable, EfiTimerDelay, EfiTpl, GblEfiDebugErrorTag,
        EFI_ALLOCATOR_TYPE_ALLOCATE_ADDRESS, EFI_ALLOCATOR_TYPE_ALLOCATE_ANY_PAGES,
        EFI_ALLOCATOR_TYPE_ALLOCATE_MAX_ADDRESS, EFI_EVENT_TYPE_NOTIFY_SIGNAL,
        EFI_EVENT_TYPE_NOTIFY_WAIT, EFI_EVENT_TYPE_RUNTIME,
        EFI_EVENT_TYPE_SIGNAL_EXIT_BOOT_SERVICES, EFI_EVENT_TYPE_SIGNAL_VIRTUAL_ADDRESS_CHANGE,
        EFI_EVENT_TYPE_TIMER, EFI_INTERFACE_TYPE_EFI_NATIVE_INTERFACE,
        EFI_LOCATE_HANDLE_SEARCH_TYPE_BY_PROTOCOL, EFI_OPEN_PROTOCOL_ATTRIBUTE_BY_HANDLE_PROTOCOL,
        EFI_RESET_TYPE_COLD, EFI_RESET_TYPE_SHUTDOWN, EFI_STATUS_DEVICE_ERROR, EFI_STATUS_SUCCESS,
        GBL_EFI_DEBUG_ERROR_TAG_BOOT_ERROR,
    },
    tpl::TplControl,
};
use liberror::{Error, Result};
use libutils::{aligned_subslice, base_type_name};
use protocol::{
    loaded_image::LoadedImageProtocol, simple_text_output::SimpleTextOutputProtocol, Protocol,
    ProtocolImpl, ProtocolInfo, Revision,
};
use zerocopy::{FromBytes, Ref};

/// Container for EFI metrics.
pub struct EfiMetrics {
    /// List of opened protocols.
    pub opened_protocols: ArrayVec<(&'static str, Revision), 32>,
}

impl EfiMetrics {
    /// Records an opened protocol version.
    fn record_protocol(&mut self, tag: &'static str, rev: Revision) {
        if !self.opened_protocols.iter().any(|(t, _)| *t == tag) {
            let _ = self.opened_protocols.try_push((tag, rev));
        }
    }
}

#[cfg(not(test))]
static EFI_METRICS: spin::Mutex<EfiMetrics> =
    spin::Mutex::new(EfiMetrics { opened_protocols: ArrayVec::new_const() });

#[cfg(test)]
thread_local! {
    static EFI_METRICS: core::cell::RefCell<EfiMetrics> = core::cell::RefCell::new(EfiMetrics { opened_protocols: ArrayVec::new_const() });
}

/// Records an opened protocol version.
pub(crate) fn record_protocol(tag: &'static str, rev: Revision) {
    #[cfg(not(test))]
    EFI_METRICS.lock().record_protocol(tag, rev);
    #[cfg(test)]
    EFI_METRICS.with_borrow_mut(|m| m.record_protocol(tag, rev));
}

/// Returns the list of opened protocols.
pub fn opened_protocols() -> ArrayVec<(&'static str, Revision), 32> {
    #[cfg(not(test))]
    return EFI_METRICS.lock().opened_protocols.clone();
    #[cfg(test)]
    return EFI_METRICS.with_borrow(|m| m.opened_protocols.clone());
}

/// `EfiEntry` stores the EFI system table pointer and image handle passed from the entry point.
/// It's the root data structure that derives all other wrapper APIs and structures.
#[derive(Debug)]
pub struct EfiEntry {
    image_handle: EfiHandle,
    systab_ptr: *const EfiSystemTable,
}

impl EfiEntry {
    /// Gets an instance of `SystemTable`.
    ///
    /// Panics if the pointer is NULL.
    pub fn system_table(&self) -> SystemTable<'_> {
        self.system_table_checked().unwrap()
    }

    /// Gets an instance of `SystemTable` if pointer is valid.
    pub fn system_table_checked(&self) -> Result<SystemTable<'_>> {
        // SAFETY: Pointers to UEFI data strucutres.
        Ok(SystemTable {
            efi_entry: self,
            table: unsafe { self.systab_ptr.as_ref() }.ok_or(Error::Unsupported)?,
        })
    }

    /// Gets the image handle.
    pub fn image_handle(&self) -> DeviceHandle {
        DeviceHandle(self.image_handle)
    }
}

/// Implement `TplControl` here for convenience so callers don't have to
/// dig down to `BootServices` themelves.
impl TplControl for EfiEntry {
    unsafe fn raise_tpl(&self, tpl: EfiTpl) -> EfiTpl {
        // SAFETY: just forwarding the call, same safety as our caller.
        unsafe { self.system_table().boot_services().boot_services.raise_tpl(tpl) }
    }

    unsafe fn restore_tpl(&self, tpl: EfiTpl) {
        // SAFETY: just forwarding the call, same safety as our caller.
        unsafe { self.system_table().boot_services().boot_services.restore_tpl(tpl) }
    }
}

/// The vendor GUID for UEFI variables defined by GBL.
pub const GBL_EFI_VENDOR_GUID: EfiGuid =
    EfiGuid::from_u64s(efi_types::GBL_EFI_VENDOR_GUID_U64_0, efi_types::GBL_EFI_VENDOR_GUID_U64_1);

/// GUID for UEFI Memory Attributes Table
pub const EFI_MEMORY_ATTRIBUTES_GUID: EfiGuid =
    EfiGuid::new(0xdcfa911d, 0x26eb, 0x469f, [0xa2, 0x20, 0x38, 0xb7, 0xdc, 0x46, 0x12, 0x20]);

/// GUID for UEFI Global variables
pub const EFI_GLOBAL_VARIABLE_GUID: EfiGuid =
    EfiGuid::new(0x8be4df61, 0x93ca, 0x11d2, [0xaa, 0x0d, 0x00, 0xe0, 0x98, 0x03, 0x2b, 0x8c]);

/// GUID for Device Tree (DTB) configuration table in system table.
pub const EFI_DTB_TABLE_GUID: EfiGuid =
    EfiGuid::new(0xb1b621d5, 0xf19c, 0x41a5, [0x83, 0x0b, 0xd9, 0x15, 0x2c, 0x69, 0xaa, 0xe0]);

/// GUID for Linux EFI loaded image fixed placement protocol.
pub const LINUX_EFI_LOADED_IMAGE_FIXED_GUID: EfiGuid =
    EfiGuid::new(0xf5a37b6d, 0x3344, 0x42a5, [0xb6, 0xbb, 0x97, 0x86, 0x48, 0xc1, 0x89, 0x0a]);

/// The name of the UEFI variable that GBL defines to determine whether to boot Fuchsia.
/// The value of the variable is ignored: if the variable is present,
/// it indicates that the bootloader should attempt to boot a Fuchsia target.
/// This may include reinitializing GPT partitions and partition contents.
#[cfg(feature = "fuchsia")]
pub const GBL_EFI_OS_BOOT_TARGET_VARNAME: &str = "gbl_os_boot_fuchsia";

/// UEFI variable that indicates the api level of the firmware.
/// This must have the same `YYYYMM` format as the ro.board.api_level system property.
pub const GBL_EFI_FW_API_LEVEL: &str = "gbl_fw_api_level";

/// Creates an `EfiEntry` and initialize EFI global allocator.
///
/// # Safety
///
/// The API modifies internal global state. It should only be called once upon EFI entry to obtain
/// an instance of `EfiEntry` for accessing other APIs. Calling it again when EFI APIs are already
/// being used can introduce a risk of race.
#[cfg(not(test))]
pub unsafe fn initialize(
    image_handle: EfiHandle,
    systab_ptr: *const EfiSystemTable,
) -> Result<EfiEntry> {
    // SAFETY: By safety requirement of this function, `initialize` is only called once upon
    // entering EFI application, where there should be no event notify function that can be
    // triggered.
    unsafe {
        // Create one for internal global allocator.
        allocation::init_efi_global_alloc(EfiEntry { image_handle, systab_ptr })?;
    }
    Ok(EfiEntry { image_handle, systab_ptr })
}

/// Exits boot service and returns the memory map in the given buffer.
///
/// The API takes ownership of the given `entry` and causes it to go out of scope.
/// This enforces strict compile time check that any reference/borrow in effect will cause compile
/// errors.
///
/// Existing heap allocated memories will maintain their states. All system memory including them
/// will be under onwership of the subsequent OS or OS loader code.
pub fn exit_boot_services(entry: EfiEntry, mmap_buffer: &mut [u8]) -> Result<EfiMemoryMap<'_>> {
    let aligned = aligned_subslice(mmap_buffer, core::mem::align_of::<EfiMemoryDescriptor>())
        .inspect_err(|e| report_error_and_reset(&entry, e, GBL_EFI_DEBUG_ERROR_TAG_BOOT_ERROR))?;

    let res =
        entry.system_table().boot_services().get_memory_map(aligned).inspect_err(|e| {
            report_error_and_reset(&entry, e, GBL_EFI_DEBUG_ERROR_TAG_BOOT_ERROR)
        })?;
    entry.system_table().boot_services().exit_boot_services(&res)?;
    // SAFETY:
    // At this point, UEFI has successfully exited boot services and no event/notification can be
    // triggered.
    #[cfg(not(test))]
    unsafe {
        allocation::exit_efi_global_alloc();
    }
    Ok(res)
}

/// `SystemTable` provides methods for accessing fields in `EFI_SYSTEM_TABLE`.
#[derive(Copy, Clone)]
pub struct SystemTable<'a> {
    efi_entry: &'a EfiEntry,
    table: &'a EfiSystemTable,
}

impl<'a> SystemTable<'a> {
    /// Creates an instance of `BootServices`
    ///
    /// Panics if not implemented by UEFI.
    pub fn boot_services(&self) -> BootServices<'a> {
        self.boot_services_checked().unwrap()
    }

    /// Creates an instance of `BootServices`
    ///
    /// Returns Err(()) if not implemented by UEFI.
    pub fn boot_services_checked(&self) -> Result<BootServices<'a>> {
        Ok(BootServices {
            efi_entry: self.efi_entry,
            // SAFETY: Pointers to UEFI data strucutres.
            boot_services: unsafe { self.table.boot_services.as_ref() }
                .ok_or(Error::Unsupported)?,
        })
    }

    /// Creates an instance of `RuntimeServices`
    ///
    /// Panics if run time services is not implemented.
    pub fn runtime_services(&self) -> RuntimeServices {
        self.runtime_services_checked().unwrap()
    }

    /// Creates an instance of `RuntimeServices` if available from system table.
    pub fn runtime_services_checked(&self) -> Result<RuntimeServices> {
        Ok(RuntimeServices {
            // SAFETY: Pointers to UEFI data strucutres.
            runtime_services: *unsafe { self.table.runtime_services.as_ref() }
                .ok_or(Error::Unsupported)?,
        })
    }

    /// Gets the `EFI_SYSTEM_TABLE.ConOut` field.
    pub fn con_out(&self) -> Result<Protocol<'a, SimpleTextOutputProtocol>> {
        // SAFETY: `EFI_SYSTEM_TABLE.ConOut` is a pointer to EfiSimpleTextOutputProtocol structure
        // by definition. It lives until ExitBootServices and thus as long as `self.efi_entry` or,
        // 'a
        Ok(unsafe {
            Protocol::<SimpleTextOutputProtocol>::new(
                // No device handle. This protocol is a permanent reference.
                DeviceHandle(null_mut()),
                core::ptr::NonNull::new(self.table.con_out).ok_or(Error::NotFound)?,
                self.efi_entry,
            )
        })
    }

    /// Gets the `EFI_SYSTEM_TABLE.ConfigurationTable` array.
    pub fn configuration_table(&self) -> Option<&[EfiConfigurationTable]> {
        match self.table.configuration_table.is_null() {
            true => None,
            // SAFETY: Non-null pointer to EFI configuration table.
            false => unsafe {
                Some(from_raw_parts(
                    self.table.configuration_table,
                    self.table.number_of_table_entries,
                ))
            },
        }
    }

    /// Returns a raw pointer to the underlying `EfiSystemTable`.
    pub fn as_ptr(&self) -> *const EfiSystemTable {
        self.table
    }
}

/// Watchdog timer code wrapper to be passed to `EFI_BOOT_SERVICE.SetWatchdogTimer()`.
///
/// The firmware reserves codes from 0x0000 to 0xFFFF, so make sure these are not used by the UEFI app.
/// https://uefi.org/specs/UEFI/2.9_A/07_Services_Boot_Services.html#efi-boot-services-setwatchdogtimer
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct WatchdogTimerCode(u64);

impl WatchdogTimerCode {
    /// The minimal allowed code to use.
    const MIN: u64 = 0x10000;

    /// Create new WatchdogTimerCode with respect to system reserved codes.
    pub const fn new(code: u64) -> Self {
        assert!(code >= Self::MIN, "Reserved UEFI watchdog code is used");
        Self(code)
    }
}

fn log_missing_protocol<T: ProtocolImpl>(entry: &EfiEntry) {
    match T::REQUIREMENT {
        protocol::Requirement::Mandatory => efi_println!(
            entry,
            "Required protocol not found: {}",
            base_type_name::<T::CInterface>()
        ),
        protocol::Requirement::Optional => {
            #[cfg(feature = "gbl_dev")]
            efi_println!(
                entry,
                "Optional protocol not found: {}",
                base_type_name::<T::CInterface>()
            )
        }
    }
}

/// `BootServices` provides methods for accessing various EFI_BOOT_SERVICES interfaces.
#[derive(Copy, Clone)]
pub struct BootServices<'a> {
    efi_entry: &'a EfiEntry,
    boot_services: &'a EfiBootService,
}

impl<'a> BootServices<'a> {
    /// Maximum number of handles to try locating via `locate_handles_by_protocol` in
    /// `find_first_and_open`.
    ///
    /// Many protocols we want to open via `find_first_and_open` have only have a few
    /// handles, so we pick an empirically reasonable size for the array.
    /// If the call to `locate_handles_by_protocol` fails with BUFFER_TOO_SMALL,
    /// fall back to finding handles via `locate_handle_buffer_by_protocol`.
    const LOCATE_HANDLE_BUFFER_SIZE: usize = 8;

    /// Wrapper of `EFI_BOOT_SERVICES.AllocatePool()`.
    #[allow(dead_code)]
    fn allocate_pool(
        &self,
        pool_type: EfiMemoryType,
        size: usize,
    ) -> Result<*mut core::ffi::c_void> {
        let mut out: *mut core::ffi::c_void = null_mut();
        // SAFETY: `EFI_BOOT_SERVICES` method call.
        unsafe {
            efi_call!(self.boot_services.allocate_pool, pool_type, size, &mut out)?;
        }
        Ok(out)
    }

    /// Wrapper of `EFI_BOOT_SERVICES.FreePool()`.
    fn free_pool(&self, buf: *mut core::ffi::c_void) -> Result<()> {
        // SAFETY: `EFI_BOOT_SERVICES` method call.
        unsafe { efi_call!(self.boot_services.free_pool, buf) }
    }

    /// Wrapper of `EFI_BOOT_SERVICES.AllocatePool()`.
    pub fn allocate_pages(
        &self,
        pool: EfiMemoryType,
        addr: AllocationAddress,
        pages: usize,
    ) -> Result<*mut core::ffi::c_void> {
        let (alloc_type, mut out) = match addr {
            AllocationAddress::Any => (EFI_ALLOCATOR_TYPE_ALLOCATE_ANY_PAGES, 0),
            AllocationAddress::Fixed(a) => (EFI_ALLOCATOR_TYPE_ALLOCATE_ADDRESS, a),
            AllocationAddress::Max(a) => (EFI_ALLOCATOR_TYPE_ALLOCATE_MAX_ADDRESS, a),
        };
        // SAFETY: `&mut out` points to a valid data and is for output only. It outlives the call
        // and will not be retained.
        unsafe { efi_call!(self.boot_services.allocate_pages, alloc_type, pool, pages, &mut out)? };
        Ok(out as _)
    }

    /// Wrapper of `EFI_BOOT_SERVICES.FreePages()`.
    pub fn free_pages(&self, buf: *mut core::ffi::c_void, pages: usize) -> Result<()> {
        // SAFETY:
        // * No memory is retained by the function call.
        // * By UEFI spec, implementation should return error where `buf` is not a valid or
        //   associated with any allocated memory.
        unsafe { efi_call!(self.boot_services.free_pages, buf as _, pages) }
    }

    /// Wrapper of `EFI_BOOT_SERVICES.OpenProtocol()`.
    pub fn open_protocol<T: ProtocolImpl>(&self, handle: DeviceHandle) -> Result<Protocol<'a, T>> {
        let mut out_handle: EfiHandle = null();
        // SAFETY: EFI_BOOT_SERVICES method call.
        unsafe {
            efi_call!(
                self.boot_services.open_protocol,
                handle.0,
                &T::GUID,
                &mut out_handle,
                self.efi_entry.image_handle().0,
                null_mut(),
                // Cannot open exclusively because firmware may require the protocol as well.
                EFI_OPEN_PROTOCOL_ATTRIBUTE_BY_HANDLE_PROTOCOL
            )?;
        }
        // SAFETY:
        // * `EFI_SYSTEM_TABLE.OpenProtocol` returns a valid pointer to
        //   `T::InterfaceType` on success.
        // * The pointer remains valid until ExitBootServices.
        // * Due to the 'a lifetime, the returned protocol will always be dropped
        //   before ExitBootServices.
        Ok(unsafe {
            Protocol::<T>::new(
                handle,
                core::ptr::NonNull::new(out_handle as *mut _).ok_or(Error::NotFound)?,
                self.efi_entry,
            )
        })
    }

    /// Call `EFI_BOOT_SERVICES.LocateHandle()` with fixed
    /// `EFI_LOCATE_HANDLE_SEARCH_TYPE_BY_PROTOCOL`, user provided buffer,
    /// and without a search key.
    pub fn locate_handles_by_protocol<T: ProtocolImpl>(
        &self,
        buffer: &'a mut [DeviceHandle],
    ) -> Result<LocatedHandles<'a>> {
        let mut num_handles = buffer.len();
        // SAFETY:
        // * EFI_BOOT_SERVICES method call.
        // * NULL is valid for `search_key`.
        // * `num_handles` is valid to read and write.
        // * `buffer` is valid to write for `num_handles` elements.
        unsafe {
            efi_call!(
                @bufsize num_handles,
                self.boot_services.locate_handle,
                EFI_LOCATE_HANDLE_SEARCH_TYPE_BY_PROTOCOL,
                &T::GUID,
                null(),
                &mut num_handles,
                buffer.as_mut_ptr() as *mut _,
            )?
        };

        Ok(LocatedHandles::new_borrowed(&buffer[..num_handles]))
    }

    /// Call `EFI_BOOT_SERVICES.LocateHandleBuffer()` with fixed
    /// `EFI_LOCATE_HANDLE_SEARCH_TYPE_BY_PROTOCOL` and without search key.
    pub fn locate_handle_buffer_by_protocol<T: ProtocolImpl>(&self) -> Result<LocatedHandles<'a>> {
        let mut num_handles: usize = 0;
        let mut handles: *mut EfiHandle = null_mut();
        // SAFETY: EFI_BOOT_SERVICES method call.
        unsafe {
            efi_call!(
                self.boot_services.locate_handle_buffer,
                EFI_LOCATE_HANDLE_SEARCH_TYPE_BY_PROTOCOL,
                &T::GUID,
                null_mut(),
                &mut num_handles as *mut usize as *mut _,
                &mut handles as *mut *mut EfiHandle
            )?
        };

        // SAFETY:
        // * If the call to `locate_handle_buffer` succeeded,
        //   `handles` should point to a `num_handles` length array
        //   of DeviceHandles.
        // * This code transfers ownership of the `handles` pointer.
        Ok(unsafe {
            LocatedHandles::new_allocated(
                NonNull::new(handles).ok_or(Error::InvalidInput)?,
                num_handles,
                &self.efi_entry,
            )
        })
    }

    /// Search and open the first found target EFI protocol.
    pub fn find_first_and_open<T: ProtocolImpl>(&self) -> Result<Protocol<'a, T>> {
        // The `open_protocol` and Protocol structure need a device handle,
        // so we can't use EFI_BOOT_SERVICES.LocateProtocol().
        //
        // Try locating handles first using an automatically allocated array.
        // If the array isn't big enough, fall back to dynamically allocating the array.
        let mut handles = [DeviceHandle::new(null()); Self::LOCATE_HANDLE_BUFFER_SIZE];
        let helper = |hs| match self.locate_handles_by_protocol::<T>(hs) {
            Ok(h) => Ok(h),
            Err(Error::BufferTooSmall(_)) => self.locate_handle_buffer_by_protocol::<T>(),
            Err(e) => Err(e),
        };

        helper(&mut handles)
            .and_then(|l| l.handles().first().cloned().ok_or(Error::NotFound))
            .inspect_err(|_| log_missing_protocol::<T>(self.efi_entry))
            .and_then(|handle| self.open_protocol::<T>(handle))
    }

    /// Wrapper of `EFI_BOOT_SERVICES.GetMemoryMap()`.
    ///
    /// On `EFI_BUFFER_TOO_SMALL`, returns the required size in [`Error::BufferTooSmall`].
    pub fn get_memory_map<'b>(&self, mmap_buffer: &'b mut [u8]) -> Result<EfiMemoryMap<'b>> {
        let mut mmap_size = mmap_buffer.len();
        let mut map_key: usize = 0;
        let mut descriptor_size: usize = 0;
        let mut descriptor_version: u32 = 0;
        // SAFETY: EFI_BOOT_SERVICES method call.
        unsafe {
            efi_call!(
                @bufsize mmap_size,
                self.boot_services.get_memory_map,
                &mut mmap_size,
                mmap_buffer.as_mut_ptr() as *mut _,
                &mut map_key,
                &mut descriptor_size,
                &mut descriptor_version
            )?;
        }
        Ok(EfiMemoryMap::new(
            &mut mmap_buffer[..mmap_size],
            map_key,
            descriptor_size,
            descriptor_version,
        ))
    }

    /// Returns the buffer size `EFI_BOOT_SERVICES.GetMemoryMap()` currently requires.
    ///
    /// Use this rather than measuring a successful call. A successful call reports the map as
    /// written, and firmware that compacts its OS-facing map writes fewer bytes than the next
    /// call will demand. A subsequent allocation can increase this size, so callers must add
    /// headroom.
    pub fn memory_map_size(&self) -> Result<usize> {
        match self.get_memory_map(&mut []) {
            Err(Error::BufferTooSmall(Some(size))) => Ok(size),
            // No conforming implementation claims a map fits in nothing.
            Ok(_) => Err(Error::InvalidState),
            Err(e) => Err(e),
        }
    }

    /// Wrapper of `EFI_BOOT_SERVICES.InstallConfigurationTable()`.
    ///
    /// # Safety
    ///
    /// If `table` is non-NULL, the memory pointed to by `table` must remain allocated and valid
    /// for as long as it is accessed via the System Table.
    pub unsafe fn install_configuration_table(
        &self,
        guid: &EfiGuid,
        table: *mut core::ffi::c_void,
    ) -> Result<()> {
        // SAFETY:
        // * `self.boot_services.install_configuration_table` points to an EFIAPI function or NULL.
        // * `guid` and `table` outlives the call.
        unsafe {
            efi_call!(self.boot_services.install_configuration_table, guid as *const _, table)
        }
    }

    /// Wrapper of `EFI_BOOT_SERVICE.ExitBootServices()`.
    fn exit_boot_services<'b>(&self, mmap: &'b EfiMemoryMap<'b>) -> Result<()> {
        // SAFETY: EFI_BOOT_SERVICES method call.
        unsafe {
            efi_call!(
                self.boot_services.exit_boot_services,
                self.efi_entry.image_handle().0,
                mmap.map_key()
            )
        }
    }

    /// Wrapper of `EFI_BOOT_SERVICE.Stall()`.
    pub fn stall(&self, micro: usize) -> Result<()> {
        // SAFETY: EFI_BOOT_SERVICES method call.
        unsafe { efi_call!(self.boot_services.stall, micro) }
    }

    /// Wraps `EFI_BOOT_SERVICE.CreateEvent()`.
    ///
    /// This function creates an event without a notification callback function; to create an event
    /// with a notification, see [create_event_with_notification].
    ///
    /// # Arguments
    /// * `event_type`: The EFI event type.
    pub fn create_event(&self, event_type: EventType) -> Result<Event<'a, 'static>> {
        let mut efi_event: EfiEvent = null_mut();
        // SAFETY:
        // * all parameters obey the `CreateEvent()` spec
        // * on success we take ownership of the provided `efi_event`
        unsafe {
            efi_call!(
                self.boot_services.create_event,
                event_type as u32,
                0,
                None,
                null_mut(),
                &mut efi_event
            )?;
        }
        Ok(Event::new(self.efi_entry, efi_event, None))
    }

    /// Wraps `EFI_BOOT_SERVICE.CreateEvent()`.
    ///
    /// This function creates an event with a notification callback function.
    ///
    /// Unlike [create_event], this function is unsafe because the callback will be executed
    /// concurrently with the main application code at a higher interrupt level, and there are
    /// a few cases where this can lead to races.
    ///
    /// # Arguments
    /// * `event_type`: The EFI event type.
    /// * `cb`: An [EventNotify] which implements the event notification function and provides the
    ///         task level priority setting.
    ///
    /// # Safety
    /// Most of the safety conditions are enforced at compile-time by the [Sync] requirement on
    /// [EventNotifyCallback] - this ensures that e.g. callers cannot capture their raw [EfiEntry]
    /// in a callback, but will need to wrap it in a [Sync] type which will ensure safe sharing
    /// between the main application and the callback.
    ///
    /// The exception is the global allocation and panic hooks, which use a separate global
    /// [EfiEntry] that is not synchronized outside the main application. The caller must ensure
    /// that the main application code is not using its [EfiEntry] while a notification callback
    /// is trying to concurrently use the global [EfiEntry].
    ///
    /// The easiest way to accomplish this is to write notifications callbacks that:
    /// * do not allocate or deallocate heap memory
    /// * do not panic
    /// Callbacks following these guidelines are safe as they do not use the global [EfiEntry].
    ///
    /// If that is not possible, then the caller must ensure that nothing else makes any calls into
    /// UEFI while the returned [Event] is alive; the callback function must have exclusive access
    /// to the UEFI APIs so it can use the globals without triggering UEFI reentry.
    ///
    /// In unittests there is no global [EfiEntry] so this is always safe.
    pub unsafe fn create_event_with_notification<'e>(
        &self,
        event_type: EventType,
        notify: &'e mut EventNotify,
    ) -> Result<Event<'a, 'e>> {
        let mut efi_event: EfiEvent = null_mut();
        // SAFETY:
        // Pointers passed are output/callback context pointers which will not be retained by the
        // callback (`fn efi_event_cb()`).
        // The returned `Event` enforces a borrow to `cb` for 'e. It closes the event when it
        // goes out of scope. This ensures that `cb` lives at least as long as the event is in
        // effect and there can be no other borrows to `cb`.
        unsafe {
            efi_call!(
                self.boot_services.create_event,
                event_type as u32,
                notify.tpl as usize,
                Some(efi_event_cb),
                notify as *mut _ as *mut _,
                &mut efi_event
            )?;
        }
        Ok(Event::new(self.efi_entry, efi_event, Some(notify.cb)))
    }

    /// Wrapper of `EFI_BOOT_SERVICE.CloseEvent()`.
    fn close_event(&self, event: &Event) -> Result<()> {
        // SAFETY: EFI_BOOT_SERVICES method call.
        unsafe { efi_call!(self.boot_services.close_event, event.efi_event) }
    }

    /// Wrapper of `EFI_BOOT_SERVICE.CheckEvent()`.
    ///
    /// On success, returns true if the event is signaled, false if not.
    pub fn check_event(&self, event: &Event) -> Result<bool> {
        // SAFETY: EFI_BOOT_SERVICES method call.
        match unsafe { efi_call!(self.boot_services.check_event, event.efi_event) } {
            Err(e) if e != Error::NotReady => Err(e),
            Ok(()) => Ok(true),
            _ => Ok(false),
        }
    }

    /// Wrapper of `EFI_BOOT_SERVICE.SetTimer()`.
    pub fn set_timer(
        &self,
        event: &Event,
        delay_type: EfiTimerDelay,
        trigger_time: Duration,
    ) -> Result<()> {
        // SAFETY: EFI_BOOT_SERVICES method call.
        unsafe {
            efi_call!(
                self.boot_services.set_timer,
                event.efi_event,
                delay_type,
                (trigger_time.as_nanos() / 100).try_into()?
            )
        }
    }

    /// Wrapper of `EFI_BOOT_SERVICE.SetWatchdogTimer()`.
    pub fn set_watchdog_timer(&self, timeout: Duration, code: WatchdogTimerCode) -> Result<()> {
        // SAFETY:
        // `watchdog_data` is allowed to be a null pointer if `data_size` is 0.
        unsafe {
            efi_call!(
                self.boot_services.set_watchdog_timer,
                timeout.as_secs().try_into()?,
                code.0,
                // Watchdog data is optional.
                0,
                null_mut(),
            )
        }
    }

    /// Wrapper of `EFI_BOOT_SERVICE.HandleProtocol()`.
    pub fn handle_protocol<T: ProtocolInfo>(
        &self,
        handle: DeviceHandle,
    ) -> Result<Protocol<'a, T>> {
        let mut interface: *mut T::InterfaceType = null_mut();

        // SAFETY:
        // `interface` is an output parameter. It is not retained and outlives the call.
        unsafe {
            efi_call!(
                self.boot_services.handle_protocol,
                handle.0,
                &T::GUID,
                &mut interface as *mut _ as *mut _
            )?;
        }

        // SAFETY:
        // * `interface` is not retained by `handle_protocol`.
        // * It is the responsibility of `boot_services.handle_protocol`
        //   to set `interface` to a valid value.
        Ok(unsafe {
            Protocol::<T>::new(
                handle,
                core::ptr::NonNull::new(interface).ok_or(Error::NotFound)?,
                self.efi_entry,
            )
        })
    }

    /// Installs a null protocol interface on a handle with
    /// `EFI_BOOT_SERVICES.InstallProtocolInterface()`.
    ///
    /// A null interface can be installed if no data structure are associated with protocol.
    pub fn install_null_protocol_interface(
        &self,
        handle: &mut EfiHandle,
        protocol: &EfiGuid,
    ) -> Result<()> {
        // SAFETY:
        // * `self.boot_services.install_protocol_interface` points to an EFIAPI function or NULL.
        // * `handle` and `protocol` outlives the call.
        unsafe {
            efi_call!(
                self.boot_services.install_protocol_interface,
                handle as *mut _,
                protocol as *const _,
                EFI_INTERFACE_TYPE_EFI_NATIVE_INTERFACE,
                null_mut()
            )
        }
    }

    /// Installs a protocol interface from a Rust implementation.
    ///
    /// This is a convenience function that creates a [Provider] from a Rust implementation
    /// and installs it as a protocol interface.
    ///
    /// The method allocates and leaks a [Provider] for each protocol installed.
    pub fn install_protocol_from_rust<T: ProtocolInfo, R>(
        &self,
        handle: Option<&mut EfiHandle>,
        rust_impl: &'static R,
    ) -> Result<()>
    where
        T::InterfaceType: Identified + BridgeToRust<R>,
    {
        let mut null: EfiHandle = null_mut();
        let handle = handle.unwrap_or(&mut null);
        let provider = Box::pin(Provider::<T::InterfaceType, R>::new(rust_impl));
        // SAFETY:
        // * `handle` is an optional output parameter. It is either NULL or points to a valid
        //   handle. It is not retained and outlives the call.
        // * `provider` is immediately leaked and ownership is fully given to the UEFI firmware.
        unsafe {
            efi_call!(
                self.boot_services.install_protocol_interface,
                handle as *mut _,
                &T::GUID,
                EFI_INTERFACE_TYPE_EFI_NATIVE_INTERFACE,
                provider.as_ref().to_ptr() as *mut _ as _
            )?;
        }
        core::mem::forget(provider);
        Ok(())
    }

    /// Loads an EFI application.
    ///
    /// On success, [`LoadedEfiImage`] is returned which represents the loaded image.
    /// The image can be started by calling [`LoadedEfiImage::start`].
    ///
    /// # Safety
    ///
    /// Caller must guarantee that `src` is a valid EFI application
    pub unsafe fn load_image(&self, src: &[u8]) -> Result<LoadedEfiImage<'a>> {
        let mut image_handle: EfiHandle = null_mut();

        // NOTE: UEFI spec defines the "source" buffer as a non-const pointer, which
        // technically allows modification of the buffer in the backend. However, in practice
        // it is treated as read-only. We pass an immutable slice pointer here as it is
        // unlikely to be modified and more idiomatic for our APIs.

        // SAFETY:
        // * `image_handle` is an output parameter. It is not retained and outlives the call.
        // * `src` is a valid slice and outlives the call.
        // * `parent_image_handle` is a valid handle for output and outlives the call.
        unsafe {
            efi_call!(
                self.boot_services.load_image,
                true, // Ignored since we use source buffer.
                self.efi_entry.image_handle().0,
                null_mut(),
                src.as_ptr() as _,
                src.len(),
                &mut image_handle
            )?;
        }

        let protocol = self
            .open_protocol::<LoadedImageProtocol>(DeviceHandle::new(image_handle))
            .inspect_err(|e| {
            efi_println!(
                self.efi_entry,
                "Failed to open LoadedImageProtocol on image handle: {e:?}",
            )
        })?;

        Ok(LoadedEfiImage { efi_entry: self.efi_entry, image_handle, protocol })
    }
}

/// A loaded EFI image.
pub struct LoadedEfiImage<'a> {
    efi_entry: &'a EfiEntry,
    /// Handle of the loaded EFI image.
    pub image_handle: EfiHandle,
    /// `LoadedImageProtocol` for the loaded image.
    pub protocol: Protocol<'a, LoadedImageProtocol>,
}

impl LoadedEfiImage<'_> {
    /// Starts the loaded EFI application.
    pub fn start(self) -> Result<()> {
        let mut exit_data_size: usize = 0;
        let bs = self.efi_entry.system_table().boot_services().boot_services;
        // SAFETY:
        // * `exit_data` is an optional output parameter and set to NULL.
        // * `exit_data_size` is an output parameter. It is not retained and outlives the call.
        //   The value is set to 0 to indicate exit_data is not used.
        unsafe { efi_call!(bs.start_image, self.image_handle, &mut exit_data_size, null_mut()) }
    }

    /// Returns the memory range occupied by the loaded EFI image.
    pub fn loaded_range(&self) -> core::ops::Range<usize> {
        let base = self.protocol.image_base();
        let size = usize::try_from(self.protocol.interface().image_size).unwrap();
        base..base.checked_add(size).unwrap()
    }
}

/// `RuntimeServices` provides methods for accessing various EFI_RUNTIME_SERVICES interfaces.
#[derive(Copy, Clone)]
pub struct RuntimeServices {
    runtime_services: EfiRuntimeService,
}

impl RuntimeServices {
    /// Wrapper of `EFI_RUNTIME_SERVICES.GetVariable()`.
    pub fn get_variable(&self, guid: &EfiGuid, name: &str, out: &mut [u8]) -> Result<usize> {
        let mut size = out.len();

        let mut name_utf16: Vec<u16> = name.encode_utf16().collect();
        name_utf16.push(0); // null-terminator

        // SAFETY:
        // * `&mut size` and `&mut out` are input/output params only and will not be retained
        // * `&mut size` and `&mut out` are valid pointers and outlive the call
        unsafe {
            efi_call!(
                @bufsize size,
                self.runtime_services.get_variable,
                name_utf16.as_ptr(),
                guid,
                null_mut(),
                &mut size,
                out.as_mut_ptr() as *mut core::ffi::c_void
            )?;
        }
        Ok(size)
    }

    /// Wrapper of `EFI_RUNTIME_SERVICES.SetVariable()`.
    pub fn set_variable(&self, guid: &EfiGuid, name: &str, data: &[u8]) -> Result<()> {
        let mut name_utf16: Vec<u16> = name.encode_utf16().collect();
        name_utf16.push(0); // null-terminator

        // SAFETY:
        // * `data.as_mut_ptr()` and `name_utf16.as_ptr()` are valid pointers,
        // * outlive the call, and are not retained.
        unsafe {
            efi_call!(
                self.runtime_services.set_variable,
                name_utf16.as_ptr(),
                guid,
                0,
                data.len(),
                data.as_ptr() as *const core::ffi::c_void
            )
        }
    }

    /// Wrapper of `EFI_RUNTIME_SERVICES.reset_system`.
    pub fn reset_system(
        &self,
        reset_type: EfiResetType,
        reset_status: EfiStatus,
        reset_data: Option<&mut [u8]>,
    ) -> Result<!> {
        let (reset_data_len, reset_data_ptr) = match reset_data {
            Some(v) => (v.len(), v.as_mut_ptr() as _),
            _ => (0, null_mut()),
        };
        // SAFETY:
        // * `reset_data_ptr` is either a valid pointer or NULL which by UEFI spec is allowed.
        // * The call reboots the device and thus is not expected to return.
        unsafe {
            self.runtime_services.reset_system.unwrap()(
                reset_type,
                reset_status,
                reset_data_len,
                reset_data_ptr,
            );
        }

        Err(Error::Aborted)
    }

    /// Performs a cold reset without status code or data.
    pub fn cold_reset(&self) -> Result<!> {
        self.reset_system(EFI_RESET_TYPE_COLD, EFI_STATUS_SUCCESS, None)
    }

    /// Shutdown the system.
    pub fn shutdown(&self) -> Result<!> {
        self.reset_system(EFI_RESET_TYPE_SHUTDOWN, EFI_STATUS_SUCCESS, None)
    }
}

/// EFI Event type to pass to BootServicess::create_event.
/// See UEFI documentation for details.
#[allow(missing_docs)]
#[repr(u32)]
pub enum EventType {
    Timer = EFI_EVENT_TYPE_TIMER.0,
    RunTime = EFI_EVENT_TYPE_RUNTIME.0,
    NotifyWait = EFI_EVENT_TYPE_NOTIFY_WAIT.0,
    NotifySignal = EFI_EVENT_TYPE_NOTIFY_SIGNAL.0,
    SignalExitBootServices = EFI_EVENT_TYPE_SIGNAL_EXIT_BOOT_SERVICES.0,
    SignalVirtualAddressChange = EFI_EVENT_TYPE_SIGNAL_VIRTUAL_ADDRESS_CHANGE.0,

    // Valid combinations:
    TimerNotifySignal = EFI_EVENT_TYPE_TIMER.0 | EFI_EVENT_TYPE_NOTIFY_SIGNAL.0,
}

/// EFI task level priority setting for event notify function.
/// See UEFI documentation for details.
#[allow(missing_docs)]
#[repr(usize)]
#[derive(Copy, Clone)]
pub enum Tpl {
    Application = 4,
    Callback = 8,
    Notify = 16,
    HighLevel = 31,
}

/// Event notification callback function.
///
/// The callback function itself takes the [EfiEvent] as an argument and has no return value.
/// This type is a mutable borrow of a closure to ensure that it will outlive the [EfiEvent] and
/// that the callback has exclusive access to it.
///
/// Additionally, the function must be [Sync] because it will be run concurrently to the main app
/// code at a higher interrupt level. One consequence of this is that we cannot capture an
/// [EfiEntry] or any related object in the closure, as they are not [Sync]. This is intentional;
/// in general UEFI APIs are not reentrant except in very limited ways, and we could trigger
/// undefined behavior if we try to call into UEFI while the main application code is also in the
/// middle of a UEFI call. Instead, the notification should signal the main app code to make any
/// necessary UEFI calls once it regains control.
pub type EventNotifyCallback<'a> = &'a mut (dyn FnMut(EfiEvent) + Sync);

/// `EventNotify` contains the task level priority setting and a mutable reference to a
/// closure for the callback. It is passed as the context pointer to low level EFI event
/// notification function entry (`unsafe extern "efiapi" fn efi_event_cb(...)`).
pub struct EventNotify<'e> {
    tpl: Tpl,
    cb: EventNotifyCallback<'e>,
}

impl<'e> EventNotify<'e> {
    /// Creates a new [EventNotify].
    pub fn new(tpl: Tpl, cb: EventNotifyCallback<'e>) -> Self {
        Self { tpl, cb }
    }
}

/// `Event` wraps the raw `EfiEvent` handle and internally enforces a borrow of the registered
/// callback for the given life time `'n`. The event is automatically closed when going out of
/// scope.
pub struct Event<'a, 'n> {
    // If `efi_entry` is None, it represents an unowned Event and won't get closed on drop.
    efi_entry: Option<&'a EfiEntry>,
    efi_event: EfiEvent,
    // The actual callback has been passed into UEFI via raw pointer in [create_event], so we
    // use [PhantomData] to ensure the callback will outlive the event.
    cb: PhantomData<Option<EventNotifyCallback<'n>>>,
}

impl<'a, 'n> Event<'a, 'n> {
    /// Creates an instance of owned `Event`. The `Event` is closed when going out of scope.
    fn new(
        efi_entry: &'a EfiEntry,
        efi_event: EfiEvent,
        _cb: Option<EventNotifyCallback<'n>>,
    ) -> Self {
        Self { efi_entry: Some(efi_entry), efi_event, cb: PhantomData }
    }

    /// Creates an  unowned `Event`. The `Event` is not closed when going out of scope.
    // TODO allow unused?
    #[allow(dead_code)]
    fn new_unowned(efi_event: EfiEvent) -> Self {
        Self { efi_entry: None, efi_event: efi_event, cb: PhantomData }
    }
}

impl Drop for Event<'_, '_> {
    fn drop(&mut self) {
        if let Some(efi_entry) = self.efi_entry {
            efi_entry.system_table().boot_services().close_event(self).unwrap();
        }
    }
}

/// Event notify function entry for EFI events.
///
/// Safety:
///
///   `ctx` must point to a `EventNotify` type object.
///   `ctx` must live longer than the event.
///   There should be no other references to `ctx`.
unsafe extern "efiapi" fn efi_event_cb(event: EfiEvent, ctx: *mut core::ffi::c_void) {
    // SAFETY: By safety requirement of this function, ctx points to a valid `EventNotify` object,
    // outlives the event/the function call, and there is no other borrows.
    let event_cb = unsafe { (ctx as *mut EventNotify).as_mut() }.unwrap();
    (event_cb.cb)(event);
}

/// A type for accessing memory map.
#[derive(Debug)]
pub struct EfiMemoryMap<'a> {
    buffer: &'a mut [u8],
    map_key: usize,
    descriptor_size: usize,
    descriptor_version: u32,
}

/// Iterator for traversing `EfiMemoryDescriptor` items in `EfiMemoryMap::buffer`.
pub struct EfiMemoryMapIter<'a: 'b, 'b> {
    memory_map: &'b EfiMemoryMap<'a>,
    offset: usize,
}

impl<'a, 'b> Iterator for EfiMemoryMapIter<'a, 'b> {
    type Item = &'b EfiMemoryDescriptor;

    fn next(&mut self) -> Option<Self::Item> {
        if self.offset >= self.memory_map.buffer.len() {
            return None;
        }
        let bytes = &self.memory_map.buffer[self.offset..][..self.memory_map.descriptor_size];
        self.offset += self.memory_map.descriptor_size;
        Some(Ref::into_ref(Ref::<_, EfiMemoryDescriptor>::new_from_prefix(bytes).unwrap().0))
    }
}

impl<'a> EfiMemoryMap<'a> {
    /// Creates a new instance with the given parameters obtained from `get_memory_map()`.
    fn new(
        buffer: &'a mut [u8],
        map_key: usize,
        descriptor_size: usize,
        descriptor_version: u32,
    ) -> Self {
        Self { buffer, map_key, descriptor_size, descriptor_version }
    }

    /// Returns the buffer.
    pub fn buffer(&self) -> &[u8] {
        self.buffer
    }

    /// Returns the value of `map_key`.
    pub fn map_key(&self) -> usize {
        self.map_key
    }

    /// Returns the value of `descriptor_version`.
    pub fn descriptor_version(&self) -> u32 {
        self.descriptor_version
    }

    /// Returns the value of `descriptor_size`.
    pub fn descriptor_size(&self) -> usize {
        self.descriptor_size
    }

    /// Returns the number of descriptors.
    pub fn len(&self) -> usize {
        self.buffer.len() / self.descriptor_size
    }
}

impl<'a: 'b, 'b> IntoIterator for &'b EfiMemoryMap<'a> {
    type Item = &'b EfiMemoryDescriptor;
    type IntoIter = EfiMemoryMapIter<'a, 'b>;

    fn into_iter(self) -> Self::IntoIter {
        EfiMemoryMapIter { memory_map: self, offset: 0 }
    }
}

/// A type for accessing Memory attributes table
pub struct EfiMemoryAttributesTable<'a> {
    /// EfiMemoryAttributesTable header
    pub header: &'a EfiMemoryAttributesTableHeader,
    tail: &'a [u8],
}

/// Iterator for traversing `EfiMemoryAttributesTable` descriptors.
pub struct EfiMemoryAttributesTableIter<'a> {
    descriptor_size: usize,
    tail: &'a [u8],
}

impl<'a> Iterator for EfiMemoryAttributesTableIter<'a> {
    type Item = &'a EfiMemoryDescriptor;

    fn next(&mut self) -> Option<Self::Item> {
        // Descriptor size can be greater than `EfiMemoryDescriptor`, so we potentially slice off
        // pieces greater than struct size. Thus can't just convert buffer to slice of
        // corresponding type.
        if let Some((desc_bytes, tail_new)) = self.tail.split_at_checked(self.descriptor_size) {
            let desc = Ref::into_ref(
                Ref::<_, EfiMemoryDescriptor>::new_from_prefix(desc_bytes).unwrap().0,
            );
            self.tail = tail_new;
            Some(desc)
        } else {
            None
        }
    }
}

impl<'a> EfiMemoryAttributesTable<'a> {
    /// Creates a new instance with the given parameters obtained from `get_memory_map()`.
    ///
    /// # Returns
    /// Ok(EfiMemoryAttributesTable) - on success
    /// Err(Error::NotFound) - if table type is incorrect
    /// Err(e) - if error `e` occurred parsing table buffer
    //
    // SAFETY:
    // `configuration_table` must be valid EFI Configuration Table object.
    pub unsafe fn new(
        configuration_table: EfiConfigurationTable,
    ) -> Result<EfiMemoryAttributesTable<'a>> {
        if configuration_table.vendor_guid != EFI_MEMORY_ATTRIBUTES_GUID {
            return Err(Error::NotFound);
        }
        let buf = configuration_table.vendor_table;

        // SAFETY: Buffer provided by EFI configuration table.
        let header = unsafe {
            let header_bytes =
                from_raw_parts(buf as *const u8, size_of::<EfiMemoryAttributesTableHeader>());
            EfiMemoryAttributesTableHeader::ref_from(header_bytes).ok_or(Error::InvalidInput)?
        };

        // Note: `descriptor_size` may be bigger than `EfiMemoryDescriptor`.
        let descriptor_size: usize = header.descriptor_size.try_into().unwrap();
        let descriptors_count: usize = header.number_of_entries.try_into().unwrap();

        // SAFETY: Buffer provided by EFI configuration table.
        let tail = unsafe {
            from_raw_parts(
                (buf as *const u8).add(core::mem::size_of_val(header)),
                descriptors_count * descriptor_size,
            )
        };

        Ok(Self { header, tail })
    }
}

impl<'a> IntoIterator for &EfiMemoryAttributesTable<'a> {
    type Item = &'a EfiMemoryDescriptor;
    type IntoIter = EfiMemoryAttributesTableIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        let descriptor_size = usize::try_from(self.header.descriptor_size).unwrap();
        let tail = &self.tail[..];
        EfiMemoryAttributesTableIter { descriptor_size, tail }
    }
}

/// A type representing a UEFI handle to a UEFI device.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct DeviceHandle(EfiHandle);

impl DeviceHandle {
    /// Public constructor
    pub fn new(handle: EfiHandle) -> Self {
        Self(handle)
    }
}

/// `LocatedHandles` holds the array of handles returned by
/// `BootServices::locate_handle_buffer_by_protocol()` or
/// `BootServices::locate_handles_by_protocol()`.
pub enum LocatedHandles<'a> {
    /// The handle buffer was allocated dynamically and must be explicitly freed.
    Allocated {
        /// The handles
        handles: &'a [DeviceHandle],
        /// Efi entry
        efi_entry: &'a EfiEntry,
    },
    /// The handle buffer has been borrowed.
    Borrowed(&'a [DeviceHandle]),
}

impl<'a> LocatedHandles<'a> {
    /// SAFETY:
    /// * `handles` is a non-null dynamically allocated pointer to `len` EfiHandles.
    /// * No other code has access to `handles` after the call.
    pub(crate) unsafe fn new_allocated(
        handles: NonNull<EfiHandle>,
        len: usize,
        efi_entry: &'a EfiEntry,
    ) -> Self {
        Self::Allocated {
            // SAFETY:
            // * It is the caller's responsibility to guarantee that `handles` is a
            //   valid array of DeviceHandle of size `len`.
            // * It is the caller's responsibility to guarantee that no other code
            //   can access `handles` after the call.
            handles: unsafe { from_raw_parts(handles.as_ptr() as *const DeviceHandle, len) },
            efi_entry: efi_entry,
        }
    }

    pub(crate) fn new_borrowed(handles: &'a [DeviceHandle]) -> Self {
        Self::Borrowed(handles)
    }

    /// Get the list of handles as a slice.
    pub fn handles(&self) -> &[DeviceHandle] {
        match self {
            Self::Allocated { handles, .. } => handles,
            Self::Borrowed(handles) => handles,
        }
    }
}

impl Drop for LocatedHandles<'_> {
    fn drop(&mut self) {
        if let Self::Allocated { handles, efi_entry } = self {
            efi_entry.system_table().boot_services().free_pool(handles.as_ptr() as *mut _).unwrap();
        }
    }
}

/// Helper macro for printing message via `EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL` in
/// `EFI_SYSTEM_TABLE.ConOut`.
#[macro_export]
macro_rules! efi_print {
    ( $efi_entry:expr, $( $x:expr ),* $(,)? ) => {
        {
            use core::fmt::Write;
            write!($efi_entry.system_table().con_out().unwrap(), $($x,)*).unwrap();
        }
    };
}

/// Similar to [efi_print!], but automatically adds the UEFI newline sequence (`\r\n`).
#[macro_export]
macro_rules! efi_println {
    ( $efi_entry:expr, $( $x:expr ),* $(,)? ) => {
        {
            // Can also use EFI_TIMESTAMP_PROTOCOL if provided.
            let _ = $crate::arch_timestamp().inspect(|v| {
                $crate::efi_print!($efi_entry, "[{:.4}] ", v.as_secs_f32());
            });
            $crate::efi_print!($efi_entry, $($x,)*);
            $crate::efi_print!($efi_entry, "\r\n");
        }
    };
}

mod log_fatal {
    use crate::{protocol, EfiEntry};
    use efi_types::defs::GblEfiDebugErrorTag;

    /// Control flow token to force fatal error logging before invoking `reset()`.
    pub(super) struct FatalErrorToken(());

    impl FatalErrorToken {
        fn new() -> Self {
            Self(())
        }
    }

    /// Generic internal code for fatal errors.
    /// In the long term, to improve flexibility, consider allowing application to
    /// install a custom handler into `EfiEntry` to be called here.
    ///
    /// Note: std::panic::PanicHookInfo and core::panic::PanicInfo are (now) different
    ///       types, but we just want to print the panic info out, so just require Display.
    pub(super) fn report_fatal_error_and_reset_internal<P: core::fmt::Display, T>(
        entry: &EfiEntry,
        panic: &P,
        tag: GblEfiDebugErrorTag,
        reset_func: fn(&EfiEntry, FatalErrorToken) -> T,
    ) -> T {
        efi_print!(entry, "Fatal error! {}\r\n", panic);
        let _ = entry
            .system_table()
            .boot_services()
            .find_first_and_open::<protocol::gbl_efi_debug::GblDebugProtocol>()
            .map(|protocol| protocol.fatal_error(tag));

        reset_func(entry, FatalErrorToken::new())
    }
}

/// "Panic function" for test code.
///
/// Call directly to panic while passing an explicit error tag.
#[cfg(test)]
fn report_error_and_reset<P: core::fmt::Display>(
    entry: &EfiEntry,
    panic_info: &P,
    tag: GblEfiDebugErrorTag,
) {
    fn reset(entry: &EfiEntry, _: log_fatal::FatalErrorToken) {
        efi_print!(entry, "Resetting...\r\n");
        test::efi_call_traces().with(|traces| {
            traces
                .borrow_mut()
                .reset_trace
                .inputs
                .push_back((EFI_RESET_TYPE_COLD, EFI_STATUS_DEVICE_ERROR))
        })
    }

    log_fatal::report_fatal_error_and_reset_internal(entry, panic_info, tag, reset)
}

/// Production panic function.
///
/// Call directly to panic while passing an explicit error tag.
#[cfg(not(test))]
pub fn report_error_and_reset<P: core::fmt::Display>(
    entry: &EfiEntry,
    panic_info: &P,
    tag: GblEfiDebugErrorTag,
) -> ! {
    fn reset(entry: &EfiEntry, _: log_fatal::FatalErrorToken) -> ! {
        efi_print!(entry, "Resetting...\r\n");
        match allocation::internal_efi_entry_and_rt().1 {
            Some(rt) => {
                let _ = rt
                    .reset_system(EFI_RESET_TYPE_COLD, EFI_STATUS_DEVICE_ERROR, None)
                    .inspect_err(|_| efi_print!(entry, "Failed to reset system. Hanging...\r\n"));
            }
            _ => efi_print!(entry, "Runtime services not supported. Hanging...\r\n"),
        }
        loop {}
    }

    log_fatal::report_fatal_error_and_reset_internal(entry, panic_info, tag, reset)
}

/// Calls `report_error_and_reset` with the global EFI entry.
/// Register this function as a panic handler within the main.rs of your EFI application
///
/// Don't set this as the panic handler within libefi so that other crates' tests
/// can depend on libefi.
///
/// Safety:
/// * It is the caller's responsibility to guarantee that the global EfiEntry has
///   been initialized and is live and valid.
pub unsafe fn report_error_and_reset_with_global_entry<P: core::fmt::Display>(
    panic_info: &P,
    tag: GblEfiDebugErrorTag,
) -> ! {
    // Safety:
    // * It is the caller's responsibility to guarantee that the global EfiEntry has
    //   been initialized and is live and valid.
    let _ = unsafe {
        with_global_efi_entry::<_, ()>(|entry| report_error_and_reset(entry, panic_info, tag))
    };
    loop {}
}

/// Cryptographic hash interfaces based on the EfiHash2Protocol.
pub mod hash2 {
    /// Re-export public interfaces.
    /// These helper types have to live with the protocol implementation but are
    /// higher-level wrappers that don't directly correspond to the protocol API.
    pub use crate::protocol::hash2::{hash, HashAlgorithm, Hasher, Sha1, Sha256, Sha512};
}

#[cfg(test)]
mod allocation {
    /// Try to print via `EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL` in `EFI_SYSTEM_TABLE.ConOut`.
    ///
    /// Errors are ignored.
    #[macro_export]
    macro_rules! efi_try_print {
        ($( $x:expr ),* $(,)? ) => {
            use core::fmt::Write;
            $crate::test::efi_call_traces().with(|traces| {
                write!(traces.borrow_mut().console_out_trace, $($x,)*).unwrap();
            });
        };
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::protocol::{block_io::BlockIoProtocol, ProtocolInfo, Requirement, Revision};
    use crate::DeviceHandle;
    use alloc::string::String;
    use core::ptr::{from_mut, NonNull};
    use efi_types::{
        EfiBlockIoProtocol, EfiEventNotify, EfiHandle, EfiLocateHandleSearchType,
        EfiMemoryAttribute, EfiOpenProtocolAttributes, EfiSimpleTextOutputProtocol, EfiStatus,
        EfiTpl, GblEfiDebugErrorTag, GblEfiDebugProtocol, EFI_MEMORY_TYPE_LOADER_CODE,
        EFI_MEMORY_TYPE_LOADER_DATA, EFI_STATUS_BUFFER_TOO_SMALL, EFI_STATUS_DEVICE_ERROR,
        EFI_STATUS_INVALID_PARAMETER, EFI_STATUS_NOT_FOUND, EFI_STATUS_NOT_READY,
        EFI_STATUS_SUCCESS, EFI_STATUS_UNSUPPORTED, EFI_TIMER_DELAY_TIMER_PERIODIC,
        GBL_EFI_DEBUG_ERROR_TAG_ASSERTION_ERROR,
    };
    use std::{
        cell::RefCell,
        collections::VecDeque,
        mem::size_of,
        panic::{catch_unwind, set_hook, take_hook, PanicHookInfo},
        slice::from_raw_parts_mut,
        sync::{Arc, Mutex},
    };
    use utils::RecurringTimer;
    use zerocopy::IntoBytes;

    /// Helper function to generate a Protocol from an interface type.
    pub fn generate_protocol<'a, P: ProtocolInfo>(
        efi_entry: &'a EfiEntry,
        proto: &'a mut P::InterfaceType,
    ) -> Protocol<'a, P> {
        // SAFETY: proto is a valid pointer and lasts at least as long as efi_entry.
        unsafe {
            Protocol::<'a, P>::new(
                DeviceHandle::new(null_mut()),
                NonNull::new(from_mut(proto)).unwrap(),
                efi_entry,
            )
        }
    }

    /// A structure to store the traces of arguments/outputs for EFI methods.
    #[derive(Default)]
    pub struct EfiCallTraces {
        pub check_event_trace: CheckEventTrace,
        pub close_event_trace: CloseEventTrace,
        // Special case
        pub console_out_trace: ConsoleOutTrace,
        pub create_event_trace: CreateEventTrace,
        pub exit_boot_services_trace: ExitBootServicespTrace,
        pub free_pool_trace: FreePoolTrace,
        pub get_memory_map_trace: GetMemoryMapTrace,
        pub handle_protocol_trace: HandleProtocolTrace,
        pub locate_handle_buffer_trace: LocateHandleBufferTrace,
        pub locate_handle_trace: LocateHandleTrace,
        pub open_protocol_trace: OpenProtocolTrace,
        pub reset_trace: ResetTrace,
        pub set_timer_trace: SetTimerTrace,
        pub set_watchdog_timer_trace: SetWatchdogTimerTrace,
    }

    // Declares a global instance of EfiCallTraces.
    // Need to use thread local storage because rust unit test is multi-threaded.
    thread_local! {
        static EFI_CALL_TRACES: RefCell<EfiCallTraces> = RefCell::new(Default::default());
    }

    impl From<usize> for DeviceHandle {
        fn from(h: usize) -> Self {
            Self(h as *mut _)
        }
    }

    /// Exports for unit-test in submodules.
    pub fn efi_call_traces() -> &'static std::thread::LocalKey<RefCell<EfiCallTraces>> {
        &EFI_CALL_TRACES
    }

    /// EFI_BOOT_SERVICE.FreePool() test implementation.
    #[derive(Default)]
    pub struct FreePoolTrace {
        // Capture `buf`
        pub inputs: VecDeque<*mut core::ffi::c_void>,
    }

    /// Mock of the `EFI_BOOT_SERVICE.FreePool` C API in test environment.
    extern "efiapi" fn free_pool(buf: *mut core::ffi::c_void) -> EfiStatus {
        EFI_CALL_TRACES.with(|traces| {
            traces.borrow_mut().free_pool_trace.inputs.push_back(buf);
            EFI_STATUS_SUCCESS
        })
    }

    /// EFI_BOOT_SERVICE.OpenProtocol() test implementation.
    #[derive(Default)]
    pub struct OpenProtocolTrace {
        // Capture `handle`, `protocol_guid`, `agent_handle`.
        pub inputs: VecDeque<(DeviceHandle, EfiGuid, EfiHandle)>,
        // Return `intf`, EfiStatus.
        pub outputs: VecDeque<(EfiHandle, EfiStatus)>,
    }

    /// Mock of the `EFI_BOOT_SERVICE.OpenProtocol` C API in test environment.
    ///
    /// # Safety
    ///
    ///   Caller should guarantee that `intf` and `protocol_guid` point to valid memory locations.
    unsafe extern "efiapi" fn open_protocol(
        handle: EfiHandle,
        protocol_guid: *const EfiGuid,
        intf: *mut *const core::ffi::c_void,
        agent_handle: EfiHandle,
        _: EfiHandle,
        attr: EfiOpenProtocolAttributes,
    ) -> EfiStatus {
        assert_eq!(attr, EFI_OPEN_PROTOCOL_ATTRIBUTE_BY_HANDLE_PROTOCOL);
        EFI_CALL_TRACES.with(|traces| {
            let trace = &mut traces.borrow_mut().open_protocol_trace;
            trace.inputs.push_back((
                DeviceHandle(handle),
                // SAFETY: function safety docs require valid `protocol_guid`.
                unsafe { *protocol_guid },
                agent_handle,
            ));

            let (intf_handle, status) = trace.outputs.pop_front().unwrap();
            // SAFETY: function safety docs require valid `intf`.
            unsafe { *intf = intf_handle };

            status
        })
    }

    /// Mock of the `EFI_BOOT_SERVICE.HandleProtocol` C API in test environment.
    ///
    /// # Safety
    ///
    ///   Caller should guarantee that `protocol_guid` points to a valid memory location.
    ///   Caller should guarantee that `interface` is valid to write to with a
    ///   value of type `<T: ProtocolInfo>::InterfaceType` such that `T::GUID` is equal
    ///   to the value of `protocol_guid`.
    unsafe extern "efiapi" fn handle_protocol(
        handle: EfiHandle,
        protocol_guid: *const EfiGuid,
        interface: *mut *mut core::ffi::c_void,
    ) -> EfiStatus {
        EFI_CALL_TRACES.with(|traces| {
            if protocol_guid.is_null() {
                return EFI_STATUS_INVALID_PARAMETER;
            }

            let mut traces = traces.borrow_mut();
            traces
                .handle_protocol_trace
                .inputs
                // SAFETY:
                // * `protocol_guid` is not NULL.
                // * It is the caller's responsibility to pass a pointer whose pointee
                //   lives for 'static.
                .push_back((DeviceHandle(handle), unsafe { *protocol_guid }));

            let intf = traces.handle_protocol_trace.outputs.pop_front().unwrap();
            if interface.is_null() {
                EFI_STATUS_INVALID_PARAMETER
            } else {
                // SAFETY:
                // * `interface` is not NULL.
                unsafe { *interface = intf };
                EFI_STATUS_SUCCESS
            }
        })
    }

    #[derive(Default)]
    pub struct HandleProtocolTrace {
        pub inputs: VecDeque<(DeviceHandle, EfiGuid)>,
        pub outputs: VecDeque<*mut core::ffi::c_void>,
    }

    #[derive(Default)]
    pub struct LocateHandleTrace {
        pub outputs: VecDeque<Vec<DeviceHandle>>,
    }

    /// EFI_BOOT_SERVICE.LocateHandleBuffer.
    #[derive(Default)]
    pub struct LocateHandleBufferTrace {
        // Capture `protocol`.
        pub inputs: VecDeque<EfiGuid>,
        // For returning in `num_handles` and `buf`.
        pub outputs: VecDeque<(usize, *const DeviceHandle)>,
    }

    /// Mock of the `EFI_BOOT_SERVICE.LocateHandle` C API in test environment.
    ///
    /// # Safety
    ///
    /// Caller is responsible for guaranteeing that
    /// * `buffer_size` is valid to read and to write
    /// * `buf` points to memory that is valid to write for `buffer_size` elements
    ///
    /// `search_type` should always be EFI_LOCATE_HANDLE_SEARCH_TYPE_BY_PROTOCOL and
    /// `search_key` should always be NULL.
    unsafe extern "efiapi" fn locate_handle(
        search_type: EfiLocateHandleSearchType,
        _protocol: *const EfiGuid,
        search_key: *const core::ffi::c_void,
        buffer_size: *mut usize,
        buf: *mut EfiHandle,
    ) -> EfiStatus {
        assert_eq!(search_type, EFI_LOCATE_HANDLE_SEARCH_TYPE_BY_PROTOCOL);
        assert_eq!(search_key, null_mut());
        EFI_CALL_TRACES.with(|traces| {
            if buf == null_mut() {
                return EFI_STATUS_INVALID_PARAMETER;
            }
            let trace = &mut traces.borrow_mut().locate_handle_trace;
            let Some(handles) = trace.outputs.pop_front() else {
                return EFI_STATUS_DEVICE_ERROR;
            };
            let buf_size;
            // SAFETY:
            // * It is a precondition that `buffer_size` be valid to read and write.
            unsafe {
                buf_size = *buffer_size;
                *buffer_size = handles.len();
            }
            if handles.len() > buf_size {
                return EFI_STATUS_BUFFER_TOO_SMALL;
            }
            // SAFETY:
            // * It is a precondition that `buf` be writable for at least
            //  `buffer_size` elements.
            // * If `buffer_size` were smaller than the number of handles,
            //   we would have returned early already.
            let out_handles = unsafe { from_raw_parts_mut(buf, handles.len()) };
            for (handle, out) in core::iter::zip(handles, out_handles.iter_mut()) {
                *out = handle.0;
            }
            EFI_STATUS_SUCCESS
        })
    }

    /// Mock of the `EFI_BOOT_SERVICE.LocateHandleBuffer` C API in test environment.
    ///
    /// # Safety
    /// Caller should guarantee that `protocol`, `num_handles`, and `buf` point to valid memory
    /// locations.
    unsafe extern "efiapi" fn locate_handle_buffer(
        search_type: EfiLocateHandleSearchType,
        protocol: *const EfiGuid,
        search_key: *const core::ffi::c_void,
        num_handles: *mut usize,
        buf: *mut *mut EfiHandle,
    ) -> EfiStatus {
        assert_eq!(search_type, EFI_LOCATE_HANDLE_SEARCH_TYPE_BY_PROTOCOL);
        assert_eq!(search_key, null_mut());
        EFI_CALL_TRACES.with(|traces| {
            let trace = &mut traces.borrow_mut().locate_handle_buffer_trace;
            // SAFETY: function safety docs require valid `protocol`.
            unsafe { trace.inputs.push_back(*protocol) };

            let Some((num, handles)) = trace.outputs.pop_front() else {
                return EFI_STATUS_DEVICE_ERROR;
            };
            // SAFETY: function safety docs require valid `num_handles`.
            unsafe { *num_handles = num as usize };
            // SAFETY: function safety docs require valid `buf`.
            unsafe { *buf = handles as *mut EfiHandle };

            EFI_STATUS_SUCCESS
        })
    }

    /// EFI_BOOT_SERVICE.GetMemoryMap.
    #[derive(Default)]
    pub struct GetMemoryMapTrace {
        // Capture `memory_map_size` and `memory_map` argument.
        pub inputs: VecDeque<(usize, *mut EfiMemoryDescriptor)>,
        // Output value `map_key`, `memory_map_size`.
        pub outputs: VecDeque<(usize, usize)>,
        // Status to return, one per call. `EFI_STATUS_SUCCESS` once exhausted.
        pub statuses: VecDeque<EfiStatus>,
    }

    /// Mock of the `EFI_BOOT_SERVICE.GetMemoryMap` C API in test environment.
    ///
    /// # Safety
    ///
    ///   Caller should guarantee that `memory_map_size`, `map_key` and `desc_size` point to valid
    ///   memory locations.
    unsafe extern "efiapi" fn get_memory_map(
        memory_map_size: *mut usize,
        memory_map: *mut EfiMemoryDescriptor,
        map_key: *mut usize,
        desc_size: *mut usize,
        _: *mut u32,
    ) -> EfiStatus {
        EFI_CALL_TRACES.with(|traces| {
            let trace = &mut traces.borrow_mut().get_memory_map_trace;
            trace.inputs.push_back((unsafe { *memory_map_size }, memory_map));
            let status = trace.statuses.pop_front().unwrap_or(EFI_STATUS_SUCCESS);
            // On EFI_BUFFER_TOO_SMALL the size written is the capacity the firmware needs.
            // SAFETY: function safety docs require valid `memory_map_size`and `map_key`.
            unsafe { (*map_key, *memory_map_size) = trace.outputs.pop_front().unwrap() };
            // SAFETY: function safety docs require valid `desc_size`.
            unsafe { *desc_size = size_of::<EfiMemoryDescriptor>() };
            status
        })
    }

    /// EFI_BOOT_SERVICE.ExitBootServices.
    #[derive(Default)]
    pub struct ExitBootServicespTrace {
        // Capture `image_handle`, `map_key`
        pub inputs: VecDeque<(EfiHandle, usize)>,
    }

    /// Mock of the `EFI_BOOT_SERVICE.ExitBootServices` C API in test environment.
    extern "efiapi" fn exit_boot_services(image_handle: EfiHandle, map_key: usize) -> EfiStatus {
        EFI_CALL_TRACES.with(|traces| {
            let trace = &mut traces.borrow_mut().exit_boot_services_trace;
            trace.inputs.push_back((image_handle, map_key));
            EFI_STATUS_SUCCESS
        })
    }

    /// EFI_BOOT_SERVICE.CreateEvent.
    #[derive(Default)]
    pub struct CreateEventTrace {
        // Capture `type_`, `notify_tpl`, `notify_fn`, `notify_ctx`
        pub inputs: VecDeque<(u32, EfiTpl, EfiEventNotify, *mut core::ffi::c_void)>,
        // Output an EfiEvent.
        pub outputs: VecDeque<EfiEvent>,
    }

    /// Mock of the `EFI_BOOT_SERVICE.CreateEvent` C API in test environment.
    ///
    /// # Safety
    ///
    ///   Caller should guarantee that `event` points to valid memory location.
    unsafe extern "efiapi" fn create_event(
        type_: u32,
        notify_tpl: EfiTpl,
        notify_fn: EfiEventNotify,
        notify_ctx: *mut core::ffi::c_void,
        event: *mut EfiEvent,
    ) -> EfiStatus {
        EFI_CALL_TRACES.with(|traces| {
            let trace = &mut traces.borrow_mut().create_event_trace;
            trace.inputs.push_back((type_, notify_tpl, notify_fn, notify_ctx));
            // SAFETY: function safety docs require valid `event`.
            unsafe { *event = trace.outputs.pop_front().unwrap() };
            EFI_STATUS_SUCCESS
        })
    }

    /// EFI_BOOT_SERVICE.CloseEvent.
    #[derive(Default)]
    pub struct CloseEventTrace {
        // Capture `event`
        pub inputs: VecDeque<EfiEvent>,
    }

    /// Mock of the `EFI_BOOT_SERVICE.CloseEvent` C API in test environment.
    extern "efiapi" fn close_event(event: EfiEvent) -> EfiStatus {
        EFI_CALL_TRACES.with(|traces| {
            let trace = &mut traces.borrow_mut().close_event_trace;
            trace.inputs.push_back(event);
            EFI_STATUS_SUCCESS
        })
    }

    /// EFI_BOOT_SERVICE.CheckEvent.
    #[derive(Default)]
    pub struct CheckEventTrace {
        // EfiStatus for return.
        pub outputs: VecDeque<EfiStatus>,
    }

    /// Mock of the `EFI_BOOT_SERVICE.CheckEvent` C API in test environment.
    extern "efiapi" fn check_event(_: EfiEvent) -> EfiStatus {
        EFI_CALL_TRACES.with(|traces| {
            let trace = &mut traces.borrow_mut().check_event_trace;
            trace.outputs.pop_front().unwrap()
        })
    }

    /// EFI_RUNTIME_SERVICES.reset_system
    #[derive(Default)]
    pub struct ResetTrace {
        pub inputs: VecDeque<(EfiResetType, EfiStatus)>,
    }

    /// EFI_BOOT_SERVICE.SetTimer.
    #[derive(Default)]
    pub struct SetTimerTrace {
        // Capture call params
        pub inputs: VecDeque<(EfiEvent, EfiTimerDelay, u64)>,
        // EfiStatus for return
        pub outputs: VecDeque<EfiStatus>,
    }

    /// Mock of the `EFI_BOOT_SERVICE.SetTimer` C API in test environment.
    extern "efiapi" fn set_timer(
        event: EfiEvent,
        delay_type: EfiTimerDelay,
        duration: u64,
    ) -> EfiStatus {
        EFI_CALL_TRACES.with(|trace| {
            let trace = &mut trace.borrow_mut().set_timer_trace;
            trace.inputs.push_back((event, delay_type, duration));
            trace.outputs.pop_front().unwrap()
        })
    }

    /// EFI_BOOT_SERVICE.SetWatchdogTimer.
    #[derive(Default)]
    pub struct SetWatchdogTimerTrace {
        // Capture call params
        pub inputs: VecDeque<(usize, u64)>,
        // EfiStatus for return
        pub outputs: VecDeque<EfiStatus>,
    }

    /// Mock of the `EFI_BOOT_SERVICE.SetWatchdogTimer` C API in test environment.
    extern "efiapi" fn set_watchdog_timer(
        timeout: usize,
        watchdog_code: u64,
        _data_size: usize,
        _watchdog_data: *mut u16,
    ) -> EfiStatus {
        EFI_CALL_TRACES.with(|traces| {
            let trace = &mut traces.borrow_mut().set_watchdog_timer_trace;
            trace.inputs.push_back((timeout, watchdog_code));
            trace.outputs.pop_front().unwrap()
        })
    }

    #[derive(Default)]
    pub struct ConsoleOutTrace {
        pub strings: Vec<String>,
    }

    impl ConsoleOutTrace {
        /// Helper method for concatenating the individual printed characters.
        pub fn as_single_string(&self) -> String {
            // Due to conversion between the internal UTF-8 representation,
            // the UTF-16 representation expected by most UEFI protocols,
            // and the desire not to allocate memory for a conversion buffer,
            // the Write implementation for SimpleTextOutputProtocol writes a single
            // character at a time and loops over the entire input string.

            let mut out = String::with_capacity(self.strings.iter().map(|s| s.len()).sum());
            out.extend(self.strings.iter().map(String::as_str));
            out
        }
    }

    impl core::fmt::Write for ConsoleOutTrace {
        fn write_str(&mut self, s: &str) -> core::fmt::Result {
            self.strings.push(s.to_string());
            Ok(())
        }
    }

    /// # SAFETY:
    ///
    /// * Caller should guarantee that `str` is a valid, null-terminated,
    ///   UTF-16 encoded string.
    unsafe extern "efiapi" fn output_string(
        _proto: *mut EfiSimpleTextOutputProtocol,
        str: *mut u16,
    ) -> EfiStatus {
        EFI_CALL_TRACES.with(|traces| {
            if str.is_null() || !str.is_aligned() {
                return EFI_STATUS_INVALID_PARAMETER;
            }

            // SAFETY: `str` is aligned and not null,
            //         and the caller is responsible for passing a null-terminated
            //         string.
            let len = (0..).find(|i| unsafe { *str.add(*i) == 0x0000 }).unwrap_or(0);

            // SAFETY: just verified that str is a null-terminated `len` long string.
            let str = unsafe { std::slice::from_raw_parts(str, len) };
            let str = std::string::String::from_utf16(str).unwrap();
            traces.borrow_mut().console_out_trace.strings.push(str);

            EFI_STATUS_SUCCESS
        })
    }

    /// A test wrapper that sets up a system table, image handle and runs a test function like it
    /// is an EFI application.
    /// TODO(300168989): Investigate using procedural macro to generate test that auto calls this.
    pub fn run_test(func: impl FnOnce(EfiHandle, *mut EfiSystemTable) -> ()) {
        // Reset all traces
        EFI_CALL_TRACES.with(|trace| {
            *trace.borrow_mut() = Default::default();
        });
        let mut sto = EfiSimpleTextOutputProtocol {
            output_string: Some(output_string),
            ..Default::default()
        };
        let mut systab = EfiSystemTable { con_out: &mut sto, ..Default::default() };
        let mut boot_services: EfiBootService = Default::default();
        boot_services.free_pool = Some(free_pool);
        boot_services.open_protocol = Some(open_protocol);
        boot_services.handle_protocol = Some(handle_protocol);
        boot_services.locate_handle_buffer = Some(locate_handle_buffer);
        boot_services.locate_handle = Some(locate_handle);
        boot_services.get_memory_map = Some(get_memory_map);
        boot_services.exit_boot_services = Some(exit_boot_services);
        boot_services.create_event = Some(create_event);
        boot_services.close_event = Some(close_event);
        boot_services.check_event = Some(check_event);
        boot_services.set_timer = Some(set_timer);
        boot_services.set_watchdog_timer = Some(set_watchdog_timer);
        systab.boot_services = &mut boot_services as *mut _;
        let image_handle: usize = 1234; // Don't care.

        func(image_handle as EfiHandle, &mut systab as *mut _);

        // Reset all traces
        EFI_CALL_TRACES.with(|trace| {
            *trace.borrow_mut() = Default::default();
        });
    }

    /// Constructs a mock protocol `P` and run the given callback on it.
    ///
    /// This is similar to `run_test()`, but also provides the construction of a single mock
    /// protocol to reduce boilerplate for tests to check the interface between a C EFI protocol
    /// struct and our Rust wrappers.
    ///
    /// # Arguments
    /// * `c_interface`: the raw C struct interface implementing the desired protocol.
    /// * `f`: the callback function to run, given the resulting protocol as an argument.
    pub fn run_test_with_mock_protocol<P: ProtocolInfo>(
        mut c_interface: P::InterfaceType,
        f: impl FnOnce(&Protocol<P>),
    ) {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            // SAFETY:
            // * `c_interface` is a valid C interface for proto `P`
            // * `c_interface` outlives the created `protocol`
            let protocol = unsafe {
                Protocol::new(
                    DeviceHandle::new(null_mut()),
                    NonNull::new(from_mut(&mut c_interface)).unwrap(),
                    &efi_entry,
                )
            };
            f(&protocol);
        });
    }

    /// Get the pointer to an object as an EfiHandle type.
    pub fn as_efi_handle<T>(val: &mut T) -> EfiHandle {
        val as *mut T as *mut _
    }

    #[test]
    fn test_open_protocol() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };

            // Set up open_protocol trace
            let mut block_io: EfiBlockIoProtocol = Default::default();
            EFI_CALL_TRACES.with(|traces| {
                traces.borrow_mut().open_protocol_trace.outputs =
                    VecDeque::from([(as_efi_handle(&mut block_io), EFI_STATUS_SUCCESS)]);
            });

            let mut device_handle: usize = 0; // Don't care
            {
                // Open a protocol
                efi_entry
                    .system_table()
                    .boot_services()
                    .open_protocol::<BlockIoProtocol>(DeviceHandle(as_efi_handle(
                        &mut device_handle,
                    )))
                    .unwrap();

                // Validate call args
                EFI_CALL_TRACES.with(|trace| {
                    assert_eq!(
                        trace.borrow_mut().open_protocol_trace.inputs,
                        [(
                            DeviceHandle(as_efi_handle(&mut device_handle)),
                            BlockIoProtocol::GUID,
                            image_handle
                        ),]
                    );
                });
            }
        })
    }

    #[test]
    fn test_null_efi_method() {
        // Test that wrapper call fails if efi method is None.
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };

            // Set up open_protocol trace
            let mut block_io: EfiBlockIoProtocol = Default::default();
            EFI_CALL_TRACES.with(|traces| {
                traces.borrow_mut().open_protocol_trace.outputs =
                    VecDeque::from([(as_efi_handle(&mut block_io), EFI_STATUS_SUCCESS)]);
            });

            // Set the method to None.
            // SAFETY:
            // run_test() guarantees `boot_services` pointer points to valid object.
            unsafe { (*(*systab_ptr).boot_services).open_protocol = None };

            let mut device_handle: usize = 0; // Don't care
            assert!(efi_entry
                .system_table()
                .boot_services()
                .open_protocol::<BlockIoProtocol>(DeviceHandle(as_efi_handle(&mut device_handle)))
                .is_err());

            efi_call_traces().with(|traces| {
                let actual = traces.borrow().console_out_trace.as_single_string();
                assert_eq!(actual, "Protocol method not found in caller 'efi::BootServices<'_>::open_protocol': open_protocol\r\n");
            });
        })
    }

    #[test]
    fn test_error_efi_method() {
        // Test that wrapper call fails if efi method returns error.
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };

            // Set up open_protocol trace.
            let mut block_io: EfiBlockIoProtocol = Default::default();
            EFI_CALL_TRACES.with(|traces| {
                traces.borrow_mut().open_protocol_trace.outputs =
                    VecDeque::from([(as_efi_handle(&mut block_io), EFI_STATUS_NOT_FOUND)]);
            });

            let mut device_handle: usize = 0; // Don't care
            assert!(efi_entry
                .system_table()
                .boot_services()
                .open_protocol::<BlockIoProtocol>(DeviceHandle(as_efi_handle(&mut device_handle)))
                .is_err());
        })
    }

    #[test]
    fn test_locate_handle_buffer_by_protocol() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };

            // Set up locate_handle_buffer_trace trace.
            let mut located_handles: [DeviceHandle; 3] = [
                DeviceHandle(1 as *const _),
                DeviceHandle(2 as *const _),
                DeviceHandle(3 as *const _),
            ];
            EFI_CALL_TRACES.with(|traces| {
                traces.borrow_mut().locate_handle_buffer_trace.outputs =
                    VecDeque::from([(located_handles.len(), located_handles.as_ptr())]);
            });

            {
                let handles = efi_entry
                    .system_table()
                    .boot_services()
                    .locate_handle_buffer_by_protocol::<BlockIoProtocol>()
                    .unwrap();

                // Returned handles are expected.
                assert_eq!(handles.handles().to_vec(), located_handles);
            }

            EFI_CALL_TRACES.with(|traces| {
                let traces = traces.borrow_mut();
                // Arguments are passed correctly.
                assert_eq!(traces.locate_handle_buffer_trace.inputs, [BlockIoProtocol::GUID]);
                // Free pool is called with the correct address.
                assert_eq!(traces.free_pool_trace.inputs, [located_handles.as_mut_ptr() as *mut _]);
            });
        })
    }

    #[test]
    fn test_find_first_and_open() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };

            // Set up locate_handle_buffer_trace trace.
            let located_handles = [
                DeviceHandle(1 as *const _),
                DeviceHandle(2 as *const _),
                DeviceHandle(3 as *const _),
            ];
            EFI_CALL_TRACES.with(|traces| {
                traces.borrow_mut().locate_handle_trace.outputs =
                    VecDeque::from([located_handles.into()]);
            });

            // Set up open_protocol trace.
            let mut block_io: EfiBlockIoProtocol = Default::default();
            EFI_CALL_TRACES.with(|traces| {
                traces.borrow_mut().open_protocol_trace.outputs =
                    VecDeque::from([(as_efi_handle(&mut block_io), EFI_STATUS_SUCCESS)]);
            });

            efi_entry
                .system_table()
                .boot_services()
                .find_first_and_open::<BlockIoProtocol>()
                .unwrap();

            // Check open_protocol is called on the first handle.
            EFI_CALL_TRACES.with(|traces| {
                assert_eq!(
                    traces.borrow_mut().open_protocol_trace.inputs,
                    [(DeviceHandle(1 as *const _), BlockIoProtocol::GUID, image_handle),]
                );
            });
        })
    }

    #[test]
    fn test_find_first_and_open_empty_handles() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };

            // Set up locate_handle_buffer_trace trace.
            EFI_CALL_TRACES.with(|traces| {
                traces.borrow_mut().locate_handle_trace.outputs = VecDeque::from([vec![]]);
            });

            // Set up open_protocol trace.
            let mut block_io: EfiBlockIoProtocol = Default::default();
            EFI_CALL_TRACES.with(|traces| {
                traces.borrow_mut().open_protocol_trace.outputs =
                    VecDeque::from([(as_efi_handle(&mut block_io), EFI_STATUS_SUCCESS)]);
            });

            let res = efi_entry
                .system_table()
                .boot_services()
                .find_first_and_open::<BlockIoProtocol>()
                .unwrap_err();

            assert_eq!(res, Error::NotFound);
        })
    }

    #[test]
    fn test_find_first_and_open_many_handles() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let handles = (1..=BootServices::LOCATE_HANDLE_BUFFER_SIZE * 4)
                .map(DeviceHandle::from)
                .collect::<Vec<_>>();

            let mut block_io: EfiBlockIoProtocol = Default::default();
            EFI_CALL_TRACES.with(|traces| {
                let mut traces = traces.borrow_mut();
                traces.locate_handle_trace.outputs = VecDeque::from([handles.clone()]);
                traces.locate_handle_buffer_trace.outputs =
                    VecDeque::from([(handles.len(), handles.as_ptr())]);
                traces.open_protocol_trace.outputs =
                    VecDeque::from([(as_efi_handle(&mut block_io), EFI_STATUS_SUCCESS)])
            });

            efi_entry
                .system_table()
                .boot_services()
                .find_first_and_open::<BlockIoProtocol>()
                .unwrap();

            EFI_CALL_TRACES.with(|traces| {
                let traces = traces.borrow_mut();
                assert_eq!(traces.locate_handle_buffer_trace.inputs, [BlockIoProtocol::GUID]);
                assert_eq!(
                    traces.open_protocol_trace.inputs,
                    [(DeviceHandle::from(1), BlockIoProtocol::GUID, image_handle),]
                );
            });
        })
    }

    #[test]
    fn test_exit_boot_services() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            // Create a buffer large enough to hold two EfiMemoryDescriptor.
            let mut descriptors: [EfiMemoryDescriptor; 2] = [
                EfiMemoryDescriptor {
                    memory_type: EFI_MEMORY_TYPE_LOADER_DATA,
                    padding: 0,
                    physical_start: 0,
                    virtual_start: 0,
                    number_of_pages: 0,
                    attributes: EfiMemoryAttribute(0),
                },
                EfiMemoryDescriptor {
                    memory_type: EFI_MEMORY_TYPE_LOADER_CODE,
                    padding: 0,
                    physical_start: 0,
                    virtual_start: 0,
                    number_of_pages: 0,
                    attributes: EfiMemoryAttribute(0),
                },
            ];
            let map_key: usize = 12345;
            // Set up get_memory_map trace.
            EFI_CALL_TRACES.with(|traces| {
                // Output only the first EfiMemoryDescriptor.
                traces.borrow_mut().get_memory_map_trace.outputs =
                    VecDeque::from([(map_key, 1 * size_of::<EfiMemoryDescriptor>())]);
            });

            // SAFETY: Buffer is guaranteed valid.
            let buffer = unsafe {
                from_raw_parts_mut(
                    descriptors.as_mut_ptr() as *mut u8,
                    descriptors.len() * size_of::<EfiMemoryDescriptor>(),
                )
            };

            // Test `exit_boot_services`
            let desc = super::exit_boot_services(efi_entry, buffer).unwrap();

            // Validate that UEFI APIs are correctly called.
            EFI_CALL_TRACES.with(|traces| {
                assert_eq!(
                    traces.borrow_mut().get_memory_map_trace.inputs,
                    [(
                        descriptors.len() * size_of::<EfiMemoryDescriptor>(),
                        descriptors.as_mut_ptr()
                    )]
                );

                assert_eq!(
                    traces.borrow_mut().exit_boot_services_trace.inputs,
                    [(image_handle, map_key)],
                );
            });

            // Validate that the returned `EfiMemoryMap` contains only 1 EfiMemoryDescriptor.
            assert_eq!(desc.into_iter().map(|v| *v).collect::<Vec<_>>(), descriptors[..1].to_vec());
            // Validate that the returned `EfiMemoryMap` has the correct map_key.
            assert_eq!(desc.map_key(), map_key);
        })
    }

    #[test]
    fn test_get_memory_map_preserves_required_size() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            const REQUIRED: usize = 4 * size_of::<EfiMemoryDescriptor>();
            EFI_CALL_TRACES.with(|traces| {
                let mut t = traces.borrow_mut();
                t.get_memory_map_trace.statuses = VecDeque::from([EFI_STATUS_BUFFER_TOO_SMALL]);
                t.get_memory_map_trace.outputs = VecDeque::from([(0, REQUIRED)]);
            });

            let mut small = [0u8; size_of::<EfiMemoryDescriptor>()];
            assert_eq!(
                efi_entry
                    .system_table()
                    .boot_services()
                    .get_memory_map(&mut small[..])
                    .unwrap_err(),
                Error::BufferTooSmall(Some(REQUIRED)),
            );
        })
    }

    #[test]
    fn test_memory_map_size_reports_firmware_capacity() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            const REQUIRED: usize = 7 * size_of::<EfiMemoryDescriptor>();
            EFI_CALL_TRACES.with(|traces| {
                let mut t = traces.borrow_mut();
                t.get_memory_map_trace.statuses = VecDeque::from([EFI_STATUS_BUFFER_TOO_SMALL]);
                t.get_memory_map_trace.outputs = VecDeque::from([(0, REQUIRED)]);
            });

            let bs = efi_entry.system_table().boot_services();
            assert_eq!(bs.memory_map_size(), Ok(REQUIRED));
            EFI_CALL_TRACES.with(|traces| {
                assert_eq!(traces.borrow().get_memory_map_trace.inputs.len(), 1);
                assert_eq!(traces.borrow().get_memory_map_trace.inputs[0].0, 0);
            });
        })
    }

    #[test]
    fn test_exit_boot_services_not_called_without_fresh_map() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            EFI_CALL_TRACES.with(|traces| {
                let mut t = traces.borrow_mut();
                t.get_memory_map_trace.statuses = VecDeque::from([EFI_STATUS_BUFFER_TOO_SMALL]);
                t.get_memory_map_trace.outputs =
                    VecDeque::from([(0, 8 * size_of::<EfiMemoryDescriptor>())]);
            });

            let mut buffer = vec![0u8; size_of::<EfiMemoryDescriptor>()];
            assert!(super::exit_boot_services(efi_entry, &mut buffer[..]).is_err());
            // A stale or absent map key would corrupt the handoff, so ExitBootServices must not
            // be reached.
            EFI_CALL_TRACES.with(|traces| {
                assert!(traces.borrow().exit_boot_services_trace.inputs.is_empty());
            });
        })
    }

    #[test]
    fn test_exit_boot_services_unaligned_buffer() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            // Create a buffer for 2 EfiMemoryDescriptor.
            let descriptors: [EfiMemoryDescriptor; 2] = [
                EfiMemoryDescriptor {
                    memory_type: EFI_MEMORY_TYPE_LOADER_DATA,
                    padding: 0,
                    physical_start: 0,
                    virtual_start: 0,
                    number_of_pages: 0,
                    attributes: EfiMemoryAttribute(0),
                },
                EfiMemoryDescriptor {
                    memory_type: EFI_MEMORY_TYPE_LOADER_CODE,
                    padding: 0,
                    physical_start: 0,
                    virtual_start: 0,
                    number_of_pages: 0,
                    attributes: EfiMemoryAttribute(0),
                },
            ];

            let map_key: usize = 12345;
            // Set up get_memory_map trace.
            EFI_CALL_TRACES.with(|traces| {
                traces.borrow_mut().get_memory_map_trace.outputs =
                    VecDeque::from([(map_key, 2 * size_of::<EfiMemoryDescriptor>())]);
            });

            // Construct the destination buffer.
            let mut buffer = [0u8; 256];
            let alignment = core::mem::align_of::<EfiMemoryDescriptor>();
            let size = core::mem::size_of::<EfiMemoryDescriptor>();
            let aligned = aligned_subslice(&mut buffer[..], alignment).unwrap();
            // Offset by 1 element so that we can make an unaligned buffer starting somewhere in
            // between.
            let start = aligned.get_mut(size..).unwrap();
            start[..size].clone_from_slice(descriptors[0].as_bytes());
            start[size..][..size].clone_from_slice(descriptors[1].as_bytes());
            // Pass an unaligned address.
            let desc = super::exit_boot_services(efi_entry, &mut aligned[size - 1..]).unwrap();
            // Validate that the returned `EfiMemoryMap` contains the correct EfiMemoryDescriptor.
            assert_eq!(desc.into_iter().map(|v| *v).collect::<Vec<_>>(), descriptors[..2].to_vec());
            // Validate that the returned `EfiMemoryMap` has the correct map_key.
            assert_eq!(desc.map_key(), map_key);
        });
    }

    #[test]
    fn test_create_event_with_notify_fn() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let mut cb_impl = |_: EfiEvent| {};
            let mut cb = EventNotify::new(Tpl::Callback, &mut cb_impl);
            let event: EfiEvent = 1234usize as _;
            EFI_CALL_TRACES.with(|traces| {
                traces.borrow_mut().create_event_trace.outputs.push_back(event);
            });
            {
                // SAFETY: event notifications are always safe in unittests.
                let _ = unsafe {
                    efi_entry
                        .system_table()
                        .boot_services()
                        .create_event_with_notification(EventType::Timer, &mut cb)
                }
                .unwrap();
            }
            let efi_cb: EfiEventNotify = Some(efi_event_cb);
            EFI_CALL_TRACES.with(|traces| {
                assert_eq!(
                    traces.borrow_mut().create_event_trace.inputs,
                    [(
                        EventType::Timer as _,
                        Tpl::Callback as _,
                        efi_cb,
                        &mut cb as *mut _ as *mut _
                    )]
                )
            });
            // Verify close_event is called.
            EFI_CALL_TRACES
                .with(|traces| assert_eq!(traces.borrow_mut().close_event_trace.inputs, [event]));
        });
    }

    #[test]
    fn test_create_event_wo_notify_fn() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let event: EfiEvent = 1234usize as _;
            EFI_CALL_TRACES.with(|traces| {
                traces.borrow_mut().create_event_trace.outputs.push_back(event);
            });
            {
                let _ = efi_entry
                    .system_table()
                    .boot_services()
                    .create_event(EventType::Timer)
                    .unwrap();
            }
            EFI_CALL_TRACES.with(|traces| {
                assert_eq!(
                    traces.borrow_mut().create_event_trace.inputs,
                    [(EventType::Timer as _, 0, None, null_mut())]
                )
            });
        });
    }

    #[test]
    fn test_check_event() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let event: EfiEvent = 1234usize as _;
            EFI_CALL_TRACES.with(|traces| {
                traces.borrow_mut().create_event_trace.outputs.push_back(event);
                traces.borrow_mut().check_event_trace.outputs.push_back(EFI_STATUS_SUCCESS);
                traces.borrow_mut().check_event_trace.outputs.push_back(EFI_STATUS_NOT_READY);
                traces.borrow_mut().check_event_trace.outputs.push_back(EFI_STATUS_UNSUPPORTED);
            });
            let res =
                efi_entry.system_table().boot_services().create_event(EventType::Timer).unwrap();
            assert_eq!(efi_entry.system_table().boot_services().check_event(&res), Ok(true));
            assert_eq!(efi_entry.system_table().boot_services().check_event(&res), Ok(false));
            assert!(efi_entry.system_table().boot_services().check_event(&res).is_err());
        });
    }

    #[test]
    fn test_check_recurring_timer() {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let event: EfiEvent = 666usize as _;

            EFI_CALL_TRACES.with(|traces| {
                let mut t = traces.borrow_mut();
                t.create_event_trace.outputs.push_back(event);
                t.set_timer_trace.outputs.push_back(EFI_STATUS_SUCCESS);
                t.check_event_trace.outputs.push_back(EFI_STATUS_SUCCESS);
            });

            let recurring_timer =
                RecurringTimer::new(&efi_entry, Duration::from_nanos(2112)).unwrap();

            EFI_CALL_TRACES.with(|traces| {
                let traces = traces.borrow();
                assert_eq!(
                    traces.create_event_trace.inputs,
                    [(EventType::Timer as _, 0, None, null_mut())]
                );
                assert_eq!(
                    traces.set_timer_trace.inputs,
                    [(event, EFI_TIMER_DELAY_TIMER_PERIODIC, 21u64)]
                );
                // Make sure timer doesn't check itself automatically during construction.
                assert_eq!(traces.check_event_trace.outputs, [EFI_STATUS_SUCCESS]);
            });

            assert_eq!(recurring_timer.check(), Ok(true));
        });
    }

    #[test]
    fn test_set_watchdog_timer() {
        const FIRST_CALL_CODE: WatchdogTimerCode = WatchdogTimerCode::new(0x10000);
        const SECOND_CALL_CODE: WatchdogTimerCode = WatchdogTimerCode::new(0x10001);

        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };

            EFI_CALL_TRACES.with(|traces| {
                let mut traces = traces.borrow_mut();
                traces.set_watchdog_timer_trace.outputs.push_back(EFI_STATUS_SUCCESS);
                traces.set_watchdog_timer_trace.outputs.push_back(EFI_STATUS_UNSUPPORTED);
            });

            assert!(efi_entry
                .system_table()
                .boot_services()
                .set_watchdog_timer(Duration::from_secs(30), FIRST_CALL_CODE)
                .is_ok());

            assert!(efi_entry
                .system_table()
                .boot_services()
                .set_watchdog_timer(Duration::from_secs(60), SECOND_CALL_CODE)
                .is_err());

            EFI_CALL_TRACES.with(|traces| {
                let traces = traces.borrow();
                assert_eq!(
                    traces.set_watchdog_timer_trace.inputs,
                    [(30, FIRST_CALL_CODE.0), (60, SECOND_CALL_CODE.0)]
                );
            });
        });
    }

    macro_rules! TestProto {
        { $required:expr } => {
            struct EfiTestProtocol;
            impl protocol::MaybeVersioned for EfiTestProtocol {}
            struct TestProtocol;

            impl ProtocolInfo for TestProtocol /* NO DOCS */ {
                type InterfaceType = EfiTestProtocol;

                const GUID: EfiGuid = EfiGuid::new(
                    0x2ec515d8,
                    0xaff5,
                    0x403f,
                    [0xb3, 0x36, 0x0f, 0x07, 0xe0, 0x74, 0x66, 0x78],
                );

                const REQUIREMENT: Requirement = $required;
            }
        }
    }

    #[test]
    fn test_required_protocol_present() {
        TestProto! {Requirement::Mandatory};

        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };

            let located_handles = [DeviceHandle(1 as *const _)];
            let mut test = TestProtocol;

            efi_call_traces().with(|traces| {
                let mut traces = traces.borrow_mut();

                traces.locate_handle_trace.outputs.push_back(located_handles.into());
                traces
                    .open_protocol_trace
                    .outputs
                    .push_back((as_efi_handle(&mut test), EFI_STATUS_SUCCESS));
            });

            assert!(efi_entry
                .system_table()
                .boot_services()
                .find_first_and_open::<TestProtocol>()
                .is_ok());

            efi_call_traces().with(|trace| {
                let out_str = trace.borrow().console_out_trace.as_single_string();
                assert_eq!(out_str, "");
            });
        });
    }

    #[test]
    fn test_required_protocol_not_present() {
        TestProto! {Requirement::Mandatory};

        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };

            efi_call_traces()
                .with(|traces| traces.borrow_mut().locate_handle_trace.outputs.clear());

            assert!(efi_entry
                .system_table()
                .boot_services()
                .find_first_and_open::<TestProtocol>()
                .is_err());

            efi_call_traces().with(|trace| {
                let out_str = trace.borrow().console_out_trace.as_single_string();
                assert_eq!(out_str, "Required protocol not found: EfiTestProtocol\r\n");
            });
        });
    }

    #[test]
    fn test_optional_protocol_present() {
        TestProto! {Requirement::Optional};

        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };

            let located_handles = [DeviceHandle(1 as *const _)];
            let mut test = TestProtocol;

            efi_call_traces().with(|traces| {
                let mut traces = traces.borrow_mut();

                traces.locate_handle_trace.outputs.push_back(located_handles.into());
                traces
                    .open_protocol_trace
                    .outputs
                    .push_back((as_efi_handle(&mut test), EFI_STATUS_SUCCESS));
            });

            assert!(efi_entry
                .system_table()
                .boot_services()
                .find_first_and_open::<TestProtocol>()
                .is_ok());

            efi_call_traces().with(|trace| {
                let out_str = trace.borrow().console_out_trace.as_single_string();
                assert_eq!(out_str, "");
            });
        });
    }

    #[test]
    fn test_optional_protocol_not_present() {
        TestProto! {Requirement::Optional};

        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };

            efi_call_traces()
                .with(|traces| traces.borrow_mut().locate_handle_trace.outputs.clear());

            assert!(efi_entry
                .system_table()
                .boot_services()
                .find_first_and_open::<TestProtocol>()
                .is_err());

            efi_call_traces().with(|trace| {
                let out_str = trace.borrow().console_out_trace.as_single_string();
                let expected_output = if cfg!(feature = "gbl_dev") {
                    "Optional protocol not found: EfiTestProtocol\r\n"
                } else {
                    ""
                };
                assert_eq!(out_str, expected_output);
            });
        });
    }

    #[test]
    fn test_protocol_default_required() {
        struct EfiTestProtocol;
        impl protocol::MaybeVersioned for EfiTestProtocol {}
        struct TestProtocol;

        impl ProtocolInfo for TestProtocol /* NO DOCS */ {
            type InterfaceType = EfiTestProtocol;

            const GUID: EfiGuid = EfiGuid::new(
                0x2ec515d8,
                0xaff5,
                0x403f,
                [0xb3, 0x36, 0x0f, 0x07, 0xe0, 0x74, 0x66, 0x78],
            );

            // Don't add a requirement override to make sure the default is 'Mandatory'.
        }

        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };

            efi_call_traces()
                .with(|traces| traces.borrow_mut().locate_handle_trace.outputs.clear());

            assert!(efi_entry
                .system_table()
                .boot_services()
                .find_first_and_open::<TestProtocol>()
                .is_err());

            efi_call_traces().with(|trace| {
                let out_str = trace.borrow().console_out_trace.as_single_string();
                assert_eq!(out_str, "Required protocol not found: EfiTestProtocol\r\n");
            });
        });
    }

    trait TriviallyConstruct {
        fn new() -> Self;
    }

    macro_rules! versioned_protocol {
        ($compile_time:expr, $run_time:expr) => {
            struct EfiTestProtocol;
            impl protocol::MaybeVersioned for EfiTestProtocol {
                const REVISION: Option<Revision> = $compile_time;
                fn revision(&self) -> Option<Revision> {
                    $run_time
                }
            }

            struct TestProtocol;
            impl ProtocolInfo for TestProtocol /* NO DOCS */ {
                type InterfaceType = EfiTestProtocol;

                const GUID: EfiGuid = EfiGuid::new(
                    0x2ec515d8,
                    0xaff5,
                    0x403f,
                    [0xb3, 0x36, 0x0f, 0x07, 0xe0, 0x74, 0x66, 0x78],
                );
            }

            impl TriviallyConstruct for TestProtocol {
                fn new() -> Self {
                    Self {}
                }
            }
        };
    }

    fn versioned_test_helper<T: ProtocolInfo + TriviallyConstruct, EMF: FnOnce(T) -> String>(
        error_msg_func: EMF,
    ) {
        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let located_handles = vec![DeviceHandle(1 as *const _)];
            let mut test = T::new();

            efi_call_traces().with(|traces| {
                let mut traces = traces.borrow_mut();

                traces.locate_handle_trace.outputs.push_back(located_handles);
                traces
                    .open_protocol_trace
                    .outputs
                    .push_back((as_efi_handle(&mut test), EFI_STATUS_SUCCESS));
            });

            assert!(efi_entry.system_table().boot_services().find_first_and_open::<T>().is_ok());

            efi_call_traces().with(|trace| {
                let out_str = trace.borrow().console_out_trace.as_single_string();
                assert_eq!(out_str.trim_end_matches("\r\n"), error_msg_func(test));
            });
        });
    }

    #[test]
    fn test_versioned_protocol_no_version() {
        versioned_protocol! {None, None};
        versioned_test_helper::<TestProtocol, _>(|_| "".into());
    }

    #[test]
    fn test_versioned_protocol_equal_version() {
        versioned_protocol! {
            Some(Revision { major: 2112, minor: 1976 }),
            Some(Revision { major: 2112, minor: 1976 })
        };
        versioned_test_helper::<TestProtocol, _>(|_| "".into());
    }

    #[test]
    fn test_versioned_protocol_major_too_large() {
        versioned_protocol! {
            Some(Revision { major: 2112, minor: 1976 }),
            Some(Revision { major: 2113, minor: 1976 })
        };
        versioned_test_helper::<TestProtocol, _>(|t| {
            format!(
                "Opening Protocol<{}>: expected major version 2112, got 2113",
                std::any::type_name_of_val(&t)
            )
        });
    }

    #[test]
    fn test_versioned_protocol_major_too_small() {
        versioned_protocol! {
            Some(Revision { major: 2112, minor: 1976 }),
            Some(Revision { major: 2111, minor: 1976 })
        };
        versioned_test_helper::<TestProtocol, _>(|t| {
            format!(
                "Opening Protocol<{}>: expected major version 2112, got 2111",
                std::any::type_name_of_val(&t)
            )
        });
    }

    #[test]
    fn test_versioned_protocol_newer_minor() {
        versioned_protocol! {
            Some(Revision { major: 2112, minor: 1976 }),
            Some(Revision { major: 2112, minor: 1977 })
        };
        versioned_test_helper::<TestProtocol, _>(|_| "".into());
    }

    #[test]
    fn test_versioned_protocol_minor_too_small() {
        versioned_protocol! {
            Some(Revision { major: 2112, minor: 1976 }),
            Some(Revision { major: 2112, minor: 1975 })
        };
        versioned_test_helper::<TestProtocol, _>(|t| {
            format!(
                "Opening Protocol<{}>: expected minor version 1976, got 1975",
                std::any::type_name_of_val(&t)
            )
        });
    }

    #[test]
    fn test_versioned_protocol_runtime_revision_unspecified() {
        versioned_protocol! {Some(Revision { major: 2112, minor: 1976 }), None};
        versioned_test_helper::<TestProtocol, _>(|t| {
            format!("Opening Protocol<{}>: cannot check revision", std::any::type_name_of_val(&t))
        });
    }

    #[test]
    fn test_panic_handler_logs_fatal_error() {
        use std::sync::atomic::{AtomicU64, Ordering};
        thread_local! {
            static PANICS_CAUGHT:AtomicU64 = AtomicU64::new(0);
        }

        unsafe extern "efiapi" fn fatal_error(
            _: *mut GblEfiDebugProtocol,
            _: *const std::ffi::c_void,
            _: GblEfiDebugErrorTag,
        ) -> EfiStatus {
            let _ = PANICS_CAUGHT.with(|pc| pc.fetch_add(1, Ordering::Relaxed));
            EFI_STATUS_SUCCESS
        }

        run_test(|image_handle, systab_ptr| {
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            crate::GLOBAL_EFI_ENTRY
                .with(|e| *e.borrow_mut() = Some(std::ptr::NonNull::from_ref(&efi_entry)));

            let mut debug_proto =
                GblEfiDebugProtocol { fatal_error: Some(fatal_error), ..Default::default() };

            let handles = &mut [DeviceHandle::from(1)];
            efi_call_traces().with(|trace| {
                let mut trace = trace.borrow_mut();

                trace.locate_handle_trace.outputs = VecDeque::from([handles.into()]);
                trace.open_protocol_trace.outputs =
                    VecDeque::from([(as_efi_handle(&mut debug_proto), EFI_STATUS_SUCCESS)]);
            });

            struct PanicHookGuard(
                Arc<Mutex<Option<Box<dyn Fn(&PanicHookInfo<'_>) + Send + Sync>>>>,
            );
            impl Drop for PanicHookGuard {
                fn drop(&mut self) {
                    // Restore the original hook.
                    if let Some(hook) = self.0.lock().unwrap().take() {
                        set_hook(hook);
                    }
                }
            }

            // TODO: Switch to `update_hook` once it is stablized
            // [update_hook](https://doc.rust-lang.org/std/panic/fn.update_hook.html)
            let old_hook = Arc::new(Mutex::new(Some(take_hook())));
            let res = {
                let _guard = PanicHookGuard(old_hook.clone());
                set_hook(Box::new(move |p_info| {
                    // First, attempt our custom EFI logging.
                    // Safety:
                    // * `GLOBAL_EFI_ENTRY` has been initialized and is live.
                    unsafe {
                        let _ = with_global_efi_entry(|entry| {
                            report_error_and_reset(
                                entry,
                                p_info,
                                GBL_EFI_DEBUG_ERROR_TAG_ASSERTION_ERROR,
                            )
                        });
                    };
                    // ALWAYS delegate to the original hook so standard error messages are printed.
                    if let Some(hook) = old_hook.lock().unwrap().as_ref() {
                        hook(p_info);
                    }
                }));

                catch_unwind(|| panic!("Don't Panic! You know where your towel is."))
            };

            assert!(res.is_err());
            assert_eq!(PANICS_CAUGHT.with(|pc| pc.load(Ordering::Relaxed)), 1);
            efi_call_traces().with(|trace| {
                assert_eq!(
                    trace.borrow().reset_trace.inputs,
                    [(EFI_RESET_TYPE_COLD, EFI_STATUS_DEVICE_ERROR)]
                )
            });
        });
    }
}
