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
//! provides a global allocator and supports auto release of dynamic UEFI resource such as
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

extern crate alloc;
use alloc::vec::Vec;

#[cfg(not(test))]
mod allocation;

#[cfg(not(test))]
pub use allocation::{efi_free, efi_malloc, EfiAllocator};

/// The Android EFI protocol implementation of an A/B slot manager.
pub mod ab_slots;
pub mod protocol;
pub mod utils;

#[cfg(not(test))]
use core::{fmt::Write, panic::PanicInfo};

use core::{marker::PhantomData, ptr::null_mut, slice::from_raw_parts};
use efi_types::{
    EfiBootService, EfiConfigurationTable, EfiEvent, EfiGuid, EfiHandle,
    EfiMemoryAttributesTableHeader, EfiMemoryDescriptor, EfiMemoryType, EfiRuntimeService,
    EfiSystemTable, EfiTimerDelay, EFI_EVENT_TYPE_NOTIFY_SIGNAL, EFI_EVENT_TYPE_NOTIFY_WAIT,
    EFI_EVENT_TYPE_RUNTIME, EFI_EVENT_TYPE_SIGNAL_EXIT_BOOT_SERVICES,
    EFI_EVENT_TYPE_SIGNAL_VIRTUAL_ADDRESS_CHANGE, EFI_EVENT_TYPE_TIMER,
    EFI_LOCATE_HANDLE_SEARCH_TYPE_BY_PROTOCOL, EFI_OPEN_PROTOCOL_ATTRIBUTE_BY_HANDLE_PROTOCOL,
    EFI_RESET_TYPE, EFI_RESET_TYPE_EFI_RESET_COLD, EFI_STATUS, EFI_STATUS_SUCCESS,
};
use liberror::{Error, Result};
use libutils::aligned_subslice;
use protocol::{
    simple_text_output::SimpleTextOutputProtocol,
    {Protocol, ProtocolInfo},
};
use zerocopy::{FromBytes, Ref};

/// `EfiEntry` stores the EFI system table pointer and image handle passed from the entry point.
/// It's the root data structure that derives all other wrapper APIs and structures.
pub struct EfiEntry {
    image_handle: EfiHandle,
    systab_ptr: *const EfiSystemTable,
}

impl EfiEntry {
    /// Gets an instance of `SystemTable`.
    pub fn system_table(&self) -> SystemTable {
        // SAFETY: Pointers to UEFI data strucutres.
        SystemTable { efi_entry: self, table: unsafe { self.systab_ptr.as_ref() }.unwrap() }
    }

    /// Gets the image handle.
    pub fn image_handle(&self) -> DeviceHandle {
        DeviceHandle(self.image_handle)
    }
}

/// The vendor GUID for UEFI variables defined by GBL.
pub const GBL_EFI_VENDOR_GUID: EfiGuid =
    EfiGuid::new(0x5a6d92f3, 0xa2d0, 0x4083, [0x91, 0xa1, 0xa5, 0x0f, 0x6c, 0x3d, 0x98, 0x30]);

/// GUID for UEFI Memory Attributes Table
pub const EFI_MEMORY_ATTRIBUTES_GUID: EfiGuid =
    EfiGuid::new(0xdcfa911d, 0x26eb, 0x469f, [0xa2, 0x20, 0x38, 0xb7, 0xdc, 0x46, 0x12, 0x20]);

/// The name of the UEFI variable that GBL defines to determine whether to boot Fuchsia.
/// The value of the variable is ignored: if the variable is present,
/// it indicates that the bootloader should attempt to boot a Fuchsia target.
/// This may include reinitializing GPT partitions and partition contents.
pub const GBL_EFI_OS_BOOT_TARGET_VARNAME: &str = "gbl_os_boot_fuchsia";

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
    let efi_entry = EfiEntry { image_handle, systab_ptr };
    // SAFETY: By safety requirement of this function, `initialize` is only called once upon
    // entering EFI application, where there should be no event notify function that can be
    // triggered.
    unsafe {
        // Create another one for internal global allocator.
        allocation::init_efi_global_alloc(EfiEntry { image_handle, systab_ptr })?;
    }
    Ok(efi_entry)
}

/// Exits boot service and returns the memory map in the given buffer.
///
/// The API takes ownership of the given `entry` and causes it to go out of scope.
/// This enforces strict compile time check that any reference/borrow in effect will cause compile
/// errors.
///
/// Existing heap allocated memories will maintain their states. All system memory including them
/// will be under onwership of the subsequent OS or OS loader code.
pub fn exit_boot_services(entry: EfiEntry, mmap_buffer: &mut [u8]) -> Result<EfiMemoryMap> {
    let aligned = aligned_subslice(mmap_buffer, core::mem::align_of::<EfiMemoryDescriptor>())?;

    let res = entry.system_table().boot_services().get_memory_map(aligned)?;
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
#[derive(Clone, Copy)]
pub struct SystemTable<'a> {
    efi_entry: &'a EfiEntry,
    table: &'a EfiSystemTable,
}

impl<'a> SystemTable<'a> {
    /// Creates an instance of `BootServices`
    pub fn boot_services(&self) -> BootServices<'a> {
        BootServices {
            efi_entry: self.efi_entry,
            // SAFETY: Pointers to UEFI data strucutres.
            boot_services: unsafe { self.table.boot_services.as_ref() }.unwrap(),
        }
    }

    /// Creates an instance of `RuntimeServices`
    pub fn runtime_services(&self) -> RuntimeServices<'a> {
        RuntimeServices {
            // SAFETY: Pointers to UEFI data strucutres.
            runtime_services: unsafe { self.table.runtime_services.as_ref() }.unwrap(),
        }
    }

    /// Gets the `EFI_SYSTEM_TABLE.ConOut` field.
    pub fn con_out(&self) -> Result<Protocol<'a, SimpleTextOutputProtocol>> {
        // SAFETY: `EFI_SYSTEM_TABLE.ConOut` is a pointer to EfiSimpleTextOutputProtocol structure
        // by definition. It lives until ExitBootService and thus as long as `self.efi_entry` or,
        // 'a
        Ok(unsafe {
            Protocol::<SimpleTextOutputProtocol>::new(
                // No device handle. This protocol is a permanent reference.
                DeviceHandle(null_mut()),
                self.table.con_out,
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
}

/// `BootServices` provides methods for accessing various EFI_BOOT_SERVICES interfaces.
#[derive(Clone, Copy)]
pub struct BootServices<'a> {
    efi_entry: &'a EfiEntry,
    boot_services: &'a EfiBootService,
}

impl<'a> BootServices<'a> {
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

    /// Wrapper of `EFI_BOOT_SERVICES.OpenProtocol()`.
    pub fn open_protocol<T: ProtocolInfo>(&self, handle: DeviceHandle) -> Result<Protocol<'a, T>> {
        let mut out_handle: EfiHandle = null_mut();
        // SAFETY: EFI_BOOT_SERVICES method call.
        unsafe {
            efi_call!(
                self.boot_services.open_protocol,
                handle.0,
                &T::GUID,
                &mut out_handle as *mut _,
                self.efi_entry.image_handle().0,
                null_mut(),
                EFI_OPEN_PROTOCOL_ATTRIBUTE_BY_HANDLE_PROTOCOL
            )?;
        }
        // SAFETY: `EFI_SYSTEM_TABLE.OpenProtocol` returns a valid pointer to `T::InterfaceType`
        // on success. The pointer remains valid until closed by
        // `EFI_BOOT_SERVICES.CloseProtocol()` when Protocol goes out of scope.
        Ok(unsafe { Protocol::<T>::new(handle, out_handle as *mut _, self.efi_entry) })
    }

    /// Wrapper of `EFI_BOOT_SERVICES.CloseProtocol()`.
    #[allow(dead_code)]
    fn close_protocol<T: ProtocolInfo>(&self, handle: DeviceHandle) -> Result<()> {
        // SAFETY: EFI_BOOT_SERVICES method call.
        unsafe {
            efi_call!(
                self.boot_services.close_protocol,
                handle.0,
                &T::GUID,
                self.efi_entry.image_handle().0,
                null_mut()
            )
        }
    }

    /// Call `EFI_BOOT_SERVICES.LocateHandleBuffer()` with fixed
    /// `EFI_LOCATE_HANDLE_SEARCH_TYPE_BY_PROTOCOL` and without search key.
    pub fn locate_handle_buffer_by_protocol<T: ProtocolInfo>(&self) -> Result<LocatedHandles<'a>> {
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
        // `handles` should be a valid pointer if the above succeeds. But just double check
        // to be safe. If assert fails, then there's a bug in the UEFI firmware.
        assert!(!handles.is_null());
        Ok(LocatedHandles::new(handles, num_handles, self.efi_entry))
    }

    /// Search and open the first found target EFI protocol.
    pub fn find_first_and_open<T: ProtocolInfo>(&self) -> Result<Protocol<'a, T>> {
        // We don't use EFI_BOOT_SERVICES.LocateProtocol() because it doesn't give device handle
        // which is required to close the protocol.
        let handle = *self
            .locate_handle_buffer_by_protocol::<T>()?
            .handles()
            .first()
            .ok_or(Error::NotFound)?;
        self.open_protocol::<T>(handle)
    }

    /// Wrapper of `EFI_BOOT_SERVICE.GetMemoryMap()`.
    pub fn get_memory_map<'b>(&self, mmap_buffer: &'b mut [u8]) -> Result<EfiMemoryMap<'b>> {
        let mut mmap_size = mmap_buffer.len();
        let mut map_key: usize = 0;
        let mut descriptor_size: usize = 0;
        let mut descriptor_version: u32 = 0;
        // SAFETY: EFI_BOOT_SERVICES method call.
        unsafe {
            efi_call!(
                self.boot_services.get_memory_map,
                &mut mmap_size,
                mmap_buffer.as_mut_ptr() as *mut _,
                &mut map_key,
                &mut descriptor_size,
                &mut descriptor_version
            )
        }?;
        Ok(EfiMemoryMap::new(
            &mut mmap_buffer[..mmap_size],
            map_key,
            descriptor_size,
            descriptor_version,
        ))
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
        trigger_time: u64,
    ) -> Result<()> {
        // SAFETY: EFI_BOOT_SERVICES method call.
        unsafe {
            efi_call!(self.boot_services.set_timer, event.efi_event, delay_type, trigger_time)
        }
    }
}

/// `RuntimeServices` provides methods for accessing various EFI_RUNTIME_SERVICES interfaces.
#[derive(Clone, Copy)]
pub struct RuntimeServices<'a> {
    runtime_services: &'a EfiRuntimeService,
}

impl<'a> RuntimeServices<'a> {
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
        reset_type: EFI_RESET_TYPE,
        reset_status: EFI_STATUS,
        reset_data: Option<&mut [u8]>,
    ) -> ! {
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

        unreachable!();
    }

    /// Performs a cold reset without status code or data.
    pub fn cold_reset(&self) -> ! {
        self.reset_system(EFI_RESET_TYPE_EFI_RESET_COLD, EFI_STATUS_SUCCESS, None)
    }
}

/// EFI Event type to pass to BootServicess::create_event.
/// See UEFI documentation for details.
#[allow(missing_docs)]
#[repr(u32)]
pub enum EventType {
    Timer = EFI_EVENT_TYPE_TIMER,
    RunTime = EFI_EVENT_TYPE_RUNTIME,
    NotifyWait = EFI_EVENT_TYPE_NOTIFY_WAIT,
    NotifySignal = EFI_EVENT_TYPE_NOTIFY_SIGNAL,
    SignalExitBootServices = EFI_EVENT_TYPE_SIGNAL_EXIT_BOOT_SERVICES,
    SignalVirtualAddressChange = EFI_EVENT_TYPE_SIGNAL_VIRTUAL_ADDRESS_CHANGE,

    // Valid combinations:
    TimerNotifySignal = EFI_EVENT_TYPE_TIMER | EFI_EVENT_TYPE_NOTIFY_SIGNAL,
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
/// notification function entry (`unsafe extern "C" fn efi_event_cb(...)`).
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
unsafe extern "C" fn efi_event_cb(event: EfiEvent, ctx: *mut core::ffi::c_void) {
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
        Some(Ref::<_, EfiMemoryDescriptor>::new_from_prefix(bytes).unwrap().0.into_ref())
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
            let desc =
                Ref::<_, EfiMemoryDescriptor>::new_from_prefix(desc_bytes).unwrap().0.into_ref();
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
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct DeviceHandle(EfiHandle);

impl DeviceHandle {
    /// Public constructor
    pub fn new(handle: EfiHandle) -> Self {
        Self(handle)
    }
}

/// `LocatedHandles` holds the array of handles return by
/// `BootServices::locate_handle_buffer_by_protocol()`.
pub struct LocatedHandles<'a> {
    handles: &'a [DeviceHandle],
    efi_entry: &'a EfiEntry,
}

impl<'a> LocatedHandles<'a> {
    pub(crate) fn new(handles: *mut EfiHandle, len: usize, efi_entry: &'a EfiEntry) -> Self {
        // Implementation is not suppose to call this with a NULL pointer.
        debug_assert!(!handles.is_null());
        Self {
            // SAFETY: Given correct UEFI firmware, non-null pointer points to valid memory.
            // The memory is owned by the objects.
            handles: unsafe { from_raw_parts(handles as *mut DeviceHandle, len) },
            efi_entry: efi_entry,
        }
    }
    /// Get the list of handles as a slice.
    pub fn handles(&self) -> &[DeviceHandle] {
        self.handles
    }
}

impl Drop for LocatedHandles<'_> {
    fn drop(&mut self) {
        self.efi_entry
            .system_table()
            .boot_services()
            .free_pool(self.handles.as_ptr() as *mut _)
            .unwrap();
    }
}

/// Helper macro for printing message via `EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL` in
/// `EFI_SYSTEM_TABLE.ConOut`.
#[macro_export]
macro_rules! efi_print {
    ( $efi_entry:expr, $( $x:expr ),* $(,)? ) => {
            write!($efi_entry.system_table().con_out().unwrap(), $($x,)*).unwrap()
    };
}

/// Similar to [efi_print!], but automatically adds the UEFI newline sequence (`\r\n`).
#[macro_export]
macro_rules! efi_println {
    ( $efi_entry:expr, $( $x:expr ),* $(,)? ) => {
        {
            efi_print!($efi_entry, $($x,)*);
            efi_print!($efi_entry, "\r\n");
        }
    };
}

/// Provides a builtin panic handler.
/// In the long term, to improve flexibility, consider allowing application to install a custom
/// handler into `EfiEntry` to be called here.
/// Don't set this as the panic handler so that other crates' tests can depend on libefi.
#[cfg(not(test))]
pub fn panic(panic: &PanicInfo) -> ! {
    // If there is a valid internal `efi_entry` from global allocator, print the panic info.
    let entry = allocation::internal_efi_entry();
    if let Some(e) = entry {
        match e.system_table().con_out() {
            Ok(mut con_out) => {
                let _ = write!(con_out, "Panics! {}\r\n", panic);
            }
            _ => {}
        }
    }
    loop {}
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::protocol::block_io::BlockIoProtocol;
    use efi_types::{
        EfiBlockIoProtocol, EfiEventNotify, EfiLocateHandleSearchType, EfiStatus, EfiTpl,
        EFI_MEMORY_TYPE_LOADER_CODE, EFI_MEMORY_TYPE_LOADER_DATA, EFI_STATUS_NOT_FOUND,
        EFI_STATUS_NOT_READY, EFI_STATUS_SUCCESS, EFI_STATUS_UNSUPPORTED,
    };
    use std::{cell::RefCell, collections::VecDeque, mem::size_of, slice::from_raw_parts_mut};
    use zerocopy::AsBytes;

    /// Helper function to generate a Protocol from an interface type.
    pub fn generate_protocol<'a, P: ProtocolInfo>(
        efi_entry: &'a EfiEntry,
        proto: &'a mut P::InterfaceType,
    ) -> Protocol<'a, P> {
        // SAFETY: proto is a valid pointer and lasts at least as long as efi_entry.
        unsafe { Protocol::<'a, P>::new(DeviceHandle::new(null_mut()), proto, efi_entry) }
    }

    /// A structure to store the traces of arguments/outputs for EFI methods.
    #[derive(Default)]
    pub struct EfiCallTraces {
        pub free_pool_trace: FreePoolTrace,
        pub open_protocol_trace: OpenProtocolTrace,
        pub close_protocol_trace: CloseProtocolTrace,
        pub locate_handle_buffer_trace: LocateHandleBufferTrace,
        pub get_memory_map_trace: GetMemoryMapTrace,
        pub exit_boot_services_trace: ExitBootServicespTrace,
        pub create_event_trace: CreateEventTrace,
        pub close_event_trace: CloseEventTrace,
        pub check_event_trace: CheckEventTrace,
    }

    // Declares a global instance of EfiCallTraces.
    // Need to use thread local storage because rust unit test is multi-threaded.
    thread_local! {
        static EFI_CALL_TRACES: RefCell<EfiCallTraces> = RefCell::new(Default::default());
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
    extern "C" fn free_pool(buf: *mut core::ffi::c_void) -> EfiStatus {
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
    unsafe extern "C" fn open_protocol(
        handle: EfiHandle,
        protocol_guid: *const EfiGuid,
        intf: *mut *mut core::ffi::c_void,
        agent_handle: EfiHandle,
        _: EfiHandle,
        attr: u32,
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

    /// EFI_BOOT_SERVICE.CloseProtocol() test implementation.
    #[derive(Default)]
    pub struct CloseProtocolTrace {
        // Capture `handle`, `protocol_guid`, `agent_handle`
        pub inputs: VecDeque<(DeviceHandle, EfiGuid, EfiHandle)>,
    }

    /// Mock of the `EFI_BOOT_SERVICE.CloseProtocol` C API in test environment.
    ///
    /// # Safety
    ///
    ///   Caller should guarantee that `protocol_guid` points to valid memory location.
    unsafe extern "C" fn close_protocol(
        handle: EfiHandle,
        protocol_guid: *const EfiGuid,
        agent_handle: EfiHandle,
        _: EfiHandle,
    ) -> EfiStatus {
        EFI_CALL_TRACES.with(|traces| {
            traces.borrow_mut().close_protocol_trace.inputs.push_back((
                DeviceHandle(handle),
                // SAFETY: function safety docs require valid `protocol_guid`.
                unsafe { *protocol_guid },
                agent_handle,
            ));
            EFI_STATUS_SUCCESS
        })
    }

    /// EFI_BOOT_SERVICE.LocateHandleBuffer.
    #[derive(Default)]
    pub struct LocateHandleBufferTrace {
        // Capture `protocol`.
        pub inputs: VecDeque<EfiGuid>,
        // For returning in `num_handles` and `buf`.
        pub outputs: VecDeque<(usize, *mut DeviceHandle)>,
    }

    /// Mock of the `EFI_BOOT_SERVICE.LocateHandleBuffer` C API in test environment.
    ///
    /// # Safety
    /// Caller should guarantee that `protocol`, `num_handles`, and `buf` point to valid memory
    /// locations.
    unsafe extern "C" fn locate_handle_buffer(
        search_type: EfiLocateHandleSearchType,
        protocol: *const EfiGuid,
        search_key: *mut core::ffi::c_void,
        num_handles: *mut usize,
        buf: *mut *mut EfiHandle,
    ) -> EfiStatus {
        assert_eq!(search_type, EFI_LOCATE_HANDLE_SEARCH_TYPE_BY_PROTOCOL);
        assert_eq!(search_key, null_mut());
        EFI_CALL_TRACES.with(|traces| {
            let trace = &mut traces.borrow_mut().locate_handle_buffer_trace;
            // SAFETY: function safety docs require valid `protocol`.
            unsafe { trace.inputs.push_back(*protocol) };

            let (num, handles) = trace.outputs.pop_front().unwrap();
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
    }

    /// Mock of the `EFI_BOOT_SERVICE.GetMemoryMap` C API in test environment.
    ///
    /// # Safety
    ///
    ///   Caller should guarantee that `memory_map_size`, `map_key` and `desc_size` point to valid
    ///   memory locations.
    unsafe extern "C" fn get_memory_map(
        memory_map_size: *mut usize,
        memory_map: *mut EfiMemoryDescriptor,
        map_key: *mut usize,
        desc_size: *mut usize,
        _: *mut u32,
    ) -> EfiStatus {
        EFI_CALL_TRACES.with(|traces| {
            let trace = &mut traces.borrow_mut().get_memory_map_trace;
            trace.inputs.push_back((unsafe { *memory_map_size }, memory_map));
            // SAFETY: function safety docs require valid `memory_map_size`and `map_key`.
            unsafe { (*map_key, *memory_map_size) = trace.outputs.pop_front().unwrap() };
            // SAFETY: function safety docs require valid `desc_size`.
            unsafe { *desc_size = size_of::<EfiMemoryDescriptor>() };
            EFI_STATUS_SUCCESS
        })
    }

    /// EFI_BOOT_SERVICE.ExitBootServices.
    #[derive(Default)]
    pub struct ExitBootServicespTrace {
        // Capture `image_handle`, `map_key`
        pub inputs: VecDeque<(EfiHandle, usize)>,
    }

    /// Mock of the `EFI_BOOT_SERVICE.ExitBootServices` C API in test environment.
    extern "C" fn exit_boot_services(image_handle: EfiHandle, map_key: usize) -> EfiStatus {
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
        // Output a EfiEvent.
        pub outputs: VecDeque<EfiEvent>,
    }

    /// Mock of the `EFI_BOOT_SERVICE.CreateEvent` C API in test environment.
    ///
    /// # Safety
    ///
    ///   Caller should guarantee that `event` points to valid memory location.
    unsafe extern "C" fn create_event(
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
    extern "C" fn close_event(event: EfiEvent) -> EfiStatus {
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
    extern "C" fn check_event(_: EfiEvent) -> EfiStatus {
        EFI_CALL_TRACES.with(|traces| {
            let trace = &mut traces.borrow_mut().check_event_trace;
            trace.outputs.pop_front().unwrap()
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

        let mut systab: EfiSystemTable = Default::default();
        let mut boot_services: EfiBootService = Default::default();

        boot_services.free_pool = Some(free_pool);
        boot_services.open_protocol = Some(open_protocol);
        boot_services.close_protocol = Some(close_protocol);
        boot_services.locate_handle_buffer = Some(locate_handle_buffer);
        boot_services.get_memory_map = Some(get_memory_map);
        boot_services.exit_boot_services = Some(exit_boot_services);
        boot_services.create_event = Some(create_event);
        boot_services.close_event = Some(close_event);
        boot_services.check_event = Some(check_event);
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
                Protocol::new(DeviceHandle::new(null_mut()), &mut c_interface, &efi_entry)
            };
            f(&protocol);
        });
    }

    /// Get the pointer to an object as an EfiHandle type.
    pub fn as_efi_handle<T>(val: &mut T) -> EfiHandle {
        val as *mut T as *mut _
    }

    #[test]
    fn test_open_close_protocol() {
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
                let protocol = efi_entry
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

                    // close_protocol not called yet.
                    assert_eq!(trace.borrow_mut().close_protocol_trace.inputs, []);
                });

                // The protocol gets the correct EfiBlockIoProtocol structure we pass in.
                assert_eq!(protocol.interface_ptr(), &mut block_io as *mut _);
            }

            // Close protocol is called as `protocol` goes out of scope.
            EFI_CALL_TRACES
                .with(|trace| assert_eq!(trace.borrow_mut().close_protocol_trace.inputs, []));
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
            let mut located_handles: [DeviceHandle; 3] =
                [DeviceHandle(1 as *mut _), DeviceHandle(2 as *mut _), DeviceHandle(3 as *mut _)];
            EFI_CALL_TRACES.with(|traces| {
                traces.borrow_mut().locate_handle_buffer_trace.outputs =
                    VecDeque::from([(located_handles.len(), located_handles.as_mut_ptr())]);
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
            let mut located_handles: [DeviceHandle; 3] =
                [DeviceHandle(1 as *mut _), DeviceHandle(2 as *mut _), DeviceHandle(3 as *mut _)];
            EFI_CALL_TRACES.with(|traces| {
                traces.borrow_mut().locate_handle_buffer_trace.outputs =
                    VecDeque::from([(located_handles.len(), located_handles.as_mut_ptr())]);
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
                    [(DeviceHandle(1 as *mut _), BlockIoProtocol::GUID, image_handle),]
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
                    attributes: 0,
                },
                EfiMemoryDescriptor {
                    memory_type: EFI_MEMORY_TYPE_LOADER_CODE,
                    padding: 0,
                    physical_start: 0,
                    virtual_start: 0,
                    number_of_pages: 0,
                    attributes: 0,
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
                    attributes: 0,
                },
                EfiMemoryDescriptor {
                    memory_type: EFI_MEMORY_TYPE_LOADER_CODE,
                    padding: 0,
                    physical_start: 0,
                    virtual_start: 0,
                    number_of_pages: 0,
                    attributes: 0,
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
}
