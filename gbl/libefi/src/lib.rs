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
//! fn main(image: EfiHandle, systab_ptr: *mut EfiSystemTable) -> efi::EfiResult<()> {
//!     let efi_entry = initialize(image, systab_ptr);
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

use core::ptr::null_mut;
#[cfg(not(test))]
use core::{fmt::Write, panic::PanicInfo};

#[rustfmt::skip]
pub mod defs;
use defs::*;

#[cfg(not(test))]
mod allocation;

mod protocol;
// Protocol type and implementation to export.
pub use protocol::BlockIoProtocol;
pub use protocol::DevicePathProtocol;
pub use protocol::DevicePathText;
pub use protocol::DevicePathToTextProtocol;
pub use protocol::LoadedImageProtocol;
pub use protocol::Protocol;
pub use protocol::ProtocolInfo;
pub use protocol::SimpleTextOutputProtocol;

mod error {
    use super::defs::EFI_STATUS_SUCCESS;
    use super::EfiStatus;

    #[derive(Debug, Copy, Clone, PartialEq)]
    pub enum ErrorTypes {
        Unknown,
        EfiStatusError(EfiStatus),
    }

    #[derive(Debug)]
    pub struct EfiError(ErrorTypes);

    impl EfiError {
        pub fn err(&self) -> ErrorTypes {
            self.0
        }
    }

    impl From<EfiStatus> for EfiError {
        fn from(efi_status: EfiStatus) -> EfiError {
            EfiError(match efi_status {
                EFI_STATUS_SUCCESS => ErrorTypes::Unknown,
                _ => ErrorTypes::EfiStatusError(
                    // Remove the highest bit in the error code so that it's eaiser to interpret
                    // when printing.
                    efi_status & !(1 << (core::mem::size_of::<EfiStatus>() * 8 - 1)),
                ),
            })
        }
    }
}

pub use error::*;

/// Result type for this library.
pub type EfiResult<T> = core::result::Result<T, EfiError>;

/// Helper method to convert an EFI status code to EfiResult.
fn map_efi_err(code: EfiStatus) -> EfiResult<()> {
    match code {
        EFI_STATUS_SUCCESS => Ok(()),
        _ => Err(code.into()),
    }
}

/// `EfiEntry` stores the EFI system table pointer and image handle passed from the entry point.
/// It's the root data structure that derives all other wrapper APIs and structures.
#[derive(Clone, Copy)]
pub struct EfiEntry {
    image_handle: EfiHandle,
    systab_ptr: *const EfiSystemTable,
}

impl EfiEntry {
    /// Get an instance of `SystemTable`.
    pub fn system_table(&self) -> SystemTable {
        // SAFETY: Pointers to UEFI data strucutres.
        SystemTable { efi_entry: self, table: unsafe { self.systab_ptr.as_ref() }.unwrap() }
    }

    /// Get the image handle.
    pub fn image_handle(&self) -> DeviceHandle {
        DeviceHandle(self.image_handle)
    }
}

/// Create an `EfiEntry` and initialize EFI global allocator. Calling this function should be the
/// first thing an EFI application does.
pub fn initialize(image_handle: EfiHandle, systab_ptr: *const EfiSystemTable) -> EfiEntry {
    let efi_entry = EfiEntry { image_handle, systab_ptr };
    #[cfg(not(test))]
    allocation::init_efi_global_alloc(efi_entry);
    efi_entry
}

/// `SystemTable` provides methods for accessing fields in `EFI_SYSTEM_TABLE`.
#[derive(Clone, Copy)]
//pub struct SystemTable<'a>(&'a EfiEntry);
pub struct SystemTable<'a> {
    efi_entry: &'a EfiEntry,
    table: &'a EfiSystemTable,
}

impl<'a> SystemTable<'a> {
    /// Create an instance of `BootServices`
    pub fn boot_services(&self) -> BootServices<'a> {
        BootServices {
            efi_entry: self.efi_entry,
            // SAFETY: Pointers to UEFI data strucutres.
            boot_services: unsafe { self.table.boot_services.as_ref() }.unwrap(),
        }
    }

    /// Get the `EFI_SYSTEM_TABLE.ConOut` field.
    pub fn con_out(&self) -> EfiResult<Protocol<'a, SimpleTextOutputProtocol>> {
        Ok(Protocol::<SimpleTextOutputProtocol>::new(
            DeviceHandle(null_mut()), // No device handle. This protocol is a permanent reference.
            self.table.con_out,
            self.efi_entry,
        ))
    }
}

/// `BootServices` provides methods for accessing various EFI_BOOT_SERVICES interfaces.
#[derive(Clone, Copy)]
pub struct BootServices<'a> {
    efi_entry: &'a EfiEntry,
    boot_services: &'a EfiBootService,
}

impl<'a> BootServices<'a> {
    /// Wrapper of `EFI_BOOT_SERVICES.AllocatePool()`
    pub fn allocate_pool(
        &self,
        pool_type: EfiMemoryType,
        size: usize,
    ) -> EfiResult<*mut core::ffi::c_void> {
        let mut out: *mut core::ffi::c_void = null_mut();
        // SAFETY: `EFI_BOOT_SERVICES` method call.
        unsafe {
            efi_call!(self.boot_services.allocate_pool, pool_type, size, &mut out)?;
        }
        Ok(out)
    }

    /// Wrapper of `EFI_BOOT_SERVICES.FreePool()`
    fn free_pool(&self, buf: *mut core::ffi::c_void) -> EfiResult<()> {
        // SAFETY: `EFI_BOOT_SERVICES` method call.
        unsafe { efi_call!(self.boot_services.free_pool, buf) }
    }

    /// Wrapper of `EFI_BOOT_SERVICES.OpenProtocol()`
    pub fn open_protocol<T: ProtocolInfo>(
        &self,
        handle: DeviceHandle,
    ) -> EfiResult<Protocol<'a, T>> {
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

        Ok(Protocol::<T>::new(handle, out_handle as *mut _, self.efi_entry))
    }

    /// Wrapper of `EFI_BOOT_SERVICES.CloseProtocol()`
    fn close_protocol<T: ProtocolInfo>(&self, handle: DeviceHandle) -> EfiResult<()> {
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
    pub fn locate_handle_buffer_by_protocol<T: ProtocolInfo>(
        &self,
    ) -> EfiResult<LocatedHandles<'a>> {
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
    pub fn find_first_and_open<T: ProtocolInfo>(&self) -> EfiResult<Protocol<'a, T>> {
        // We don't use EFI_BOOT_SERVICES.LocateProtocol() because it doesn't give device handle
        // which is required to close the protocol.
        let handle = *self
            .locate_handle_buffer_by_protocol::<T>()?
            .handles()
            .first()
            .ok_or::<EfiError>(EFI_STATUS_NOT_FOUND.into())?;
        self.open_protocol::<T>(handle)
    }
}

/// A type representing a UEFI handle to a UEFI device.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct DeviceHandle(EfiHandle);

/// `LocatedHandles` holds the array of handles return by
/// `BootServices::locate_handle_buffer_by_protocol()`
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
            handles: unsafe { core::slice::from_raw_parts(handles as *mut DeviceHandle, len) },
            efi_entry: efi_entry,
        }
    }
    /// Get the list of handles as a slice
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

/// Provide a builtin panic handler.
/// In the long term, to improve flexibility, consider allowing application to install a custom
/// handler into `EfiEntry` to be called here.
#[cfg(not(test))]
#[panic_handler]
fn panic(panic: &PanicInfo) -> ! {
    // If there is a valid internal `efi_entry` from global allocator, print the panic info.
    let entry = allocation::internal_efi_entry();
    if let Some(e) = entry {
        match e.system_table().con_out() {
            Ok(mut con_out) => {
                let _ = write!(con_out, "Panics! {}\n", panic);
            }
            _ => {}
        }
    }
    loop {}
}

#[cfg(test)]
mod test {
    use super::*;
    use std::cell::RefCell;
    use std::collections::VecDeque;

    /// A structure to store the traces of arguments/outputs for EFI methods.
    #[derive(Default)]
    pub struct EfiCallTraces {
        pub free_pool_trace: FreePoolTrace,
        pub open_protocol_trace: OpenProtocolTrace,
        pub close_protocol_trace: CloseProtocolTrace,
        pub locate_handle_buffer_trace: LocateHandleBufferTrace,
    }

    // Declare a global instance of EfiCallTraces.
    // Need to use thread local storage because rust unit test is multi-threaded.
    thread_local! {
        static EFI_CALL_TRACES: RefCell<EfiCallTraces> = RefCell::new(Default::default());
    }

    /// Export for unit-test in submodules.
    pub fn efi_call_traces() -> &'static std::thread::LocalKey<RefCell<EfiCallTraces>> {
        &EFI_CALL_TRACES
    }

    /// EFI_BOOT_SERVICE.FreePool() test implementation.
    #[derive(Default)]
    pub struct FreePoolTrace {
        // Capture `buf`
        pub inputs: VecDeque<*mut core::ffi::c_void>,
    }

    unsafe extern "C" fn free_pool(buf: *mut core::ffi::c_void) -> EfiStatus {
        EFI_CALL_TRACES.with(|traces| {
            traces.borrow_mut().free_pool_trace.inputs.push_back(buf);
            EFI_STATUS_SUCCESS
        })
    }

    /// EFI_BOOT_SERVICE.OpenProtocol() test implementation.
    #[derive(Default)]
    pub struct OpenProtocolTrace {
        // Capture `handle`, `protocol_guid`, `agent_handle`
        pub inputs: VecDeque<(DeviceHandle, EfiGuid, EfiHandle)>,
        // Return `intf`, EfiStatus
        pub outputs: VecDeque<(EfiHandle, EfiStatus)>,
    }

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
            trace.inputs.push_back((DeviceHandle(handle), *protocol_guid, agent_handle));

            let (intf_handle, status) = trace.outputs.pop_front().unwrap();
            // SAFETY:
            // A correct implementation of BootServices::open_protocol guarantee to pass valid
            // pointers here.
            *unsafe { intf.as_mut() }.unwrap() = intf_handle;

            status
        })
    }

    /// EFI_BOOT_SERVICE.CloseProtocol() test implementation.
    #[derive(Default)]
    pub struct CloseProtocolTrace {
        // Capture `handle`, `protocol_guid`, `agent_handle`
        pub inputs: VecDeque<(DeviceHandle, EfiGuid, EfiHandle)>,
    }

    unsafe extern "C" fn close_protocol(
        handle: EfiHandle,
        protocol_guid: *const EfiGuid,
        agent_handle: EfiHandle,
        _: EfiHandle,
    ) -> EfiStatus {
        EFI_CALL_TRACES.with(|traces| {
            traces.borrow_mut().close_protocol_trace.inputs.push_back((
                DeviceHandle(handle),
                *protocol_guid,
                agent_handle,
            ));
            EFI_STATUS_SUCCESS
        })
    }

    /// EFI_BOOT_SERVICE.LocateHandleBuffer
    #[derive(Default)]
    pub struct LocateHandleBufferTrace {
        // Capture `protocol`
        pub inputs: VecDeque<EfiGuid>,
        // For returning in `num_handles` and `buf`
        pub outputs: VecDeque<(usize, *mut DeviceHandle)>,
    }

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
            trace.inputs.push_back(*protocol);

            let (num, handles) = trace.outputs.pop_front().unwrap();
            // SAFETY:
            // A correct implementation of BootServices::open_protocol guarantees to pass valid
            // pointers here.
            unsafe {
                *num_handles = num as usize;
                *buf = handles as *mut EfiHandle;
            };

            EFI_STATUS_SUCCESS
        })
    }

    /// A test wrapper that sets up a system table, image handle and runs a test function like it
    /// is an EFI application.
    /// TODO(300168989): Investigate using procedural macro to generate test that auto calls this.
    pub fn run_test(func: fn(EfiHandle, *mut EfiSystemTable) -> ()) {
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
        systab.boot_services = &mut boot_services as *mut _;
        let image_handle: usize = 1234; // Don't care.

        func(image_handle as EfiHandle, &mut systab as *mut _);

        // Reset all traces
        EFI_CALL_TRACES.with(|trace| {
            *trace.borrow_mut() = Default::default();
        });
    }

    /// Get the pointer to an object as an EfiHandle type.
    fn as_efi_handle<T>(val: &mut T) -> EfiHandle {
        val as *mut T as *mut _
    }

    #[test]
    fn test_open_close_protocol() {
        run_test(|image, systab| {
            let efi_entry = initialize(image, systab);

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
                            image
                        ),]
                    );

                    // close_protocol not called yet.
                    assert_eq!(trace.borrow_mut().close_protocol_trace.inputs, []);
                });

                // The protocol gets the correct EfiBlockIoProtocol structure we pass in.
                assert_eq!(protocol.interface_ptr(), &mut block_io as *mut _);
            }

            // Close protocol is called as `protocol` goes out of scope .
            EFI_CALL_TRACES.with(|trace| {
                assert_eq!(
                    trace.borrow_mut().close_protocol_trace.inputs,
                    [(
                        DeviceHandle(as_efi_handle(&mut device_handle)),
                        BlockIoProtocol::GUID,
                        image
                    ),]
                )
            });
        })
    }

    #[test]
    fn test_null_efi_method() {
        // Test that wrapper call fails if efi method is None.
        run_test(|image, systab| {
            let efi_entry = initialize(image, systab);

            // Set up open_protocol trace
            let mut block_io: EfiBlockIoProtocol = Default::default();
            EFI_CALL_TRACES.with(|traces| {
                traces.borrow_mut().open_protocol_trace.outputs =
                    VecDeque::from([(as_efi_handle(&mut block_io), EFI_STATUS_SUCCESS)]);
            });

            // Set the method to None.
            // SAFETY:
            // run_test() guarantees `boot_services` pointer points to valid object.
            unsafe { (*(*systab).boot_services).open_protocol = None };

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
        run_test(|image, systab| {
            let efi_entry = initialize(image, systab);

            // Set up open_protocol trace
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
        run_test(|image, systab| {
            let efi_entry = initialize(image, systab);

            // Set up locate_handle_buffer_trace trace
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
        run_test(|image, systab| {
            let efi_entry = initialize(image, systab);

            // Set up locate_handle_buffer_trace trace
            let mut located_handles: [DeviceHandle; 3] =
                [DeviceHandle(1 as *mut _), DeviceHandle(2 as *mut _), DeviceHandle(3 as *mut _)];
            EFI_CALL_TRACES.with(|traces| {
                traces.borrow_mut().locate_handle_buffer_trace.outputs =
                    VecDeque::from([(located_handles.len(), located_handles.as_mut_ptr())]);
            });

            // Set up open_protocol trace
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

            // Check open_protocol is called on the first handle
            EFI_CALL_TRACES.with(|traces| {
                assert_eq!(
                    traces.borrow_mut().open_protocol_trace.inputs,
                    [(DeviceHandle(1 as *mut _), BlockIoProtocol::GUID, image),]
                );
            });
        })
    }

    #[test]
    fn test_efi_error() {
        let res: EfiResult<()> = Err(EFI_STATUS_NOT_FOUND.into());
        assert_eq!(res.unwrap_err().err(), ErrorTypes::EfiStatusError(14));
    }
}
