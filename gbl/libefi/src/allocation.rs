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

use crate::{EfiEntry, RuntimeServices};
use efi_types::EFI_MEMORY_TYPE_LOADER_DATA;

use core::mem::size_of_val;
use core::ptr::null_mut;
use core::{
    alloc::{GlobalAlloc, Layout},
    fmt::Write,
};
use liberror::{Error, Result};
use safemath::SafeNum;

/// Implements a global allocator using `EFI_BOOT_SERVICES.AllocatePool()/FreePool()`
///
/// To use, add this exact declaration to the application code:
///
/// ```
/// #[no_mangle]
/// #[global_allocator]
/// static mut EFI_GLOBAL_ALLOCATOR: EfiAllocator = EfiState::new();
/// ```
///
/// This is only useful for real UEFI applications; attempting to install the `EFI_GLOBAL_ALLOCATOR`
/// for host-side unit tests will cause the test to panic immediately.
pub struct EfiAllocator {
    state: EfiState,
    runtime_services: Option<RuntimeServices>,
}

/// Represents the global EFI state.
enum EfiState {
    /// Initial state, no UEFI entry point has been set, global hooks will not work.
    Uninitialized,
    /// [EfiEntry] is registered, global hooks are active.
    Initialized(EfiEntry),
    /// ExitBootServices has been called, global hooks will not work.
    Exited,
}

impl EfiState {
    /// Returns a reference to the EfiEntry.
    fn efi_entry(&self) -> Option<&EfiEntry> {
        match self {
            EfiState::Initialized(ref entry) => Some(entry),
            _ => None,
        }
    }
}

// This is a bit ugly, but we only expect this library to be used by our EFI application so it
// doesn't need to be super clean or scalable. The user has to declare the global variable
// exactly as written in the [EfiAllocator] docs for this to link properly.
extern "Rust" {
    static mut EFI_GLOBAL_ALLOCATOR: EfiAllocator;
}

/// An internal API to obtain library internal global EfiEntry and RuntimeServices.
pub(crate) fn internal_efi_entry_and_rt(
) -> (Option<&'static EfiEntry>, Option<&'static RuntimeServices>) {
    // SAFETY:
    // EFI_GLOBAL_ALLOCATOR is only read by `internal_efi_entry_and_rt()` and modified by
    // `init_efi_global_alloc()` and `exit_efi_global_alloc()`. The safety requirements of
    // `init_efi_global_alloc()` and `exit_efi_global_alloc()` mandate that there can be no EFI
    // event/notification/interrupt that can be triggered when they are called. This suggests that
    // there cannot be concurrent read and modification on `EFI_GLOBAL_ALLOCATOR` possible. Thus its
    // access is safe from race condition.
    unsafe { EFI_GLOBAL_ALLOCATOR.get_efi_entry_and_rt() }
}

/// Try to print via `EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL` in `EFI_SYSTEM_TABLE.ConOut`.
///
/// Errors are ignored.
#[macro_export]
macro_rules! efi_try_print {
    ($( $x:expr ),* $(,)? ) => {
        {
            let _ = (|| -> Result<()> {
                if let Some(entry) = crate::allocation::internal_efi_entry_and_rt().0 {
                    write!(entry.system_table_checked()?.con_out()?, $($x,)*)?;
                }
                Ok(())
            })();
        }
    };
}

/// Initializes global allocator.
///
/// # Safety
///
/// This function modifies global variable `EFI_GLOBAL_ALLOCATOR`. It should only be called when
/// there is no event/notification function that can be triggered or modify it. Otherwise there
/// is a risk of race condition.
pub(crate) unsafe fn init_efi_global_alloc(efi_entry: EfiEntry) -> Result<()> {
    // SAFETY: See SAFETY of `internal_efi_entry_and_rt()`
    unsafe {
        EFI_GLOBAL_ALLOCATOR.runtime_services =
            efi_entry.system_table_checked().and_then(|v| v.runtime_services_checked()).ok();
        match EFI_GLOBAL_ALLOCATOR.state {
            EfiState::Uninitialized => {
                EFI_GLOBAL_ALLOCATOR.state = EfiState::Initialized(efi_entry);
                Ok(())
            }
            _ => Err(Error::AlreadyStarted),
        }
    }
}

/// Internal API to invalidate global allocator after ExitBootService().
///
/// # Safety
///
/// This function modifies global variable `EFI_GLOBAL_ALLOCATOR`. It should only be called when
/// there is no event/notification function that can be triggered or modify it. Otherwise there
/// is a risk of race condition.
pub(crate) unsafe fn exit_efi_global_alloc() {
    // SAFETY: See SAFETY of `internal_efi_entry_and_rt()`
    unsafe {
        EFI_GLOBAL_ALLOCATOR.state = EfiState::Exited;
    }
}

impl EfiAllocator {
    /// Creates a new instance.
    pub const fn new() -> Self {
        Self { state: EfiState::Uninitialized, runtime_services: None }
    }

    /// Gets EfiEntry and RuntimeServices
    fn get_efi_entry_and_rt(&self) -> (Option<&EfiEntry>, Option<&RuntimeServices>) {
        (self.state.efi_entry(), self.runtime_services.as_ref())
    }

    /// Allocate memory via EFI_BOOT_SERVICES.
    fn allocate(&self, size: usize) -> *mut u8 {
        self.state
            .efi_entry()
            .ok_or(Error::InvalidState)
            .and_then(|v| v.system_table_checked())
            .and_then(|v| v.boot_services_checked())
            .and_then(|v| v.allocate_pool(EFI_MEMORY_TYPE_LOADER_DATA, size))
            .inspect_err(|e| efi_try_print!("failed to allocate: {e}"))
            .unwrap_or(null_mut()) as _
    }

    /// Deallocate memory previously allocated by `Self::allocate()`.
    ///
    /// Errors are logged but ignored.
    fn deallocate(&self, ptr: *mut u8) {
        match self.state.efi_entry() {
            Some(ref entry) => {
                let _ = entry
                    .system_table_checked()
                    .and_then(|v| v.boot_services_checked())
                    .and_then(|v| v.free_pool(ptr as *mut _))
                    .inspect_err(|e| efi_try_print!("failed to deallocate: {e}"));
            }
            // After EFI_BOOT_SERVICES.ExitBootServices(), all allocated memory is considered
            // leaked and under full ownership of subsequent OS loader code.
            _ => {}
        }
    }
}

// Alignment guaranteed by EFI AllocatePoll()
const EFI_ALLOCATE_POOL_ALIGNMENT: usize = 8;

unsafe impl GlobalAlloc for EfiAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        (|| -> Result<*mut u8> {
            let align = layout.align();

            // EFI AllocatePoll() must be at 8-bytes aligned so we can just use returned pointer.
            if align <= EFI_ALLOCATE_POOL_ALIGNMENT {
                let ptr = self.allocate(layout.size());
                assert_eq!(ptr as usize % EFI_ALLOCATE_POOL_ALIGNMENT, 0);
                return Ok(ptr);
            }

            // If requested alignment is > EFI_ALLOCATE_POOL_ALIGNMENT then make sure to allocate
            // bigger buffer and adjust ptr to be aligned.
            let mut offset: usize = 0usize;
            let extra_size = SafeNum::from(align) + size_of_val(&offset);
            let size = SafeNum::from(layout.size()) + extra_size;

            // TODO(300168989):
            // `AllocatePool()` can be slow for allocating large buffers. In this case,
            // `AllocatePages()` is recommended.
            let unaligned_ptr = self.allocate(size.try_into()?);
            if unaligned_ptr.is_null() {
                return Err(Error::Other(Some("Allocation failed")));
            }
            offset = align - (unaligned_ptr as usize % align);

            // SAFETY:
            // - `unaligned_ptr` is guaranteed to point to buffer big enough to contain offset+size
            // bytes since this is the size passed to `allocate`
            // - ptr+layout.size() is also pointing to valid buffer since actual allocate size takes
            // into account additional suffix for usize variable
            unsafe {
                let ptr = unaligned_ptr.add(offset);
                core::slice::from_raw_parts_mut(ptr.add(layout.size()), size_of_val(&offset))
                    .copy_from_slice(&offset.to_ne_bytes());
                Ok(ptr)
            }
        })()
        .unwrap_or(null_mut()) as _
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // If alignment is EFI_ALLOCATE_POOL_ALIGNMENT or less, then we can just used ptr directly
        if layout.align() <= EFI_ALLOCATE_POOL_ALIGNMENT {
            self.deallocate(ptr);
            return;
        }

        let mut offset: usize = 0usize;
        offset = usize::from_ne_bytes(
            // SAFETY:
            // * `ptr` is allocated by `alloc` and has enough padding after `ptr`+size to hold
            // suffix `offset: usize`.
            // * Alignment of `ptr` is 1 for &[u8]
            unsafe { core::slice::from_raw_parts(ptr.add(layout.size()), size_of_val(&offset)) }
                .try_into()
                .unwrap(),
        );

        // SAFETY:
        // (`ptr` - `offset`) must be valid unaligned pointer to buffer allocated by `alloc`
        let real_start_ptr = unsafe { ptr.sub(offset) };
        self.deallocate(real_start_ptr);
    }
}

/// API for allocating raw memory via EFI_BOOT_SERVICES
pub fn efi_malloc(size: usize) -> *mut u8 {
    // SAFETY: See SAFETY of `internal_efi_entry()`.
    unsafe { EFI_GLOBAL_ALLOCATOR.allocate(size) }
}

/// API for deallocating raw memory previously allocated by `efi_malloc()`. Passing invalid
/// pointer will cause the function to panic.
pub fn efi_free(ptr: *mut u8) {
    // SAFETY: See SAFETY of `internal_efi_entry()`.
    unsafe { EFI_GLOBAL_ALLOCATOR.deallocate(ptr) }
}
