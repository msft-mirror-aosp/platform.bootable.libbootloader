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

use crate::{AllocationAddress, EfiEntry, RuntimeServices};
use efi_types::EFI_MEMORY_TYPE_LOADER_DATA;

#[cfg(feature = "gbl_tracing")]
use core::sync::atomic::{AtomicUsize, Ordering};
use core::{
    alloc::{GlobalAlloc, Layout},
    mem::size_of,
    ptr::{copy, null_mut},
    slice::from_raw_parts,
};
use liberror::{Error, Result};
use safemath::SafeNum;

// Alignment guaranteed by EFI AllocatePoll()
const EFI_ALLOCATE_POOL_ALIGNMENT: usize = 8;
// Page size of AllocatePages() by UEFI spec.
const EFI_PAGE_SIZE: usize = efi_types::EFI_PAGE_SIZE as usize;

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
//
// TODO(b/396460116): Investigate using Mutex for the variable.
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
    #[allow(static_mut_refs)]
    unsafe {
        EFI_GLOBAL_ALLOCATOR.get_efi_entry_and_rt()
    }
}

/// Try to print via `EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL` in `EFI_SYSTEM_TABLE.ConOut`.
///
/// Errors are ignored.
#[macro_export]
macro_rules! efi_try_print {
    ($( $x:expr ),* $(,)? ) => {
        {
            let _ = (|| -> liberror::Result<()> {
                use core::fmt::Write;
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

    /// Computes the number of pages with a total size no smaller than `size`.
    fn pages(size: usize) -> Result<usize> {
        Ok(usize::try_from(SafeNum::from(size).round_up(EFI_PAGE_SIZE))? / EFI_PAGE_SIZE)
    }

    /// Allocates memory via EFI `AllocatePages()`.
    fn allocate_pages(&self, size: usize) -> Result<*mut u8> {
        let entry = self.state.efi_entry().ok_or(Error::InvalidState)?;
        let bs = entry.system_table_checked()?.boot_services_checked()?;
        let ptr = bs.allocate_pages(
            EFI_MEMORY_TYPE_LOADER_DATA,
            AllocationAddress::Any,
            Self::pages(size)?,
        )?;
        Ok(ptr as _)
    }

    /// Deallocates memory previously allocated by `allocate_pages()`.
    ///
    /// Errors are logged but ignored.
    fn deallocate_pages(&self, ptr: *mut u8, size: usize) {
        let Some(ref entry) = self.state.efi_entry() else {
            // After EFI_BOOT_SERVICES.ExitBootServices(), all allocated memory is considered
            // leaked and under full ownership of subsequent OS loader code.
            return;
        };
        let _ = entry
            .system_table_checked()
            .and_then(|v| v.boot_services_checked())
            .and_then(|v| v.free_pages(ptr as *mut _, Self::pages(size).unwrap()))
            .inspect_err(|e| efi_try_print!("Failed to deallocate pages: {e}\r\n"));
    }

    /// Allocate memory via EFI_BOOT_SERVICES.AllocatePool().
    fn allocate(&self, size: usize) -> *mut u8 {
        self.state
            .efi_entry()
            .ok_or(Error::InvalidState)
            .and_then(|v| v.system_table_checked())
            .and_then(|v| v.boot_services_checked())
            .and_then(|v| v.allocate_pool(EFI_MEMORY_TYPE_LOADER_DATA, size))
            .inspect_err(|e| efi_try_print!("Failed to allocate: {e}"))
            .unwrap_or_default() as _
    }

    /// Deallocates memory previously allocated by `Self::allocate()`.
    ///
    /// Errors are logged but ignored.
    fn deallocate(&self, ptr: *mut u8) {
        match self.state.efi_entry() {
            Some(ref entry) => {
                let _ = entry
                    .system_table_checked()
                    .and_then(|v| v.boot_services_checked())
                    .and_then(|v| v.free_pool(ptr as *mut _))
                    .inspect_err(|e| efi_try_print!("Failed to deallocate: {e}"));
            }
            // After EFI_BOOT_SERVICES.ExitBootServices(), all allocated memory is considered
            // leaked and under full ownership of subsequent OS loader code.
            _ => {}
        }
    }

    /// Selects whether to allocate by EFI pages and calculate the total alloc size accommodating
    /// alignment adjustment.
    fn select_alloc_type(layout: &Layout) -> Result<(bool, usize)> {
        let (sz, align) = (layout.size(), layout.align());
        let (by_pages, alloc_native_alignment) = match sz % EFI_PAGE_SIZE == 0 {
            true => (true, EFI_PAGE_SIZE),
            _ => (false, EFI_ALLOCATE_POOL_ALIGNMENT),
        };
        // If requested alignment is > alloc_alignment then make sure to allocate bigger buffer
        // to adjust ptr to be aligned and stores the real start address.
        Ok(match align > alloc_native_alignment {
            true => (by_pages, (SafeNum::from(align) + size_of::<usize>() + sz).try_into()?),
            _ => (by_pages, sz),
        })
    }
}

#[cfg(feature = "gbl_tracing")]
static HEAP_USAGE: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for EfiAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        (|| -> Result<*mut u8> {
            let (by_pages, alloc_sz) = Self::select_alloc_type(&layout)?;
            #[cfg(feature = "gbl_tracing")]
            {
                let total = HEAP_USAGE.fetch_add(alloc_sz, Ordering::Relaxed);
                trace::gbl_trace_add_heap_snapshot((total + alloc_sz) as _);
            }
            let ptr = match by_pages {
                false => self.allocate(alloc_sz),
                _ => self.allocate_pages(alloc_sz)?,
            };

            if ptr.is_null() {
                return Err(Error::Other(Some("Allocation failed")));
            } else if alloc_sz == layout.size() {
                // No need for alignment adjustment.
                return Ok(ptr);
            }
            let addr_bytes = (ptr as usize).to_ne_bytes();
            let offset = layout.align() - (ptr as usize % layout.align());
            assert!(offset <= alloc_sz && alloc_sz - offset >= layout.size());

            // SAFETY:
            // - `ptr` is guaranteed to point to buffer bigger than `layout.size()`, plus the
            //   alignment (and thus `offset`) and plus a usize value.
            unsafe {
                let ptr = ptr.add(offset);
                copy(addr_bytes.as_ptr(), ptr.add(layout.size()), addr_bytes.len());
                Ok(ptr)
            }
        })()
        .unwrap_or(null_mut()) as _
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let (by_pages, alloc_sz) = Self::select_alloc_type(&layout).unwrap();
        #[cfg(feature = "gbl_tracing")]
        {
            let total = HEAP_USAGE.fetch_sub(alloc_sz, Ordering::Relaxed);
            trace::gbl_trace_add_heap_snapshot((total - alloc_sz) as _);
        }
        let sz = layout.size();
        // Checks if alignment adjustment was performed and finds real allocated pointer.
        let ptr = match alloc_sz == sz {
            true => ptr,
            _ => {
                // SAFETY:
                // `ptr` guarantees to point to a buffer big enough to contain `layout.size()`,
                // plus a valid usize value.
                let addr_bytes = unsafe { from_raw_parts(ptr.add(sz), size_of::<usize>()) };
                usize::from_ne_bytes(addr_bytes.try_into().unwrap()) as _
            }
        };

        match by_pages {
            false => self.deallocate(ptr),
            _ => self.deallocate_pages(ptr, alloc_sz),
        };
    }
}
