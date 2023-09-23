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

use super::defs::EFI_MEMORY_TYPE_LOADER_DATA;
use super::EfiEntry;
use core::alloc::{GlobalAlloc, Layout};
use core::ptr::null_mut;

// Implement a global allocator using `EFI_BOOT_SERVICES.AllocatePool()/FreePool()`
pub struct EfiAllocator(Option<EfiEntry>);

#[global_allocator]
static mut EFI_GLOBAL_ALLOCATOR: EfiAllocator = EfiAllocator(None);

unsafe impl GlobalAlloc for EfiAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let size = layout.size();
        let align = layout.align();
        // TODO(300168989): `EFI_BOOT_SERVICES.AllocatePool()` is only 8-byte aligned. Add support
        // for arbitrary alignment.
        // `AllocatePool()` can be slow for allocating large buffers. In this case,
        // `AllocatePages()` is recommended.
        assert_eq!(8usize.checked_rem(align).unwrap(), 0);
        match self
            .0
            .unwrap()
            .system_table()
            .boot_services()
            .allocate_pool(EFI_MEMORY_TYPE_LOADER_DATA, size)
        {
            Ok(p) => p as *mut _,
            _ => null_mut(),
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        self.0.unwrap().system_table().boot_services().free_pool(ptr as *mut _).unwrap();
    }
}

/// Initialize global allocator.
pub fn init_efi_global_alloc(efi_entry: EfiEntry) {
    // SAFETY: EFI application is single thread only.
    unsafe {
        EFI_GLOBAL_ALLOCATOR = EfiAllocator(Some(efi_entry));
    }
}
