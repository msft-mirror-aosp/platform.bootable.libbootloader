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

//! The GBL UEFI application.
//!
//! This just contains the minimal entry point and global hook declarations
//! needed for a full application build; all the logic should go in the
//! `gbl_efi` library instead.

#![no_std]
#![no_main]

#[cfg(target_arch = "riscv64")]
mod riscv64;

use cfg_if::cfg_if;
use core::panic::PanicInfo;
use efi::{
    efi_println, initialize,
    protocol::random_number_generator::{RandomNumberGeneratorProtocol, RngAlgorithm},
    report_error_and_reset_with_global_entry, EfiAllocator, EfiEntry,
};
use efi_types::{EfiHandle, EfiSystemTable, GBL_EFI_DEBUG_ERROR_TAG_ASSERTION_ERROR};
use gbl_efi::app_main;

use libstack::initialize_canary;

#[panic_handler]
fn handle_panic(p_info: &PanicInfo) -> ! {
    // Safety:
    // * The very first thing the application does is initialize the global EFI entry.
    unsafe {
        report_error_and_reset_with_global_entry(p_info, GBL_EFI_DEBUG_ERROR_TAG_ASSERTION_ERROR)
    }
}

#[no_mangle]
#[global_allocator]
static mut EFI_GLOBAL_ALLOCATOR: EfiAllocator = EfiAllocator::new();

/// Pull in the sysdeps required by libavb so the linker can find them.
extern crate avb_sysdeps;
/// Pull in the sysdeps required by boringssl so the linker can find them.
extern crate boringssl_sysdeps;
/// Pull in the getentropy implementation.
extern crate efi_rng;

fn generate_canary(entry: &EfiEntry) -> usize {
    let canary = entry
        .system_table()
        .boot_services()
        .find_first_and_open::<RandomNumberGeneratorProtocol>()
        .and_then(|rng_proto| rng_proto.get_rng(RngAlgorithm::Default));

    cfg_if! {
        if #[cfg(feature = "gbl_dev")] {
            let canary_default;
            cfg_if! {
                if #[cfg(target_pointer_width = "64")] {
                    canary_default = 0x27085dc5dd4d6b7dusize ^ (entry as *const _ as usize);
                } else {
                    compile_error!("Only 64 bit targets are supported");
                }
            }
            canary
                .unwrap_or_else(|e| {
                    efi_println!(entry,
                                 "SECURITY WARNING: Failed to generate stack canary, using fallback: {:?}", e);
                    canary_default}
                )
        } else {
            // It's better to crash on failure than to ignore the error.
            canary
                .inspect_err(|e| efi_println!(entry, "SECURITY ERROR: Failed to generate stack canary: {:?}", e))
                .unwrap()
        }
    }
}

/// The function implements a simple handshake protocol between GBL and GDB for the initial
/// execution break and passing of GBL load address in memory, which is needed for GDB to load
/// symbols.
#[cfg(any(feature = "gdb_debug", feature = "always-wait-gdb"))]
fn wait_gdb(entry: &EfiEntry) -> libgbl::Result<()> {
    // Our debug script `qemu_gdb_example/load_gbl_debug_bin.py` looks for this magic to determine
    // if GBL is ready for debug. Must be kept in sync with
    // `qemu_gdb_example/load_gbl_debug_bin.py`.
    const GDB_MAGIC: u64 = 0x166eb3328561cfe7;
    let image_base = gbl_efi::utils::image_base(entry)?;
    efi_println!(entry, "Image base: {:#x}", image_base);
    let mut buf = [0u8; 1];
    if cfg!(feature = "always-wait-gdb")
        || entry
            .system_table()
            .runtime_services()
            .get_variable(&efi::EFI_GLOBAL_VARIABLE_GUID, "gbl_debug", &mut buf)
            .is_ok()
    {
        #[cfg(target_arch = "x86_64")]
        {
            efi_println!(entry, "Set $rax=0 from debugger to continue.");
            // Sets $rax to `GDB_MAGIC` and $rcx to the image load address
            // which will be retrieved by the debug script for loading debug
            // symbols. Loops until $rax is set 0 either by the
            // debug script or manually from gdb.

            // SAFETY: The assembly code only sets $rax and $rcx reigster.
            // It explicitly marks them as clobbered and does not modify
            // any memory.
            unsafe {
                core::arch::asm!(
                    "2:",
                    "cmp rax, 0",
                    "jne 2b",
                    in("rax") GDB_MAGIC,
                    in("rcx") image_base,
                    clobber_abi("C"),
                );
            }
            efi_println!(entry, "gdb connected!");
        }
        #[cfg(target_arch = "aarch64")]
        {
            efi_println!(entry, "Set $x0=0 from debugger to continue.");
            // Sets $x0 to `GDB_MAGIC` and $x2 to the image load address
            // which will be retrieved by the debug script for loading debug
            // symbols. Loops until $x0 is set 0 either by the
            // debug script or manually from gdb.

            // SAFETY: The assembly code only sets $x0 and $x2 reigster.
            // It explicitly marks them as clobbered and does not modify
            // any memory.
            unsafe {
                core::arch::asm!(
                    "2:",
                    "cmp x0, 0",
                    "b.ne 2b",
                    in("x0") GDB_MAGIC,
                    in("x2") image_base,
                    clobber_abi("C"),
                );
            }
        }
        #[cfg(target_arch = "riscv64")]
        {
            let _ = GDB_MAGIC; // Suppresses unused variables error.
            unimplemented!();
        }
    }
    Ok(())
}

/// EFI application entry point. Does not return.
///
/// # Safety
/// `image_handle` and `systab_ptr` must be valid objects that adhere to the UEFI specification.
#[no_mangle]
pub unsafe extern "C" fn efi_main(image_handle: EfiHandle, systab_ptr: *mut EfiSystemTable) {
    // SAFETY:
    // * caller provides valid `image_handle` and `systab_ptr` objects
    // * we only call `initialize()` once
    let Ok(entry) = (unsafe { initialize(image_handle, systab_ptr) }) else {
        // Can't panic, can't log. Just return.
        return;
    };
    let canary = generate_canary(&entry);
    // SAFETY:
    // * `systab_ptr` is non-NULL because this is a just-started UEFI application.
    // * `initialize_canary` has sole access to static mutable variables.
    // * UEFI is single-threaded, so there can be no concurrent
    //   mutations to static, mutable variables.
    // * `efi_main` does not exit as required by `initialize_canary`.
    //
    // Note: the mask clears the two least significant bytes,
    // and `usize::to_le` ensures that those null bytes are on the left.
    unsafe {
        initialize_canary(systab_ptr, usize::to_le(canary & !0xFFFF));
    }

    #[cfg(any(feature = "gdb_debug", feature = "always-wait-gdb"))]
    let _ = wait_gdb(&entry).inspect_err(|_| efi_println!(entry, "Failed to wait gdb connection."));

    app_main(entry).unwrap();
}
