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

//! Docs for booting on AArch64 is at:
//!
//!   https://www.kernel.org/doc/html/v5.11/arm64/booting.html

use core::arch::asm;

#[derive(Debug, PartialEq)]
pub enum ExceptionLevel {
    EL0,
    EL1,
    EL2,
    EL3,
}

/// Gets the current EL;
pub fn current_el() -> ExceptionLevel {
    let mut el: u64;
    // SAFETY: The assembly code only read current exception level.
    unsafe {
        asm!(
            "mrs {el}, CurrentEL",
            el = out(reg) el,
        );
    }
    el = (el >> 2) & 3;
    match el {
        0 => ExceptionLevel::EL0,
        1 => ExceptionLevel::EL1,
        2 => ExceptionLevel::EL2,
        3 => ExceptionLevel::EL3,
        v => panic!("Unknown EL {v}"),
    }
}

extern "C" {
    /// Clean and invalidate data cache by address range. The function is from ATF library.
    fn flush_dcache_range(addr: usize, len: usize);
}

/// Flush all data cache for the given buffer.
fn flush_dcache_buffer(buf: &[u8]) {
    unsafe { flush_dcache_range(buf.as_ptr() as usize, buf.len()) }
    // SAFETY: Assembly code for instruction synchronization.
    unsafe { asm!("isb") };
}

/// Disable cache, MMU and jump to the given kernel address with arguments.
///
/// # Args
///
/// * `addr`: Address to jump.
/// * `arg[0-3]`: Arguments for the target jump address.
///
/// # Safety
///
/// * Caller must ensure that `addr` contains valid execution code.
/// * Caller must ensure to flush any data cache for memory regions that contain data to be accessed
///   by the destination code, including the execution code itself at address `addr`
unsafe fn jump_kernel(addr: usize, arg0: usize, arg1: usize, arg2: usize, arg3: usize) -> ! {
    // TODO(b/334962949): Disable other stuffs such as interrupt, async abort, branch prediction etc.

    // After disabling MMU and cache, memory regions that have unflushed cache are stale and cannot
    // be trusted, including stack memory. Therefore all needed data including local variables must
    // be ensured to be loaded to registers first. `disable_cache_mmu_and_jump` only operates on
    // registers and does not access stack or any other memory.
    asm!(
        "b disable_cache_mmu_and_jump",
        in("x0") arg0,
        in("x1") arg1,
        in("x2") arg2,
        in("x3") arg3,
        in("x4") addr,
    );
    unreachable!();
}

/// Boots a Linux kernel in mode EL2 or lower with the given FDT blob.
///
/// # Safety
///
/// Caller must ensure that `kernel` contains a valid Linux kernel.
pub unsafe fn jump_linux_el2_or_lower(kernel: &[u8], ramdisk: &[u8], fdt: &[u8]) -> ! {
    assert_ne!(current_el(), ExceptionLevel::EL3);
    // The following is sufficient to work for existing use cases such as Cuttlefish. But there are
    // additional initializations listed
    // https://www.kernel.org/doc/html/v5.11/arm64/booting.html that may need to be performed
    // explicitly for other platforms.

    flush_dcache_buffer(kernel);
    flush_dcache_buffer(ramdisk);
    flush_dcache_buffer(fdt);
    // SAFETY:
    // * `kernel`, `ramdisk` and `fdt` have been flushed.
    // * By requirement of this function, `kernel` is a valid kernel entry point.
    unsafe { jump_kernel(kernel.as_ptr() as _, fdt.as_ptr() as _, 0, 0, 0) };
}

/// Boots a ZBI kernel in mode EL2 or lower with the given ZBI blob.
///
/// # Safety
///
/// Caller must ensure that `zbi_kernel` contains a valid zircon kernel ZBI item and `entry_off` is
/// the correct kernel entry offset.
pub unsafe fn jump_zircon_el2_or_lower(zbi_kernel: &[u8], entry_off: usize, zbi_item: &[u8]) -> ! {
    assert_ne!(current_el(), ExceptionLevel::EL3);
    flush_dcache_buffer(zbi_kernel);
    flush_dcache_buffer(zbi_item);
    let addr = (zbi_kernel.as_ptr() as usize).checked_add(entry_off).unwrap();
    // SAFETY:
    // * `zbi_kernel` and `zbi_item` have been flushed.
    // * By requirement of this function, the computed `addr` is a valid kernel entry point.
    unsafe { jump_kernel(addr, zbi_item.as_ptr() as _, 0, 0, 0) };
}
