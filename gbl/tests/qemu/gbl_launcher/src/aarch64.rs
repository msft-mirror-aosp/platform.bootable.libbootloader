// Copyright (C) 2026 The Android Open Source Project
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

//! AArch64 specific utilities.

use boot::aarch64::{current_el, ExceptionLevel};
use core::arch::asm;

/// Walks the page tables for the given virtual address range and calls the closure `f` for each
/// block/page descriptor found. The closure is called with the descriptor pointer and the block
/// size.
///
/// # Safety
///
/// * The caller must guarantee that a valid page table is already set in TTBR0/TTBR1.
/// * The caller must guarantee that the page table memory is not being borrowed else where.
pub unsafe fn walk_page_table(
    va_start: usize,
    va_size: usize,
    mut f: impl FnMut(&mut u64, core::ops::Range<usize>),
) -> Result<(), &'static str> {
    // Mask to extract the physical base address (bits [47:12]) from an ARM64 translation table
    // descriptor.
    const AARCH64_DESCRIPTOR_ADDR_MASK: u64 = 0x0000_FFFF_FFFF_F000;

    let mut ttbr0: u64 = 0;
    // SAFETY: Reading from TTBR0 is always safe, and we are not accessing any other memory.
    unsafe {
        match current_el() {
            ExceptionLevel::EL1 => asm!("mrs {}, ttbr0_el1", out(reg) ttbr0),
            ExceptionLevel::EL2 => asm!("mrs {}, ttbr0_el2", out(reg) ttbr0),
            _ => return Err("Unsupported Exception Level"),
        }
    }

    let end_va = va_start + va_size;
    let mut va = va_start;
    while va < end_va {
        // Reset table_ptr to the root Level 0 page table at the start of each virtual address
        // iteration.
        let mut table_ptr = (ttbr0 & AARCH64_DESCRIPTOR_ADDR_MASK) as *mut u64;

        // The array [39, 30, 21, 12] contains the bit shift amounts for each page table
        // translation level (L0 to L3) in a standard 4KB granule, 48-bit AArch64 virtual
        // address space. We shift the virtual address right by these amounts and mask with
        // `0x1ff` (since each table has 512 entries, which requires 9 bits) to obtain the
        // index of the descriptor at that level.
        // - L0 (shift 39): Indexes 512GB regions
        // - L1 (shift 30): Indexes 1GB regions
        // - L2 (shift 21): Indexes 2MB regions
        // - L3 (shift 12): Indexes 4KB regions
        let shift_amounts: [usize; 4] = [39, 30, 21, 12];
        for (level, shift_amount) in shift_amounts.iter().enumerate() {
            let idx = (va >> shift_amount) & 0x1ff;
            // SAFETY: By safety requirement of this function, the aarch64 page table is valid
            // and not being borrowed elsewhere.
            let desc = unsafe { table_ptr.add(idx).as_mut().unwrap() };
            // Bit 0 of a descriptor determines whether the entry is valid/present (1) or invalid
            // (0).
            if (*desc & 1) == 0 {
                return Err("Page table entry invalid");
            }

            // In Levels 0, 1, 2, if bit 1 is 0, this is a block mapping (leaf).
            // At Level 3, it is always a page mapping (leaf), which has bit 1 set to 1.
            if level == 3 || (*desc & 2) == 0 {
                // Level 0 block descriptors are invalid/reserved in ARM64.
                if level == 0 {
                    return Err("Invalid page table. L0 must be a table descriptor.");
                }

                let block_size = 1 << shift_amount;

                // Check that the virtual address is aligned to the region boundary.
                if (va & (block_size - 1)) != 0 {
                    return Err("Target memory address is not aligned on mmap boundary");
                } else if va + block_size > end_va {
                    return Err("Target memory region extends beyond user-provided range");
                }
                f(desc, va..va + block_size);
                va += block_size;
                break;
            } else {
                // Extract next level table physical base address.
                table_ptr = (*desc & AARCH64_DESCRIPTOR_ADDR_MASK) as *mut u64;
                continue;
            }
        }
    }
    Ok(())
}

/// Marks a virtual memory range as BTI-guarded.
///
/// This function iterates through all translation descriptors mapping the target range.
/// For each descriptor that represents an executable page (i.e., PXN and UXN/XN are 0),
/// it sets the Guarded Page (GP) attribute (bit 50). Non-executable pages are left unmodified.
///
/// # Safety
///
/// * The caller must guarantee that a valid page table is set in TTBR0/TTBR1.
/// * The caller must guarantee that the page table memory is not being borrowed else where.
pub unsafe fn mark_memory_guarded(va_start: usize, va_size: usize) -> Result<(), &'static str> {
    // SAFETY: By safety requirement of the function, a valid page table is already set and not
    // being borrowed elsewhere.
    unsafe {
        // Pass 1: Verifies that the target address aligned on mmap boundaries.
        walk_page_table(va_start, va_size, |_, _| {})?;
        // Pass 2: Sets the GP bit only on executable descriptors.
        walk_page_table(va_start, va_size, |desc, _| {
            // A page is executable if both PXN (bit 53) and UXN/XN (bit 54) are 0.
            if (*desc & (1u64 << 53)) == 0 && (*desc & (1u64 << 54)) == 0 {
                *desc |= 1u64 << 50; // Set Guarded Page (GP) bit
            }
        })?;
    }

    // Invalidate Translation Lookaside Buffer so that the new page table is used immediately.
    //
    // SAFETY:
    // - By safety requirement of this function, the system starts with a valid page table.
    // - The only change to page table is setting the GP bit. Translation mapping is unchanged.
    //   The page table continues to be safe for current program state.
    unsafe {
        match current_el() {
            ExceptionLevel::EL1 => asm!("dsb sy", "tlbi vmalle1is", "dsb sy", "isb"),
            ExceptionLevel::EL2 => asm!("dsb sy", "tlbi alle2is", "dsb sy", "isb"),
            _ => unreachable!(),
        }
    }
    Ok(())
}

/// Enables Pointer Authentication (PAC) in hardware using Key A (`SCTLR_ELx.EnIA`).
///
///
/// Notes: must be inlined into a function that never returns (`efi_main`), because enabling
/// `EnIA` mid-function would cause a non-inlined function's epilogue `autiasp` to authenticate
/// an unsigned `x30` saved before `EnIA` was enabled.
#[inline(always)]
pub fn enable_pac() {
    const SCTLR_ENIA: u64 = 1 << 31;
    // SAFETY:
    // - The assembly only accesses architectural system registers (`APIAKeyLo_EL1`,
    //   `APIAKeyHi_EL1`, and `SCTLR_EL1`/`SCTLR_EL2` after checking `current_el()`); none of the
    //   constants used here are interpreted as raw pointers or used to access memory.
    // - Temporary register modifications are declared via `out(reg) _`, leaving stack and memory
    //   state untouched.
    // - Programming `APIAKey_EL1` and setting `SCTLR_ELx.EnIA` only enables hardware instruction
    //   pointer authentication, which does not alter memory mappings or violate Rust's memory
    //   safety guarantees.
    unsafe {
        // `.arch_extension pauth` is required for the baseline `armv8-a` target to recognize
        // FEAT_PAuth system register names.
        asm!(
            ".arch_extension pauth",
            "msr apiakeylo_el1, {key_lo}",
            "msr apiakeyhi_el1, {key_hi}",
            key_lo = in(reg) 0x0123_4567_89ab_cdefu64,
            key_hi = in(reg) 0xfedc_ba98_7654_3210u64,
        );
        match current_el() {
            ExceptionLevel::EL1 => asm!(
                "mrs {tmp}, sctlr_el1",
                "orr {tmp}, {tmp}, {enia}",
                "msr sctlr_el1, {tmp}",
                "isb",
                tmp = out(reg) _,
                enia = in(reg) SCTLR_ENIA,
            ),
            ExceptionLevel::EL2 => asm!(
                "mrs {tmp}, sctlr_el2",
                "orr {tmp}, {tmp}, {enia}",
                "msr sctlr_el2, {tmp}",
                "isb",
                tmp = out(reg) _,
                enia = in(reg) SCTLR_ENIA,
            ),
            _ => unreachable!(),
        }
    }
}
