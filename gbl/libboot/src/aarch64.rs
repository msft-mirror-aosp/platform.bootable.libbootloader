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

/// Boots a Linux kernel in mode EL2 or lower with the given FDT blob.
///
/// # Safety
///
/// Caller must ensure that `kernel` contains a valid Linux kernel.
pub unsafe fn jump_linux_el2_or_lower(kernel: &[u8], fdt: &[u8]) -> ! {
    assert_ne!(current_el(), ExceptionLevel::EL3);
    // TODO(b/305093905): Perform other initialization including disabling MMU, flushing cache and
    // masking interrupt.

    asm!(
        "mov x1, 0",
        "mov x2, 0",
        "mov x3, 0",
        "br x4",
        in("x4") kernel.as_ptr() as usize,
        in("x0") fdt.as_ptr() as usize,
    );

    unreachable!();
}
