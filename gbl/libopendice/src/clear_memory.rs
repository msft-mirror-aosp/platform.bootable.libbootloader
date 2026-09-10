// Copyright 2025, The Android Open Source Project
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

//! Routine for clearing memory containing confidential data, used by the open-dice library.

use core::ffi::c_void;
use zeroize::Zeroize;

#[cfg(target_arch = "aarch64")]
mod aarch64 {
    use core::arch::asm;

    extern "C" {
        /// Clean and invalidate data cache by address range. The function is from ATF library.
        fn flush_dcache_range(addr: usize, len: usize);
    }

    // TODO: Deduplicate `flush_dcache_buffer` across libboot, libopendice, and libutils.
    /// Flush all data cache for the given buffer.
    #[inline]
    pub fn flush_dcache_buffer(buf: &[u8]) {
        // SAFETY: Safe because the cache is invalidated for a valid, read/write memory range
        // from a single allocation, with no concurrent access and no MMIO/device memory involved.
        // This preserves memory safety guarantees and does not affect Rust.
        unsafe { flush_dcache_range(buf.as_ptr() as usize, buf.len()) }
        // SAFETY: Assembly code for instruction synchronization, does not affect Rust.
        unsafe { asm!("isb") };
    }
}

/// Zeroes data over the provided address range & flushes data caches.
///
/// # Safety
///
/// The provided address and size must be for an address range that is valid for read and write
/// from a single allocation (e.g. stack array).
#[no_mangle]
unsafe extern "C" fn DiceClearMemory(_ctx: *mut c_void, size: usize, addr: *mut c_void) {
    // SAFETY: As per function requirements, `addr` is non-null and valid for writes of `size`
    // bytes, it's properly aligned for `u8`, and the memory remains valid for the entire lifetime
    // of `addr`.
    let s = unsafe { core::slice::from_raw_parts_mut(addr as *mut u8, size) };
    s.zeroize();

    #[cfg(target_arch = "aarch64")]
    aarch64::flush_dcache_buffer(s);
}
