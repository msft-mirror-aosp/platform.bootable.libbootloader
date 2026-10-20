// Copyright (C) 2024 The Android Open Source Project
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

//! Low-level utilities shared across multiple GBL libraries.

#![cfg_attr(not(test), no_std)]

#[cfg(target_arch = "aarch64")]
use core::arch::asm;
use liberror::{Error, Result};
use safemath::SafeNum;

/// A generic, shared buffer pool.
pub mod buffer_pool;

/// Shared object guarded by a RefCell
pub mod shared;

/// RAII guard for zeroizing memory on drop.
pub mod zeroize_guard;
pub use zeroize_guard::ZeroizeGuard;

#[cfg(target_arch = "aarch64")]
pub mod aarch64;

/// Returns the largest aligned subslice.
///
/// This function drops as many bytes as needed from the front of the given slice to ensure the
/// result is properly-aligned. It does not truncate bytes from the end, so the resulting size may
/// not be a multiple of `alignment`.
///
/// If the next `alignment` boundary would be directly following the last byte, this returns the
/// 0-length slice at that alignment rather than an error, to match standard slicing behavior.
///
/// # Arguments
/// * `bytes`: the byte slice to align
/// * `alignment`: the desired starting alignment
///
/// # Returns
/// * The subslice on success
/// * [Error::ArithmeticOverflow] if `bytes` overflows when finding the next `alignment`
/// * [Error::BufferTooSmall] if `bytes` is not large enough to reach the next `alignment`. The
///   error will contain the size that would have been needed to reach `alignment`.
pub fn aligned_subslice<T>(bytes: &mut [u8], alignment: T) -> Result<&mut [u8]>
where
    T: Copy + Into<SafeNum>,
{
    let addr = bytes.as_ptr() as usize;
    let aligned_offset = (SafeNum::from(addr).round_up(alignment) - addr).try_into()?;
    Ok(bytes.get_mut(aligned_offset..).ok_or(Error::BufferTooSmall(Some(aligned_offset)))?)
}

/// A helper for getting the offset of the first byte with and aligned address.
///
/// # Arguments
/// * `bytes`: the byte slice
/// * `alignment`: the desired starting alignment.
///
/// # Returns
///
/// * Returns Ok(offset) on success, Err() on integer overflow.
pub fn aligned_offset<T>(buffer: &[u8], alignment: T) -> Result<usize>
where
    T: Copy + Into<SafeNum>,
{
    let addr = SafeNum::from(buffer.as_ptr() as usize);
    (addr.round_up(alignment) - addr).try_into().map_err(From::from)
}

/// Get timestamp from architecture specific timer.
#[cfg(target_arch = "aarch64")]
pub fn arch_timestamp() -> Result<core::time::Duration> {
    let (cnt, freq): (u64, u64);
    // SAFETY: Generic timer is always available on AArch64 and safe to read.
    unsafe {
        asm!(
            "isb",
            "mrs {cnt}, cntpct_el0",
            "mrs {freq}, cntfrq_el0",
            cnt = out(reg) cnt,
            freq = out(reg) freq,
        );
    }
    let (cnt, freq): (u128, u128) = (cnt as _, freq as _);
    let nanos = cnt * 1000 * 1000 * 1000 / freq;
    Ok(core::time::Duration::from_nanos(nanos as u64))
}

/// Get timestamp from architecture specific timer.
#[cfg(all(target_arch = "x86_64", not(test), not(target_os = "linux")))]
pub fn arch_timestamp() -> Result<core::time::Duration> {
    const NANOS_PER_SEC: u128 = 1_000_000_000;
    let freq_hz = tsc_freq_hz()? as u128;
    // SAFETY: `rdtsc` is guaranteed to be supported by the baseline `x86_64` ISA, is permitted in
    // ring 0 (UEFI/kernel execution), and only reads the timestamp counter without modifying
    // memory or CPU state.
    let tsc = unsafe { core::arch::x86_64::_rdtsc() } as u128;
    Ok(core::time::Duration::from_nanos((tsc * NANOS_PER_SEC / freq_hz) as u64))
}

/// Queries the TSC frequency in Hz from CPUID leaf `0x15` or calibrates it against PIT Channel 2.
#[cfg(all(target_arch = "x86_64", not(test), not(target_os = "linux")))]
fn tsc_freq_hz() -> Result<u64> {
    use core::{
        arch::x86_64::{__cpuid, _rdtsc},
        hint::spin_loop,
        sync::atomic::{AtomicU64, Ordering},
    };
    use x86_64::instructions::port::{PortRead, PortWrite};

    const CPUID_TSC_FREQ_LEAF: u32 = 0x15;
    const PIT_FREQ_HZ: u64 = 1_193_182;
    const PIT_CALIBRATION_TICKS: u16 = 5_966; // ~5 ms
    const PIT_PORT_CH2_DATA: u16 = 0x42;
    const PIT_PORT_CMD: u16 = 0x43;
    const PIT_PORT_CTRL: u16 = 0x61;
    const PIT_CTRL_GATE2: u8 = 0x01;
    const PIT_CTRL_SPKR: u8 = 0x02;
    const PIT_CTRL_OUT2: u8 = 0x20;
    const PIT_CMD_CH2_MODE0: u8 = 0xb0;
    const PIT_MAX_POLL_ITERS: u32 = 1_000_000;

    static TSC_FREQ_HZ: AtomicU64 = AtomicU64::new(0);
    let cached = TSC_FREQ_HZ.load(Ordering::Relaxed);
    if cached != 0 {
        return Ok(cached);
    }

    // SAFETY: `cpuid`, `rdtsc`, and port I/O to the architectural PIT ports (`0x42`, `0x43`,
    // `0x61`) are permitted in ring 0 (UEFI/kernel execution) and do not affect memory safety.
    let freq_hz = unsafe {
        let tsc_leaf = (__cpuid(0).eax >= CPUID_TSC_FREQ_LEAF)
            .then(|| __cpuid(CPUID_TSC_FREQ_LEAF))
            .filter(|l| l.eax != 0 && l.ebx != 0 && l.ecx != 0);
        if let Some(leaf) = tsc_leaf {
            (leaf.ecx as u64) * (leaf.ebx as u64) / (leaf.eax as u64)
        } else {
            let ctrl = u8::read_from_port(PIT_PORT_CTRL);
            u8::write_to_port(PIT_PORT_CTRL, (ctrl & !PIT_CTRL_SPKR) | PIT_CTRL_GATE2);
            u8::write_to_port(PIT_PORT_CMD, PIT_CMD_CH2_MODE0);
            u8::write_to_port(PIT_PORT_CH2_DATA, (PIT_CALIBRATION_TICKS & 0xff) as u8);
            u8::write_to_port(PIT_PORT_CH2_DATA, (PIT_CALIBRATION_TICKS >> 8) as u8);

            if (u8::read_from_port(PIT_PORT_CTRL) & PIT_CTRL_OUT2) != 0 {
                return Err(Error::Unsupported);
            }
            let start = _rdtsc();
            let mut expired = false;
            for _ in 0..PIT_MAX_POLL_ITERS {
                if (u8::read_from_port(PIT_PORT_CTRL) & PIT_CTRL_OUT2) != 0 {
                    expired = true;
                    break;
                }
                spin_loop();
            }
            let end = _rdtsc();
            if !expired || end <= start {
                return Err(Error::Unsupported);
            }
            (end - start) * PIT_FREQ_HZ / (PIT_CALIBRATION_TICKS as u64)
        }
    };
    if freq_hz == 0 {
        return Err(Error::Unsupported);
    }
    TSC_FREQ_HZ.store(freq_hz, Ordering::Relaxed);
    Ok(freq_hz)
}

/// Get timestamp from architecture specific timer.
#[cfg(not(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", not(test), not(target_os = "linux"))
)))]
pub fn arch_timestamp() -> Result<core::time::Duration> {
    // Implement for other architectures if needed. For riscv64, we can use `rdtime`.
    Err(Error::Unsupported)
}

#[cfg(test)]
mod test {
    use super::*;
    use libtestutils::AlignedBuffer;

    #[test]
    fn aligned_subslice_already_aligned() {
        let mut bytes = AlignedBuffer::new(16, 8);

        // bytes is `align(8)`, so must be 1/2/4/8-aligned.
        assert_eq!(aligned_subslice(&mut bytes, 1).unwrap().as_ptr_range(), bytes.as_ptr_range());
        assert_eq!(aligned_subslice(&mut bytes, 2).unwrap().as_ptr_range(), bytes.as_ptr_range());
        assert_eq!(aligned_subslice(&mut bytes, 4).unwrap().as_ptr_range(), bytes.as_ptr_range());
        assert_eq!(aligned_subslice(&mut bytes, 8).unwrap().as_ptr_range(), bytes.as_ptr_range());
    }

    #[test]
    fn aligned_subslice_unaligned() {
        let mut bytes = AlignedBuffer::new(16, 8);

        // bytes is 8-aligned, so offsetting by <8 should snap to the next 8-alignment.
        assert_eq!(
            aligned_subslice(&mut bytes[1..], 8).unwrap().as_ptr_range(),
            bytes[8..].as_ptr_range()
        );
        assert_eq!(
            aligned_subslice(&mut bytes[4..], 8).unwrap().as_ptr_range(),
            bytes[8..].as_ptr_range()
        );
        assert_eq!(
            aligned_subslice(&mut bytes[7..], 8).unwrap().as_ptr_range(),
            bytes[8..].as_ptr_range()
        );
    }

    #[test]
    fn aligned_subslice_empty_slice() {
        let mut bytes = AlignedBuffer::new(16, 8);

        // If the next alignment is just past the input, return the empty slice.
        assert_eq!(
            aligned_subslice(&mut bytes[9..], 8).unwrap().as_ptr_range(),
            bytes[16..].as_ptr_range()
        );
    }

    #[test]
    fn aligned_subslice_buffer_overflow() {
        let mut bytes = AlignedBuffer::new(7, 8); // 7 bytes; can't reach the next 8-alignment.

        assert_eq!(aligned_subslice(&mut bytes[1..], 8), Err(Error::BufferTooSmall(Some(7))));
        assert_eq!(aligned_subslice(&mut bytes[6..], 8), Err(Error::BufferTooSmall(Some(2))));
    }

    #[test]
    fn aligned_subslice_alignment_overflow() {
        let mut bytes = AlignedBuffer::new(16, 8);

        assert!(matches!(
            aligned_subslice(&mut bytes, SafeNum::MAX),
            Err(Error::ArithmeticOverflow(_))
        ));
    }
}
