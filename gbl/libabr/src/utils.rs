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

use abr::{AbrData, ONE_SHOT_BOOTLOADER, ONE_SHOT_RECOVERY};

/// Converts big endian order to host order.
#[no_mangle]
#[allow(non_snake_case)]
pub extern "C" fn AbrBigEndianToHost(val: u32) -> u32 {
    u32::from_be(val)
}

/// Converts host order to big endian.
#[no_mangle]
#[allow(non_snake_case)]
pub extern "C" fn AbrHostToBigEndian(val: u32) -> u32 {
    val.to_be()
}

/// Checks if one-shot recovery boot is set in the given one-shot flags
#[no_mangle]
#[allow(non_snake_case)]
pub extern "C" fn AbrIsOneShotRecoveryBootSet(flags: u8) -> bool {
    // Temporary workaround for an upstream `rustc` regression on `x86_64` where `extern "C"`
    // functions returning `bool` (`i1`) omit the LLVM `zeroext` attribute. Because
    // `ONE_SHOT_RECOVERY` is bit 0 (`1`), LLVM optimizes `(flags & 1) != 0` into
    // `trunc i8 %flags to i1`, which lowers to a no-op register move (`movl %edi, %eax`) and
    // leaves the upper bits of `%al` unmasked for C/C++ callers. Wrapping the masked value in
    // `black_box` forces an explicit mask and comparison.
    //
    // Remove `black_box` once the upstream fix (https://github.com/rust-lang/rust/pull/163917)
    // rolls into the toolchain.
    core::hint::black_box(flags & ONE_SHOT_RECOVERY) != 0
}

/// Checks if one-shot recovery boot is set in the given AbrData
///
/// # Safety
///
/// Caller must make sure to pass a valid, aligned pointer for `abr_data`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrIsOneShotRecoveryBoot(abr_data: *const AbrData) -> bool {
    // SAFETY: Caller guarantees `abr_data` is valid and aligned.
    // We check for non-nullness and return `false` as a safe default otherwise.
    unsafe { abr_data.as_ref() }
        .map(|d| AbrIsOneShotRecoveryBootSet(d.one_shot_flags))
        .unwrap_or(false)
}

/// Checks if one-shot bootloader boot is set in the given one-shot flags
#[no_mangle]
#[allow(non_snake_case)]
pub extern "C" fn AbrIsOneShotBootloaderBootSet(flags: u8) -> bool {
    (flags & ONE_SHOT_BOOTLOADER) != 0
}

/// Checks if one-shot bootloader boot is set in the given AbrData
///
/// # Safety
///
/// Caller must make sure to pass a valid, aligned pointer for `abr_data`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrIsOneShotBootloaderBoot(abr_data: *const AbrData) -> bool {
    // SAFETY: Caller guarantees `abr_data` is valid and aligned.
    // We check for non-nullness and return `false` as a safe default otherwise.
    unsafe { abr_data.as_ref() }
        .map(|d| AbrIsOneShotBootloaderBootSet(d.one_shot_flags))
        .unwrap_or(false)
}

/// Sets the one-shot recovery flag in the given AbrData.
///
/// # Safety
///
/// Caller must make sure to pass a valid, aligned pointer for `abr_data`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrSetOneShotRecoveryBoot(abr_data: *mut AbrData, enable: bool) {
    // SAFETY: Caller guarantees `abr_data` is valid and aligned.
    // We check for non-nullness and do nothing if NULL.
    if let Some(abr_data) = unsafe { abr_data.as_mut() } {
        abr_data.set_one_shot_recovery(enable);
    }
}

/// Sets the one-shot bootloader flag in the given AbrData.
///
/// # Safety
///
/// Caller must make sure to pass a valid, aligned pointer for `abr_data`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrSetOneShotBootloaderBoot(abr_data: *mut AbrData, enable: bool) {
    // SAFETY: Caller guarantees `abr_data` is valid and aligned.
    // We check for non-nullness and do nothing if NULL.
    if let Some(abr_data) = unsafe { abr_data.as_mut() } {
        abr_data.set_one_shot_bootloader(enable);
    }
}
