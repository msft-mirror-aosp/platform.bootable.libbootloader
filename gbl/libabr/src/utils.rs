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
    (flags & ONE_SHOT_RECOVERY) != 0
}

/// Checks if one-shot recovery boot is set in the given AbrData
///
/// # Safety
///
/// Caller must make sure to pass a valid pointer for `abr_data`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrIsOneShotRecoveryBoot(abr_data: *const AbrData) -> bool {
    // SAFETY: function safety requires `abr_data` to be a valid pointer.
    AbrIsOneShotRecoveryBootSet(unsafe { abr_data.as_ref() }.unwrap().one_shot_flags)
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
/// Caller must make sure to pass a valid pointer for `abr_data`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrIsOneShotBootloaderBoot(abr_data: *const AbrData) -> bool {
    // SAFETY: function safety requires `abr_data` to be a valid pointer.
    AbrIsOneShotBootloaderBootSet(unsafe { abr_data.as_ref() }.unwrap().one_shot_flags)
}

/// Sets the one-shot recovery flag in the given AbrData.
///
/// # Safety
///
/// Caller must make sure to pass a valid pointer for `abr_data`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrSetOneShotRecoveryBoot(abr_data: *mut AbrData, enable: bool) {
    // SAFETY: function safety requires `abr_data` to be a valid pointer.
    unsafe { abr_data.as_mut() }.unwrap().set_one_shot_recovery(enable);
}

/// Sets the one-shot bootloader flag in the given AbrData.
///
/// # Safety
///
/// Caller must make sure to pass a valid pointer for `abr_data`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrSetOneShotBootloaderBoot(abr_data: *mut AbrData, enable: bool) {
    // SAFETY: function safety requires `abr_data` to be a valid pointer.
    unsafe { abr_data.as_mut() }.unwrap().set_one_shot_bootloader(enable);
}
