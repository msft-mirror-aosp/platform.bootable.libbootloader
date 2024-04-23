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

//! This file provides C interface wrappers of libabr APIs.

#![cfg_attr(not(test), no_std)]

use abr::{
    get_and_clear_one_shot_flag, get_boot_slot, get_slot_info, get_slot_last_marked_active,
    mark_slot_active, mark_slot_successful, mark_slot_unbootable, set_one_shot_bootloader,
    set_one_shot_recovery, AbrResult, Error, Ops, SlotIndex, SlotInfo as AbrSlotInfo, SlotState,
};
use core::{
    ffi::{c_char, c_uint, c_void},
    fmt::Write,
};

pub mod utils;

pub const ABR_RESULT_OK: c_uint = 0;
pub const ABR_RESULT_ERR_IO: c_uint = 1;
pub const ABR_RESULT_ERR_INVALID_DATA: c_uint = 2;
pub const ABR_RESULT_ERR_UNSUPPORTED_VERSION: c_uint = 3;

// ABR system dependencies.
//
// These correspond to the definitions in Fuchsia upstream header
// "src/firmware/lib/abr/include/lib/abr/sysdeps.h", which will eventually migrate over.
extern "C" {
    /// Prints out a NULL-terminated string.
    pub fn AbrPrint(message: *const c_char);

    /// Aborts the program or reboots the device if |abort| is not implemented.
    pub fn AbrAbort();
}

/// A helper to print an ASCII character via `AbrPrint()`.
fn abr_print_ascii_char(ch: u8) {
    let s = [ch, 0];
    // SAFETY:
    // * `s` is a valid buffer
    // * `s` is for input only and will not be retained by the function.
    unsafe { AbrPrint(s.as_ptr() as _) }
}

/// A helper structure that implements formatted write using `AbrPrint()`.
struct AbrPrintSysdeps {}

impl Write for AbrPrintSysdeps {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        if s.is_ascii() {
            s.as_bytes().iter().for_each(|v| abr_print_ascii_char(*v));
        }
        Ok(())
    }
}

/// A panic handler is needed when building as a static library. We simply call into
/// the AbrAbort() system dependency.
#[cfg(not(test))]
#[panic_handler]
fn panic(panic: &core::panic::PanicInfo<'_>) -> ! {
    write!(AbrPrintSysdeps {}, "libabr panics! {}", panic).unwrap();
    // SAFETY: Call to external C function. The function simply aborts/reboots the system.
    unsafe { AbrAbort() };
    unreachable!()
}

/// This corresponds to the `AbrOps` C definition in Fuchsia upstream header
/// "src/firmware/lib/abr/include/lib/abr/ops.h", which will eventually migrate over.
///
/// typedef struct AbrOps {
///     void* context;
///     bool (*read_abr_metadata)(void* context, size_t size, uint8_t* buffer);
///     bool (*write_abr_metadata)(void* context, const uint8_t* buffer, size_t size);
/// } AbrOps;
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct AbrOps {
    pub context: *mut c_void,
    pub read_abr_metadata:
        Option<unsafe extern "C" fn(context: *mut c_void, size: usize, buffer: *mut u8) -> bool>,
    pub write_abr_metadata:
        Option<unsafe extern "C" fn(context: *mut c_void, buffer: *const u8, size: usize) -> bool>,
}

/// `AbrOpsSafe` wraps a reference to `AbrOps` and is created by an unsafe constructor that
/// establishes necessary safety invariants on `AbrOps`.
struct AbrOpsSafe<'a> {
    ops: &'a AbrOps,
    log: AbrPrintSysdeps,
}

impl<'a> AbrOpsSafe<'a> {
    /// Creates a new instance from a reference to `AbrOps`.
    ///
    /// # Safety
    ///
    /// * Caller must make sure that `ops.context` is either not used, or points to a valid and
    ///   correct type of value needed by `ops.read_abr_metadata` and `ops.write_abr_metadata`.
    unsafe fn new(ops: &'a AbrOps) -> Self {
        Self { ops, log: AbrPrintSysdeps {} }
    }
}

type AbrSlotIndex = c_uint;

impl Ops for AbrOpsSafe<'_> {
    fn read_abr_metadata(&mut self, out: &mut [u8]) -> Result<(), Option<&'static str>> {
        let read_abr_metadata =
            self.ops.read_abr_metadata.ok_or(Some("Missing read_abr_metadata() method"))?;
        // SAFETY:
        // * By safety requirement of `AbrOpsSafe::new()`, `self.ops.context` is either unused, or
        //   a valid pointer to a correct type of object used by `self.ops.read_abr_metadata`.
        // * `out` is a valid buffer
        // * `out` is for reading data only and will not be retained by the function.
        match unsafe { read_abr_metadata(self.ops.context, out.len(), out.as_mut_ptr() as _) } {
            false => Err(Some("read_abr_metadata() failed")),
            _ => Ok(()),
        }
    }

    fn write_abr_metadata(&mut self, data: &mut [u8]) -> Result<(), Option<&'static str>> {
        let write_abr_metadata =
            self.ops.write_abr_metadata.ok_or(Some("Missing write_abr_metadata() method"))?;
        // SAFETY:
        // * By safety requirement of `AbrOpsSafe::new()`, `self.ops.context` is either unused, or
        //   a valid pointer to a correct type of object used by `self.ops.write_abr_metadata`.
        // * `data` is a valid buffer.
        // * `data` is for input only and will not be retained by the function.
        match unsafe { write_abr_metadata(self.ops.context, data.as_ptr() as _, data.len()) } {
            false => Err(Some("write_abr_metadata() failed")),
            _ => Ok(()),
        }
    }

    fn console(&mut self) -> Option<&mut dyn core::fmt::Write> {
        Some(&mut self.log)
    }
}

/// A helper that extracts the return value and maps the result to an integer A/B/R result code.
fn unpack_result<T: Into<O>, O>(res: AbrResult<T>, val: &mut O) -> c_uint {
    match res {
        Err(e) => match e {
            Error::BadMagic | Error::BadChecksum | Error::InvalidData => {
                ABR_RESULT_ERR_INVALID_DATA
            }
            Error::UnsupportedVersion => ABR_RESULT_ERR_UNSUPPORTED_VERSION,
            Error::OpsError(_) => ABR_RESULT_ERR_IO,
        },
        Ok(v) => {
            *val = v.into();
            ABR_RESULT_OK
        }
    }
}

/// C interface wrapper of `abr::get_boot_slot()`
///
/// # Safety
///
/// * Caller must make sure to pass a valid pointer for `abr_ops`.
/// * Caller must make sure that `ops.context` is either not used, or points to a valid and correct
///   type of value needed by `ops.read_abr_metadata` and `ops.write_abr_metadata`.
/// * Caller must make sure to pass either a NULL or valid pointer for `is_slot_marked_successful`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrGetBootSlot(
    abr_ops: *const AbrOps,
    update_metadata: bool,
    is_slot_marked_successful: *mut bool,
) -> AbrSlotIndex {
    let mut abr_ops = AbrOpsSafe::new(abr_ops.as_ref().unwrap());
    let (slot_index, successful) = get_boot_slot(&mut abr_ops, update_metadata);
    match is_slot_marked_successful.as_mut() {
        Some(v) => *v = successful,
        _ => {}
    };
    slot_index.into()
}

// NULL terminated strings for slot suffixes.
const SLOT_A_SUFFIX: &[u8] = b"_a\0";
const SLOT_B_SUFFIX: &[u8] = b"_b\0";
const SLOT_R_SUFFIX: &[u8] = b"_r\0";
const SLOT_SUFFIX_INVALID: &[u8] = b"\0";

/// C interface for getting slot suffix.
#[no_mangle]
#[allow(non_snake_case)]
pub extern "C" fn AbrGetSlotSuffix(slot_index: AbrSlotIndex) -> *const c_char {
    match slot_index.try_into() {
        Ok(SlotIndex::A) => &SLOT_A_SUFFIX,
        Ok(SlotIndex::B) => &SLOT_B_SUFFIX,
        Ok(SlotIndex::R) => &SLOT_R_SUFFIX,
        Err(_) => &SLOT_SUFFIX_INVALID,
    }
    .as_ptr() as _
}

/// C interface wrapper of `abr::mark_slot_active()`
///
/// # Safety
///
/// * Caller must make sure to pass a valid pointer for `abr_ops`.
/// * Caller must make sure that `ops.context` is either not used, or points to a valid and correct
///   type of value needed by `ops.read_abr_metadata` and `ops.write_abr_metadata`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrMarkSlotActive(
    abr_ops: *const AbrOps,
    slot_index: AbrSlotIndex,
) -> c_uint {
    let slot_index = match slot_index.try_into() {
        Ok(v) => v,
        Err(_) => return ABR_RESULT_ERR_INVALID_DATA,
    };
    unpack_result(
        mark_slot_active(&mut AbrOpsSafe::new(abr_ops.as_ref().unwrap()), slot_index),
        &mut (),
    )
}

/// C interface wrapper of `abr::get_slot_last_marked_active()`
///
/// # Safety
///
/// * Caller must make sure to pass a valid pointer for `abr_ops` and `out_slot`.
/// * Caller must make sure that `ops.context` is either not used, or points to a valid and correct
///   type of value needed by `ops.read_abr_metadata` and `ops.write_abr_metadata`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrGetSlotLastMarkedActive(
    abr_ops: *const AbrOps,
    out_slot: *mut AbrSlotIndex,
) -> c_uint {
    unpack_result(
        get_slot_last_marked_active(&mut AbrOpsSafe::new(abr_ops.as_ref().unwrap())),
        out_slot.as_mut().unwrap(),
    )
}

/// C interface wrapper of `abr::mark_slot_unbootable()`
///
/// # Safety
///
/// * Caller must make sure to pass a valid pointer for `abr_ops`.
/// * Caller must make sure that `ops.context` is either not used, or points to a valid and correct
///   type of value needed by `ops.read_abr_metadata` and `ops.write_abr_metadata`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrMarkSlotUnbootable(
    abr_ops: *const AbrOps,
    slot_index: AbrSlotIndex,
) -> c_uint {
    let slot_index = match slot_index.try_into() {
        Ok(v) => v,
        Err(_) => return ABR_RESULT_ERR_INVALID_DATA,
    };
    unpack_result(
        mark_slot_unbootable(&mut AbrOpsSafe::new(abr_ops.as_ref().unwrap()), slot_index),
        &mut (),
    )
}

/// C interface wrapper of `abr::mark_slot_successful()`
///
/// # Safety
///
/// * Caller must make sure to pass a valid pointer for `abr_ops`.
/// * Caller must make sure that `ops.context` is either not used, or points to a valid and correct
///   type of value needed by `ops.read_abr_metadata` and `ops.write_abr_metadata`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrMarkSlotSuccessful(
    abr_ops: *const AbrOps,
    slot_index: AbrSlotIndex,
) -> c_uint {
    let slot_index = match slot_index.try_into() {
        Ok(v) => v,
        Err(_) => return ABR_RESULT_ERR_INVALID_DATA,
    };
    unpack_result(
        mark_slot_successful(&mut AbrOpsSafe::new(abr_ops.as_ref().unwrap()), slot_index),
        &mut (),
    )
}

/// `SlotInfo` contains the current state of a A/B/R slot.
///
/// TODO(b/338243123): Detailed documentation is available in Fuchsia upstream header
/// "src/firmware/lib/abr/include/lib/abr/abr.h", which will migrate to the GBL repo.
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct SlotInfo {
    /// Whether the slot is expected to be bootable.
    pub is_bootable: bool,
    /// Whether the slot is the highest priority A/B slot.
    pub is_active: bool,
    /// Whether the slot is currently marked successful.
    pub is_marked_successful: bool,
    /// If not marked successful, this represents the number of attempts left for booting this slot.
    pub num_tries_remaining: u8,
}

impl From<AbrSlotInfo> for SlotInfo {
    fn from(val: abr::SlotInfo) -> Self {
        let is_marked_successful = matches!(val.state, SlotState::Successful);
        let num_tries_remaining = match val.state {
            SlotState::Bootable(v) => v,
            _ => 0,
        };
        Self {
            is_bootable: is_marked_successful || num_tries_remaining > 0,
            is_active: val.is_active,
            is_marked_successful,
            num_tries_remaining,
        }
    }
}

/// C interface wrapper of `abr::get_slot_info()`
///
/// # Safety
///
/// * Caller must make sure to pass a valid pointer for `abr_ops` and 'info'.
/// * Caller must make sure that `ops.context` is either not used, or points to a valid and correct
///   type of value needed by `ops.read_abr_metadata` and `ops.write_abr_metadata`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrGetSlotInfo(
    abr_ops: *const AbrOps,
    slot_index: AbrSlotIndex,
    info: *mut SlotInfo,
) -> c_uint {
    let slot_index = match slot_index.try_into() {
        Ok(v) => v,
        Err(_) => return ABR_RESULT_ERR_INVALID_DATA,
    };
    unpack_result(
        get_slot_info(&mut AbrOpsSafe::new(abr_ops.as_ref().unwrap()), slot_index)
            .map(|v| SlotInfo::from(v)),
        info.as_mut().unwrap(),
    )
}

/// C interface wrapper of `abr::set_one_shot_recovery()`
///
/// # Safety
///
/// * Caller must make sure to pass a valid pointer for `abr_ops`.
/// * Caller must make sure that `ops.context` is either not used, or points to a valid and correct
///   type of value needed by `ops.read_abr_metadata` and `ops.write_abr_metadata`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrSetOneShotRecovery(abr_ops: *const AbrOps, enable: bool) -> c_uint {
    unpack_result(
        set_one_shot_recovery(&mut AbrOpsSafe::new(abr_ops.as_ref().unwrap()), enable),
        &mut (),
    )
}

/// C interface wrapper of `abr::set_one_shot_bootloader()`
///
/// # Safety
///
/// * Caller must make sure to pass a valid pointer for `abr_ops`.
/// * Caller must make sure that `ops.context` is either not used, or points to a valid and correct
///   type of value needed by `ops.read_abr_metadata` and `ops.write_abr_metadata`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrSetOneShotBootloader(abr_ops: *const AbrOps, enable: bool) -> c_uint {
    unpack_result(
        set_one_shot_bootloader(&mut AbrOpsSafe::new(abr_ops.as_ref().unwrap()), enable),
        &mut (),
    )
}

/// Gets and clears the one shot flag.
///
/// # Safety
///
/// * Caller must make sure to pass a valid pointer for `abr_ops` and `flags`.
/// * Caller must make sure that `ops.context` is either not used, or points to a valid and correct
///   type of value needed by `ops.read_abr_metadata` and `ops.write_abr_metadata`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrGetAndClearOneShotFlags(
    abr_ops: *const AbrOps,
    flags: *mut c_uint,
) -> c_uint {
    unpack_result(
        get_and_clear_one_shot_flag(&mut AbrOpsSafe::new(abr_ops.as_ref().unwrap())),
        flags.as_mut().unwrap(),
    )
}

// Needed because of no-std environment in static lib build.
#[cfg(not(test))]
#[no_mangle]
pub extern "C" fn rust_eh_personality() {}
