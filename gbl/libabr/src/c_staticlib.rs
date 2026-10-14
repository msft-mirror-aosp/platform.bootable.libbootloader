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
    get_active_slot_from_data, get_and_clear_one_shot_flag, get_boot_slot, get_slot_info,
    get_slot_last_marked_active, mark_slot_active, mark_slot_successful, mark_slot_unbootable,
    set_one_shot_bootloader, set_one_shot_recovery, AbrData, AbrSlotData, Error, Ops, Result,
    SlotIndex, SlotInfo as AbrSlotInfo, SlotState, UnbootableReason, ABR_DATA_SIZE,
};
use core::{
    ffi::{c_char, c_uint, c_void},
    fmt::Write,
};

/// Utility C APIs for A/B/R metadata manipulation.
pub mod utils;

/// Operation succeeded.
pub const ABR_RESULT_OK: c_uint = 0;
/// I/O error occurred while reading or writing metadata.
pub const ABR_RESULT_ERR_IO: c_uint = 1;
/// Invalid metadata or argument.
pub const ABR_RESULT_ERR_INVALID_DATA: c_uint = 2;
/// Metadata major version is unsupported.
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
///     bool (*read_abr_metadata_custom)(void* context, AbrSlotData* a_slot_data,
///                                      AbrSlotData* b_slot_data, uint8_t* one_shot_flags);
///     bool (*write_abr_metadata_custom)(void* context, const AbrSlotData* a_slot_data,
///                                       const AbrSlotData* b_slot_data, uint8_t one_shot_flags);
/// } AbrOps;
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct AbrOps {
    /// Custom context pointer passed to callbacks.
    pub context: *mut c_void,
    /// Callback to read raw A/B/R metadata bytes.
    pub read_abr_metadata:
        Option<unsafe extern "C" fn(context: *mut c_void, size: usize, buffer: *mut u8) -> bool>,
    /// Callback to write raw A/B/R metadata bytes.
    pub write_abr_metadata:
        Option<unsafe extern "C" fn(context: *mut c_void, buffer: *const u8, size: usize) -> bool>,
    /// Callback to read custom A/B/R slot data and one-shot flags.
    pub read_abr_metadata_custom: Option<
        unsafe extern "C" fn(
            context: *mut c_void,
            a_slot_data: *mut AbrSlotData,
            b_slot_data: *mut AbrSlotData,
            one_shot_flags: *mut u8,
        ) -> bool,
    >,
    /// Callback to write custom A/B/R slot data and one-shot flags.
    pub write_abr_metadata_custom: Option<
        unsafe extern "C" fn(
            context: *mut c_void,
            a_slot_data: *const AbrSlotData,
            b_slot_data: *const AbrSlotData,
            one_shot_flags: u8,
        ) -> bool,
    >,
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
    ///   correct type of value needed by `ops.read_abr_metadata`, `ops.write_abr_metadata`,
    ///   `ops.read_abr_metadata_custom` and `ops.write_abr_metadata_custom`.
    unsafe fn new(ops: &'a AbrOps) -> Self {
        Self { ops, log: AbrPrintSysdeps {} }
    }
}

type AbrSlotIndex = c_uint;

impl Ops for AbrOpsSafe<'_> {
    fn read_abr_metadata(&mut self, out: &mut [u8]) -> Result<()> {
        if let Some(f) = self.ops.read_abr_metadata.as_ref() {
            // SAFETY:
            // * By safety requirement of `AbrOpsSafe::new()`, `self.ops.context` is either unused,
            //   or a valid pointer to a correct type of object used by
            //   `self.ops.read_abr_metadata`.
            // * `out` is a valid buffer
            // * `out` is for reading data only and will not be retained by the function.
            match unsafe { f(self.ops.context, out.len(), out.as_mut_ptr() as _) } {
                false => Err("read_abr_metadata() failed".into()),
                _ => Ok(()),
            }
        } else if let Some(f) = self.ops.read_abr_metadata_custom.as_ref() {
            let mut data: AbrData = Default::default();
            // SAFETY:
            // * By safety requirement of `AbrOpsSafe::new()`, `self.ops.context` is either unused,
            //   or a valid pointer to a correct type of object used by
            //   `self.ops.read_abr_metadata_custom`.
            // * Pointers to `slot_a`, `slot_b` and `one_shot_flags` are a valid memory locations.
            // * `slot_a`, `slot_b` and `one_shot_flags` are for output and will not be retained by
            //   the function.
            match unsafe {
                f(
                    self.ops.context,
                    &mut data.slot_data[SlotIndex::A as usize],
                    &mut data.slot_data[SlotIndex::B as usize],
                    &mut data.one_shot_flags,
                )
            } {
                false => Err("read_abr_metadata_custom() failed".into()),
                _ => Ok(out[..ABR_DATA_SIZE].clone_from_slice(&data.serialize())),
            }
        } else {
            Err("No valid read methods".into())
        }
    }

    fn write_abr_metadata(&mut self, data: &mut [u8]) -> Result<()> {
        if let Some(f) = self.ops.write_abr_metadata.as_ref() {
            // SAFETY:
            // * By safety requirement of `AbrOpsSafe::new()`, `self.ops.context` is either unused,
            //   or a valid pointer to a correct type of object used by
            //   `self.ops.write_abr_metadata`.
            // * `data` is a valid buffer.
            // * `data` is for input only and will not be retained by the function.
            match unsafe { f(self.ops.context, data.as_ptr() as _, data.len()) } {
                false => Err("write_abr_metadata() failed".into()),
                _ => Ok(()),
            }
        } else if let Some(f) = self.ops.write_abr_metadata_custom.as_ref() {
            let mut abr_data = [0u8; ABR_DATA_SIZE];
            abr_data.clone_from_slice(data.get(..ABR_DATA_SIZE).ok_or("Invalid data")?);
            let abr_data = AbrData::deserialize(&mut abr_data).unwrap();
            // SAFETY:
            // * By safety requirement of `AbrOpsSafe::new()`, `self.ops.context` is either unused,
            //   or a valid pointer to a correct type of object used by
            //   `self.ops.write_abr_metadata_custom`.
            // * Pointers to `slot_a` and `slot_b` are a valid memory locations.
            // * `slot_a` and `slot_b` are for input and will not be retained by the function.
            match unsafe {
                f(
                    self.ops.context,
                    &abr_data.slot_data[SlotIndex::A as usize],
                    &abr_data.slot_data[SlotIndex::B as usize],
                    abr_data.one_shot_flags,
                )
            } {
                false => Err("read_abr_metadata_custom() failed".into()),
                _ => Ok(()),
            }
        } else {
            Err("No valid write methods".into())
        }
    }

    fn console(&mut self) -> Option<&mut dyn core::fmt::Write> {
        Some(&mut self.log)
    }
}

/// A helper that extracts the return value and maps the result to an integer A/B/R result code.
fn unpack_result<T: Into<O>, O>(res: Result<T>, val: &mut O) -> c_uint {
    match res {
        Err(e) => match e {
            Error::BadMagic | Error::BadChecksum | Error::InvalidInput => {
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
/// * Caller must make sure to pass a valid, aligned pointer for `abr_ops`.
/// * Caller must make sure that `abr_ops.context` is either not used, or points to a valid and
///   correct type of value needed by `abr_ops.read_abr_metadata`, `abr_ops.write_abr_metadata`,
///   `abr_ops.read_abr_metadata_custom`, and `abr_ops.write_abr_metadata_custom`.
/// * Caller must make sure to pass either a NULL or valid, aligned pointer for
///   `is_slot_marked_successful`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrGetBootSlot(
    abr_ops: *const AbrOps,
    update_metadata: bool,
    is_slot_marked_successful: *mut bool,
) -> AbrSlotIndex {
    // SAFETY: The caller guarantees `abr_ops` is a valid, aligned pointer. We check for
    // non-nullness here and safely default to the Recovery slot if NULL.
    let Some(abr_ops) = (unsafe { abr_ops.as_ref() }) else {
        // SAFETY: The caller guarantees `is_slot_marked_successful` is a valid, aligned pointer or
        // NULL.
        if let Some(v) = unsafe { is_slot_marked_successful.as_mut() } {
            *v = false;
        }
        return SlotIndex::R.into();
    };
    // SAFETY: The caller guarantees `abr_ops.context` is valid for `AbrOpsSafe::new`.
    let mut abr_ops = unsafe { AbrOpsSafe::new(abr_ops) };

    let (slot_index, successful) = get_boot_slot(&mut abr_ops, update_metadata);
    // SAFETY: The caller guarantees `is_slot_marked_successful` is a valid, aligned pointer or
    // NULL.
    if let Some(v) = unsafe { is_slot_marked_successful.as_mut() } {
        *v = successful;
    }
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
/// * Caller must make sure to pass a valid, aligned pointer for `abr_ops`.
/// * Caller must make sure that `abr_ops.context` is either not used, or points to a valid and
///   correct type of value needed by `abr_ops.read_abr_metadata`, `abr_ops.write_abr_metadata`,
///   `abr_ops.read_abr_metadata_custom`, and `abr_ops.write_abr_metadata_custom`.
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

    // SAFETY: The caller guarantees `abr_ops` is a valid, aligned pointer. We check for
    // non-nullness here.
    let Some(abr_ops) = (unsafe { abr_ops.as_ref() }) else {
        return ABR_RESULT_ERR_INVALID_DATA;
    };
    // SAFETY: The caller guarantees `abr_ops.context` is valid for `AbrOpsSafe::new`.
    let mut abr_ops = unsafe { AbrOpsSafe::new(abr_ops) };

    unpack_result(mark_slot_active(&mut abr_ops, slot_index), &mut ())
}

/// C interface wrapper of `abr::get_slot_last_marked_active()`
///
/// # Safety
///
/// * Caller must make sure to pass valid, aligned pointers for `abr_ops` and `out_slot`.
/// * Caller must make sure that `abr_ops.context` is either not used, or points to a valid and
///   correct type of value needed by `abr_ops.read_abr_metadata`, `abr_ops.write_abr_metadata`,
///   `abr_ops.read_abr_metadata_custom`, and `abr_ops.write_abr_metadata_custom`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrGetSlotLastMarkedActive(
    abr_ops: *const AbrOps,
    out_slot: *mut AbrSlotIndex,
) -> c_uint {
    // SAFETY: The caller guarantees `abr_ops` and `out_slot` are valid, aligned pointers. We check
    // for non-nullness here.
    let (Some(abr_ops), Some(out_slot)) = (unsafe { (abr_ops.as_ref(), out_slot.as_mut()) }) else {
        return ABR_RESULT_ERR_INVALID_DATA;
    };
    // SAFETY: The caller guarantees `abr_ops.context` is valid for `AbrOpsSafe::new`.
    let mut abr_ops = unsafe { AbrOpsSafe::new(abr_ops) };

    unpack_result(get_slot_last_marked_active(&mut abr_ops), out_slot)
}

/// C interface wrapper of `abr::mark_slot_unbootable()`
///
/// # Safety
///
/// * Caller must make sure to pass a valid, aligned pointer for `abr_ops`.
/// * Caller must make sure that `abr_ops.context` is either not used, or points to a valid and
///   correct type of value needed by `abr_ops.read_abr_metadata`, `abr_ops.write_abr_metadata`,
///   `abr_ops.read_abr_metadata_custom`, and `abr_ops.write_abr_metadata_custom`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrMarkSlotUnbootable(
    abr_ops: *const AbrOps,
    slot_index: AbrSlotIndex,
    reason: c_uint,
) -> c_uint {
    let (Ok(slot_index), Ok(reason)) = (slot_index.try_into(), reason.try_into()) else {
        return ABR_RESULT_ERR_INVALID_DATA;
    };

    // SAFETY: The caller guarantees `abr_ops` is a valid, aligned pointer. We check for
    // non-nullness here.
    let Some(abr_ops) = (unsafe { abr_ops.as_ref() }) else {
        return ABR_RESULT_ERR_INVALID_DATA;
    };
    // SAFETY: The caller guarantees `abr_ops.context` is valid for `AbrOpsSafe::new`.
    let mut abr_ops = unsafe { AbrOpsSafe::new(abr_ops) };

    unpack_result(mark_slot_unbootable(&mut abr_ops, slot_index, reason), &mut ())
}

/// C interface wrapper of `abr::mark_slot_successful()`
///
/// # Safety
///
/// * Caller must make sure to pass a valid, aligned pointer for `abr_ops`.
/// * Caller must make sure that `abr_ops.context` is either not used, or points to a valid and
///   correct type of value needed by `abr_ops.read_abr_metadata`, `abr_ops.write_abr_metadata`,
///   `abr_ops.read_abr_metadata_custom`, and `abr_ops.write_abr_metadata_custom`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrMarkSlotSuccessful(
    abr_ops: *const AbrOps,
    slot_index: AbrSlotIndex,
    from_unbootable_ok: bool,
) -> c_uint {
    let slot_index = match slot_index.try_into() {
        Ok(v) => v,
        Err(_) => return ABR_RESULT_ERR_INVALID_DATA,
    };

    // SAFETY: The caller guarantees `abr_ops` is a valid, aligned pointer. We check for
    // non-nullness here.
    let Some(abr_ops) = (unsafe { abr_ops.as_ref() }) else {
        return ABR_RESULT_ERR_INVALID_DATA;
    };
    // SAFETY: The caller guarantees `abr_ops.context` is valid for `AbrOpsSafe::new`.
    let mut abr_ops = unsafe { AbrOpsSafe::new(abr_ops) };

    unpack_result(mark_slot_successful(&mut abr_ops, slot_index, from_unbootable_ok), &mut ())
}

/// `SlotInfo` contains the current state of an A/B/R slot.
///
/// TODO(b/338243123): Detailed documentation is available in Fuchsia upstream header
/// "src/firmware/lib/abr/include/lib/abr/abr.h", which will migrate to the GBL repo.
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct SlotInfo {
    /// Whether the slot is expected to be bootable.
    pub is_bootable: bool,
    /// Whether the slot is the highest priority A/B slot.
    pub is_active: bool,
    /// Whether the slot is currently marked successful.
    pub is_marked_successful: bool,
    /// If not marked successful, this represents the number of attempts left for booting this slot.
    pub num_tries_remaining: u8,
    /// If not bootable, this represents the reason why.
    pub unbootable_reason: u8,
}

impl From<AbrSlotInfo> for SlotInfo {
    fn from(val: abr::SlotInfo) -> Self {
        let is_marked_successful = matches!(val.state, SlotState::Successful);
        let num_tries_remaining = match val.state {
            SlotState::Bootable(v) => v,
            _ => 0,
        };
        let unbootable_reason = match val.state {
            SlotState::Unbootable(r) => r.into(),
            _ => UnbootableReason::None.into(),
        };
        Self {
            is_bootable: is_marked_successful || num_tries_remaining > 0,
            is_active: val.is_active,
            is_marked_successful,
            num_tries_remaining,
            unbootable_reason,
        }
    }
}

/// C interface wrapper of `abr::get_slot_info()`
///
/// # Safety
///
/// * Caller must make sure to pass valid, aligned pointers for `abr_ops` and `info`.
/// * Caller must make sure that `abr_ops.context` is either not used, or points to a valid and
///   correct type of value needed by `abr_ops.read_abr_metadata`, `abr_ops.write_abr_metadata`,
///   `abr_ops.read_abr_metadata_custom`, and `abr_ops.write_abr_metadata_custom`.
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

    // SAFETY: The caller guarantees `abr_ops` and `info` are valid, aligned pointers. We check for
    // non-nullness here.
    let (Some(abr_ops), Some(info)) = (unsafe { (abr_ops.as_ref(), info.as_mut()) }) else {
        return ABR_RESULT_ERR_INVALID_DATA;
    };
    // SAFETY: The caller guarantees `abr_ops.context` is valid for `AbrOpsSafe::new`.
    let mut abr_ops = unsafe { AbrOpsSafe::new(abr_ops) };

    unpack_result(get_slot_info(&mut abr_ops, slot_index).map(|v| SlotInfo::from(v)), info)
}

/// C interface wrapper of `abr::set_one_shot_recovery()`
///
/// # Safety
///
/// * Caller must make sure to pass a valid, aligned pointer for `abr_ops`.
/// * Caller must make sure that `abr_ops.context` is either not used, or points to a valid and
///   correct type of value needed by `abr_ops.read_abr_metadata`, `abr_ops.write_abr_metadata`,
///   `abr_ops.read_abr_metadata_custom`, and `abr_ops.write_abr_metadata_custom`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrSetOneShotRecovery(abr_ops: *const AbrOps, enable: bool) -> c_uint {
    // SAFETY: The caller guarantees `abr_ops` is a valid, aligned pointer. We check for
    // non-nullness here.
    let Some(abr_ops) = (unsafe { abr_ops.as_ref() }) else {
        return ABR_RESULT_ERR_INVALID_DATA;
    };
    // SAFETY: The caller guarantees `abr_ops.context` is valid for `AbrOpsSafe::new`.
    let mut abr_ops = unsafe { AbrOpsSafe::new(abr_ops) };

    unpack_result(set_one_shot_recovery(&mut abr_ops, enable), &mut ())
}

/// C interface wrapper of `abr::set_one_shot_bootloader()`
///
/// # Safety
///
/// * Caller must make sure to pass a valid, aligned pointer for `abr_ops`.
/// * Caller must make sure that `abr_ops.context` is either not used, or points to a valid and
///   correct type of value needed by `abr_ops.read_abr_metadata`, `abr_ops.write_abr_metadata`,
///   `abr_ops.read_abr_metadata_custom`, and `abr_ops.write_abr_metadata_custom`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrSetOneShotBootloader(abr_ops: *const AbrOps, enable: bool) -> c_uint {
    // SAFETY: The caller guarantees `abr_ops` is a valid, aligned pointer. We check for
    // non-nullness here.
    let Some(abr_ops) = (unsafe { abr_ops.as_ref() }) else {
        return ABR_RESULT_ERR_INVALID_DATA;
    };
    // SAFETY: The caller guarantees `abr_ops.context` is valid for `AbrOpsSafe::new`.
    let mut abr_ops = unsafe { AbrOpsSafe::new(abr_ops) };

    unpack_result(set_one_shot_bootloader(&mut abr_ops, enable), &mut ())
}

/// Gets and clears the one shot flag.
///
/// # Safety
///
/// * Caller must make sure to pass valid, aligned pointers for `abr_ops` and `flags`.
/// * Caller must make sure that `abr_ops.context` is either not used, or points to a valid and
///   correct type of value needed by `abr_ops.read_abr_metadata`, `abr_ops.write_abr_metadata`,
///   `abr_ops.read_abr_metadata_custom`, and `abr_ops.write_abr_metadata_custom`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrGetAndClearOneShotFlags(
    abr_ops: *const AbrOps,
    flags: *mut c_uint,
) -> c_uint {
    // SAFETY: The caller guarantees `abr_ops` and `flags` are valid, aligned pointers. We check for
    // non-nullness here.
    let (Some(abr_ops), Some(flags)) = (unsafe { (abr_ops.as_ref(), flags.as_mut()) }) else {
        return ABR_RESULT_ERR_INVALID_DATA;
    };
    // SAFETY: The caller guarantees `abr_ops.context` is valid for `AbrOpsSafe::new`.
    let mut abr_ops = unsafe { AbrOpsSafe::new(abr_ops) };

    unpack_result(get_and_clear_one_shot_flag(&mut abr_ops), flags)
}

/// C interface wrapper of `AbrSlotData::get_normalized_priority()`.
///
/// # Safety
///
/// * Caller must make sure to pass a valid, aligned pointer for `slot_data`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrGetNormalizedPriority(slot_data: *const AbrSlotData) -> u8 {
    // SAFETY: Caller guarantees `slot_data` is valid and aligned.
    // We check for non-nullness and return 0 (unbootable) as a safe default otherwise.
    unsafe { slot_data.as_ref() }.map(|s| s.get_normalized_priority()).unwrap_or(0)
}

/// C interface wrapper of `abr::get_active_slot_from_data()`.
///
/// # Safety
///
/// * Caller must make sure to pass valid, aligned pointers for `data_a` and `data_b`.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn AbrGetActiveSlotFromData(
    data_a: *const AbrSlotData,
    data_b: *const AbrSlotData,
) -> AbrSlotIndex {
    // SAFETY: Caller guarantees pointers are valid and aligned.
    // If either is NULL, we safely default to the Recovery slot.
    match unsafe { (data_a.as_ref(), data_b.as_ref()) } {
        (Some(a), Some(b)) => get_active_slot_from_data(a, b).into(),
        _ => SlotIndex::R.into(),
    }
}

/// Needed because of no-std environment in static lib build.
#[cfg(not(test))]
#[no_mangle]
pub extern "C" fn rust_eh_personality() {}
