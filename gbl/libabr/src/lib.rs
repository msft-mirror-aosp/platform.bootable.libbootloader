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

//! Fuchsia A/B/R boot slot library.

#![cfg_attr(not(test), no_std)]

use core::{cmp::min, ffi::c_uint, fmt::Write, mem::size_of};

use liberror::{Error, Result};

const ABR_MAGIC: &[u8; 4] = b"\0AB0";
const ABR_MAJOR_VERSION: u8 = 2;
const ABR_MINOR_VERSION: u8 = 2;

// The following flags are harcoded as u8 instead of using the bitflag crate to avoid additional
// crate dependency and improve portability.

/// One-shot recovery boot bit for the flag returned by `get_and_clear_one_shot_flag()`.
pub const ONE_SHOT_RECOVERY: u8 = 1 << 0;
/// One-shot bootloader boot bit for the flag returned by `get_and_clear_one_shot_flag()`.
pub const ONE_SHOT_BOOTLOADER: u8 = 1 << 1;

const ABR_MAX_PRIORITY: u8 = 15;
/// Maximum number of retries.
pub const ABR_MAX_TRIES_REMAINING: u8 = 7;

/// `Ops` provides the backend interfaces needed by A/B/R APIs.
pub trait Ops {
    /// Reads exactly `out.len()` bytes into `out` from the persistent storage hosting the A/B/R
    /// metadata.
    fn read_abr_metadata(&mut self, out: &mut [u8]) -> Result<()>;

    /// Writes exactly `data.len()` bytes from `data` to the persistent storage hosting the A/B/R
    /// metadata.
    fn write_abr_metadata(&mut self, data: &mut [u8]) -> Result<()>;

    /// Returns an optional console writer for logging error messages.
    fn console(&mut self) -> Option<&mut dyn Write>;
}

impl Ops for [u8; ABR_DATA_SIZE] {
    fn read_abr_metadata(&mut self, out: &mut [u8]) -> Result<()> {
        Ok(out
            .clone_from_slice(self.get(..out.len()).ok_or(Error::BufferTooSmall(Some(out.len())))?))
    }

    fn write_abr_metadata(&mut self, data: &mut [u8]) -> Result<()> {
        Ok(self
            .get_mut(..data.len())
            .ok_or(Error::BufferTooSmall(Some(data.len())))?
            .clone_from_slice(data))
    }

    fn console(&mut self) -> Option<&mut dyn Write> {
        None
    }
}

/// Helper macro for printing ABR log messages.
macro_rules! avb_print {
    ( $abr_ops:expr, $( $x:expr ),* $(,)? ) => {
            match $abr_ops.console() {
                Some(f) => write!(f, $($x,)*).unwrap(),
                _ => {}
            }
    };
}

/// `SlotIndex` represents the A/B/R slot index.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum SlotIndex {
    /// A slot; normal boot.
    A,
    /// B slot; normal boot.
    B,
    /// R slot; recovery boot. Doesn't have any associated metadata (e.g. cannot be active, no
    /// retries), but is unconditionally used as a fallback if both A and B are unbootable.
    R,
}

impl SlotIndex {
    // Get the other counterpart of a A/B slot.
    fn other(&self) -> Self {
        match self {
            SlotIndex::A => SlotIndex::B,
            SlotIndex::B => SlotIndex::A,
            _ => panic!("Invalid slot index for `fn other()`"),
        }
    }
}

// Implement conversion to c_uint for C interfaces
impl From<SlotIndex> for c_uint {
    fn from(_val: SlotIndex) -> Self {
        match _val {
            SlotIndex::A => 0,
            SlotIndex::B => 1,
            SlotIndex::R => 2,
        }
    }
}

// Implement conversion from c_uint for C interfaces.
impl TryFrom<c_uint> for SlotIndex {
    type Error = Error;

    fn try_from(val: c_uint) -> Result<SlotIndex> {
        match val {
            v if v == (SlotIndex::A).into() => Ok(SlotIndex::A),
            v if v == (SlotIndex::B).into() => Ok(SlotIndex::B),
            v if v == (SlotIndex::R).into() => Ok(SlotIndex::R),
            _ => Err(Error::InvalidInput),
        }
    }
}

/// `SlotInfo` represents the current state of a A/B/R slot.
pub enum SlotState {
    /// Slot has successfully booted.
    Successful,
    /// Slot can be attempted but is not known to be successful. Contained value is the number
    /// of boot attempts remaining before being marked as `Unbootable`.
    Bootable(u8),
    /// Slot is unbootable.
    Unbootable,
}

/// `SlotInfo` contains the current state and active status of a A/B/R slot.
pub struct SlotInfo {
    /// The [SlotState] describing the bootability.
    pub state: SlotState,
    /// Whether this is currently the active slot.
    pub is_active: bool,
}

/// `AbrSlotData` is the wire format metadata for A/B slot.
#[repr(C, packed)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Default)]
pub struct AbrSlotData {
    /// Slot priority. Unbootable slots should always have priority 0.
    pub priority: u8,
    /// Boot attempts remaining.
    pub tries_remaining: u8,
    /// Whether this slot is known successful.
    pub successful_boot: u8,
    /// Reserved for future use; must be set to 0.
    pub reserved: u8,
}

const ABR_SLOT_DATA_SIZE: usize = size_of::<AbrSlotData>();

impl AbrSlotData {
    /// Parses from bytes.
    pub fn deserialize(bytes: &[u8; ABR_SLOT_DATA_SIZE]) -> Self {
        Self {
            priority: bytes[0],
            tries_remaining: bytes[1],
            successful_boot: bytes[2],
            reserved: bytes[3],
        }
    }

    /// Serializes to bytes.
    pub fn serialize(&self) -> [u8; ABR_SLOT_DATA_SIZE] {
        [self.priority, self.tries_remaining, self.successful_boot, self.reserved]
    }

    /// Returns if slot is bootable
    fn is_slot_bootable(&self) -> bool {
        self.priority > 0 && (self.successful_boot == 1 || self.tries_remaining > 0)
    }

    fn set_slot_unbootable(&mut self) {
        self.tries_remaining = 0;
        self.successful_boot = 0;
    }

    /// Gets normalized priority.
    fn get_normalized_priority(&self) -> u8 {
        match self.is_slot_bootable() {
            true => self.priority,
            _ => 0,
        }
    }

    /// Ensures all unbootable or invalid states are marked as the canonical `unbootable` state.
    /// That is priority=0, tries_remaining=0, and successful_boot=0.
    fn slot_normalize(&mut self) {
        if self.priority > 0 {
            if self.tries_remaining == 0 && self.successful_boot == 0 {
                // All tries exhausted
                self.set_slot_unbootable();
            }
            if self.tries_remaining > 0 && self.successful_boot == 1 {
                // Illegal state. Reset to not successful state
                self.tries_remaining = ABR_MAX_TRIES_REMAINING;
                self.successful_boot = 0;
            }
            self.priority = min(self.priority, ABR_MAX_PRIORITY);
            self.tries_remaining = min(self.tries_remaining, ABR_MAX_TRIES_REMAINING);
        } else {
            self.set_slot_unbootable();
        }
    }
}

/// `AbrData` is the wire format of A/B/R metadata.
#[repr(C, packed)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct AbrData {
    /// Magic value; must be [ABR_MAGIC].
    pub magic: [u8; 4],
    /// Metadata major version, incremented when changes may break backwards compatibility.
    pub version_major: u8,
    /// Metadata minor version, incremented when changes do not break backwards compatibility.
    pub version_minor: u8,
    /// Reserved for future use; must be 0.
    pub reserved: [u8; 2],
    /// A/B slot data.
    pub slot_data: [AbrSlotData; 2],
    /// One-shot to bootloader/recovery.
    pub one_shot_flags: u8,
    /// Reserved for future use; must be 0.
    pub reserved2: [u8; 11],
    /// CRC32 checksum of this struct.
    pub crc32: u32,
}

/// Size of `AbrData`
pub const ABR_DATA_SIZE: usize = size_of::<AbrData>();

impl AbrData {
    /// Returns the numeric index value for a `SlotIndex`. This is for indexing into
    /// `Self::slot_data`.
    fn slot_num_index(slot_index: SlotIndex) -> usize {
        match slot_index {
            SlotIndex::A => 0,
            SlotIndex::B => 1,
            _ => panic!("Invalid slot index"),
        }
    }

    /// Returns a const reference to `Self::slot_data['slot_index']`
    fn slot_data(&self, slot_index: SlotIndex) -> &AbrSlotData {
        &self.slot_data[Self::slot_num_index(slot_index)]
    }

    /// Returns a mutable reference to `Self::slot_data[`slot_index`]`
    fn slot_data_mut(&mut self, slot_index: SlotIndex) -> &mut AbrSlotData {
        &mut self.slot_data[Self::slot_num_index(slot_index)]
    }

    /// Reads, parses and checks metadata from persistent storage.
    pub fn deserialize(abr_ops: &mut dyn Ops) -> Result<Self> {
        let mut bytes = [0u8; ABR_DATA_SIZE];
        abr_ops.read_abr_metadata(&mut bytes[..])?;
        // Usually, the parsing below should be done using the zerocopy crate. However, the Fuchsia
        // source tree uses the unreleased alpha/beta version of zerocopy which can have
        // drastically different usage and bound requirements. In order to minimize maintenance
        // burden for Android and Fuchsia build, we manually copy and parse from the bytes directly
        // to avoid zerocopy crate dependency.
        let res = Self {
            magic: bytes[..4].try_into().unwrap(),
            version_major: bytes[4],
            version_minor: bytes[5],
            reserved: bytes[6..8].try_into().unwrap(),
            slot_data: [
                AbrSlotData::deserialize(&bytes[8..12].try_into().unwrap()),
                AbrSlotData::deserialize(&bytes[12..16].try_into().unwrap()),
            ],
            one_shot_flags: bytes[16],
            reserved2: bytes[17..28].try_into().unwrap(),
            crc32: u32::from_be_bytes(bytes[28..ABR_DATA_SIZE].try_into().unwrap()),
        };

        if res.magic != *ABR_MAGIC {
            avb_print!(abr_ops, "Magic is incorrect.\n");
            return Err(Error::BadMagic);
        }
        if res.crc32 != crc32(&bytes[..28]) {
            avb_print!(abr_ops, "CRC32 does not match.\n");
            return Err(Error::BadChecksum);
        }
        if res.version_major > ABR_MAJOR_VERSION {
            avb_print!(abr_ops, "No support for given major version.\n");
            return Err(Error::UnsupportedVersion);
        }

        Ok(res)
    }

    /// Updates CRC32 and writes metadata to persistent storage.
    pub fn serialize(&mut self) -> [u8; ABR_DATA_SIZE] {
        let mut res = [0u8; ABR_DATA_SIZE];
        res[..4].clone_from_slice(&self.magic);
        res[4] = self.version_major;
        res[5] = self.version_minor;
        res[6..8].clone_from_slice(&self.reserved);
        res[8..12].clone_from_slice(&self.slot_data(SlotIndex::A).serialize());
        res[12..16].clone_from_slice(&self.slot_data(SlotIndex::B).serialize());
        res[16] = self.one_shot_flags;
        res[17..28].clone_from_slice(&self.reserved2[..]);
        self.crc32 = crc32(&res[..28]);
        res[28..ABR_DATA_SIZE].clone_from_slice(&self.crc32.to_be_bytes());
        res
    }

    /// Returns an invalid instance.
    fn null() -> Self {
        Self { magic: [0u8; 4], ..Default::default() }
    }

    /// Gets the active slot
    fn get_active_slot(&self) -> SlotIndex {
        let priority_a = self.slot_data(SlotIndex::A).get_normalized_priority();
        let priority_b = self.slot_data(SlotIndex::B).get_normalized_priority();
        if priority_b > priority_a {
            return SlotIndex::B;
        } else if priority_a > 0 {
            return SlotIndex::A;
        }
        return SlotIndex::R;
    }

    /// Is the given slot active.
    fn is_slot_active(&self, slot_index: SlotIndex) -> bool {
        self.get_active_slot() == slot_index
    }

    /// Returns if one-shot recovery is set.
    fn is_one_shot_recovery(&self) -> bool {
        (self.one_shot_flags & ONE_SHOT_RECOVERY) != 0
    }

    /// Sets one-shot recovery.
    pub fn set_one_shot_recovery(&mut self, enable: bool) {
        match enable {
            true => self.one_shot_flags |= ONE_SHOT_RECOVERY,
            _ => self.one_shot_flags &= !ONE_SHOT_RECOVERY,
        }
    }

    /// Sets one-shot bootloader
    pub fn set_one_shot_bootloader(&mut self, enable: bool) {
        match enable {
            true => self.one_shot_flags |= ONE_SHOT_BOOTLOADER,
            _ => self.one_shot_flags &= !ONE_SHOT_BOOTLOADER,
        }
    }
}

impl Default for AbrData {
    fn default() -> Self {
        Self {
            magic: *ABR_MAGIC,
            version_major: ABR_MAJOR_VERSION,
            version_minor: ABR_MINOR_VERSION,
            reserved: Default::default(),
            slot_data: [
                AbrSlotData {
                    priority: ABR_MAX_PRIORITY,
                    tries_remaining: ABR_MAX_TRIES_REMAINING,
                    successful_boot: 0,
                    reserved: 0,
                },
                AbrSlotData {
                    priority: ABR_MAX_PRIORITY - 1,
                    tries_remaining: ABR_MAX_TRIES_REMAINING,
                    successful_boot: 0,
                    reserved: 0,
                },
            ],
            one_shot_flags: 0,
            reserved2: Default::default(),
            crc32: 0,
        }
    }
}

/// Loads |abr_data| from persistent storage and normalizes it, initializing new data if necessary.
/// Changes as a result of normalization are not written back to persistent storage but a copy of
/// the exact original data from persistent storage is provided in |abr_data_orig| for future use
/// with save_metadata_if_changed().
///
/// On success returns Ok((abr_data, abr_data_orig)). On failure an Error is returned.
fn load_metadata(abr_ops: &mut dyn Ops) -> Result<(AbrData, AbrData)> {
    let mut abr_data_orig = AbrData::null();
    let mut abr_data = match AbrData::deserialize(abr_ops) {
        Ok(v) => {
            abr_data_orig = v;
            v
        }
        Err(Error::Other(e)) => {
            avb_print!(abr_ops, "read_abr_metadata error: {:?}\n", e);
            return Err(e.into());
        }
        Err(Error::UnsupportedVersion) => {
            // We don't want to clobber valid data in persistent storage, but we can't use this
            // data, so bail out.
            return Err(Error::UnsupportedVersion);
        }
        _ => Default::default(),
    };
    abr_data.slot_data_mut(SlotIndex::A).slot_normalize();
    abr_data.slot_data_mut(SlotIndex::B).slot_normalize();

    Ok((abr_data, abr_data_orig))
}

/// Serializes and saves metadata to persistent storage.
fn save_metadata(abr_ops: &mut dyn Ops, abr_data: &mut AbrData) -> Result<()> {
    let mut bytes = abr_data.serialize();
    abr_ops.write_abr_metadata(&mut bytes)?;
    Ok(())
}

/// Writes metadata to disk only if it has changed. `abr_data_orig` should be from load_metadata().
fn save_metadata_if_changed(
    abr_ops: &mut dyn Ops,
    abr_data: &mut AbrData,
    abr_data_orig: &AbrData,
) -> Result<()> {
    match abr_data == abr_data_orig {
        true => Ok(()),
        _ => save_metadata(abr_ops, abr_data),
    }
}

/// Equivalent to C API `AbrGetBootSlot()`.
///
/// TODO(b/338243123): Detailed documentation is available in Fuchsia upstream header
/// "src/firmware/lib/abr/include/lib/abr/abr.h", which will migrate to the GBL repo.
pub fn get_boot_slot(abr_ops: &mut dyn Ops, update_metadata: bool) -> (SlotIndex, bool) {
    let mut is_slot_marked_successful = false;
    let (mut abr_data, abr_data_orig) = match load_metadata(abr_ops) {
        Ok(v) => v,
        Err(e) => {
            avb_print!(
                abr_ops,
                "Failed to load metadata {:?}, falling back to recovery mode.\n",
                e
            );
            return (SlotIndex::R, is_slot_marked_successful);
        }
    };

    if abr_data.is_one_shot_recovery() && update_metadata {
        abr_data.set_one_shot_recovery(false);
        match save_metadata(abr_ops, &mut abr_data) {
            Ok(()) => return (SlotIndex::R, is_slot_marked_successful),
            Err(e) => {
                avb_print!(
                    abr_ops,
                    "Failed to update one-shot state {:?}. Ignoring one-shot request.\n",
                    e
                );
                abr_data.set_one_shot_recovery(true);
            }
        }
    }

    // Chooses the highest priority and bootable slot. Otherwise R slot.
    let slot_to_boot = abr_data.get_active_slot();
    match slot_to_boot {
        SlotIndex::R => {}
        v => {
            is_slot_marked_successful = abr_data.slot_data(v).successful_boot == 1;
        }
    };

    if update_metadata {
        // In addition to any changes that resulted from normalization, there are a couple changes
        // to be made here. First is to decrement the tries remaining for a slot not yet marked as
        // successful.
        if slot_to_boot != SlotIndex::R && !is_slot_marked_successful {
            let slot_data = abr_data.slot_data_mut(slot_to_boot);
            slot_data.tries_remaining = slot_data.tries_remaining.checked_sub(1).unwrap();
        }
        // Second is to clear the successful_boot bit from any successfully-marked slots that
        // aren't the slot we're booting. It's possible that booting from one slot will render the
        // other slot unbootable (say, by migrating a config file format in a shared partiton).
        // Clearing these bits minimizes the risk we'll have an unhealthy slot marked
        // "successful_boot", which would prevent the system from automatically booting into
        // recovery.
        for slot in [SlotIndex::A, SlotIndex::B] {
            if slot != slot_to_boot && abr_data.slot_data(slot).successful_boot == 1 {
                abr_data.slot_data_mut(slot).tries_remaining = ABR_MAX_TRIES_REMAINING;
                abr_data.slot_data_mut(slot).successful_boot = 0;
            }
        }
        if let Err(e) = save_metadata_if_changed(abr_ops, &mut abr_data, &abr_data_orig) {
            // We have no choice but to proceed without updating metadata.
            avb_print!(abr_ops, "Failed to update metadata {:?}, proceeding anyways.\n", e);
        }
    }
    (slot_to_boot, is_slot_marked_successful)
}

/// Equivalent to C API `AbrMarkSlotActive()`.
///
/// TODO(b/338243123): Detailed documentation is available in Fuchsia upstream header
/// "src/firmware/lib/abr/include/lib/abr/abr.h", which will migrate to the GBL repo.
pub fn mark_slot_active(abr_ops: &mut dyn Ops, slot_index: SlotIndex) -> Result<()> {
    if slot_index == SlotIndex::R {
        avb_print!(abr_ops, "Invalid argument: Cannot mark slot R as active.\n");
        return Err(Error::InvalidInput);
    }
    let (mut abr_data, abr_data_orig) = load_metadata(abr_ops)?;
    // Make requested slot top priority, unsuccessful, and with max tries.
    abr_data.slot_data_mut(slot_index).priority = ABR_MAX_PRIORITY;
    abr_data.slot_data_mut(slot_index).tries_remaining = ABR_MAX_TRIES_REMAINING;
    abr_data.slot_data_mut(slot_index).successful_boot = 0;

    // Ensure other slot doesn't have as high a priority
    let other = slot_index.other();
    abr_data.slot_data_mut(other).priority =
        min(abr_data.slot_data_mut(other).priority, ABR_MAX_PRIORITY - 1);

    save_metadata_if_changed(abr_ops, &mut abr_data, &abr_data_orig)
}

/// Equivalent to C API `AbrGetSlotLastMarkedActive()`.
///
/// TODO(b/338243123): Detailed documentation is available in Fuchsia upstream header
/// "src/firmware/lib/abr/include/lib/abr/abr.h", which will migrate to the GBL repo.
pub fn get_slot_last_marked_active(abr_ops: &mut dyn Ops) -> Result<SlotIndex> {
    let (abr_data, _) = load_metadata(abr_ops)?;
    Ok(
        match abr_data.slot_data(SlotIndex::B).priority > abr_data.slot_data(SlotIndex::A).priority
        {
            true => SlotIndex::B,
            false => SlotIndex::A,
        },
    )
}

/// Equivalent to C API `AbrMarkSlotUnbootable()`.
///
/// TODO(b/338243123): Detailed documentation is available in Fuchsia upstream header
/// "src/firmware/lib/abr/include/lib/abr/abr.h", which will migrate to the GBL repo.
pub fn mark_slot_unbootable(abr_ops: &mut dyn Ops, slot_index: SlotIndex) -> Result<()> {
    if slot_index == SlotIndex::R {
        avb_print!(abr_ops, "Invalid argument: Cannot mark slot R as unbootable.\n");
        return Err(Error::InvalidInput);
    }
    let (mut abr_data, abr_data_orig) = load_metadata(abr_ops)?;
    abr_data.slot_data_mut(slot_index).set_slot_unbootable();
    save_metadata_if_changed(abr_ops, &mut abr_data, &abr_data_orig)
}

/// Equivalent to C API `AbrMarkSlotSuccessful()`.
///
/// TODO(b/338243123): Detailed documentation is available in Fuchsia upstream header
/// "src/firmware/lib/abr/include/lib/abr/abr.h", which will migrate to the GBL repo.
pub fn mark_slot_successful(abr_ops: &mut dyn Ops, slot_index: SlotIndex) -> Result<()> {
    if slot_index == SlotIndex::R {
        avb_print!(abr_ops, "Invalid argument: Cannot mark slot R as successful.\n");
        return Err(Error::InvalidInput);
    }
    let (mut abr_data, abr_data_orig) = load_metadata(abr_ops)?;

    if !abr_data.slot_data(slot_index).is_slot_bootable() {
        avb_print!(abr_ops, "Invalid argument: Cannot mark unbootable slot as successful.\n");
        return Err(Error::InvalidInput);
    }

    abr_data.slot_data_mut(slot_index).tries_remaining = 0;
    abr_data.slot_data_mut(slot_index).successful_boot = 1;

    // Proactively remove any success mark on the other slot
    //
    // This can theoretically be removed since get_boot_slot() clear successful bit on non-boot
    // slots. However, legacy devices might still be using old versions of ABR implementation that
    // don't clear it. Therefore, we keep this logic to be safe.
    //
    // Context: https://fxbug.dev/42142842, https://crbug.com/fuchsia/64057.
    let other = slot_index.other();
    if abr_data.slot_data(other).is_slot_bootable() {
        abr_data.slot_data_mut(other).tries_remaining = ABR_MAX_TRIES_REMAINING;
        abr_data.slot_data_mut(other).successful_boot = 0;
    }
    save_metadata_if_changed(abr_ops, &mut abr_data, &abr_data_orig)
}

/// Equivalent to C API `AbrGetSlotInfo()`.
///
/// TODO(b/338243123): Detailed documentation is available in Fuchsia upstream header
/// "src/firmware/lib/abr/include/lib/abr/abr.h", which will migrate to the GBL repo.
pub fn get_slot_info(abr_ops: &mut dyn Ops, slot_index: SlotIndex) -> Result<SlotInfo> {
    let (abr_data, _) = load_metadata(abr_ops)?;
    Ok(match slot_index {
        // Assume that R slot is always OK.
        SlotIndex::R => SlotInfo {
            state: SlotState::Successful,
            is_active: abr_data.is_slot_active(SlotIndex::R),
        },
        _ => {
            let slot_data = abr_data.slot_data(slot_index);
            let state = match slot_data.successful_boot == 1 {
                true => SlotState::Successful,
                _ if slot_data.is_slot_bootable() => SlotState::Bootable(slot_data.tries_remaining),
                _ => SlotState::Unbootable,
            };
            SlotInfo { state, is_active: abr_data.is_slot_active(slot_index) }
        }
    })
}

/// Equivalent to C API `AbrSetOneShotRecovery()`.
///
/// TODO(b/338243123): Detailed documentation is available in Fuchsia upstream header
/// "src/firmware/lib/abr/include/lib/abr/abr.h", which will migrate to the GBL repo.
pub fn set_one_shot_recovery(abr_ops: &mut dyn Ops, enable: bool) -> Result<()> {
    let (mut abr_data, abr_data_orig) = load_metadata(abr_ops)?;
    abr_data.set_one_shot_recovery(enable);
    save_metadata_if_changed(abr_ops, &mut abr_data, &abr_data_orig)
}

/// Equivalent to C API `AbrSetOneShotBootloader()`.
///
/// TODO(b/338243123): Detailed documentation is available in Fuchsia upstream header
/// "src/firmware/lib/abr/include/lib/abr/abr.h", which will migrate to the GBL repo.
pub fn set_one_shot_bootloader(abr_ops: &mut dyn Ops, enable: bool) -> Result<()> {
    let (mut abr_data, abr_data_orig) = load_metadata(abr_ops)?;
    abr_data.set_one_shot_bootloader(enable);
    save_metadata_if_changed(abr_ops, &mut abr_data, &abr_data_orig)
}

/// Equivalent to C API `AbrGetAndClearOneShotFlags()`.
///
/// TODO(b/338243123): Detailed documentation is available in Fuchsia upstream header
/// "src/firmware/lib/abr/include/lib/abr/abr.h", which will migrate to the GBL repo.
pub fn get_and_clear_one_shot_flag(abr_ops: &mut dyn Ops) -> Result<u8> {
    let (mut abr_data, abr_data_orig) = load_metadata(abr_ops)?;
    let res = abr_data.one_shot_flags;
    abr_data.one_shot_flags = 0;
    save_metadata_if_changed(abr_ops, &mut abr_data, &abr_data_orig)?;
    Ok(res)
}

/// Gets and clears one shot bootloader flag only.
pub fn get_and_clear_one_shot_bootloader(abr_ops: &mut dyn Ops) -> Result<bool> {
    let (mut abr_data, abr_data_orig) = load_metadata(abr_ops)?;
    let res = abr_data.one_shot_flags;
    abr_data.one_shot_flags &= !ONE_SHOT_BOOTLOADER;
    save_metadata_if_changed(abr_ops, &mut abr_data, &abr_data_orig)?;
    Ok((res & ONE_SHOT_BOOTLOADER) != 0)
}

/// Reverses the bit of a byte.
fn reverse_byte(b: u8) -> u8 {
    const LOOKUP_TABLE_4BIT_REVERSE: &[u8] =
        &[0x0, 0x8, 0x4, 0xC, 0x2, 0xA, 0x6, 0xE, 0x1, 0x9, 0x5, 0xD, 0x3, 0xB, 0x7, 0xF];
    LOOKUP_TABLE_4BIT_REVERSE[(b >> 4) as usize]
        | (LOOKUP_TABLE_4BIT_REVERSE[(b & 0xf) as usize] << 4)
}

// Reverses the bits of a u32;
fn reverse_u32(val: u32) -> u32 {
    let mut bytes = val.to_le_bytes();
    bytes.iter_mut().for_each(|v| *v = reverse_byte(*v));
    u32::from_be_bytes(bytes)
}

// Calculates the crc32 of the given bytes.
fn crc32(data: &[u8]) -> u32 {
    let mut res: u32 = 0xffffffff;
    for b in data {
        res ^= (reverse_byte(*b) as u32) << 24;
        for _ in 0..8 {
            if (res & 0x80000000) != 0 {
                res = (res << 1) ^ 0x04C11DB7;
            } else {
                res <<= 1;
            }
        }
    }
    reverse_u32(!res)
}

#[cfg(test)]
mod test {
    use super::*;
    // Testing is currently done against the C interface tests in upstream Fuchsia:
    // https://fuchsia.googlesource.com/fuchsia/+/96f7268b497f998ffcbeef73425b031bd7f4db65/src/firmware/lib/abr/test/libabr_test.cc
    // These tests will be ported to here as rust tests in the future.

    #[test]
    fn test_get_and_clear_one_shot_bootloader() {
        let mut meta = [0u8; ABR_DATA_SIZE];
        set_one_shot_bootloader(&mut meta, true).unwrap();
        set_one_shot_recovery(&mut meta, true).unwrap();
        assert!(get_and_clear_one_shot_bootloader(&mut meta).unwrap());
        assert_eq!(get_and_clear_one_shot_flag(&mut meta).unwrap(), ONE_SHOT_RECOVERY);
    }
}
