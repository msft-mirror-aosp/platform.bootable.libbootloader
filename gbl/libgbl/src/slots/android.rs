// Copyright (C) 2024  Google LLC
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

use super::partition::{MetadataBytes, SlotBlock};
use super::{
    BootTarget, BootToken, Bootability, Manager, OneShot, RecoveryTarget, Slot, SlotIterator,
    Suffix, UnbootableReason,
};

use core::convert::TryInto;
use core::iter::zip;
use core::mem::size_of;
use core::ops::{BitAnd, BitOr, Not, Shl, Shr};
use crc32fast::Hasher;
use liberror::Error;
use zerocopy::byteorder::little_endian::U32 as LittleEndianU32;
use zerocopy::{AsBytes, ByteSlice, FromBytes, FromZeroes, Ref};

extern crate static_assertions;

const MAX_SLOTS: u8 = 4;

// TODO(b/332338968): remove the manual field definitions and use bindgen definitions.

// Helper function to extract values from bitfields.
// Preconditions:
// 1) All bits in a bitfield are consecutive.
// 1a) No fields interleave their bits.
// 2) `offset` defines the position of the least significant bit in the field.
// 3) If a bit is set in `mask`, all bits of lower significance are set.
// 4) If a bit is NOT set in `mask`, all bits of greater significanec are NOT set.
fn get_field<N, R>(base: N, offset: N, mask: N) -> R
where
    N: Shr<Output = N> + BitAnd<Output = N>,
    R: Default + TryFrom<N>,
{
    ((base >> offset) & mask).try_into().unwrap_or_default()
}

// Helper function to set values in bit fields.
// All the preconditions for `get_field` apply.
// Returns the modified field. It is the caller's responsibility
// to assign the result appropriately.
fn set_field<N, R>(base: N, val: R, offset: N, mask: N) -> N
where
    N: Copy + Shl<Output = N> + BitAnd<Output = N> + BitOr<Output = N> + Not<Output = N>,
    R: Into<N>,
{
    (base & !(mask << offset)) | ((val.into() & mask) << offset)
}

const DEFAULT_PRIORITY: u8 = 7;
const DEFAULT_RETRIES: u8 = 7;

/// Android reference implementation for slot-specific metadata.
/// See `BootloaderControl` for more background information.
///
/// Does NOT contain unbootable reason information.
#[repr(C, packed)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, AsBytes, FromBytes, FromZeroes)]
struct SlotMetaData(u16);

impl SlotMetaData {
    const PRIORITY_MASK: u16 = 0b1111;
    const PRIORITY_OFFSET: u16 = 0;

    const TRIES_MASK: u16 = 0b111;
    const TRIES_OFFSET: u16 = 4;

    const SUCCESSFUL_MASK: u16 = 0b1;
    const SUCCESSFUL_OFFSET: u16 = 7;

    const VERITY_CORRUPTED_MASK: u16 = 0b1;
    const VERITY_CORRUPTED_OFFSET: u16 = 8;

    fn priority(&self) -> u8 {
        get_field(self.0, Self::PRIORITY_OFFSET, Self::PRIORITY_MASK)
    }
    fn set_priority(&mut self, priority: u8) {
        self.0 = set_field(self.0, priority, Self::PRIORITY_OFFSET, Self::PRIORITY_MASK)
    }

    fn tries(&self) -> u8 {
        get_field(self.0, Self::TRIES_OFFSET, Self::TRIES_MASK)
    }
    fn set_tries(&mut self, tries: u8) {
        self.0 = set_field(self.0, tries, Self::TRIES_OFFSET, Self::TRIES_MASK)
    }

    fn successful(&self) -> bool {
        get_field::<_, u8>(self.0, Self::SUCCESSFUL_OFFSET, Self::SUCCESSFUL_MASK) != 0
    }
    fn set_successful(&mut self, successful: bool) {
        self.0 = set_field(self.0, successful, Self::SUCCESSFUL_OFFSET, Self::SUCCESSFUL_MASK);
    }

    fn verity_corrupted(&self) -> bool {
        get_field::<_, u8>(self.0, Self::VERITY_CORRUPTED_OFFSET, Self::VERITY_CORRUPTED_MASK) != 0
    }
    fn set_verity_corrupted(&mut self, verity_corrupted: bool) {
        self.0 = set_field(
            self.0,
            verity_corrupted,
            Self::VERITY_CORRUPTED_OFFSET,
            Self::VERITY_CORRUPTED_MASK,
        );
    }
}
static_assertions::const_assert_eq!(
    core::mem::size_of::<SlotMetaData>(),
    core::mem::size_of::<u16>()
);

impl Default for SlotMetaData {
    fn default() -> Self {
        let mut val = Self(0);
        val.set_priority(DEFAULT_PRIORITY);
        val.set_tries(DEFAULT_RETRIES);

        val
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, AsBytes, FromBytes, FromZeroes)]
#[repr(C, packed)]
struct ControlBits(u16);

impl ControlBits {
    const NB_SLOT_MASK: u16 = 0b111;
    const NB_SLOT_OFFSET: u16 = 0;

    const RECOVERY_TRIES_MASK: u16 = 0b111;
    const RECOVERY_TRIES_OFFSET: u16 = 3;

    const MERGE_STATUS_MASK: u16 = 0b111;
    const MERGE_STATUS_OFFSET: u16 = 6;

    fn nb_slots(&self) -> u8 {
        core::cmp::min(get_field(self.0, Self::NB_SLOT_OFFSET, Self::NB_SLOT_MASK), MAX_SLOTS)
    }
    fn set_nb_slots(&mut self, nb_slots: u8) {
        self.0 = set_field(
            self.0,
            core::cmp::min(nb_slots, MAX_SLOTS),
            Self::NB_SLOT_OFFSET,
            Self::NB_SLOT_MASK,
        );
    }

    fn recovery_tries(&self) -> u8 {
        get_field(self.0, Self::RECOVERY_TRIES_OFFSET, Self::RECOVERY_TRIES_MASK)
    }
    fn set_recovery_tries(&mut self, recovery_tries: u8) {
        self.0 = set_field(
            self.0,
            recovery_tries,
            Self::RECOVERY_TRIES_OFFSET,
            Self::RECOVERY_TRIES_MASK,
        );
    }

    fn merge_status(&self) -> u8 {
        get_field(self.0, Self::MERGE_STATUS_OFFSET, Self::MERGE_STATUS_MASK)
    }
    fn set_merge_status(&mut self, merge_status: u8) {
        self.0 =
            set_field(self.0, merge_status, Self::MERGE_STATUS_OFFSET, Self::MERGE_STATUS_MASK);
    }
}

const BOOT_CTRL_MAGIC: u32 = 0x42414342;
const BOOT_CTRL_VERSION: u8 = 1;

/// The reference implementation for Android A/B bootloader message structures.
/// It is designed to be put in the `slot_suffix` field of the `bootloader_message`
/// structure described bootloader_message.h.
///
/// See //hardware/interfaces/boot/1.1/default/boot_control/libboot_control.cpp
/// and //hardware/interfaces/boot/1.1/default/boot_control/include/private/boot_control_definition.h
/// for structure definition and semantics.
///
/// Does NOT support oneshots
#[repr(C, packed)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, AsBytes, FromBytes, FromZeroes)]
struct BootloaderControl {
    slot_suffix: [u8; 4],
    magic: u32,
    version: u8,
    control_bits: ControlBits,
    reserved0: [u8; 1],
    slot_metadata: [SlotMetaData; MAX_SLOTS as usize],
    reserved1: [u8; 8],
    crc32: LittleEndianU32,
}
static_assertions::const_assert_eq!(core::mem::size_of::<BootloaderControl>(), 32);

impl BootloaderControl {
    fn calculate_crc32(&self) -> u32 {
        let mut hasher = Hasher::new();
        hasher.update(&self.as_bytes()[..(size_of::<Self>() - size_of::<LittleEndianU32>())]);
        hasher.finalize()
    }
}

impl Default for BootloaderControl {
    fn default() -> Self {
        let mut data = Self {
            slot_suffix: Default::default(),
            magic: BOOT_CTRL_MAGIC,
            version: BOOT_CTRL_VERSION,
            control_bits: Default::default(),
            reserved0: Default::default(),
            slot_metadata: Default::default(),
            reserved1: Default::default(),
            crc32: LittleEndianU32::ZERO,
        };
        // The slot suffix field stores the current active slot,
        // which starts as the first one.
        // Notice that it stores the entire suffix,
        // including the leading underscore.
        '_'.encode_utf8(&mut data.slot_suffix[0..]);
        'a'.encode_utf8(&mut data.slot_suffix[1..]);
        data.control_bits.set_nb_slots(4);
        data.crc32.set(data.calculate_crc32());
        data
    }
}

impl MetadataBytes for BootloaderControl {
    fn validate<B: ByteSlice>(buffer: B) -> Result<Ref<B, Self>, Error> {
        let boot_control_data = Ref::<B, Self>::new_from_prefix(buffer)
            .ok_or(Error::BufferTooSmall(Some(size_of::<BootloaderControl>())))?
            .0;

        if boot_control_data.magic != BOOT_CTRL_MAGIC {
            return Err(Error::BadMagic);
        }
        if boot_control_data.version > BOOT_CTRL_VERSION {
            return Err(Error::UnsupportedVersion);
        }
        if boot_control_data.crc32.get() != boot_control_data.calculate_crc32() {
            return Err(Error::BadChecksum);
        }

        Ok(boot_control_data)
    }

    fn prepare_for_sync(&mut self) {
        self.crc32 = self.calculate_crc32().into();
    }
}

impl super::private::SlotGet for SlotBlock<'_, BootloaderControl> {
    fn get_slot_by_number(&self, number: usize) -> Result<Slot, Error> {
        let lower_ascii_suffixes = ('a'..='z').map(Suffix);
        let control = self.get_data();
        let (suffix, &slot_data) = zip(lower_ascii_suffixes, control.slot_metadata.iter())
            // Note: there may be fewer slots than the maximum possible
            .take(control.control_bits.nb_slots().into())
            .nth(number)
            .ok_or(Error::BadIndex(number))?;

        let bootability = match (slot_data.successful(), slot_data.tries()) {
            (true, _) => Bootability::Successful,
            (false, t) if t > 0 => Bootability::Retriable(t.into()),
            (_, _) => Bootability::Unbootable(UnbootableReason::Unknown),
        };

        Ok(Slot { suffix, priority: slot_data.priority().into(), bootability })
    }
}

impl Manager for SlotBlock<'_, BootloaderControl> {
    fn slots_iter(&self) -> SlotIterator {
        SlotIterator::new(self)
    }

    fn get_boot_target(&self) -> Result<BootTarget, Error> {
        Ok(self
            .slots_iter()
            .filter(Slot::is_bootable)
            .max_by_key(|slot| (slot.priority, slot.suffix.rank()))
            .map_or(
                // TODO(b/326253270): how is the recovery slot actually determined?
                BootTarget::Recovery(RecoveryTarget::Slotted(self.get_slot_last_set_active()?)),
                BootTarget::NormalBoot,
            ))
    }

    fn set_slot_unbootable(
        &mut self,
        slot_suffix: Suffix,
        reason: UnbootableReason,
    ) -> Result<(), Error> {
        let (idx, slot) = self
            .slots_iter()
            .enumerate()
            .find(|(_, slot)| slot.suffix == slot_suffix)
            .ok_or(Error::InvalidInput)?;
        if slot.bootability == Bootability::Unbootable(reason) {
            return Ok(());
        }

        let slot_data = &mut self.get_mut_data().slot_metadata[idx];
        slot_data.set_tries(0);
        slot_data.set_successful(false);

        Ok(())
    }

    fn mark_boot_attempt(&mut self) -> Result<BootToken, Error> {
        let target_slot = match self.get_boot_target()? {
            BootTarget::NormalBoot(slot) => slot,
            BootTarget::Recovery(RecoveryTarget::Dedicated) => Err(Error::OperationProhibited)?,
            BootTarget::Recovery(RecoveryTarget::Slotted(slot)) => {
                self.slots_iter().find(|s| s.suffix == slot.suffix).ok_or(Error::InvalidInput)?;
                return self.take_boot_token().ok_or(Error::OperationProhibited);
            }
        };

        let (idx, slot) = self
            .slots_iter()
            .enumerate()
            .find(|(_, slot)| slot.suffix == target_slot.suffix)
            .ok_or(Error::InvalidInput)?;
        match slot.bootability {
            Bootability::Unbootable(_) => Err(Error::OperationProhibited),
            Bootability::Retriable(_) => {
                let metadata = &mut self.get_mut_data().slot_metadata[idx];
                metadata.set_tries(metadata.tries() - 1);
                let token = self.take_boot_token().ok_or(Error::OperationProhibited)?;
                Ok(token)
            }
            Bootability::Successful => {
                let token = self.take_boot_token().ok_or(Error::OperationProhibited)?;
                Ok(token)
            }
        }
    }

    fn set_active_slot(&mut self, slot_suffix: Suffix) -> Result<(), Error> {
        let idx =
            self.slots_iter().position(|s| s.suffix == slot_suffix).ok_or(Error::InvalidInput)?;

        let data = self.get_mut_data();
        for (i, slot) in data.slot_metadata.iter_mut().enumerate() {
            if i == idx {
                *slot = Default::default();
            } else {
                slot.set_priority(DEFAULT_PRIORITY - 1);
            }
        }

        // Note: we know this is safe because the slot suffix is an ASCII char,
        // which is only 1 byte long in utf8.
        // The 0th element of self.data.slot_suffix is an underscore character.
        slot_suffix.0.encode_utf8(&mut self.get_mut_data().slot_suffix[1..]);

        Ok(())
    }

    fn set_oneshot_status(&mut self, _: OneShot) -> Result<(), Error> {
        Err(Error::OperationProhibited)
    }

    fn clear_oneshot_status(&mut self) {}

    fn write_back(&mut self, block_dev: &mut dyn gbl_storage::AsBlockDevice) {
        self.sync_to_disk(block_dev)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::slots::{android::BootloaderControl, partition::MetadataBytes};

    #[test]
    fn test_slot_block_defaults() {
        let sb: SlotBlock<BootloaderControl> = Default::default();
        let expected: Vec<Slot> = ('a'..='d')
            .map(|c| Slot {
                suffix: c.into(),
                priority: DEFAULT_PRIORITY.into(),
                bootability: Bootability::Retriable(sb.get_max_retries().unwrap()),
            })
            .collect();
        let actual: Vec<Slot> = sb.slots_iter().collect();
        assert_eq!(actual, expected);
        assert_eq!(sb.get_oneshot_status(), None);
        assert_eq!(sb.get_boot_target().unwrap(), BootTarget::NormalBoot(expected[0]));
        // Include the explicit null bytes for safety.
        assert_eq!(sb.get_data().slot_suffix.as_slice(), "_a\0\0".as_bytes());
    }

    #[test]
    fn test_slot_block_fewer_slots() {
        let mut sb: SlotBlock<BootloaderControl> = Default::default();
        sb.get_mut_data().control_bits.set_nb_slots(2);

        let expected: Vec<Slot> = ('a'..='b')
            .map(|c| Slot {
                suffix: c.into(),
                priority: DEFAULT_PRIORITY.into(),
                bootability: Bootability::Retriable(sb.get_max_retries().unwrap()),
            })
            .collect();
        let actual: Vec<Slot> = sb.slots_iter().collect();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_slot_block_slot_count_saturates() {
        let mut ctrl: BootloaderControl = Default::default();
        ctrl.control_bits.set_nb_slots(255);
        assert_eq!(ctrl.control_bits.nb_slots(), MAX_SLOTS);

        let mut sb: SlotBlock<BootloaderControl> = Default::default();
        sb.get_mut_data().control_bits.set_nb_slots(255);
        assert_eq!(sb.slots_iter().count(), MAX_SLOTS.into());
    }

    #[test]
    fn test_slot_block_parse() {
        let boot_ctrl: BootloaderControl = Default::default();
        assert_eq!(
            BootloaderControl::validate(boot_ctrl.as_bytes()),
            Ok(Ref::new(boot_ctrl.as_bytes()).unwrap())
        );
    }

    #[test]
    fn test_slot_block_parse_buffer_too_small() {
        let buffer: [u8; 0] = Default::default();
        assert_eq!(
            BootloaderControl::validate(buffer.as_slice()),
            Err(Error::BufferTooSmall(Some(size_of::<BootloaderControl>())))
        );
    }

    #[test]
    fn test_slot_block_parse_bad_magic() {
        let mut boot_ctrl: BootloaderControl = Default::default();
        boot_ctrl.magic += 1;
        assert_eq!(BootloaderControl::validate(boot_ctrl.as_bytes()), Err(Error::BadMagic));
    }

    #[test]
    fn test_slot_block_parse_bad_version() {
        let mut boot_ctrl: BootloaderControl = Default::default();
        boot_ctrl.version = 15;
        assert_eq!(
            BootloaderControl::validate(boot_ctrl.as_bytes()),
            Err(Error::UnsupportedVersion)
        );
    }

    #[test]
    fn test_slot_block_parse_bad_crc() {
        let mut boot_ctrl: BootloaderControl = Default::default();
        let bad_crc = boot_ctrl.crc32.get() ^ LittleEndianU32::MAX_VALUE.get();
        boot_ctrl.crc32 = bad_crc.into();
        assert_eq!(BootloaderControl::validate(boot_ctrl.as_bytes()), Err(Error::BadChecksum));
    }

    #[test]
    fn test_get_boot_target_recovery() {
        let mut sb: SlotBlock<BootloaderControl> = Default::default();
        sb.get_mut_data().slot_metadata.iter_mut().for_each(|bits| bits.set_tries(0));
        let a_slot = sb.slots_iter().next().unwrap();

        assert_eq!(
            sb.get_boot_target().unwrap(),
            BootTarget::Recovery(RecoveryTarget::Slotted(a_slot))
        );
    }

    #[test]
    fn test_get_boot_target_recovery_nondefault_recovery_slot() {
        let mut sb: SlotBlock<BootloaderControl> = Default::default();
        let b_suffix: Suffix = 'b'.into();
        assert!(sb.set_active_slot(b_suffix).is_ok());
        sb.get_mut_data().slot_metadata.iter_mut().for_each(|bits| bits.set_tries(0));
        let b_slot = sb.slots_iter().find(|s| s.suffix == b_suffix).unwrap();

        assert_eq!(
            sb.get_boot_target().unwrap(),
            BootTarget::Recovery(RecoveryTarget::Slotted(b_slot))
        );
    }

    #[test]
    fn test_get_slot_last_set_active() {
        let mut sb: SlotBlock<BootloaderControl> = Default::default();
        let v: Vec<Slot> = sb.slots_iter().collect();
        assert_eq!(sb.set_active_slot(v[1].suffix), Ok(()));
        assert_eq!(sb.get_slot_last_set_active().unwrap(), v[1]);
        for slot in v.iter() {
            assert_eq!(sb.set_slot_unbootable(slot.suffix, UnbootableReason::NoMoreTries), Ok(()));
        }

        assert_eq!(sb.get_slot_last_set_active().unwrap(), sb.slots_iter().nth(1).unwrap());
        assert_eq!(sb.get_data().slot_suffix.as_slice(), "_b\0\0".as_bytes());
    }

    #[test]
    fn test_slot_mark_boot_attempt() {
        let mut sb: SlotBlock<BootloaderControl> = Default::default();
        let slot = Slot { suffix: 'a'.into(), ..Default::default() };
        assert_eq!(sb.mark_boot_attempt(), Ok(BootToken(())));
        assert_eq!(
            sb.slots_iter().next().unwrap(),
            Slot {
                suffix: slot.suffix,
                priority: DEFAULT_PRIORITY.into(),
                bootability: Bootability::Retriable((DEFAULT_RETRIES - 1).into())
            }
        );

        // Make sure we can call exactly once
        assert_eq!(sb.mark_boot_attempt(), Err(Error::OperationProhibited));
    }

    #[test]
    fn test_slot_mark_boot_attempt_no_more_tries() {
        let mut sb: SlotBlock<BootloaderControl> = Default::default();
        sb.get_mut_data().slot_metadata[0].set_tries(1);
        let slot = Slot { suffix: 'a'.into(), ..Default::default() };
        assert_eq!(sb.mark_boot_attempt(), Ok(BootToken(())));
        assert_eq!(
            sb.slots_iter().next().unwrap(),
            Slot {
                suffix: slot.suffix,
                priority: DEFAULT_PRIORITY.into(),
                // Default implementation does not track unbootable reasons
                bootability: Bootability::Unbootable(UnbootableReason::Unknown)
            }
        );
        assert_eq!(sb.get_data().slot_metadata[0].tries(), 0);
    }

    #[test]
    fn test_slot_mark_boot_attempt_successful() {
        let mut sb: SlotBlock<BootloaderControl> = Default::default();
        let initial_tries;
        {
            let metadata = &mut sb.get_mut_data().slot_metadata[0];
            initial_tries = metadata.tries();
            metadata.set_successful(true);
        }
        let target = BootTarget::NormalBoot(Slot {
            suffix: 'a'.into(),
            priority: DEFAULT_PRIORITY.into(),
            bootability: Bootability::Successful,
        });
        assert_eq!(sb.mark_boot_attempt(), Ok(BootToken(())));
        assert_eq!(BootTarget::NormalBoot(sb.slots_iter().next().unwrap()), target);
        assert_eq!(sb.get_data().slot_metadata[0].tries(), initial_tries);
    }

    #[test]
    fn test_mark_slot_tried_slotted_recovery() {
        let mut sb: SlotBlock<BootloaderControl> = Default::default();
        assert!(sb.set_slot_unbootable('a'.into(), UnbootableReason::UserRequested).is_ok());
        assert!(sb.set_slot_unbootable('b'.into(), UnbootableReason::UserRequested).is_ok());
        assert_eq!(sb.mark_boot_attempt(), Ok(BootToken(())));
    }

    #[test]
    fn test_set_oneshot_status_unsupported() {
        let mut sb: SlotBlock<BootloaderControl> = Default::default();
        let oneshots = [
            OneShot::Bootloader,
            OneShot::Continue(RecoveryTarget::Dedicated),
            OneShot::Continue(RecoveryTarget::Slotted(sb.get_slot_last_set_active().unwrap())),
        ];

        for oneshot in oneshots {
            assert_eq!(sb.set_oneshot_status(oneshot), Err(Error::OperationProhibited));
        }
    }
}
