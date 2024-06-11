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

extern crate bitflags;
extern crate crc32fast;
extern crate zerocopy;

use super::partition::{MetadataBytes, MetadataParseError, SlotBlock};
use super::{
    BootTarget, BootToken, Bootability, Error, Manager, OneShot, RecoveryTarget, Slot,
    SlotIterator, Suffix, UnbootableReason,
};
use bitflags::bitflags;
use core::iter::zip;
use core::mem::size_of;
use crc32fast::Hasher;
use zerocopy::byteorder::big_endian::U32 as BigEndianU32;
use zerocopy::{AsBytes, ByteSlice, FromBytes, FromZeroes, Ref};

const DEFAULT_PRIORITY: u8 = 15;
const DEFAULT_RETRIES: u8 = 7;

#[repr(C, packed)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, AsBytes, FromBytes, FromZeroes)]
struct AbrSlotData {
    priority: u8,
    tries: u8,
    successful: u8,
    unbootable_reason: u8,
}

impl Default for AbrSlotData {
    fn default() -> Self {
        Self {
            priority: DEFAULT_PRIORITY,
            tries: DEFAULT_RETRIES,
            successful: 0,
            unbootable_reason: 0,
        }
    }
}

#[repr(C, packed)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, AsBytes, FromBytes, FromZeroes)]
struct OneShotFlags(u8);

bitflags! {
    impl OneShotFlags: u8 {
        /// No oneshot specified
        const NONE = 0;
        /// Oneshot boot to recovery mode
        const RECOVERY = 1 << 0;
        /// Oneshot boot to fastboot
        const BOOTLOADER = 1 << 1;
    }
}

impl From<OneShotFlags> for Option<OneShot> {
    fn from(flags: OneShotFlags) -> Self {
        match flags {
            OneShotFlags::RECOVERY => Some(OneShot::Continue(RecoveryTarget::Dedicated)),
            OneShotFlags::BOOTLOADER => Some(OneShot::Bootloader),
            _ => None,
        }
    }
}

impl From<Option<OneShot>> for OneShotFlags {
    fn from(oneshot: Option<OneShot>) -> Self {
        if let Some(target) = oneshot {
            match target {
                OneShot::Bootloader => Self::BOOTLOADER,
                OneShot::Continue(RecoveryTarget::Dedicated) => Self::RECOVERY,
                _ => Self::NONE,
            }
        } else {
            Self::NONE
        }
    }
}

const ABR_MAGIC: &[u8; 4] = b"\0AB0";
const ABR_VERSION_MAJOR: u8 = 2;
const ABR_VERSION_MINOR: u8 = 3;

#[repr(C, packed)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, AsBytes, FromBytes, FromZeroes)]
struct AbrData {
    magic: [u8; 4],
    version_major: u8,
    version_minor: u8,
    reserved: [u8; 2],
    slot_data: [AbrSlotData; 2],
    oneshot_flag: OneShotFlags,
    reserved2: [u8; 11],
    crc32: BigEndianU32,
}

impl AbrData {
    fn calculate_crc32(&self) -> u32 {
        let mut hasher = Hasher::new();
        // Note: core::offset_of isn't stable yet,
        // and size_of_val isn't permitted on unaligned structs.
        hasher.update(&self.as_bytes()[..(size_of::<Self>() - size_of::<BigEndianU32>())]);
        hasher.finalize()
    }
}

impl MetadataBytes for AbrData {
    fn validate<B: ByteSlice>(buffer: B) -> Result<Ref<B, AbrData>, MetadataParseError> {
        let abr_data =
            Ref::<B, AbrData>::new_from_prefix(buffer).ok_or(MetadataParseError::BufferTooSmall)?.0;

        if abr_data.magic != *ABR_MAGIC {
            return Err(MetadataParseError::BadMagic);
        }
        if abr_data.version_major > ABR_VERSION_MAJOR {
            return Err(MetadataParseError::BadVersion);
        }
        if abr_data.crc32.get() != abr_data.calculate_crc32() {
            return Err(MetadataParseError::BadChecksum);
        }

        Ok(abr_data)
    }

    fn prepare_for_sync(&mut self) {
        self.version_minor = ABR_VERSION_MINOR;
        self.crc32 = self.calculate_crc32().into();
    }
}

impl Default for AbrData {
    fn default() -> Self {
        let mut data = Self {
            magic: *ABR_MAGIC,
            version_major: ABR_VERSION_MAJOR,
            version_minor: ABR_VERSION_MINOR,
            reserved: Default::default(),
            slot_data: Default::default(),
            oneshot_flag: OneShotFlags::NONE,
            reserved2: Default::default(),
            crc32: BigEndianU32::ZERO,
        };
        data.crc32.set(data.calculate_crc32());
        data
    }
}

impl super::private::SlotGet for SlotBlock<'_, AbrData> {
    fn get_slot_by_number(&self, number: usize) -> Result<Slot, Error> {
        let lower_ascii_suffixes = ('a'..='z').map(Suffix);
        let (suffix, &abr_slot) = zip(lower_ascii_suffixes, self.get_data().slot_data.iter())
            .nth(number)
            .ok_or_else(|| Suffix::try_from(number).map_or(Error::Other, Error::NoSuchSlot))?;

        let bootability = match (abr_slot.successful, abr_slot.tries) {
            (s, _) if s != 0 => Bootability::Successful,
            (0, t) if t > 0 => Bootability::Retriable(t.into()),
            (_, _) => Bootability::Unbootable(abr_slot.unbootable_reason.into()),
        };

        Ok(Slot { suffix, priority: abr_slot.priority.into(), bootability })
    }
}

impl Manager for SlotBlock<'_, AbrData> {
    fn get_boot_target(&self) -> BootTarget {
        self.slots_iter()
            .filter(Slot::is_bootable)
            .max_by_key(|slot| (slot.priority, slot.suffix.rank()))
            .map_or(BootTarget::Recovery(RecoveryTarget::Dedicated), BootTarget::NormalBoot)
    }

    fn slots_iter(&self) -> SlotIterator {
        SlotIterator::new(self)
    }

    fn set_slot_unbootable(
        &mut self,
        slot_suffix: Suffix,
        reason: UnbootableReason,
    ) -> Result<(), Error> {
        let (idx, slot) = self.get_index_and_slot_with_suffix(slot_suffix)?;
        if slot.bootability == Bootability::Unbootable(reason) {
            return Ok(());
        }

        let abr_data = self.get_mut_data();
        let slot_data = &mut abr_data.slot_data[idx];
        slot_data.unbootable_reason = reason.into();
        slot_data.tries = 0;
        slot_data.successful = 0;

        Ok(())
    }

    fn mark_boot_attempt(&mut self) -> Result<BootToken, Error> {
        let target = if let Some(OneShot::Continue(r)) = self.get_oneshot_status() {
            BootTarget::Recovery(r)
        } else {
            self.get_boot_target()
        };
        let target_slot = match target {
            BootTarget::NormalBoot(slot) => slot,
            BootTarget::Recovery(RecoveryTarget::Slotted(_)) => Err(Error::OperationProhibited)?,
            BootTarget::Recovery(RecoveryTarget::Dedicated) => {
                // Even though boot to recovery does not cause a metadata update,
                // we still need to gate access to the boot token.
                return self.take_boot_token().ok_or(Error::OperationProhibited);
            }
        };

        let (idx, slot) = self.get_index_and_slot_with_suffix(target_slot.suffix)?;

        match slot.bootability {
            Bootability::Unbootable(_) => Err(Error::OperationProhibited),
            Bootability::Retriable(_) => {
                let abr_slot = &mut self.get_mut_data().slot_data[idx];
                abr_slot.tries -= 1;
                if abr_slot.tries == 0 {
                    abr_slot.unbootable_reason = UnbootableReason::NoMoreTries.into();
                }
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
        let (idx, _) = self.get_index_and_slot_with_suffix(slot_suffix)?;

        let abr_data = self.get_mut_data();
        for (i, slot) in abr_data.slot_data.iter_mut().enumerate() {
            if i == idx {
                *slot = Default::default();
            } else {
                slot.priority = DEFAULT_PRIORITY - 1;
            }
        }
        Ok(())
    }

    fn get_oneshot_status(&self) -> Option<OneShot> {
        self.get_data().oneshot_flag.into()
    }

    fn set_oneshot_status(&mut self, oneshot: OneShot) -> Result<(), Error> {
        if Some(oneshot) == self.get_oneshot_status() {
            return Ok(());
        }

        let oneshot_flag = OneShotFlags::from(Some(oneshot));
        if oneshot_flag == OneShotFlags::NONE {
            Err(match oneshot {
                OneShot::Continue(RecoveryTarget::Slotted(_)) => Error::OperationProhibited,
                _ => Error::Other,
            })
        } else {
            self.get_mut_data().oneshot_flag = oneshot_flag;
            Ok(())
        }
    }

    fn clear_oneshot_status(&mut self) {
        if self.get_oneshot_status().is_some() {
            self.get_mut_data().oneshot_flag = OneShotFlags::NONE;
        }
    }

    fn write_back<B: gbl_storage::AsBlockDevice>(&mut self, block_dev: &mut B) {
        self.sync_to_disk(block_dev);
    }
}

impl<'a> SlotBlock<'a, AbrData> {
    fn get_index_and_slot_with_suffix(&self, slot_suffix: Suffix) -> Result<(usize, Slot), Error> {
        self.slots_iter()
            .enumerate()
            .find(|(_, s)| s.suffix == slot_suffix)
            .ok_or(Error::NoSuchSlot(slot_suffix))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::slots::{partition::CacheStatus, Cursor};
    use gbl_storage::AsBlockDevice;
    use gbl_storage_testlib::TestBlockDevice;

    #[test]
    fn test_slot_block_defaults() {
        let sb: SlotBlock<AbrData> = Default::default();
        let expected: Vec<Slot> = vec![
            Slot {
                suffix: 'a'.into(),
                priority: DEFAULT_PRIORITY.into(),
                bootability: Bootability::Retriable(sb.get_max_retries()),
            },
            Slot {
                suffix: 'b'.into(),
                priority: DEFAULT_PRIORITY.into(),
                bootability: Bootability::Retriable(sb.get_max_retries()),
            },
        ];
        let actual: Vec<Slot> = sb.slots_iter().collect();
        assert_eq!(actual, expected);
        assert_eq!(sb.get_oneshot_status(), None);
    }

    #[test]
    fn test_suffix() {
        let slot = Slot { suffix: 'a'.into(), ..Default::default() };
        assert_eq!(BootTarget::Recovery(RecoveryTarget::Dedicated).suffix(), 'r'.into());
        assert_eq!(BootTarget::Recovery(RecoveryTarget::Slotted(slot)).suffix(), slot.suffix);
        assert_eq!(BootTarget::NormalBoot(slot).suffix(), slot.suffix);
    }

    #[test]
    fn test_slot_block_parse() {
        let abr: AbrData = Default::default();
        assert_eq!(AbrData::validate(abr.as_bytes()), Ok(Ref::new(abr.as_bytes()).unwrap()));
    }

    #[test]
    fn test_slot_block_parse_buffer_too_small() {
        let buffer: [u8; 0] = Default::default();
        assert_eq!(AbrData::validate(&buffer[..]), Err(MetadataParseError::BufferTooSmall),);
    }

    #[test]
    fn test_slot_block_parse_bad_magic() {
        let mut abr: AbrData = Default::default();
        abr.magic[0] += 1;
        assert_eq!(AbrData::validate(abr.as_bytes()), Err(MetadataParseError::BadMagic));
    }

    #[test]
    fn test_slot_block_parse_bad_version_major() {
        let mut abr: AbrData = Default::default();
        abr.version_major = 15;
        assert_eq!(AbrData::validate(abr.as_bytes()), Err(MetadataParseError::BadVersion));
    }

    #[test]
    fn test_slot_block_parse_bad_crc() {
        let mut abr: AbrData = Default::default();
        let bad_crc = abr.crc32.get() ^ BigEndianU32::MAX_VALUE.get();
        abr.crc32 = bad_crc.into();
        assert_eq!(AbrData::validate(abr.as_bytes()), Err(MetadataParseError::BadChecksum));
    }

    #[test]
    fn test_slot_mark_boot_attempt() {
        let mut sb: SlotBlock<AbrData> = Default::default();
        assert_eq!(sb.mark_boot_attempt(), Ok(BootToken(())));
        assert_eq!(
            sb.slots_iter().next().unwrap(),
            Slot {
                suffix: 'a'.into(),
                priority: DEFAULT_PRIORITY.into(),
                bootability: Bootability::Retriable((DEFAULT_RETRIES - 1).into())
            }
        );

        // Make sure we can call exactly once
        assert_eq!(sb.mark_boot_attempt(), Err(Error::OperationProhibited));
    }

    #[test]
    fn test_slot_mark_boot_attempt_tracks_active() {
        let mut sb: SlotBlock<AbrData> = Default::default();
        assert!(sb.set_active_slot('b'.into()).is_ok());

        assert_eq!(sb.mark_boot_attempt(), Ok(BootToken(())));
        assert_eq!(
            sb.get_boot_target(),
            BootTarget::NormalBoot(Slot {
                suffix: 'b'.into(),
                priority: DEFAULT_PRIORITY.into(),
                bootability: Bootability::Retriable((DEFAULT_RETRIES - 1).into())
            })
        );
    }

    #[test]
    fn test_slot_mark_boot_attempt_no_more_tries() {
        let mut sb: SlotBlock<AbrData> = Default::default();
        sb.get_mut_data().slot_data[0].tries = 1;
        assert_eq!(sb.mark_boot_attempt(), Ok(BootToken(())));
        assert_eq!(
            sb.slots_iter().next().unwrap(),
            Slot {
                suffix: 'a'.into(),
                priority: DEFAULT_PRIORITY.into(),
                bootability: Bootability::Unbootable(UnbootableReason::NoMoreTries)
            }
        );
    }

    #[test]
    fn test_slot_mark_boot_attempt_successful() {
        let mut sb: SlotBlock<AbrData> = Default::default();
        sb.get_mut_data().slot_data[0].successful = 1;
        let target = BootTarget::NormalBoot(Slot {
            suffix: 'a'.into(),
            priority: DEFAULT_PRIORITY.into(),
            bootability: Bootability::Successful,
        });
        assert_eq!(sb.mark_boot_attempt(), Ok(BootToken(())));
        assert_eq!(sb.get_boot_target(), target);
    }

    #[test]
    fn test_slot_mark_tried_recovery() {
        let mut sb: SlotBlock<AbrData> = Default::default();
        let recovery_tgt = BootTarget::Recovery(RecoveryTarget::Dedicated);
        assert!(sb.set_slot_unbootable('a'.into(), UnbootableReason::UserRequested).is_ok());
        assert!(sb.set_slot_unbootable('b'.into(), UnbootableReason::UserRequested).is_ok());
        assert_eq!(sb.mark_boot_attempt(), Ok(BootToken(())));

        // Make sure a second attempt fails due to the moved boot token
        assert_eq!(sb.mark_boot_attempt(), Err(Error::OperationProhibited));
    }

    #[test]
    fn test_slot_mark_tried_recovery_oneshot() {
        let mut sb: SlotBlock<AbrData> = Default::default();
        let tgt = sb.get_boot_target();
        assert!(sb.set_oneshot_status(OneShot::Continue(RecoveryTarget::Dedicated)).is_ok());
        assert_eq!(sb.mark_boot_attempt(), Ok(BootToken(())));

        // Verify that tries weren't decremented
        assert_eq!(sb.get_boot_target(), tgt);
    }

    macro_rules! set_unbootable_tests {
                ($($name:ident: $value:expr,)*) => {
                    $(
                        #[test]
                        fn $name() {
                            let mut sb: SlotBlock<AbrData> = Default::default();
                            let suffix: Suffix = 'a'.into();
                            assert_eq!(sb.set_slot_unbootable(suffix, $value), Ok(()));
                            assert_eq!(sb.slots_iter()
                                       .find(|s| s.suffix == suffix)
                                       .unwrap()
                                       .bootability,
                                       Bootability::Unbootable($value)
                            );
                        }
                    )*
                }
            }

    use UnbootableReason::*;
    set_unbootable_tests! {
        test_set_unbootable_no_more_tries: NoMoreTries,
        test_set_unbootable_system_update: SystemUpdate,
        test_set_unbootable_user_requested: UserRequested,
        test_set_unbootable_verification_failure: VerificationFailure,
        test_set_unbootable_unknown: Unknown,
    }

    #[test]
    fn test_no_bootable_slots_boot_recovery() {
        let mut sb: SlotBlock<AbrData> = Default::default();
        let v: Vec<Slot> = sb.slots_iter().collect();
        for slot in v {
            assert_eq!(
                sb.set_slot_unbootable(slot.suffix, UnbootableReason::UserRequested),
                Ok(())
            );
        }
        assert_eq!(sb.get_boot_target(), BootTarget::Recovery(RecoveryTarget::Dedicated));
    }

    #[test]
    fn test_set_active_slot() {
        let mut sb: SlotBlock<AbrData> = Default::default();
        let v: Vec<Slot> = sb.slots_iter().collect();

        assert_eq!(sb.get_boot_target(), BootTarget::NormalBoot(v[0]));
        for slot in v.iter() {
            assert_eq!(sb.set_active_slot(slot.suffix), Ok(()));
            assert_eq!(sb.get_boot_target(), BootTarget::NormalBoot(*slot));
        }
    }

    #[test]
    fn test_set_active_slot_no_such_slot() {
        let mut sb: SlotBlock<AbrData> = Default::default();
        let bad_suffix: Suffix = '$'.into();
        assert_eq!(sb.set_active_slot(bad_suffix), Err(Error::NoSuchSlot(bad_suffix)));
    }

    #[test]
    fn test_get_slot_last_set_active() {
        let mut sb: SlotBlock<AbrData> = Default::default();
        let v: Vec<Slot> = sb.slots_iter().collect();
        assert_eq!(sb.set_active_slot(v[0].suffix), Ok(()));
        assert_eq!(sb.get_slot_last_set_active(), v[0]);
        for slot in v.iter() {
            assert_eq!(sb.set_slot_unbootable(slot.suffix, NoMoreTries), Ok(()));
        }

        assert_eq!(sb.get_slot_last_set_active(), sb.slots_iter().next().unwrap());
    }

    macro_rules! set_oneshot_tests {
                ($($name:ident: $value:expr,)*) => {
                    $(
                        #[test]
                        fn $name(){
                            let mut sb: SlotBlock<AbrData> = Default::default();
                            assert_eq!(sb.set_oneshot_status($value), Ok(()));
                            assert_eq!(sb.get_oneshot_status(), Some($value));

                            assert_eq!(sb.get_boot_target(),
                                       BootTarget::NormalBoot(
                                           Slot{
                                               suffix: 'a'.into(),
                                               priority: DEFAULT_PRIORITY.into(),
                                               bootability: Bootability::Retriable(sb.get_max_retries()),
                                           },
                                       ));
                        }
                    )*
                }
            }

    set_oneshot_tests! {
        test_set_oneshot_bootloader: OneShot::Bootloader,
        test_set_oneshot_recovery: OneShot::Continue(RecoveryTarget::Dedicated),
    }

    #[test]
    fn test_clear_oneshot_status() {
        let mut sb: SlotBlock<AbrData> = Default::default();
        assert_eq!(sb.set_oneshot_status(OneShot::Bootloader), Ok(()));
        sb.clear_oneshot_status();
        assert_eq!(sb.get_oneshot_status(), None);
    }

    #[test]
    fn test_set_oneshot_mistaken_recovery_slotted() {
        let mut sb: SlotBlock<AbrData> = Default::default();
        let slot = sb.slots_iter().next().unwrap();
        assert_eq!(
            sb.set_oneshot_status(OneShot::Continue(RecoveryTarget::Slotted(slot))),
            Err(Error::OperationProhibited)
        );
    }

    #[test]
    fn test_deserialize_default_to_dirty_cache() {
        let mut abr_data: AbrData = Default::default();
        // Changing the success both invalidates the crc
        // and lets us verify that the deserialized slot block
        // uses defaulted backing bytes instead of the provided bytes.
        abr_data.slot_data[0].successful = 1;
        let sb = SlotBlock::<AbrData>::deserialize(
            abr_data.as_bytes(),
            "partition_moniker",
            0,
            BootToken(()),
        );
        assert_eq!(sb.cache_status(), CacheStatus::Dirty);
        assert_eq!(
            sb.slots_iter().next().unwrap().bootability,
            Bootability::Retriable(DEFAULT_RETRIES.into())
        );
    }

    #[test]
    fn test_deserialize_modified_to_clean_cache() {
        let mut abr_data: AbrData = Default::default();
        abr_data.slot_data[0].successful = 1;
        // If we recalculate the crc,
        // that just means we have a metadata block that stores
        // relevant, non-default information.
        abr_data.crc32.set(abr_data.calculate_crc32());
        let sb = SlotBlock::<AbrData>::deserialize(
            abr_data.as_bytes(),
            "partition_moniker",
            0,
            BootToken(()),
        );
        assert_eq!(sb.cache_status(), CacheStatus::Clean);
        assert_eq!(sb.slots_iter().next().unwrap().bootability, Bootability::Successful);
    }

    #[test]
    fn test_writeback() {
        const PARTITION: &str = "test_partition";
        const OFFSET: u64 = 2112; // Deliberately wrong to test propagation of parameter.
        let mut block_dev: TestBlockDevice =
            include_bytes!("../../testdata/writeback_test_disk.bin").as_slice().into();
        assert!(block_dev.sync_gpt().is_ok());
        let mut sb: SlotBlock<AbrData> = Default::default();
        sb.partition = PARTITION;
        sb.partition_offset = OFFSET;

        let mut read_buffer: [u8; size_of::<AbrData>()] = Default::default();

        // Clean cache, write_back is a no-op
        sb.write_back(&mut block_dev);
        let res = block_dev.read_gpt_partition(PARTITION, OFFSET, &mut read_buffer);
        assert!(res.is_ok());
        assert_eq!(read_buffer, [0; std::mem::size_of::<AbrData>()]);

        // Make a change, write_back writes back to the defined partition
        // at the defined offset.
        assert_eq!(sb.set_oneshot_status(OneShot::Bootloader), Ok(()));
        assert_eq!(sb.cache_status(), CacheStatus::Dirty);

        sb.write_back(&mut block_dev);
        let res = block_dev.read_gpt_partition(PARTITION, OFFSET, &mut read_buffer);
        assert!(res.is_ok());
        assert_eq!(read_buffer, sb.get_data().as_bytes());
        assert_eq!(sb.cache_status(), CacheStatus::Clean);
    }

    #[test]
    fn test_writeback_with_cursor() {
        const PARTITION: &str = "test_partition";
        const OFFSET: u64 = 2112; // Deliberately wrong to test propagation of parameter.
        let mut block_dev: TestBlockDevice =
            include_bytes!("../../testdata/writeback_test_disk.bin").as_slice().into();
        assert!(block_dev.sync_gpt().is_ok());
        let mut read_buffer: [u8; size_of::<AbrData>()] = Default::default();
        let mut abr_data;

        let mut sb: SlotBlock<AbrData> = Default::default();
        sb.partition = PARTITION;
        sb.partition_offset = OFFSET;

        // New block to trigger drop on the cursor.
        {
            let mut cursor = Cursor { ctx: sb, block_dev: &mut block_dev };
            assert!(cursor.ctx.set_active_slot('b'.into()).is_ok());
            abr_data = cursor.ctx.get_data().clone();
        }

        // Need to manually recalculate crc because the cursor updates that
        // right before writing to disk.
        abr_data.prepare_for_sync();
        let res = block_dev.read_gpt_partition(PARTITION, OFFSET, &mut read_buffer);
        assert!(res.is_ok());
        assert_eq!(read_buffer, abr_data.as_bytes());
    }
}
