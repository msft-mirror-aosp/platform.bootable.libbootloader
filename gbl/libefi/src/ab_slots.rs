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

extern crate gbl_storage;
extern crate libgbl as gbl;

use core::convert::TryInto;

pub use gbl::slots::Error;
use gbl::slots::{
    BootTarget, BootToken, Manager, OneShot, RecoveryTarget, Slot, SlotIterator, Suffix, Tries,
    UnbootableReason,
};

use crate::defs::{
    EFI_BOOT_REASON_BOOTLOADER, EFI_BOOT_REASON_EMPTY_EFI_BOOT_REASON, EFI_BOOT_REASON_RECOVERY,
};
use crate::protocol::{ab_slot, Protocol};
use crate::ErrorTypes;

const SUBREASON_BUF_LEN: usize = 64;

/// Implementation for A/B slot manager based on custom EFI protocol.
pub struct ABManager<'a> {
    protocol: Protocol<'a, ab_slot::GblSlotProtocol>,
    boot_token: Option<BootToken>,
    last_set_active_idx: Option<u8>,
}

impl<'a> ABManager<'a> {
    #[cfg(test)]
    fn new_without_token(protocol: Protocol<'a, ab_slot::GblSlotProtocol>) -> Self {
        Self { protocol, boot_token: None, last_set_active_idx: None }
    }
}

impl gbl::slots::private::SlotGet for ABManager<'_> {
    fn get_slot_by_number(&self, number: usize) -> Result<Slot, Error> {
        let idx = u8::try_from(number).or(Err(Error::BadSlotIndex(number)))?;
        let info = self.protocol.get_slot_info(idx).map_err(|e| match e.err() {
            ErrorTypes::Unknown => Error::Other,
            _ => Error::BadSlotIndex(number),
        })?;
        info.try_into()
    }
}

impl Manager for ABManager<'_> {
    fn get_boot_target(&self) -> Result<BootTarget, Error> {
        let slot = self.get_slot_last_set_active()?;
        let mut subreason = [0u8; SUBREASON_BUF_LEN];
        let (reason, _) = self.protocol.get_boot_reason(subreason.as_mut_slice())?;
        // Don't currently care about the subreason
        // CStr::from_bytes_until_nul(&subreason[..strlen])?
        let target = match reason {
            EFI_BOOT_REASON_RECOVERY => BootTarget::Recovery(RecoveryTarget::Slotted(slot)),
            _ => BootTarget::NormalBoot(slot),
        };
        Ok(target)
    }

    fn slots_iter(&self) -> SlotIterator {
        SlotIterator::new(self)
    }

    fn get_slot_last_set_active(&self) -> Result<Slot, Error> {
        use gbl::slots::private::SlotGet;

        if let Some(idx) = self.last_set_active_idx {
            self.get_slot_by_number(idx.into())
        } else {
            self.protocol.get_current_slot()?.try_into()
        }
    }

    fn mark_boot_attempt(&mut self) -> Result<BootToken, Error> {
        self.protocol.mark_boot_attempt().or(Err(Error::OperationProhibited))?;
        self.boot_token.take().ok_or(Error::OperationProhibited)
    }

    fn set_active_slot(&mut self, slot_suffix: Suffix) -> Result<(), Error> {
        let idx: u8 = self
            .slots_iter()
            .position(|s| s.suffix == slot_suffix)
            .ok_or(Error::NoSuchSlot(slot_suffix))?
            .try_into()
            // This 'or' is technically unreachable because the protocol
            // can't give us an index larger than a u8.
            .or(Err(Error::Other))?;
        self.protocol.set_active_slot(idx).or(Err(Error::Other)).and_then(|_| {
            self.last_set_active_idx = Some(idx);
            Ok(())
        })
    }

    fn set_slot_unbootable(
        &mut self,
        slot_suffix: Suffix,
        reason: UnbootableReason,
    ) -> Result<(), Error> {
        let idx: u8 = self
            .slots_iter()
            .position(|s| s.suffix == slot_suffix)
            .ok_or(Error::NoSuchSlot(slot_suffix))?
            .try_into()
            // This 'or' is technically unreachable because the protocol
            // can't give us an index larger than a u8.
            .or(Err(Error::Other))?;
        self.protocol.set_slot_unbootable(idx, u8::from(reason).into()).or(Err(Error::Other))
    }

    fn get_max_retries(&self) -> Result<Tries, Error> {
        Ok(self.protocol.load_boot_data()?.max_retries.into())
    }

    fn get_oneshot_status(&self) -> Option<OneShot> {
        let mut subreason = [0u8; SUBREASON_BUF_LEN];
        let (reason, _) = self.protocol.get_boot_reason(subreason.as_mut_slice()).ok()?;
        // Currently we only care if the primary boot reason is BOOTLOADER.
        // CStr::from_bytes_until_nul(&subreason[..strlen]).ok()?
        match reason {
            EFI_BOOT_REASON_BOOTLOADER => Some(OneShot::Bootloader),
            _ => None,
        }
    }

    fn set_oneshot_status(&mut self, os: OneShot) -> Result<(), Error> {
        // Android doesn't have a concept of OneShot to recovery,
        // and the subreason shouldn't matter.
        match os {
            OneShot::Bootloader => {
                self.protocol.set_boot_reason(EFI_BOOT_REASON_BOOTLOADER, &[]).or(Err(Error::Other))
            }
            _ => Err(Error::OperationProhibited),
        }
    }

    fn clear_oneshot_status(&mut self) {
        let mut subreason = [0u8; SUBREASON_BUF_LEN];
        // Only clear if the boot reason is the one we care about.
        // CStr::from_bytes_until_nul(&subreason[..strlen]).or(Err(Error::Other))?
        if let Ok((EFI_BOOT_REASON_BOOTLOADER, _)) =
            self.protocol.get_boot_reason(subreason.as_mut_slice())
        {
            let _ = self.protocol.set_boot_reason(EFI_BOOT_REASON_EMPTY_EFI_BOOT_REASON, &[]);
        }
    }

    fn write_back(&mut self, _: &mut dyn gbl_storage::AsBlockDevice) {
        // Note: `expect` instead of swallowing the error.
        // It is important that changes are not silently dropped.
        self.protocol.flush().expect("could not write back modifications to slot metadata");
    }
}

#[cfg(test)]
mod test {
    extern crate avb_sysdeps;

    use super::*;
    use crate::defs::{
        EfiGblSlotInfo, EfiGblSlotMetadataBlock, EfiGblSlotProtocol, EfiStatus,
        EFI_BOOT_REASON_EMPTY_EFI_BOOT_REASON, EFI_BOOT_REASON_RECOVERY, EFI_BOOT_REASON_WATCHDOG,
        EFI_STATUS_INVALID_PARAMETER, EFI_STATUS_SUCCESS,
    };
    use crate::protocol::{Protocol, ProtocolInfo};
    use crate::test::*;
    use crate::{DeviceHandle, EfiEntry};
    use core::ptr::null_mut;
    use gbl::slots::{Bootability, Cursor, RecoveryTarget, UnbootableReason};
    use gbl::{Gbl, GblOps, Result as GblResult};
    use gbl_storage_testlib::TestBlockDevice;
    // TODO(b/350526796): use ptr.is_aligned() when Rust 1.79 is in Android
    use std::mem::align_of;
    use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};

    // The thread-local atomics are an ugly, ugly hack to pass state between
    // the protocol method functions and the rest of the test body.
    // Because the variables are thread-local, it is safe to run tests concurrently
    // so long as they establish correct initial values.
    // Also, because no atomic is being read or written to by more than one thread,
    // Ordering::Relaxed is perfectly fine.
    thread_local! {
        static ATOMIC: AtomicBool = AtomicBool::new(false);
    }

    thread_local! {
        static BOOT_REASON: AtomicU32 = AtomicU32::new(EFI_BOOT_REASON_EMPTY_EFI_BOOT_REASON);
    }

    // This provides reasonable defaults for all tests that need to get slot info.
    //
    // SAFETY: checks that `info` is properly aligned and not null.
    // Caller must make sure `info` points to a valid EfiGblSlotInfo struct.
    unsafe extern "C" fn get_info(
        _: *mut EfiGblSlotProtocol,
        idx: u8,
        info: *mut EfiGblSlotInfo,
    ) -> EfiStatus {
        // TODO(b/350526796): use ptr.is_aligned() when Rust 1.79 is in Android
        if !info.is_null() && (info as usize) % align_of::<EfiGblSlotInfo>() == 0 && idx < 3 {
            let slot_info = EfiGblSlotInfo {
                suffix: ('a' as u8 + idx).into(),
                unbootable_reason: 0,
                priority: idx + 1,
                tries: idx,
                successful: 2 & idx,
                merge_status: 0,
            };
            unsafe { *info = slot_info };
            EFI_STATUS_SUCCESS
        } else {
            EFI_STATUS_INVALID_PARAMETER
        }
    }

    extern "C" fn flush(_: *mut EfiGblSlotProtocol) -> EfiStatus {
        ATOMIC.with(|a| a.store(true, Ordering::Relaxed));
        EFI_STATUS_SUCCESS
    }

    struct TestGblOps<'a> {
        manager: ABManager<'a>,
    }

    impl<'a> TestGblOps<'a> {
        fn new(protocol: Protocol<'a, ab_slot::GblSlotProtocol>) -> Self {
            Self { manager: ABManager::new_without_token(protocol) }
        }
    }

    impl<'b> GblOps for TestGblOps<'b> {
        fn load_slot_interface<'a, B: gbl_storage::AsBlockDevice>(
            &'a mut self,
            block_dev: &'a mut B,
            boot_token: BootToken,
        ) -> GblResult<Cursor<'a, B>> {
            self.manager.boot_token = Some(boot_token);
            Ok(Cursor { ctx: &mut self.manager, block_dev })
        }
    }

    fn generate_protocol<'a, P: ProtocolInfo>(
        efi_entry: &'a EfiEntry,
        proto: &'a mut P::InterfaceType,
    ) -> Protocol<'a, P> {
        // SAFETY: proto is a valid pointer and lasts at least as long as efi_entry.
        unsafe { Protocol::<'a, P>::new(DeviceHandle::new(null_mut()), proto, efi_entry) }
    }

    #[test]
    fn test_manager_flush_on_close() {
        ATOMIC.with(|a| a.store(false, Ordering::Relaxed));
        run_test(|image_handle, systab_ptr| {
            let mut ab = EfiGblSlotProtocol { flush: Some(flush), ..Default::default() };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol = generate_protocol::<ab_slot::GblSlotProtocol>(&efi_entry, &mut ab);

            {
                let mut block_device: TestBlockDevice = Default::default();
                let mut test_ops = TestGblOps::new(protocol);
                let mut gbl = Gbl::<TestGblOps>::new(&mut test_ops);
                let _ = gbl.load_slot_interface(&mut block_device).unwrap();
            }
        });
        assert!(ATOMIC.with(|a| a.load(Ordering::Relaxed)));
    }

    #[test]
    fn test_iterator() {
        run_test(|image_handle, systab_ptr| {
            let mut ab = EfiGblSlotProtocol {
                get_slot_info: Some(get_info),
                flush: Some(flush),
                ..Default::default()
            };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol = generate_protocol::<ab_slot::GblSlotProtocol>(&efi_entry, &mut ab);
            let mut block_device: TestBlockDevice = Default::default();
            let mut test_ops = TestGblOps::new(protocol);
            let mut gbl = Gbl::<TestGblOps>::new(&mut test_ops);
            let cursor = gbl.load_slot_interface(&mut block_device).unwrap();

            let slots: Vec<Slot> = cursor.ctx.slots_iter().collect();
            assert_eq!(
                slots,
                vec![
                    Slot {
                        suffix: 'a'.into(),
                        priority: 1usize.into(),
                        bootability: Bootability::Unbootable(UnbootableReason::Unknown),
                    },
                    Slot {
                        suffix: 'b'.into(),
                        priority: 2usize.into(),
                        bootability: Bootability::Retriable(1usize.into()),
                    },
                    Slot {
                        suffix: 'c'.into(),
                        priority: 3usize.into(),
                        bootability: Bootability::Successful,
                    }
                ]
            )
        });
    }

    #[test]
    fn test_active_slot() {
        // SAFETY: verfies that `info` properly aligned and not null.
        // It is the callers responsibility to make sure
        // that `info` points to a valid EfiGblSlotInfo.
        unsafe extern "C" fn get_current_slot(
            _: *mut EfiGblSlotProtocol,
            info: *mut EfiGblSlotInfo,
        ) -> EfiStatus {
            // TODO(b/350526796): use ptr.is_aligned() when Rust 1.79 is in Android
            if info.is_null() || (info as usize) % align_of::<EfiGblSlotInfo>() != 0 {
                return EFI_STATUS_INVALID_PARAMETER;
            }
            let slot_info = EfiGblSlotInfo {
                suffix: 'a' as u32,
                unbootable_reason: 0,
                priority: 7,
                tries: 15,
                successful: 1,
                merge_status: 0,
            };

            unsafe { *info = slot_info };
            EFI_STATUS_SUCCESS
        }

        // SAFETY: verifies that `reason` and `subreason_size` are aligned and not null.
        // It is the caller's responsibility to make sure that `reason`
        // and `subreason_size` point to valid output parameters.
        unsafe extern "C" fn get_boot_reason(
            _: *mut EfiGblSlotProtocol,
            reason: *mut u32,
            subreason_size: *mut usize,
            _subreason: *mut u8,
        ) -> EfiStatus {
            if reason.is_null()
                || subreason_size.is_null()
            // TODO(b/350526796): use ptr.is_aligned() when Rust 1.79 is in Android
                || (reason as usize) % align_of::<u32>() != 0
                || (subreason_size as usize) % align_of::<usize>() != 0
            {
                return EFI_STATUS_INVALID_PARAMETER;
            }

            unsafe {
                *reason = BOOT_REASON.with(|r| r.load(Ordering::Relaxed));
                *subreason_size = 0;
            }
            EFI_STATUS_SUCCESS
        }

        BOOT_REASON.with(|r| r.store(EFI_BOOT_REASON_EMPTY_EFI_BOOT_REASON, Ordering::Relaxed));
        run_test(|image_handle, systab_ptr| {
            let mut ab = EfiGblSlotProtocol {
                get_current_slot: Some(get_current_slot),
                get_boot_reason: Some(get_boot_reason),
                flush: Some(flush),
                ..Default::default()
            };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol = generate_protocol::<ab_slot::GblSlotProtocol>(&efi_entry, &mut ab);
            let mut block_device: TestBlockDevice = Default::default();
            let mut test_ops = TestGblOps::new(protocol);
            let mut gbl = Gbl::<TestGblOps>::new(&mut test_ops);
            let cursor = gbl.load_slot_interface(&mut block_device).unwrap();

            let slot = Slot {
                suffix: 'a'.into(),
                priority: 7usize.into(),
                bootability: Bootability::Successful,
            };
            assert_eq!(cursor.ctx.get_boot_target().unwrap(), BootTarget::NormalBoot(slot));
            assert_eq!(cursor.ctx.get_slot_last_set_active().unwrap(), slot);

            BOOT_REASON.with(|r| r.store(EFI_BOOT_REASON_RECOVERY, Ordering::Relaxed));

            assert_eq!(
                cursor.ctx.get_boot_target().unwrap(),
                BootTarget::Recovery(RecoveryTarget::Slotted(slot))
            );
        });
    }

    #[test]
    fn test_mark_boot_attempt() {
        extern "C" fn mark_boot_attempt(_: *mut EfiGblSlotProtocol) -> EfiStatus {
            ATOMIC.with(|a| a.store(true, Ordering::Relaxed));
            EFI_STATUS_SUCCESS
        }

        ATOMIC.with(|a| a.store(false, Ordering::Relaxed));
        run_test(|image_handle, systab_ptr| {
            let mut ab = EfiGblSlotProtocol {
                mark_boot_attempt: Some(mark_boot_attempt),
                flush: Some(flush),
                ..Default::default()
            };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol = generate_protocol::<ab_slot::GblSlotProtocol>(&efi_entry, &mut ab);
            let mut block_device: TestBlockDevice = Default::default();
            let mut test_ops = TestGblOps::new(protocol);
            let mut gbl = Gbl::<TestGblOps>::new(&mut test_ops);
            let cursor = gbl.load_slot_interface(&mut block_device).unwrap();
            assert!(cursor.ctx.mark_boot_attempt().is_ok());
            assert!(ATOMIC.with(|a| a.load(Ordering::Relaxed)));

            assert_eq!(cursor.ctx.mark_boot_attempt(), Err(gbl::slots::Error::OperationProhibited));
        });
    }

    #[test]
    fn test_get_max_retries() {
        // SAFETY: verifies that `meta` is properly aligned and not null.
        // It is the caller's responsibility to make sure that `meta` points to
        // a valid EfiGblSlotMetadataBlock.
        unsafe extern "C" fn load_boot_data(
            _: *mut EfiGblSlotProtocol,
            meta: *mut EfiGblSlotMetadataBlock,
        ) -> EfiStatus {
            // TODO(b/350526796): use ptr.is_aligned() when Rust 1.79 is in Android
            if meta.is_null() || (meta as usize) % align_of::<EfiGblSlotMetadataBlock>() != 0 {
                return EFI_STATUS_INVALID_PARAMETER;
            }

            let meta_block = EfiGblSlotMetadataBlock {
                unbootable_metadata: 1,
                max_retries: 66,
                slot_count: 32, // why not?
            };

            unsafe { *meta = meta_block };
            EFI_STATUS_SUCCESS
        }

        run_test(|image_handle, systab_ptr| {
            let mut ab = EfiGblSlotProtocol {
                load_boot_data: Some(load_boot_data),
                flush: Some(flush),
                ..Default::default()
            };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol = generate_protocol::<ab_slot::GblSlotProtocol>(&efi_entry, &mut ab);
            let mut block_device: TestBlockDevice = Default::default();
            let mut test_ops = TestGblOps::new(protocol);
            let mut gbl = Gbl::<TestGblOps>::new(&mut test_ops);
            let cursor = gbl.load_slot_interface(&mut block_device).unwrap();
            assert_eq!(cursor.ctx.get_max_retries().unwrap(), 66usize.into());
        });
    }

    #[test]
    fn test_set_active_slot() {
        extern "C" fn set_active_slot(_: *mut EfiGblSlotProtocol, idx: u8) -> EfiStatus {
            // This is deliberate: we want to make sure that other logic catches
            // 'no such slot' first but we also want to verify that errors propagate.
            if idx != 2 {
                EFI_STATUS_SUCCESS
            } else {
                EFI_STATUS_INVALID_PARAMETER
            }
        }

        run_test(|image_handle, systab_ptr| {
            let mut ab = EfiGblSlotProtocol {
                get_slot_info: Some(get_info),
                set_active_slot: Some(set_active_slot),
                flush: Some(flush),
                ..Default::default()
            };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol = generate_protocol::<ab_slot::GblSlotProtocol>(&efi_entry, &mut ab);
            let mut block_device: TestBlockDevice = Default::default();
            let mut test_ops = TestGblOps::new(protocol);
            let mut gbl = Gbl::<TestGblOps>::new(&mut test_ops);
            let cursor = gbl.load_slot_interface(&mut block_device).unwrap();

            assert_eq!(cursor.ctx.set_active_slot('b'.into()), Ok(()));
            assert_eq!(cursor.ctx.set_active_slot('c'.into()), Err(Error::Other));

            let bad_suffix = '$'.into();
            assert_eq!(cursor.ctx.set_active_slot(bad_suffix), Err(Error::NoSuchSlot(bad_suffix)));
        });
    }

    #[test]
    fn test_set_slot_unbootable() {
        extern "C" fn set_slot_unbootable(
            _: *mut EfiGblSlotProtocol,
            idx: u8,
            _: u32,
        ) -> EfiStatus {
            // Same thing here as with set_active_slot.
            // We want to make sure that iteration over the slots
            // catches invalid suffixes, but we also want to make sure
            // that errors from the protocol percolate up.
            if idx == 0 {
                EFI_STATUS_SUCCESS
            } else {
                EFI_STATUS_INVALID_PARAMETER
            }
        }

        run_test(|image_handle, systab_ptr| {
            let mut ab = EfiGblSlotProtocol {
                get_slot_info: Some(get_info),
                set_slot_unbootable: Some(set_slot_unbootable),
                flush: Some(flush),
                ..Default::default()
            };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol = generate_protocol::<ab_slot::GblSlotProtocol>(&efi_entry, &mut ab);
            let mut block_device: TestBlockDevice = Default::default();
            let mut test_ops = TestGblOps::new(protocol);
            let mut gbl = Gbl::<TestGblOps>::new(&mut test_ops);
            let cursor = gbl.load_slot_interface(&mut block_device).unwrap();

            assert_eq!(
                cursor.ctx.set_slot_unbootable('a'.into(), UnbootableReason::SystemUpdate),
                Ok(())
            );

            assert_eq!(
                cursor.ctx.set_slot_unbootable('b'.into(), UnbootableReason::UserRequested),
                Err(Error::Other)
            );

            let bad_suffix = '$'.into();
            assert_eq!(
                cursor.ctx.set_slot_unbootable(bad_suffix, UnbootableReason::NoMoreTries),
                Err(Error::NoSuchSlot(bad_suffix))
            );
        });
    }

    #[test]
    fn test_oneshot() {
        // SAFETY: checks that `reason` is not null and is properly aligned.
        // Caller must make sure reason points to a valid u32.
        unsafe extern "C" fn get_boot_reason(
            _: *mut EfiGblSlotProtocol,
            reason: *mut u32,
            _: *mut usize,
            _: *mut u8,
        ) -> EfiStatus {
            // TODO(b/350526796): use ptr.is_aligned() when Rust 1.79 is in Android
            if reason.is_null() || (reason as usize) % align_of::<u32>() != 0 {
                return EFI_STATUS_INVALID_PARAMETER;
            }

            unsafe { *reason = BOOT_REASON.with(|r| r.load(Ordering::Relaxed)) };

            EFI_STATUS_SUCCESS
        }

        extern "C" fn set_boot_reason(
            _: *mut EfiGblSlotProtocol,
            reason: u32,
            _: usize,
            _: *const u8,
        ) -> EfiStatus {
            BOOT_REASON.with(|r| r.store(reason, Ordering::Relaxed));
            EFI_STATUS_SUCCESS
        }

        BOOT_REASON.with(|r| r.store(EFI_BOOT_REASON_EMPTY_EFI_BOOT_REASON, Ordering::Relaxed));
        run_test(|image_handle, systab_ptr| {
            let mut ab = EfiGblSlotProtocol {
                get_boot_reason: Some(get_boot_reason),
                set_boot_reason: Some(set_boot_reason),
                flush: Some(flush),
                ..Default::default()
            };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol = generate_protocol::<ab_slot::GblSlotProtocol>(&efi_entry, &mut ab);
            let mut block_device: TestBlockDevice = Default::default();
            let mut test_ops = TestGblOps::new(protocol);
            let mut gbl = Gbl::<TestGblOps>::new(&mut test_ops);
            let cursor = gbl.load_slot_interface(&mut block_device).unwrap();

            assert_eq!(cursor.ctx.get_oneshot_status(), None);
            assert_eq!(
                cursor.ctx.set_oneshot_status(OneShot::Continue(RecoveryTarget::Dedicated)),
                Err(gbl::slots::Error::OperationProhibited)
            );
            assert_eq!(cursor.ctx.set_oneshot_status(OneShot::Bootloader), Ok(()));
            assert_eq!(cursor.ctx.get_oneshot_status(), Some(OneShot::Bootloader));

            cursor.ctx.clear_oneshot_status();
            assert_eq!(cursor.ctx.get_oneshot_status(), None);

            BOOT_REASON.with(|r| r.store(EFI_BOOT_REASON_WATCHDOG, Ordering::Relaxed));
            assert_eq!(cursor.ctx.get_oneshot_status(), None);
            cursor.ctx.clear_oneshot_status();
            assert_eq!(BOOT_REASON.with(|r| r.load(Ordering::Relaxed)), EFI_BOOT_REASON_WATCHDOG);
        });
    }
}
