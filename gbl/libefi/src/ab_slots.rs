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
use gbl::slots::{
    BootTarget, BootToken, Manager, OneShot, RecoveryTarget, Slot, SlotIterator, Suffix, Tries,
    UnbootableReason,
};
use liberror::{Error, Result};

use efi_types::{
    GBL_EFI_BOOT_REASON_GBL_EFI_BOOTLOADER as REASON_BOOTLOADER,
    GBL_EFI_BOOT_REASON_GBL_EFI_EMPTY_BOOT_REASON as REASON_EMPTY,
    GBL_EFI_BOOT_REASON_GBL_EFI_RECOVERY as REASON_RECOVERY,
};

use crate::protocol::{gbl_efi_ab_slot as ab_slot, Protocol};

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
    fn get_slot_by_number(&self, number: usize) -> Result<Slot> {
        let idx = u8::try_from(number).or(Err(Error::BadIndex(number)))?;
        let info = self.protocol.get_slot_info(idx).or(Err(Error::BadIndex(number)))?;
        info.try_into()
    }
}

impl Manager for ABManager<'_> {
    fn get_boot_target(&self) -> Result<BootTarget> {
        let slot = self.get_slot_last_set_active()?;
        let mut subreason = [0u8; SUBREASON_BUF_LEN];
        let (reason, _) = self.protocol.get_boot_reason(subreason.as_mut_slice())?;
        // Don't currently care about the subreason
        // CStr::from_bytes_until_nul(&subreason[..strlen])?
        let target = match reason {
            REASON_RECOVERY => BootTarget::Recovery(RecoveryTarget::Slotted(slot)),
            _ => BootTarget::NormalBoot(slot),
        };
        Ok(target)
    }

    fn slots_iter(&self) -> SlotIterator {
        SlotIterator::new(self)
    }

    fn get_slot_last_set_active(&self) -> Result<Slot> {
        use gbl::slots::private::SlotGet;

        if let Some(idx) = self.last_set_active_idx {
            self.get_slot_by_number(idx.into())
        } else {
            self.protocol.get_current_slot()?.try_into()
        }
    }

    fn mark_boot_attempt(&mut self) -> Result<BootToken> {
        self.protocol.mark_boot_attempt().or(Err(Error::OperationProhibited))?;
        self.boot_token.take().ok_or(Error::OperationProhibited)
    }

    fn set_active_slot(&mut self, slot_suffix: Suffix) -> Result<()> {
        let idx: u8 = self
            .slots_iter()
            .position(|s| s.suffix == slot_suffix)
            .ok_or(Error::InvalidInput)?
            .try_into()
            // This 'or' is technically unreachable because the protocol
            // can't give us an index larger than a u8.
            .or(Err(Error::Other(None)))?;
        self.protocol.set_active_slot(idx).or(Err(Error::Other(None))).and_then(|_| {
            self.last_set_active_idx = Some(idx);
            Ok(())
        })
    }

    fn set_slot_unbootable(&mut self, slot_suffix: Suffix, reason: UnbootableReason) -> Result<()> {
        let idx: u8 = self
            .slots_iter()
            .position(|s| s.suffix == slot_suffix)
            .ok_or(Error::InvalidInput)?
            .try_into()
            // This 'or' is technically unreachable because the protocol
            // can't give us an index larger than a u8.
            .or(Err(Error::Other(None)))?;
        self.protocol.set_slot_unbootable(idx, u8::from(reason).into())
    }

    fn get_max_retries(&self) -> Result<Tries> {
        Ok(self.protocol.load_boot_data()?.max_retries.into())
    }

    fn get_oneshot_status(&self) -> Option<OneShot> {
        let mut subreason = [0u8; SUBREASON_BUF_LEN];
        let (reason, _) = self.protocol.get_boot_reason(subreason.as_mut_slice()).ok()?;
        // Currently we only care if the primary boot reason is BOOTLOADER.
        // CStr::from_bytes_until_nul(&subreason[..strlen]).ok()?
        match reason {
            REASON_BOOTLOADER => Some(OneShot::Bootloader),
            _ => None,
        }
    }

    fn set_oneshot_status(&mut self, os: OneShot) -> Result<()> {
        // Android doesn't have a concept of OneShot to recovery,
        // and the subreason shouldn't matter.
        match os {
            OneShot::Bootloader => {
                self.protocol.set_boot_reason(REASON_BOOTLOADER, &[]).or(Err(Error::Other(None)))
            }
            _ => Err(Error::OperationProhibited),
        }
    }

    fn clear_oneshot_status(&mut self) {
        let mut subreason = [0u8; SUBREASON_BUF_LEN];
        // Only clear if the boot reason is the one we care about.
        // CStr::from_bytes_until_nul(&subreason[..strlen]).or(Err(Error::Other))?
        if let Ok((REASON_BOOTLOADER, _)) = self.protocol.get_boot_reason(subreason.as_mut_slice())
        {
            let _ = self.protocol.set_boot_reason(REASON_EMPTY, &[]);
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
    use crate::protocol::Protocol;
    use crate::test::*;
    use crate::EfiEntry;
    use efi_types::{
        EfiStatus, GblEfiABSlotProtocol, GblEfiSlotInfo, GblEfiSlotMetadataBlock,
        EFI_STATUS_INVALID_PARAMETER, EFI_STATUS_SUCCESS,
        GBL_EFI_BOOT_REASON_GBL_EFI_EMPTY_BOOT_REASON as REASON_EMPTY,
        GBL_EFI_BOOT_REASON_GBL_EFI_RECOVERY as REASON_RECOVERY,
        GBL_EFI_BOOT_REASON_GBL_EFI_WATCHDOG as REASON_WATCHDOG,
    };
    use gbl::{
        ops::{AvbIoResult, CertPermanentAttributes, SHA256_DIGEST_SIZE},
        partition::PartitionBlockDevice,
        slots::{Bootability, Cursor, RecoveryTarget, UnbootableReason},
        BootImages, Gbl, GblOps, Result as GblResult,
    };
    use gbl_storage_testlib::TestBlockDevice;
    use libgbl::ops::ImageBuffer;
    // TODO(b/350526796): use ptr.is_aligned() when Rust 1.79 is in Android
    use std::{
        fmt::Write,
        mem::align_of,
        num::NonZeroUsize,
        sync::atomic::{AtomicBool, AtomicU32, Ordering},
    };
    use zbi::ZbiContainer;

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
        static BOOT_REASON: AtomicU32 = AtomicU32::new(REASON_EMPTY);
    }

    // This provides reasonable defaults for all tests that need to get slot info.
    //
    // SAFETY: checks that `info` is properly aligned and not null.
    // Caller must make sure `info` points to a valid GblEfiSlotInfo struct.
    unsafe extern "C" fn get_info(
        _: *mut GblEfiABSlotProtocol,
        idx: u8,
        info: *mut GblEfiSlotInfo,
    ) -> EfiStatus {
        // TODO(b/350526796): use ptr.is_aligned() when Rust 1.79 is in Android
        if !info.is_null() && (info as usize) % align_of::<GblEfiSlotInfo>() == 0 && idx < 3 {
            let slot_info = GblEfiSlotInfo {
                suffix: ('a' as u8 + idx).into(),
                unbootable_reason: 0,
                priority: idx + 1,
                tries: idx,
                successful: 2 & idx,
            };
            unsafe { *info = slot_info };
            EFI_STATUS_SUCCESS
        } else {
            EFI_STATUS_INVALID_PARAMETER
        }
    }

    extern "C" fn flush(_: *mut GblEfiABSlotProtocol) -> EfiStatus {
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

    impl<'a> GblOps<'a> for TestGblOps<'_>
    where
        Self: 'a,
    {
        fn console_out(&mut self) -> Option<&mut dyn Write> {
            unimplemented!();
        }

        fn should_stop_in_fastboot(&mut self) -> Result<bool> {
            unimplemented!();
        }

        fn preboot(&mut self, _: BootImages) -> Result<()> {
            unimplemented!();
        }

        fn reboot(&mut self) {
            unimplemented!();
        }

        fn partitions(&self) -> Result<&'a [PartitionBlockDevice<'a, Self::PartitionBlockIo>]> {
            unimplemented!();
        }

        fn zircon_add_device_zbi_items(&mut self, _: &mut ZbiContainer<&mut [u8]>) -> Result<()> {
            unimplemented!();
        }

        fn do_fastboot<B: gbl_storage::AsBlockDevice>(&self, _: &mut Cursor<B>) -> GblResult<()> {
            unimplemented!();
        }

        fn load_slot_interface<'b, B: gbl_storage::AsBlockDevice>(
            &'b mut self,
            block_dev: &'b mut B,
            boot_token: BootToken,
        ) -> GblResult<Cursor<'b, B>> {
            self.manager.boot_token = Some(boot_token);
            Ok(Cursor { ctx: &mut self.manager, block_dev })
        }

        fn avb_read_is_device_unlocked(&mut self) -> AvbIoResult<bool> {
            unimplemented!();
        }

        fn avb_read_rollback_index(&mut self, _rollback_index_location: usize) -> AvbIoResult<u64> {
            unimplemented!();
        }

        fn avb_write_rollback_index(
            &mut self,
            _rollback_index_location: usize,
            _index: u64,
        ) -> AvbIoResult<()> {
            unimplemented!();
        }

        fn avb_cert_read_permanent_attributes(
            &mut self,
            _attributes: &mut CertPermanentAttributes,
        ) -> AvbIoResult<()> {
            unimplemented!();
        }

        fn avb_cert_read_permanent_attributes_hash(
            &mut self,
        ) -> AvbIoResult<[u8; SHA256_DIGEST_SIZE]> {
            unimplemented!();
        }

        fn get_image_buffer<'c>(
            &mut self,
            _image_name: &str,
            _size: NonZeroUsize,
        ) -> GblResult<ImageBuffer<'c>> {
            unimplemented!();
        }

        fn get_custom_device_tree(&mut self) -> Option<&'a [u8]> {
            unimplemented!();
        }
    }

    #[test]
    fn test_manager_flush_on_close() {
        ATOMIC.with(|a| a.store(false, Ordering::Relaxed));
        run_test(|image_handle, systab_ptr| {
            let mut ab = GblEfiABSlotProtocol { flush: Some(flush), ..Default::default() };
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
            let mut ab = GblEfiABSlotProtocol {
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
        // that `info` points to a valid GblEfiSlotInfo.
        unsafe extern "C" fn get_current_slot(
            _: *mut GblEfiABSlotProtocol,
            info: *mut GblEfiSlotInfo,
        ) -> EfiStatus {
            // TODO(b/350526796): use ptr.is_aligned() when Rust 1.79 is in Android
            if info.is_null() || (info as usize) % align_of::<GblEfiSlotInfo>() != 0 {
                return EFI_STATUS_INVALID_PARAMETER;
            }
            let slot_info = GblEfiSlotInfo {
                suffix: 'a' as u32,
                unbootable_reason: 0,
                priority: 7,
                tries: 15,
                successful: 1,
            };

            unsafe { *info = slot_info };
            EFI_STATUS_SUCCESS
        }

        // SAFETY: verifies that `reason` and `subreason_size` are aligned and not null.
        // It is the caller's responsibility to make sure that `reason`
        // and `subreason_size` point to valid output parameters.
        unsafe extern "C" fn get_boot_reason(
            _: *mut GblEfiABSlotProtocol,
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

        BOOT_REASON.with(|r| r.store(REASON_EMPTY, Ordering::Relaxed));
        run_test(|image_handle, systab_ptr| {
            let mut ab = GblEfiABSlotProtocol {
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

            BOOT_REASON.with(|r| r.store(REASON_RECOVERY, Ordering::Relaxed));

            assert_eq!(
                cursor.ctx.get_boot_target().unwrap(),
                BootTarget::Recovery(RecoveryTarget::Slotted(slot))
            );
        });
    }

    #[test]
    fn test_mark_boot_attempt() {
        extern "C" fn mark_boot_attempt(_: *mut GblEfiABSlotProtocol) -> EfiStatus {
            ATOMIC.with(|a| a.store(true, Ordering::Relaxed));
            EFI_STATUS_SUCCESS
        }

        ATOMIC.with(|a| a.store(false, Ordering::Relaxed));
        run_test(|image_handle, systab_ptr| {
            let mut ab = GblEfiABSlotProtocol {
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

            assert_eq!(cursor.ctx.mark_boot_attempt(), Err(Error::OperationProhibited));
        });
    }

    #[test]
    fn test_get_max_retries() {
        // SAFETY: verifies that `meta` is properly aligned and not null.
        // It is the caller's responsibility to make sure that `meta` points to
        // a valid GblEfiSlotMetadataBlock.
        unsafe extern "C" fn load_boot_data(
            _: *mut GblEfiABSlotProtocol,
            meta: *mut GblEfiSlotMetadataBlock,
        ) -> EfiStatus {
            // TODO(b/350526796): use ptr.is_aligned() when Rust 1.79 is in Android
            if meta.is_null() || (meta as usize) % align_of::<GblEfiSlotMetadataBlock>() != 0 {
                return EFI_STATUS_INVALID_PARAMETER;
            }

            let meta_block = GblEfiSlotMetadataBlock {
                unbootable_metadata: 1,
                max_retries: 66,
                slot_count: 32, // why not?
                merge_status: 0,
            };

            unsafe { *meta = meta_block };
            EFI_STATUS_SUCCESS
        }

        run_test(|image_handle, systab_ptr| {
            let mut ab = GblEfiABSlotProtocol {
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
        extern "C" fn set_active_slot(_: *mut GblEfiABSlotProtocol, idx: u8) -> EfiStatus {
            // This is deliberate: we want to make sure that other logic catches
            // 'no such slot' first but we also want to verify that errors propagate.
            if idx != 2 {
                EFI_STATUS_SUCCESS
            } else {
                EFI_STATUS_INVALID_PARAMETER
            }
        }

        run_test(|image_handle, systab_ptr| {
            let mut ab = GblEfiABSlotProtocol {
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
            assert_eq!(cursor.ctx.set_active_slot('c'.into()), Err(Error::Other(None)));

            let bad_suffix = '$'.into();
            assert_eq!(cursor.ctx.set_active_slot(bad_suffix), Err(Error::InvalidInput));
        });
    }

    #[test]
    fn test_set_slot_unbootable() {
        extern "C" fn set_slot_unbootable(
            _: *mut GblEfiABSlotProtocol,
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
            let mut ab = GblEfiABSlotProtocol {
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
                Err(Error::InvalidInput)
            );
        });
    }

    #[test]
    fn test_oneshot() {
        // SAFETY: checks that `reason` is not null and is properly aligned.
        // Caller must make sure reason points to a valid u32.
        unsafe extern "C" fn get_boot_reason(
            _: *mut GblEfiABSlotProtocol,
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
            _: *mut GblEfiABSlotProtocol,
            reason: u32,
            _: usize,
            _: *const u8,
        ) -> EfiStatus {
            BOOT_REASON.with(|r| r.store(reason, Ordering::Relaxed));
            EFI_STATUS_SUCCESS
        }

        BOOT_REASON.with(|r| r.store(REASON_EMPTY, Ordering::Relaxed));
        run_test(|image_handle, systab_ptr| {
            let mut ab = GblEfiABSlotProtocol {
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
                Err(Error::OperationProhibited)
            );
            assert_eq!(cursor.ctx.set_oneshot_status(OneShot::Bootloader), Ok(()));
            assert_eq!(cursor.ctx.get_oneshot_status(), Some(OneShot::Bootloader));

            cursor.ctx.clear_oneshot_status();
            assert_eq!(cursor.ctx.get_oneshot_status(), None);

            BOOT_REASON.with(|r| r.store(REASON_WATCHDOG, Ordering::Relaxed));
            assert_eq!(cursor.ctx.get_oneshot_status(), None);
            cursor.ctx.clear_oneshot_status();
            assert_eq!(BOOT_REASON.with(|r| r.load(Ordering::Relaxed)), REASON_WATCHDOG);
        });
    }
}
