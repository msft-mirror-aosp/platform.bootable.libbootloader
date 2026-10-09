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

//! This file provides APIs for loading, verifying and booting Fuchsia/Zircon.

use crate::{
    gbl_avb::ops::GblAvbOps, gbl_println, ops::OneShotBootMode, GblOps, Result as GblResult,
};
pub use abr::{get_and_clear_one_shot_bootloader, get_boot_slot, Ops as AbrOps, SlotIndex};
use bytes::buf::UninitSlice;
use core::fmt::Write;
use gbl_storage::CheckedGet;
use liberror::{Error, Result};
use safemath::SafeNum;
use zbi::{ZbiContainer, ZbiFlags, ZbiHeader, ZbiType};
use zerocopy::IntoBytes;

mod vboot;

mod load;
pub use load::{zircon_load_verify_abr_with_buffer, zircon_main, LoadedVerifiedZircon};

const DURABLE_BOOT_PARTITION: &str = "durable_boot";
const MISC_PARTITION: &str = "misc";
const ABR_PARTITION_ALIASES: &[&str] = &[DURABLE_BOOT_PARTITION, MISC_PARTITION];

/// Helper function to find partition given a list of possible aliases.
fn find_part_aliases<'a, 'b>(
    ops: &mut (impl GblOps<'a> + ?Sized),
    aliases: &'b [&str],
) -> Result<&'b str> {
    Ok(*aliases
        .iter()
        .find(|v| matches!(ops.partition_size(v), Ok(Some(_))))
        .ok_or(Error::NotFound)?)
}

/// `GblAbrOps` wraps an object implementing `GblOps` and implements the `abr::Ops` trait.
pub(crate) struct GblAbrOps<'a, T: ?Sized>(pub &'a mut T);

impl<'b, T: GblOps<'b> + ?Sized> AbrOps for GblAbrOps<'_, T> {
    fn read_abr_metadata(&mut self, out: &mut [u8]) -> Result<()> {
        let part = find_part_aliases(self.0, &ABR_PARTITION_ALIASES)?;
        self.0.read_from_partition_sync(part, 0, out)
    }

    fn write_abr_metadata(&mut self, data: &mut [u8]) -> Result<()> {
        let part = find_part_aliases(self.0, &ABR_PARTITION_ALIASES)?;
        self.0.write_to_partition_sync(part, 0, data)
    }

    fn console(&mut self) -> Option<&mut dyn Write> {
        self.0.console_out()
    }
}

/// A helper for splitting the trailing unused portion of a ZBI container buffer.
///
/// Returns a tuple of used subslice and unused subslice
pub(crate) fn zbi_split_unused_buffer_mut(zbi: &mut [u8]) -> GblResult<(&mut [u8], &mut [u8])> {
    Ok(zbi.split_at_mut(ZbiContainer::parse(&zbi[..])?.container_size()?))
}

/// Same as zbi_split_unused_buffer_mut but on immutable slice.
pub(crate) fn zbi_split_unused_buffer_ref(zbi: &[u8]) -> GblResult<(&[u8], &[u8])> {
    Ok(zbi.split_at(ZbiContainer::parse(&zbi[..])?.container_size()?))
}

/// Gets the list of aliases for slotted/slotless zircon partition name.
fn zircon_part_name_aliases(slot: Option<SlotIndex>) -> &'static [&'static str] {
    match slot {
        Some(SlotIndex::A) => &["zircon_a", "zircon-a"][..],
        Some(SlotIndex::B) => &["zircon_b", "zircon-b"][..],
        Some(SlotIndex::R) => &["zircon_r", "zircon-r"][..],
        _ => &["zircon"][..],
    }
}

/// Gets the slotted/slotless standard zircon partition name.
pub fn zircon_part_name(slot: Option<SlotIndex>) -> &'static str {
    zircon_part_name_aliases(slot)[0]
}

/// Gets the ZBI command line string for the current slot.
fn slot_cmd_line(slot: SlotIndex) -> &'static str {
    match slot {
        SlotIndex::A => "zvb.current_slot=a",
        SlotIndex::B => "zvb.current_slot=b",
        SlotIndex::R => "zvb.current_slot=r",
    }
}

/// Helper for reading zircon image from disk.
pub(crate) fn read_zircon_image<'a, 'b>(
    ops: &mut impl GblOps<'a>,
    slot: Option<SlotIndex>,
    out: impl Into<&'b mut UninitSlice>,
) -> GblResult<usize> {
    let zircon_part = find_part_aliases(ops, zircon_part_name_aliases(slot))?;
    // Reads ZBI header to compute the total size of kernel.
    let mut zbi_header: ZbiHeader = Default::default();
    ops.read_from_partition_sync(zircon_part, 0, zbi_header.as_bytes_mut())?;
    let image_length =
        usize::try_from(SafeNum::from(zbi_header.as_bytes_mut().len()) + zbi_header.length)
            .map_err(Error::from)?;
    // Reads the entire kernel
    let buf = out.into().get_mut(..image_length)?;
    ops.read_from_partition_sync(zircon_part, 0, buf)?;
    Ok(image_length)
}

/// Helper for fixing up ZBI items.
pub(crate) fn fixup_zbi_items<'a>(
    ops: &mut impl GblOps<'a>,
    slot: Option<SlotIndex>,
    zbi_items: &mut ZbiContainer<&mut [u8]>,
) -> GblResult<()> {
    // Appends current slot item.
    if let Some(slot) = slot {
        zbi_items.create_entry_with_payload(
            ZbiType::CmdLine,
            0,
            ZbiFlags::default(),
            slot_cmd_line(slot).as_bytes(),
        )?;
    }

    // Appends device specific ZBI items.
    ops.zircon_add_device_zbi_items(zbi_items)?;
    // Appends staged bootloader file if present.
    if GblAvbOps::new(ops, None, &mut [], false).avb_read_device_status()?.is_unlocked
        && let Some(Ok(v)) =
            ops.get_zbi_bootloader_files_buffer_aligned().map(|v| ZbiContainer::parse(v))
    {
        zbi_items.extend(&v)?;
    }
    Ok(())
}

/// Checks whether platform or A/B/R metadata instructs GBL to boot into fastboot or recovery mode.
///
/// # Returns
///
/// Returns `(enter_fastboot, oneshot_recovery)`.
pub(crate) fn zircon_check_boot_mode<'a>(ops: &mut impl GblOps<'a>) -> (bool, bool) {
    match get_and_clear_one_shot_bootloader(&mut GblAbrOps(ops)) {
        Ok(true) => {
            gbl_println!(ops, "A/B/R one-shot-bootloader is set");
            return (true, false);
        }
        Err(e) => {
            gbl_println!(ops, "Warning: error while checking A/B/R one-shot-bootloader ({:?})", e);
            gbl_println!(ops, "Ignoring error and considering it not set");
        }
        _ => {}
    };

    let one_shot_boot_mode = ops
        .get_one_shot_boot_mode()
        .inspect_err(|e| {
            gbl_println!(ops, "Failed to check hardware triggered boot mode override: {e}");
            gbl_println!(ops, "Ignoring error and assuming not triggered");
        })
        .unwrap_or(None);
    gbl_println!(ops, "Hardware triggered boot mode override: {one_shot_boot_mode:?}");

    match one_shot_boot_mode {
        Some(OneShotBootMode::Bootloader) => {
            gbl_println!(ops, "Hardware trigger instructs GBL to enter fastboot mode");
            (true, false)
        }
        Some(OneShotBootMode::Recovery) => {
            gbl_println!(ops, "Hardware trigger instructs GBL to enter recovery mode");
            (false, true)
        }
        None => (false, false),
    }
}

/// Checks whether platform or A/B/R metadata instructs GBL to boot into fastboot mode.
///
/// # Returns
///
/// Returns true if fastboot mode is enabled, false if not.
pub fn zircon_check_enter_fastboot<'a>(ops: &mut impl GblOps<'a>) -> bool {
    zircon_check_boot_mode(ops).0
}

#[cfg(test)]
pub(crate) mod test {
    use super::*;
    use crate::{
        ops::{
            test::{FakeGblOps, FakeGblOpsStorage, TestGblDisk},
            CertPermanentAttributes,
        },
        tests::read_test_data,
    };
    use abr::{get_and_clear_one_shot_flag, set_one_shot_bootloader};
    use avb_bindgen::{AVB_CERT_PIK_VERSION_LOCATION, AVB_CERT_PSK_VERSION_LOCATION};
    use std::collections::{BTreeSet, HashMap};
    use zerocopy::FromBytes;

    // The cert test keys were both generated with rollback version 42.
    pub(crate) const TEST_CERT_PIK_VERSION: u64 = 42;
    pub(crate) const TEST_CERT_PSK_VERSION: u64 = 42;

    // The rollback index value and location in the generated test vbmetadata.
    // See `gen_zircon_test_images()` in libgbl/testdata/gen_test_data.py.
    pub(crate) const TEST_ROLLBACK_INDEX_LOCATION: usize = 1;
    pub(crate) const TEST_ROLLBACK_INDEX_VALUE: u64 = 2;

    pub(crate) const ZIRCON_A_ZBI_FILE: &str = "zircon_a.zbi";
    pub(crate) const ZIRCON_B_ZBI_FILE: &str = "zircon_b.zbi";
    pub(crate) const ZIRCON_R_ZBI_FILE: &str = "zircon_r.zbi";
    pub(crate) const ZIRCON_SLOTLESS_ZBI_FILE: &str = "zircon_slotless.zbi";
    pub(crate) const VBMETA_A_FILE: &str = "vbmeta_a.bin";
    pub(crate) const VBMETA_B_FILE: &str = "vbmeta_b.bin";
    pub(crate) const VBMETA_R_FILE: &str = "vbmeta_r.bin";
    pub(crate) const VBMETA_SLOTLESS_FILE: &str = "vbmeta_slotless.bin";

    // The `reserve_memory_size` value in the test ZBI kernel.
    // See `gen_zircon_test_images()` in libgbl/testdata/gen_test_data.py.
    pub(crate) const TEST_KERNEL_RESERVED_MEMORY_SIZE: usize = 1024;

    /// Returns a default [FakeGblOpsStorage] with valid test images.
    ///
    /// Rather than the typical use case of partitions on a single GPT device, this structures data
    /// as separate raw single-partition devices. This is easier for tests since we don't need to
    /// generate a GPT, and should be functionally equivalent since our code looks for partitions
    /// on all devices.
    pub(crate) fn create_storage() -> FakeGblOpsStorage {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"zircon_a", read_test_data(ZIRCON_A_ZBI_FILE));
        storage.add_raw_device(c"zircon_b", read_test_data(ZIRCON_B_ZBI_FILE));
        storage.add_raw_device(c"zircon_r", read_test_data(ZIRCON_R_ZBI_FILE));
        storage.add_raw_device(c"zircon", read_test_data(ZIRCON_SLOTLESS_ZBI_FILE));
        storage.add_raw_device(c"vbmeta_a", read_test_data(VBMETA_A_FILE));
        storage.add_raw_device(c"vbmeta_b", read_test_data(VBMETA_B_FILE));
        storage.add_raw_device(c"vbmeta_r", read_test_data(VBMETA_R_FILE));
        storage.add_raw_device(c"vbmeta", read_test_data(VBMETA_SLOTLESS_FILE));
        storage.add_raw_device(c"durable_boot", vec![0u8; 64 * 1024]);
        storage
    }

    /// Returns a default [FakeGblOpsStorage] with valid test images and using legacy partition
    /// names.
    pub(crate) fn create_storage_legacy_names() -> FakeGblOpsStorage {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"zircon-a", read_test_data(ZIRCON_A_ZBI_FILE));
        storage.add_raw_device(c"zircon-b", read_test_data(ZIRCON_B_ZBI_FILE));
        storage.add_raw_device(c"zircon-r", read_test_data(ZIRCON_R_ZBI_FILE));
        storage.add_raw_device(c"zircon", read_test_data(ZIRCON_SLOTLESS_ZBI_FILE));
        storage.add_raw_device(c"vbmeta_a", read_test_data(VBMETA_A_FILE));
        storage.add_raw_device(c"vbmeta_b", read_test_data(VBMETA_B_FILE));
        storage.add_raw_device(c"vbmeta_r", read_test_data(VBMETA_R_FILE));
        storage.add_raw_device(c"vbmeta", read_test_data(VBMETA_SLOTLESS_FILE));
        storage.add_raw_device(c"misc", vec![0u8; 64 * 1024]);
        storage
    }

    pub(crate) fn create_gbl_ops<'a>(partitions: &'a [TestGblDisk]) -> FakeGblOps<'a> {
        let mut ops = FakeGblOps::new(&partitions);
        ops.avb_ops.rollbacks = HashMap::from([
            (TEST_ROLLBACK_INDEX_LOCATION, Ok(0)),
            (AVB_CERT_PSK_VERSION_LOCATION.try_into().unwrap(), Ok(0)),
            (AVB_CERT_PIK_VERSION_LOCATION.try_into().unwrap(), Ok(0)),
        ]);
        ops.avb_ops.use_cert = true;
        ops.avb_ops.cert_permanent_attributes = Some(
            CertPermanentAttributes::read_from(
                &read_test_data("cert_permanent_attributes.bin")[..],
            )
            .unwrap(),
        );
        ops.avb_ops.cert_permanent_attributes_hash =
            Some(read_test_data("cert_permanent_attributes.hash").try_into().unwrap());
        ops
    }

    /// Normalizes a ZBI container by converting each ZBI item into raw bytes and storing them in
    /// an ordered set. The function is mainly used for comparing two ZBI containers have identical
    /// set of items, disregarding order.
    pub(crate) fn normalize_zbi(zbi: &[u8]) -> BTreeSet<Vec<u8>> {
        let zbi = ZbiContainer::parse(zbi).unwrap();
        BTreeSet::from_iter(zbi.iter().map(|v| {
            let mut hdr = *v.header;
            hdr.crc32 = 0; // ignores crc32 field.
            hdr.flags &= !ZbiFlags::CRC32.bits();
            [hdr.as_bytes(), v.payload.as_bytes()].concat()
        }))
    }

    /// Helper to append a command line ZBI item to a ZBI container
    pub(crate) fn append_cmd_line(zbi: &mut [u8], cmd: &[u8]) {
        let mut container = ZbiContainer::parse(zbi).unwrap();
        container.create_entry_with_payload(ZbiType::CmdLine, 0, ZbiFlags::default(), cmd).unwrap();
    }

    /// Helper to append a command line ZBI item to a ZBI container
    pub(crate) fn append_zbi_file(zbi: &mut [u8], payload: &[u8]) {
        let mut container = ZbiContainer::parse(zbi).unwrap();
        container
            .create_entry_with_payload(ZbiType::BootloaderFile, 0, ZbiFlags::default(), payload)
            .unwrap();
    }

    /// Modifies data in the given partition.
    pub(crate) fn corrupt_data(ops: &mut FakeGblOps, part_name: &str) {
        let mut data = [0u8];
        assert!(ops.read_from_partition_sync(part_name, 64, &mut data[..]).is_ok());
        data[0] ^= 0x01;
        assert!(ops.write_to_partition_sync(part_name, 64, &mut data[..]).is_ok());
    }

    #[test]
    fn test_check_enter_fastboot_via_get_one_shot_boot_mode() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        assert!(!zircon_check_enter_fastboot(&mut ops));
        ops.one_shot_boot_mode = Some(OneShotBootMode::Bootloader);
        assert!(zircon_check_enter_fastboot(&mut ops));
        ops.one_shot_boot_mode = Some(OneShotBootMode::Recovery);
        assert!(!zircon_check_enter_fastboot(&mut ops));
        // The hardware-triggered recovery mode is not persisted to A/B/R metadata.
        assert_eq!(get_and_clear_one_shot_flag(&mut GblAbrOps(&mut ops)), Ok(0));
    }

    #[test]
    fn test_check_enter_fastboot_abr() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        set_one_shot_bootloader(&mut GblAbrOps(&mut ops), true).unwrap();
        assert!(zircon_check_enter_fastboot(&mut ops));
        // One-shot only.
        assert!(!zircon_check_enter_fastboot(&mut ops));
    }

    #[test]
    fn test_check_enter_fastboot_prioritize_abr() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        set_one_shot_bootloader(&mut GblAbrOps(&mut ops), true).unwrap();
        ops.one_shot_boot_mode = Some(OneShotBootMode::Bootloader);
        assert!(zircon_check_enter_fastboot(&mut ops));
        ops.one_shot_boot_mode = None;
        // A/B/R metadata should be prioritized in the previous check and thus one-shot-bootloader
        // flag should be cleared.
        assert!(!zircon_check_enter_fastboot(&mut ops));
    }
}
