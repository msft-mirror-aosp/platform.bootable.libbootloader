// Copyright 2025, The Android Open Source Project
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

use crate::{
    android_boot::GblFastbootEntry,
    constants::{PAGE_SIZE, ZIRCON_KERNEL_ALIGNMENT},
    fastboot::LoadedImageInfo,
    fuchsia_boot::{
        fixup_zbi_items, read_zircon_image, vboot::zircon_verify_kernel_in_place,
        zbi_split_unused_buffer_mut, zircon_check_boot_mode, zircon_part_name, GblAbrOps,
    },
    gbl_println, GblOps, Result as GblResult,
};
pub use abr::{get_boot_slot, SlotIndex};
use liberror::Error;
use libgblutils::aligned_subslice;
use safemath::SafeNum;
use zbi::{ZbiContainer, ZbiFlags, ZbiType};
use zerocopy::IntoBytes;

/// Relocates a ZBI kernel to a different buffer.
///
/// * `dest` must be aligned to `ZIRCON_KERNEL_ALIGNMENT`.
/// * `dest` will be a ZBI container containing only the kernel item.
fn relocate_kernel(kernel: &[u8], dest: &mut [u8]) -> GblResult<()> {
    if (dest.as_ptr() as usize % ZIRCON_KERNEL_ALIGNMENT) != 0 {
        return Err(Error::InvalidAlignment.into());
    }

    let kernel = ZbiContainer::parse(&kernel[..])?;
    let kernel_item = kernel.get_bootable_kernel_item()?;
    let hdr = kernel_item.header;
    // Creates a new ZBI kernel item at the destination.
    let mut relocated = ZbiContainer::new(&mut dest[..])?;
    let zbi_type = ZbiType::try_from(hdr.type_)?;
    relocated.create_entry_with_payload(
        zbi_type,
        hdr.extra,
        hdr.get_flags() & !ZbiFlags::CRC32,
        kernel_item.payload.as_bytes(),
    )?;
    let (_, reserved_sz) = relocated.get_kernel_entry_and_reserved_memory_size()?;
    let buf_len = u64::try_from(zbi_split_unused_buffer_mut(dest)?.1.len()).map_err(Error::from)?;
    match reserved_sz > buf_len {
        true => {
            let required_sz = SafeNum::from(dest.len()) + reserved_sz - buf_len;
            Err(Error::BufferTooSmall(required_sz.try_into().ok()).into())
        }
        _ => Ok(()),
    }
}

/// Relocate a ZBI kernel to the trailing unused buffer.
///
/// Returns the original ZBI container slice and relocated kernel subslice.
fn relocate_to_tail(kernel: &mut [u8]) -> GblResult<(&mut [u8], &mut [u8])> {
    let reloc_size = ZbiContainer::parse(&kernel[..])?.get_buffer_size_for_kernel_relocation()?;
    let (original, relocated) = zbi_split_unused_buffer_mut(kernel)?;
    let relocated = aligned_subslice(relocated, ZIRCON_KERNEL_ALIGNMENT)?;
    let off = (SafeNum::from(relocated.len()) - reloc_size)
        .round_down(ZIRCON_KERNEL_ALIGNMENT)
        .try_into()
        .map_err(Error::from)?;
    let relocated = &mut relocated[off..];
    relocate_kernel(original, relocated)?;
    let reloc_addr = relocated.as_ptr() as usize;
    Ok(kernel.split_at_mut(reloc_addr.checked_sub(kernel.as_ptr() as usize).unwrap()))
}

/// Performs load, verification and fixup in a caller provided buffer.
///
/// On success, returns a pair of buffers corresponding to the zbi items and kernel.
fn zircon_load_verify_fixup<'a, 'b>(
    ops: &mut impl GblOps<'a>,
    slot: Option<SlotIndex>,
    slot_booted_successfully: bool,
    load_buffer: &'b mut [u8],
) -> GblResult<(&'b mut [u8], &'b mut [u8])> {
    // Zircon kernel requires ZBI items address to be page aligned.
    let load = aligned_subslice(load_buffer, PAGE_SIZE)?;
    read_zircon_image(ops, slot, &mut *load)?;
    // Performs AVB verification.
    zircon_verify_kernel_in_place(ops, slot, slot_booted_successfully, &mut load[..])?;
    // Append additional ZBI items.
    fixup_zbi_items(ops, slot, &mut ZbiContainer::parse(&mut load[..])?)?;
    // Relocates the kernel to the tail to reserved extra memory that the kernel may require.
    relocate_to_tail(&mut load[..])
}

/// Contains loaded zircon ZBI items, kernel and selected slot.
pub struct LoadedVerifiedZircon<'a> {
    /// Slice containing the ZBI items.
    pub zbi_items: &'a mut [u8],
    /// Slice containing the relocated kernel.
    pub kernel: &'a mut [u8],
    /// The selected slot.
    pub slot: SlotIndex,
}

/// Performs A/B/R slot selection and loads, verifies and fixes up the corresponding slot of zircon
/// image.
///
/// # Args
///
/// * `ops`: An implementation of GblOps.
/// * `load_buffer`: A buffer for loading, verifying and fixing up.
///
/// # Returns
///
/// On success, returns a `LoadedVerifiedZircon`.
pub fn zircon_load_verify_abr_with_buffer<'a, 'b>(
    ops: &mut impl GblOps<'a>,
    load_buffer: &'b mut [u8],
) -> GblResult<LoadedVerifiedZircon<'b>> {
    zircon_load_verify_abr_with_mode(ops, load_buffer, false)
}

fn zircon_load_verify_abr_with_mode<'a, 'b>(
    ops: &mut impl GblOps<'a>,
    load_buffer: &'b mut [u8],
    oneshot_recovery: bool,
) -> GblResult<LoadedVerifiedZircon<'b>> {
    let (slot, successful) = if oneshot_recovery {
        (SlotIndex::R, false)
    } else {
        get_boot_slot(&mut GblAbrOps(ops), true)
    };
    gbl_println!(ops, "Loading kernel from {}...", zircon_part_name(Some(slot)));
    let (zbi_items, kernel) = zircon_load_verify_fixup(ops, Some(slot), successful, load_buffer)?;
    gbl_println!(ops, "Successfully loaded slot: {}", zircon_part_name(Some(slot)));
    Ok(LoadedVerifiedZircon { zbi_items, kernel, slot })
}

/// Main entry function for zircon bootloader (before booting)
///
/// The API handles boot mode, fastboot, A/B/R slot selection, loads, verification and fix up of
/// zircon images.
///
/// # Args
///
/// * `ops`: An implementation of GblOps.
/// * `load`: A buffer for loading, verifying and fixing up.
/// * `run_fastboot`: A closure for running GBL fastboot. The closure is passed a
///   `GblFastbootEntry` type which provides methods for running GBL fastboot. The caller is
///   responsible for preparing the required inputs and calling the method in the closure. See
///   `GblFastbootEntry` for more details.
///
/// # Returns
///
/// On success, returns a `LoadedVerifiedZircon`.
pub fn zircon_main<'a, 'b, G: GblOps<'a>>(
    ops: &mut G,
    load: &'b mut [u8],
    run_fastboot: impl FnOnce(GblFastbootEntry<'_, G>),
) -> GblResult<LoadedVerifiedZircon<'b>> {
    gbl_println!(ops, "Loading and verifying Fuchsia...");

    // TODO(b/445679472): Revisit this after Fuchsia adopts BCB or its own boot mode standard.
    // Checks and enters fastboot.
    let result = &mut Default::default();
    let (enter_fastboot, oneshot_recovery) = zircon_check_boot_mode(ops);
    if enter_fastboot {
        gbl_println!(ops, "Entering fastboot mode...");
        run_fastboot(GblFastbootEntry {
            ops,
            boot_buffer: (&mut load[..]).into(),
            result,
            load_result: None,
        });
        gbl_println!(ops, "Leaving fastboot mode...");
    }

    // Checks if "fastboot boot" has loaded an android image.
    if let LoadedImageInfo::Fuchsia { slot, .. } = result.loaded_image_info {
        gbl_println!(ops, "Booting from \"fastboot boot\"");
        let (zbi_items, kernel) = result.split_loaded_fuchsia(load).unwrap();
        return Ok(LoadedVerifiedZircon { zbi_items, kernel, slot });
    }

    zircon_load_verify_abr_with_mode(ops, load, oneshot_recovery)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        fastboot::test::{make_expected_transport_out, SharedTestListener},
        fuchsia_boot::test::{
            append_cmd_line, append_zbi_file, create_gbl_ops, create_storage,
            create_storage_legacy_names, normalize_zbi, TEST_CERT_PIK_VERSION,
            TEST_CERT_PSK_VERSION, TEST_KERNEL_RESERVED_MEMORY_SIZE, TEST_ROLLBACK_INDEX_LOCATION,
            TEST_ROLLBACK_INDEX_VALUE, ZIRCON_A_ZBI_FILE, ZIRCON_SLOTLESS_ZBI_FILE,
        },
        ops::{
            test::{DefaultOk, FakeGblOps},
            OneShotBootMode,
        },
        tests::read_test_data,
    };
    use abr::{
        get_and_clear_one_shot_flag, mark_slot_active, mark_slot_successful, mark_slot_unbootable,
        set_one_shot_bootloader, UnbootableReason, ABR_MAX_TRIES_REMAINING,
    };
    use avb::IoError as AvbIoError;
    use avb_bindgen::{AVB_CERT_PIK_VERSION_LOCATION, AVB_CERT_PSK_VERSION_LOCATION};
    use fastboot::LockState;
    use libtestutils::AlignedBuffer;
    use std::string::String;
    use zbi::{ZbiItem, ZBI_ALIGNMENT_USIZE};

    /// Converts a ZBI item to printable string for debugging.
    fn zbi_item_to_str(item: &[u8]) -> String {
        let item = ZbiItem::parse(item).unwrap().0;
        let payload = match item.header.type_ {
            v if v == ZbiType::CmdLine as _ => String::from_utf8(item.payload.to_vec()).unwrap(),
            _ => format!("{} bytes", item.payload.len()),
        };
        format!("{:?}: {}", *item.header, payload)
    }

    /// Converts a normalized ZBI container to printable string for debugging.
    fn normalized_zbi_to_str(zbi: &[u8]) -> String {
        normalize_zbi(zbi).iter().map(|v| zbi_item_to_str(v)).collect::<Vec<_>>().join("\n")
    }

    /// Generates expected zbi items after successful load/verification/fixup
    pub(crate) fn make_expected_zbi_items(
        slot: SlotIndex,
        expected_kernel: &[u8],
    ) -> AlignedBuffer {
        let mut expected_zbi_items = AlignedBuffer::new(256 * 1024, ZBI_ALIGNMENT_USIZE);
        let mut items = ZbiContainer::new(&mut expected_zbi_items[..]).unwrap();
        items.extend(&ZbiContainer::parse(&expected_kernel[..]).unwrap()).unwrap();
        append_cmd_line(&mut expected_zbi_items, FakeGblOps::ADDED_ZBI_COMMANDLINE_CONTENTS);
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_0=val\0");
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_1=val\0");
        append_cmd_line(
            &mut expected_zbi_items,
            format!("zvb.current_slot={}", char::from(slot)).as_bytes(),
        );
        expected_zbi_items
    }

    pub(crate) fn make_expected_zbi_items_with_bootloader_files(
        slot: SlotIndex,
        expected_kernel: &[u8],
    ) -> AlignedBuffer {
        let mut expected_zbi_items = make_expected_zbi_items(slot, expected_kernel);
        append_zbi_file(&mut expected_zbi_items[..], FakeGblOps::TEST_BOOTLOADER_FILE_1);
        append_zbi_file(&mut expected_zbi_items[..], FakeGblOps::TEST_BOOTLOADER_FILE_2);
        expected_zbi_items
    }

    /// Helper macro for comparing between two ZBI containers.
    macro_rules! assert_zbi_eq {
        ( $actual:expr, $expected:expr ) => {{
            assert_eq!(
                normalize_zbi($actual),
                normalize_zbi($expected),
                "\nactual: \n{}, \nexpected: \n{}\n",
                normalized_zbi_to_str($actual),
                normalized_zbi_to_str($expected)
            );
        }};
    }

    // Checks that the given zbi_items and kernel are correctly fixed up against test images.
    pub(crate) fn check_fixedup(
        slot: SlotIndex,
        zbi_items: &[u8],
        kernel: &[u8],
        lock_state: LockState,
    ) {
        let expected_kernel = read_test_data(&format!("zircon_{}.zbi", char::from(slot)));
        let expected_zbi_items = match lock_state {
            fastboot::LockState::Locked => make_expected_zbi_items(slot, &expected_kernel),
            fastboot::LockState::Unlocked => {
                make_expected_zbi_items_with_bootloader_files(slot, &expected_kernel)
            }
        };
        assert_zbi_eq!(zbi_items, &expected_zbi_items);
        assert_zbi_eq!(kernel, &expected_kernel);
        assert_eq!(zbi_items.as_ptr() as usize % PAGE_SIZE, 0);
    }

    /// Checks that rollback indices are not updated.
    pub(crate) fn check_rollback_not_updated(ops: &mut FakeGblOps) {
        assert_eq!(
            ops.avb_ops.rollbacks,
            [
                (TEST_ROLLBACK_INDEX_LOCATION, Ok(0)),
                (usize::try_from(AVB_CERT_PSK_VERSION_LOCATION).unwrap(), Ok(0)),
                (usize::try_from(AVB_CERT_PIK_VERSION_LOCATION).unwrap(), Ok(0))
            ]
            .into()
        );
    }

    /// Set next ABR boot target.
    fn set_next_boot_slot(ops: &mut FakeGblOps, slot: SlotIndex) {
        match slot {
            SlotIndex::R => {
                mark_slot_unbootable(&mut GblAbrOps(ops), SlotIndex::A, UnbootableReason::None)
                    .unwrap();
                mark_slot_unbootable(&mut GblAbrOps(ops), SlotIndex::B, UnbootableReason::None)
                    .unwrap()
            }
            _ => mark_slot_active(&mut GblAbrOps(ops), slot).unwrap(),
        }
    }

    /// Tests zircon_main loads and verifies `slot` that is not marked successful.
    fn test_zircon_main_unsuccessful_slot(slot: SlotIndex) {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut load_buffer = AlignedBuffer::new(256 * 1024, ZIRCON_KERNEL_ALIGNMENT);
        set_next_boot_slot(&mut ops, slot);
        let LoadedVerifiedZircon { zbi_items, kernel, slot: booted_slot } =
            zircon_main(&mut ops, &mut load_buffer[..], |_| {}).unwrap();
        assert_eq!(booted_slot, slot);
        check_fixedup(slot, zbi_items, kernel, LockState::Locked);
        // Rollback indices are not updated because slots are not successful.
        check_rollback_not_updated(&mut ops);
    }

    #[test]
    fn test_zircon_main_unsuccessful_slot_a() {
        test_zircon_main_unsuccessful_slot(SlotIndex::A);
    }

    #[test]
    fn test_zircon_main_unsuccessful_slot_b() {
        test_zircon_main_unsuccessful_slot(SlotIndex::B);
    }

    #[test]
    fn test_zircon_main_unsuccessful_slot_r() {
        test_zircon_main_unsuccessful_slot(SlotIndex::R);
    }

    /// Checks that rollback indices are updated.
    pub(crate) fn check_rollback_updated(ops: &mut FakeGblOps) {
        assert_eq!(
            ops.avb_ops.rollbacks,
            [
                (TEST_ROLLBACK_INDEX_LOCATION, Ok(TEST_ROLLBACK_INDEX_VALUE)),
                (
                    usize::try_from(AVB_CERT_PSK_VERSION_LOCATION).unwrap(),
                    Ok(TEST_CERT_PSK_VERSION)
                ),
                (
                    usize::try_from(AVB_CERT_PIK_VERSION_LOCATION).unwrap(),
                    Ok(TEST_CERT_PIK_VERSION)
                )
            ]
            .into()
        );
    }

    /// Tests zircon_main loads and verifies `slot` that is already marked successful. Rollback
    /// indices should be updated.
    fn test_zircon_main_successful_slot(slot: SlotIndex) {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut load_buffer = AlignedBuffer::new(256 * 1024, ZIRCON_KERNEL_ALIGNMENT);
        mark_slot_active(&mut GblAbrOps(&mut ops), slot).unwrap();
        mark_slot_successful(&mut GblAbrOps(&mut ops), slot, false).unwrap();
        let LoadedVerifiedZircon { zbi_items, kernel, slot: booted_slot } =
            zircon_main(&mut ops, &mut load_buffer[..], |_| {}).unwrap();
        assert_eq!(booted_slot, slot);

        check_fixedup(slot, zbi_items, kernel, LockState::Locked);
        // Rollback indices are updated because slots are successful.
        check_rollback_updated(&mut ops);
    }

    #[test]
    fn test_zircon_main_successful_slot_a() {
        test_zircon_main_successful_slot(SlotIndex::A);
    }

    #[test]
    fn test_zircon_main_successful_slot_b() {
        test_zircon_main_successful_slot(SlotIndex::B);
    }

    #[test]
    fn test_zircon_main_one_shot_recovery() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut load_buffer = AlignedBuffer::new(256 * 1024, ZIRCON_KERNEL_ALIGNMENT);
        mark_slot_active(&mut GblAbrOps(&mut ops), SlotIndex::A).unwrap();
        mark_slot_successful(&mut GblAbrOps(&mut ops), SlotIndex::A, false).unwrap();
        ops.one_shot_boot_mode = Some(OneShotBootMode::Recovery);
        let LoadedVerifiedZircon { zbi_items, kernel, slot: booted_slot } =
            zircon_main(&mut ops, &mut load_buffer[..], |_| {
                panic!("Should not enter fastboot on OneShotBootMode::Recovery")
            })
            .unwrap();
        assert_eq!(booted_slot, SlotIndex::R);
        check_fixedup(SlotIndex::R, zbi_items, kernel, LockState::Locked);
        check_rollback_not_updated(&mut ops);
        // The hardware-triggered recovery request must not leave a persistent one-shot flag in
        // A/B/R metadata.
        assert_eq!(get_and_clear_one_shot_flag(&mut GblAbrOps(&mut ops)), Ok(0));

        // One-shot recovery is cleared after one boot; subsequent boot selects active slot A.
        let LoadedVerifiedZircon { zbi_items, kernel, slot: booted_slot } =
            zircon_main(&mut ops, &mut load_buffer[..], |_| panic!("Should not enter fastboot"))
                .unwrap();
        assert_eq!(booted_slot, SlotIndex::A);
        check_fixedup(SlotIndex::A, zbi_items, kernel, LockState::Locked);
        check_rollback_updated(&mut ops);
    }

    fn test_zircon_main_fails_on_corrupted_slot(slot: SlotIndex) {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let part = format!("zircon_{}", char::from(slot));
        // Corrupt offset = 64. Skips the ZBI header
        ops.flip_partition_bytes(&part, 64, 1);
        let mut load_buffer = AlignedBuffer::new(256 * 1024, ZIRCON_KERNEL_ALIGNMENT);
        set_next_boot_slot(&mut ops, slot);
        let _ = mark_slot_successful(&mut GblAbrOps(&mut ops), slot, false);
        assert!(zircon_main(&mut ops, &mut load_buffer[..], |_| {}).is_err());
        check_rollback_not_updated(&mut ops);
    }

    #[test]
    fn test_zircon_main_fails_on_corrupted_slot_a() {
        test_zircon_main_fails_on_corrupted_slot(SlotIndex::A);
    }

    #[test]
    fn test_zircon_main_fails_on_corrupted_slot_b() {
        test_zircon_main_fails_on_corrupted_slot(SlotIndex::B);
    }

    #[test]
    fn test_zircon_main_fails_on_corrupted_slot_r() {
        test_zircon_main_fails_on_corrupted_slot(SlotIndex::R);
    }

    /// Test failure due to rollback protection.
    fn test_zircon_main_fails_on_rollback_protection(slot: SlotIndex) {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        ops.avb_ops
            .rollbacks
            .insert(TEST_ROLLBACK_INDEX_LOCATION, Ok(TEST_ROLLBACK_INDEX_VALUE + 1));
        let mut load_buffer = AlignedBuffer::new(256 * 1024, ZIRCON_KERNEL_ALIGNMENT);
        set_next_boot_slot(&mut ops, slot);
        let _ = mark_slot_successful(&mut GblAbrOps(&mut ops), slot, false);
        assert!(zircon_main(&mut ops, &mut load_buffer[..], |_| {}).is_err());
        assert_eq!(
            ops.avb_ops.rollbacks,
            [
                (TEST_ROLLBACK_INDEX_LOCATION, Ok(TEST_ROLLBACK_INDEX_VALUE + 1)),
                (usize::try_from(AVB_CERT_PSK_VERSION_LOCATION).unwrap(), Ok(0)),
                (usize::try_from(AVB_CERT_PIK_VERSION_LOCATION).unwrap(), Ok(0))
            ]
            .into()
        );
    }

    #[test]
    fn test_zircon_main_fails_on_rollback_protection_slot_a() {
        test_zircon_main_fails_on_rollback_protection(SlotIndex::A);
    }

    #[test]
    fn test_zircon_main_fails_on_rollback_protection_slot_b() {
        test_zircon_main_fails_on_rollback_protection(SlotIndex::B);
    }

    #[test]
    fn test_zircon_main_fails_on_rollback_protection_slot_r() {
        test_zircon_main_fails_on_rollback_protection(SlotIndex::R);
    }

    /// Tests that unlocked mode ignores avb failures
    fn test_zircon_main_unlock_ignore_avb_failures(slot: SlotIndex) {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        ops.avb_device_status.is_unlocked = true;
        ops.avb_ops
            .rollbacks
            .insert(TEST_ROLLBACK_INDEX_LOCATION, Ok(TEST_ROLLBACK_INDEX_VALUE + 1));
        let mut load_buffer = AlignedBuffer::new(256 * 1024, ZIRCON_KERNEL_ALIGNMENT);
        set_next_boot_slot(&mut ops, slot);
        let LoadedVerifiedZircon { zbi_items, kernel, slot: booted_slot } =
            zircon_main(&mut ops, &mut load_buffer[..], |_| {}).unwrap();
        assert_eq!(booted_slot, slot);
        check_fixedup(slot, zbi_items, kernel, LockState::Unlocked);
    }

    #[test]
    fn test_zircon_main_unlock_ignore_avb_failures_slot_a() {
        test_zircon_main_unlock_ignore_avb_failures(SlotIndex::A);
    }

    #[test]
    fn test_zircon_main_unlock_ignore_avb_failures_slot_b() {
        test_zircon_main_unlock_ignore_avb_failures(SlotIndex::B);
    }

    #[test]
    fn test_zircon_main_unlock_ignore_avb_failures_slot_r() {
        test_zircon_main_unlock_ignore_avb_failures(SlotIndex::R);
    }

    /// Generates expected zbi items without avb zbi items.
    pub(crate) fn make_expected_zbi_items_wo_avb(
        slot: SlotIndex,
        expected_kernel: &[u8],
    ) -> AlignedBuffer {
        let mut expected_zbi_items = AlignedBuffer::new(256 * 1024, ZBI_ALIGNMENT_USIZE);
        let mut items = ZbiContainer::new(&mut expected_zbi_items[..]).unwrap();
        items.extend(&ZbiContainer::parse(&expected_kernel[..]).unwrap()).unwrap();
        append_cmd_line(&mut expected_zbi_items, FakeGblOps::ADDED_ZBI_COMMANDLINE_CONTENTS);
        append_cmd_line(
            &mut expected_zbi_items,
            format!("zvb.current_slot={}", char::from(slot)).as_bytes(),
        );
        append_zbi_file(&mut expected_zbi_items, FakeGblOps::TEST_BOOTLOADER_FILE_1);
        append_zbi_file(&mut expected_zbi_items, FakeGblOps::TEST_BOOTLOADER_FILE_2);
        expected_zbi_items
    }

    /// Tests that vbmeta items are ignored if it is corrupted.
    fn test_zircon_main_unlock_ignore_vbmeta_items_if_corrupted(slot: SlotIndex) {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        ops.avb_device_status.is_unlocked = true;
        let part = format!("vbmeta_{}", char::from(slot));
        ops.flip_partition_bytes(&part, 0, 64);
        let mut load_buffer = AlignedBuffer::new(256 * 1024, ZIRCON_KERNEL_ALIGNMENT);
        set_next_boot_slot(&mut ops, slot);
        let LoadedVerifiedZircon { zbi_items, kernel, slot: booted_slot } =
            zircon_main(&mut ops, &mut load_buffer[..], |_| {}).unwrap();
        assert_eq!(booted_slot, slot);

        let expected_kernel = read_test_data(&format!("zircon_{}.zbi", char::from(slot)));
        // vbmeta zbi items are ignored.
        let expected_zbi_items = make_expected_zbi_items_wo_avb(slot, &expected_kernel);
        assert_zbi_eq!(zbi_items, &expected_zbi_items);
        assert_zbi_eq!(kernel, &expected_kernel);
    }

    #[test]
    fn test_zircon_main_unlock_ignore_vbmeta_items_if_corrupted_slot_a() {
        test_zircon_main_unlock_ignore_vbmeta_items_if_corrupted(SlotIndex::A);
    }

    #[test]
    fn test_zircon_main_unlock_ignore_vbmeta_items_if_corrupted_slot_b() {
        test_zircon_main_unlock_ignore_vbmeta_items_if_corrupted(SlotIndex::B);
    }

    #[test]
    fn test_zircon_main_unlock_ignore_vbmeta_items_if_corrupted_slot_r() {
        test_zircon_main_unlock_ignore_vbmeta_items_if_corrupted(SlotIndex::R);
    }

    /// Helper for booting an image via "fastboot boot"
    fn zircon_main_fastboot_boot<'a>(
        ops: &mut FakeGblOps,
        load_buffer: &'a mut [u8],
        bootimg: &[u8],
        listener: &SharedTestListener,
    ) -> GblResult<LoadedVerifiedZircon<'a>> {
        set_one_shot_bootloader(&mut GblAbrOps(ops), true).unwrap();
        zircon_main(ops, &mut load_buffer[..], |fb| {
            listener.add_transport_input(format!("download:{:#x}", bootimg.len()).as_bytes());
            listener.add_transport_input(&bootimg);
            listener.add_transport_input(b"boot");
            listener.add_transport_input(b"continue");
            fb.run_n::<2>(&mut vec![0u8; 256 * 1024], &mut [listener], Some(listener));
        })
    }

    /// Helper for testing "fastboot boot" succeeds on valid images.
    fn test_zircon_main_fastboot_boot_succeed_on_valid_images(slot: SlotIndex) {
        let listener = SharedTestListener::default();
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        ops.avb_device_status.is_unlocked = true;
        let mut load_buffer = AlignedBuffer::new(256 * 1024, ZIRCON_KERNEL_ALIGNMENT);
        let bootimg = read_test_data("zircon_fastboot_bootimg");
        set_next_boot_slot(&mut ops, slot);
        let LoadedVerifiedZircon { zbi_items, kernel, slot: booted_slot } =
            zircon_main_fastboot_boot(&mut ops, &mut load_buffer[..], &bootimg, &listener).unwrap();
        assert_eq!(slot, booted_slot);
        let expected_kernel = read_test_data("zircon_slotless.zbi");
        let expected_zbi_items =
            make_expected_zbi_items_with_bootloader_files(slot, &expected_kernel);
        assert_zbi_eq!(zbi_items, &expected_zbi_items);
        assert_zbi_eq!(kernel, &expected_kernel);
        check_rollback_not_updated(&mut ops);

        assert_eq!(
            listener.transport_out_queue(),
            make_expected_transport_out(&[
                b"DATA00003000",
                b"OKAY",
                format!("INFOBoot image as Fuchsia slot {}", char::from(slot)).as_bytes(),
                b"OKAY",
            ]),
            "\nActual Transport output:\n{}",
            listener.dump_transport_out_queue()
        );
    }

    #[test]
    fn test_zircon_main_fastboot_boot_succeed_on_valid_images_slot_a() {
        test_zircon_main_fastboot_boot_succeed_on_valid_images(SlotIndex::A)
    }

    #[test]
    fn test_zircon_main_fastboot_boot_succeed_on_valid_images_slot_b() {
        test_zircon_main_fastboot_boot_succeed_on_valid_images(SlotIndex::B)
    }

    #[test]
    fn test_zircon_main_fastboot_boot_succeed_on_valid_images_slot_r() {
        test_zircon_main_fastboot_boot_succeed_on_valid_images(SlotIndex::R)
    }

    // This test uses a call counter to return different lock states
    // to Fastboot and AVB. This is fragile and relies on the exact order of calls
    // (Fastboot first, AVB second). Revisit if implementation changes.
    // TODO(b/506730736): Revisit this fragile call counter approach and support
    // fastboot boot in locked mode via command override without re-implementing the
    // boot flow.
    #[test]
    fn test_zircon_main_fastboot_boot_fail_on_corrupted_images() {
        let listener = SharedTestListener::default();
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut calls = 0;
        let mut handler = || {
            calls += 1;
            Ok(crate::gbl_avb::AvbDeviceStatus { is_unlocked: calls == 1, ..Default::default() })
        };
        ops.avb_read_device_status_handler = Some(&mut handler);
        let mut load_buffer = AlignedBuffer::new(256 * 1024, ZIRCON_KERNEL_ALIGNMENT);
        let mut bootimg = read_test_data("zircon_fastboot_bootimg");
        bootimg[4096 + 64] = !bootimg[4096 + 64];
        let LoadedVerifiedZircon { zbi_items, kernel, .. } =
            zircon_main_fastboot_boot(&mut ops, &mut load_buffer[..], &bootimg, &listener).unwrap();
        // fastboot boot fails. Device should boot normally.
        check_fixedup(SlotIndex::A, zbi_items, kernel, LockState::Locked);

        assert_eq!(
            listener.transport_out_queue(),
            make_expected_transport_out(&[
                b"DATA00003000",
                b"OKAY",
                b"FAILAvbSlotVerifyError(Verification(None))",
                b"OKAY",
            ]),
            "\nActual Transport output:\n{}",
            listener.dump_transport_out_queue()
        );
    }

    // This test uses a call counter to return different lock states
    // to Fastboot and AVB. This is fragile and relies on the exact order of calls
    // (Fastboot first, AVB second). Revisit if implementation changes.
    // TODO(b/506730736): Revisit this fragile call counter approach and support
    // fastboot boot in locked mode via command override without re-implementing the boot flow.
    #[test]
    fn test_zircon_main_fastboot_boot_fails_on_rollback_protection() {
        let listener = SharedTestListener::default();
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut calls = 0;
        let mut handler = || {
            calls += 1;
            Ok(crate::gbl_avb::AvbDeviceStatus { is_unlocked: calls == 1, ..Default::default() })
        };
        ops.avb_read_device_status_handler = Some(&mut handler);
        ops.avb_ops
            .rollbacks
            .insert(TEST_ROLLBACK_INDEX_LOCATION, Ok(TEST_ROLLBACK_INDEX_VALUE + 1));
        let mut load_buffer = AlignedBuffer::new(256 * 1024, ZIRCON_KERNEL_ALIGNMENT);
        let bootimg = read_test_data("zircon_fastboot_bootimg");
        assert!(
            zircon_main_fastboot_boot(&mut ops, &mut load_buffer[..], &bootimg, &listener).is_err()
        );

        assert_eq!(
            listener.transport_out_queue(),
            make_expected_transport_out(&[
                b"DATA00003000",
                b"OKAY",
                b"FAILAvbSlotVerifyError(RollbackIndex(None))",
                b"OKAY",
            ]),
            "\nActual Transport output:\n{}",
            listener.dump_transport_out_queue()
        );
    }

    #[test]
    fn test_zircon_main_fastboot_boot_unlock_ignore_avb_failure() {
        let listener = SharedTestListener::default();
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        ops.avb_device_status.is_unlocked = true;
        ops.avb_ops
            .rollbacks
            .insert(TEST_ROLLBACK_INDEX_LOCATION, Ok(TEST_ROLLBACK_INDEX_VALUE + 1));
        let mut load_buffer = AlignedBuffer::new(256 * 1024, ZIRCON_KERNEL_ALIGNMENT);
        let bootimg = read_test_data("zircon_fastboot_bootimg");
        let LoadedVerifiedZircon { zbi_items, kernel, .. } =
            zircon_main_fastboot_boot(&mut ops, &mut load_buffer[..], &bootimg, &listener).unwrap();
        let expected_kernel = read_test_data("zircon_slotless.zbi");
        let expected_zbi_items =
            make_expected_zbi_items_with_bootloader_files(SlotIndex::A, &expected_kernel);
        assert_zbi_eq!(zbi_items, &expected_zbi_items);
        assert_zbi_eq!(kernel, &expected_kernel);

        assert_eq!(
            listener.transport_out_queue(),
            make_expected_transport_out(&[
                b"DATA00003000",
                b"OKAY",
                b"INFOBoot image as Fuchsia slot a",
                b"OKAY",
            ]),
            "\nActual Transport output:\n{}",
            listener.dump_transport_out_queue()
        );
    }

    #[test]
    fn test_zircon_main_fastboot_boot_unlock_ignore_vbmeta_items_if_corrupted() {
        let listener = SharedTestListener::default();
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        ops.avb_device_status.is_unlocked = true;
        ops.avb_ops
            .rollbacks
            .insert(TEST_ROLLBACK_INDEX_LOCATION, Ok(TEST_ROLLBACK_INDEX_VALUE + 1));
        let mut load_buffer = AlignedBuffer::new(256 * 1024, ZIRCON_KERNEL_ALIGNMENT);
        let mut bootimg = read_test_data("zircon_fastboot_bootimg");
        let kernel_len = read_test_data("zircon_slotless.zbi").len();
        bootimg[4096 + kernel_len..].fill(0);
        let LoadedVerifiedZircon { zbi_items, kernel, .. } =
            zircon_main_fastboot_boot(&mut ops, &mut load_buffer[..], &bootimg, &listener).unwrap();
        let expected_kernel = read_test_data("zircon_slotless.zbi");
        let expected_zbi_items = make_expected_zbi_items_wo_avb(SlotIndex::A, &expected_kernel);
        assert_zbi_eq!(zbi_items, &expected_zbi_items);
        assert_zbi_eq!(kernel, &expected_kernel);

        assert_eq!(
            listener.transport_out_queue(),
            make_expected_transport_out(&[
                b"DATA00003000",
                b"OKAY",
                b"INFOBoot image as Fuchsia slot a",
                b"OKAY",
            ]),
            "\nActual Transport output:\n{}",
            listener.dump_transport_out_queue()
        );
    }

    #[test]
    fn test_zircon_load_verify_fixup_slotless() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut load_buffer = AlignedBuffer::new(256 * 1024, ZIRCON_KERNEL_ALIGNMENT);
        let (zbi_items, kernel) =
            zircon_load_verify_fixup(&mut ops, None, true, &mut load_buffer).unwrap();

        let expected_kernel = read_test_data(ZIRCON_SLOTLESS_ZBI_FILE);

        // Create ZBI Items without slot (mostly taken from make_expected_zbi_items_wo_avb)
        let mut expected_zbi_items = AlignedBuffer::new(256 * 1024, ZBI_ALIGNMENT_USIZE);
        let mut items = ZbiContainer::new(&mut expected_zbi_items[..]).unwrap();
        items.extend(&ZbiContainer::parse(&expected_kernel[..]).unwrap()).unwrap();
        append_cmd_line(&mut expected_zbi_items, FakeGblOps::ADDED_ZBI_COMMANDLINE_CONTENTS);
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_0=val\0");
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_1=val\0");

        assert_zbi_eq!(kernel, &expected_kernel);
        assert_zbi_eq!(zbi_items, &expected_zbi_items);
    }

    #[test]
    #[cfg(feature = "gbl_dev")]
    fn test_zircon_load_verify_no_avb_status() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        ops.avb_device_status = DefaultOk(Err(AvbIoError::NotImplemented));

        let mut load_buffer = AlignedBuffer::new(256 * 1024, ZIRCON_KERNEL_ALIGNMENT);
        let (zbi_items, kernel) =
            zircon_load_verify_fixup(&mut ops, None, true, &mut load_buffer).unwrap();

        let expected_kernel = read_test_data(ZIRCON_SLOTLESS_ZBI_FILE);

        // Create ZBI Items without slot (mostly taken from make_expected_zbi_items_wo_avb)
        let mut expected_zbi_items = AlignedBuffer::new(256 * 1024, ZBI_ALIGNMENT_USIZE);
        let mut items = ZbiContainer::new(&mut expected_zbi_items[..]).unwrap();
        items.extend(&ZbiContainer::parse(&expected_kernel[..]).unwrap()).unwrap();
        append_cmd_line(&mut expected_zbi_items, FakeGblOps::ADDED_ZBI_COMMANDLINE_CONTENTS);
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_0=val\0");
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_1=val\0");
        append_zbi_file(&mut expected_zbi_items, FakeGblOps::TEST_BOOTLOADER_FILE_1);
        append_zbi_file(&mut expected_zbi_items, FakeGblOps::TEST_BOOTLOADER_FILE_2);

        assert_zbi_eq!(kernel, &expected_kernel);
        assert_zbi_eq!(zbi_items, &expected_zbi_items);
    }

    #[test]
    fn test_zircon_load_verify_fixup_not_enough_buffer() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let zircon_a_zbi = read_test_data(ZIRCON_A_ZBI_FILE);
        // Allocate a buffer that is too small.
        let mut load_buffer = AlignedBuffer::new(
            zircon_a_zbi.len() + TEST_KERNEL_RESERVED_MEMORY_SIZE - 1,
            ZIRCON_KERNEL_ALIGNMENT,
        );
        let result = zircon_load_verify_fixup(&mut ops, Some(SlotIndex::A), true, &mut load_buffer);
        assert!(result.is_err());
    }

    #[test]
    fn test_zircon_load_verify_abr_with_buffer_exhaust_retries() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut load_buffer = AlignedBuffer::new(256 * 1024, ZIRCON_KERNEL_ALIGNMENT);

        for _ in 0..ABR_MAX_TRIES_REMAINING {
            let result = zircon_load_verify_abr_with_buffer(&mut ops, &mut load_buffer).unwrap();
            assert_eq!(result.slot, SlotIndex::A);
        }
        for _ in 0..ABR_MAX_TRIES_REMAINING {
            let result = zircon_load_verify_abr_with_buffer(&mut ops, &mut load_buffer).unwrap();
            assert_eq!(result.slot, SlotIndex::B);
        }
        // Tests that load falls back to R eventually.
        let result = zircon_load_verify_abr_with_buffer(&mut ops, &mut load_buffer).unwrap();
        assert_eq!(result.slot, SlotIndex::R);
    }

    #[test]
    fn test_zircon_load_verify_abr_with_buffer_legacy_naming() {
        let storage = create_storage_legacy_names();
        let mut ops = create_gbl_ops(&storage);
        let mut load_buffer = AlignedBuffer::new(256 * 1024, ZIRCON_KERNEL_ALIGNMENT);

        // Tests by exhausting all slots retries so it exercises all legacy name matching code
        // paths.
        for _ in 0..ABR_MAX_TRIES_REMAINING {
            let result = zircon_load_verify_abr_with_buffer(&mut ops, &mut load_buffer).unwrap();
            assert_eq!(result.slot, SlotIndex::A);
        }
        for _ in 0..ABR_MAX_TRIES_REMAINING {
            let result = zircon_load_verify_abr_with_buffer(&mut ops, &mut load_buffer).unwrap();
            assert_eq!(result.slot, SlotIndex::B);
        }
        // Tests that load falls back to R eventually.
        let result = zircon_load_verify_abr_with_buffer(&mut ops, &mut load_buffer).unwrap();
        assert_eq!(result.slot, SlotIndex::R);
    }

    #[test]
    fn test_zircon_load_verify_fixup_no_bootloader_file() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        // Ensure no bootloader files are present.
        ops.zbi_bootloader_files_buffer.fill(0);
        let mut load_buffer = AlignedBuffer::new(256 * 1024, ZIRCON_KERNEL_ALIGNMENT);

        let (zbi_items, kernel) =
            zircon_load_verify_fixup(&mut ops, Some(SlotIndex::A), true, &mut load_buffer).unwrap();

        let expected_kernel = read_test_data(ZIRCON_A_ZBI_FILE);

        // Make ZBI items without bootloader (make_expected_zbi_items() as reference).
        let mut expected_zbi_items = AlignedBuffer::new(256 * 1024, ZBI_ALIGNMENT_USIZE);
        let mut items = ZbiContainer::new(&mut expected_zbi_items[..]).unwrap();
        items.extend(&ZbiContainer::parse(&expected_kernel[..]).unwrap()).unwrap();
        append_cmd_line(&mut expected_zbi_items, FakeGblOps::ADDED_ZBI_COMMANDLINE_CONTENTS);
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_0=val\0");
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_1=val\0");
        append_cmd_line(
            &mut expected_zbi_items,
            format!("zvb.current_slot={}", char::from(SlotIndex::A)).as_bytes(),
        );

        assert_zbi_eq!(kernel, &expected_kernel);
        assert_zbi_eq!(zbi_items, &expected_zbi_items);
    }
}
