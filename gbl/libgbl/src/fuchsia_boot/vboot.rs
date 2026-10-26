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

use crate::{
    fuchsia_boot::{zbi_split_unused_buffer_mut, zircon_part_name, SlotIndex},
    gbl_avb::ops::{GblAvbOps, PreloadBufferState},
    gbl_println, GblOps, Result as GblResult,
};
use avb::{slot_verify, Descriptor, HashtreeErrorMode, Ops as _, SlotVerifyError, SlotVerifyFlags};
use zbi::{merge_within, ZbiContainer};
use zerocopy::SplitByteSliceMut;

/// Performs AVB verification of a ZBI kernel from the given buffer and fixes up AVB ZBI items into
/// the same ZBI container. `load_buffer` should reserve extra space for in-coming AVB items.
pub(crate) fn zircon_verify_kernel_in_place<'a>(
    gbl_ops: &mut impl GblOps<'a>,
    slot: Option<SlotIndex>,
    slot_booted_successfully: bool,
    load_buffer: &mut [u8],
) -> GblResult<()> {
    let (kernel, desc_buf) = zbi_split_unused_buffer_mut(&mut load_buffer[..])?;
    let desc_zbi_off = kernel.len();
    // Collects ZBI items from vbmetadata and appends to the `desc_buf` buffer.
    let mut avb_desc = ZbiContainer::new(&mut desc_buf[..])?;
    zircon_verify_kernel_internal(gbl_ops, slot, slot_booted_successfully, kernel, &mut avb_desc)?;
    // Merges the vbmeta descriptor ZBI container into the ZBI kernel container.
    merge_within(load_buffer, desc_zbi_off)?;
    Ok(())
}

/// Internal helper for AVB verification for zircon.
fn zircon_verify_kernel_internal<'a, 'b, B: SplitByteSliceMut + PartialEq>(
    gbl_ops: &mut impl GblOps<'b>,
    slot: Option<SlotIndex>,
    slot_booted_successfully: bool,
    zbi_kernel: &'a mut [u8],
    zbi_items: &mut ZbiContainer<B>,
) -> GblResult<()> {
    let (kernel, _) = zbi_split_unused_buffer_mut(&mut zbi_kernel[..])?;

    // Verifies the kernel.
    let part = zircon_part_name(slot);
    let slotless_part = zircon_part_name(None);
    let mut preloaded = [(slotless_part, PreloadBufferState::Loaded(&kernel[..]))];
    let mut avb_ops = GblAvbOps::new(gbl_ops, slot, &mut preloaded[..], true);

    // Determines verify flags and error mode.
    let unlocked = avb_ops.read_is_device_unlocked()?;
    let mode = HashtreeErrorMode::AVB_HASHTREE_ERROR_MODE_EIO; // Don't care for fuchsia
    let flag = match unlocked {
        true => SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_ALLOW_VERIFICATION_ERROR,
        _ => SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_NONE,
    };

    // TODO(b/578053265): Supports optional additional partitions to verify.
    let verify_res = slot_verify(&mut avb_ops, &[c"zircon"], slot.map(|s| s.into()), flag, mode);
    let verified_success = verify_res.is_ok();
    let verify_data = match verify_res {
        Ok(ref v) => {
            gbl_println!(avb_ops.gbl_ops, "{} successfully verified", part);
            v
        }
        Err(ref e)
            if let Some(data) = e.verification_data()
                && unlocked =>
        {
            // Verification failed but was able to load the images from disk,
            // and we're unlocked so it's OK to proceed.
            gbl_println!(
                avb_ops.gbl_ops,
                "Verification failed, but device is unlocked - continuing boot"
            );
            data
        }
        Err(SlotVerifyError::InvalidMetadata) | Err(SlotVerifyError::UnsupportedVersion)
            if unlocked =>
        {
            // The vbmetadata is invalid or unknown version, but we're unlocked
            // so we can just return success. In this case there will be no
            // vbmeta items to collect or rollbacks to set.
            //
            // This is useful so that boards don't have to flash a random vbmeta
            // image just to boot.
            gbl_println!(
                avb_ops.gbl_ops,
                "Failed to load vbmeta, but device is unlocked - continuing boot"
            );
            return Ok(());
        }
        Err(e) => {
            // Anything else is a critical failure (e.g. I/O error, OOM, etc).
            // In these cases we want to fail even on an unlocked board because
            // the state is now unknown and unpredictable. It's also more useful
            // for board bringup if we fail when the callbacks are not properly
            // implemented.
            gbl_println!(avb_ops.gbl_ops, "Verification failed: {:?}", e);
            return Err(e.without_verify_data().into());
        }
    };

    let top_level_vbmeta = verify_data.vbmeta_data().first().unwrap();
    assert!(
        top_level_vbmeta.partition_name() == c"vbmeta",
        "GBL requires the vbmeta partition as the top-level verification structure. Please \
        contact the GBL team if you encounter this error."
    );

    // Collects ZBI items from top-level vbmetadata and appends to the `zbi_items`.
    //
    // Do not allow ZBIs from chained vbmeta blobs as this could allow privilege escalation
    // from chained authorities that were never intended to be able to control the ZBI.
    for prop in top_level_vbmeta.descriptors()?.iter().filter_map(|d| match d {
        Descriptor::Property(p) if p.key.starts_with("zbi") => Some(p),
        _ => None,
    }) {
        zbi_items.extend_unaligned(prop.value_with_nul.split_last().unwrap().1)?;
    }

    // Update rollback indices if the slot has successfully booted following:
    // https://android.googlesource.com/platform/external/avb/+/android16-release/README.md#updating-stored-rollback-indexes
    if verified_success && slot_booted_successfully && !unlocked {
        avb_ops.update_rollback_indexes(verify_data)?;
    }

    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        constants::ZIRCON_KERNEL_ALIGNMENT,
        fuchsia_boot::test::{
            append_cmd_line, corrupt_data, create_gbl_ops, create_storage, normalize_zbi,
            TEST_ROLLBACK_INDEX_LOCATION, ZIRCON_A_ZBI_FILE,
        },
        ops::test::{FakeGblOps, FakeGblOpsStorage},
        tests::read_test_data,
    };
    use avb::{IoError, CERT_PIK_VERSION_LOCATION, CERT_PSK_VERSION_LOCATION};
    use libtestutils::AlignedBuffer;
    use zbi::ZBI_ALIGNMENT_USIZE;

    // The cert test keys were both generated with rollback version 42.
    const TEST_CERT_PIK_VERSION: u64 = 42;
    const TEST_CERT_PSK_VERSION: u64 = 42;

    /// Checks if the given ZBI contains the items from our test vbmeta.
    ///
    /// gen_test_data.py embeds a ZBI in the vbmeta property descriptor, with
    /// a few test commandline items. Successful verification should extract
    /// these items from vbmeta and put them in the ZBI item buffer.
    ///
    /// # Arguments
    /// * `zbi_items_buffer`: the ZBI item buffer to check.
    ///
    /// # Returns
    /// True if the given ZBI items are equal to the vbmeta property items,
    /// false if the given ZBI items are empty. Panics otherwise, since these
    /// are the only expected ZBI states in these tests.
    fn zbi_contains_vbmeta_items(zbi_items_buffer: &[u8]) -> bool {
        let normalized = normalize_zbi(&zbi_items_buffer);

        let mut empty_zbi = AlignedBuffer::new(1024, ZBI_ALIGNMENT_USIZE);
        ZbiContainer::new(&mut empty_zbi[..]).unwrap();
        if normalize_zbi(&empty_zbi) == normalized {
            return false;
        }

        let mut vbmeta_zbi = empty_zbi;
        append_cmd_line(&mut vbmeta_zbi, b"vb_prop_0=val\0");
        append_cmd_line(&mut vbmeta_zbi, b"vb_prop_1=val\0");
        if normalize_zbi(&vbmeta_zbi) == normalized {
            return true;
        }

        panic!("Unexpected ZBI items: {:?}", normalized);
    }

    /// Select between testing verification with a valid or corrupted kernel.
    #[derive(PartialEq, Eq)]
    enum KernelState {
        Valid,
        Corrupted,
    }

    /// Calls [zircon_verify_kernel] on the test Zircon A ZBI.
    ///
    /// This helper handles all the common logic necessary to create and
    /// preload the buffers and perform verification.
    ///
    /// Additionally, this verifies some conditions that should always hold,
    /// for example when verification fails the rollbacks should never change.
    ///
    /// # Arguments
    /// * `ops`: the ops to use; in keeping with our verification flows, the
    ///   ZBI will be provided as a preloaded buffer, and everything else will
    ///   be fetched via `ops`.
    /// * `slot_booted_successfully`: true to indicate that the slot has been
    ///   marked successful, which affects the rollback behavior.
    /// * `kernel_state`: whether to preload a valid or corrupted ZBI kernel.
    ///
    /// # Returns
    /// On success, a tuple containing the resulting:
    /// * kernel load buffer
    /// * ZBI items buffer
    fn test_verify_zircon(
        ops: &mut FakeGblOps,
        slot_booted_successfully: bool,
        kernel_state: KernelState,
    ) -> GblResult<(AlignedBuffer, AlignedBuffer)> {
        // Create the [AlignedBuffer] objects for the load buffer and ZBI items.
        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        let mut load_buffer = AlignedBuffer::new(zbi.len(), ZIRCON_KERNEL_ALIGNMENT);
        load_buffer[..zbi.len()].clone_from_slice(zbi);
        let mut zbi_items_buffer = AlignedBuffer::new(1024, ZBI_ALIGNMENT_USIZE);

        if kernel_state == KernelState::Corrupted {
            // Corrupt the first kernel byte, past two ZBI headers. This was
            // chosen arbitrarily, any modification would work.
            load_buffer[64] = !load_buffer[64];
        };

        // Save a copy of the rollbacks and load buffer to compare later.
        let original_rollbacks = ops.avb_ops.rollbacks.clone();
        let original_load_buffer = Vec::from(&load_buffer[..]);

        let mut zbi_items = ZbiContainer::new(&mut zbi_items_buffer[..]).unwrap();

        // Copy ZBI items after kernel first. Because ordering matters, and new items should override
        // older ones.
        let zbi_container = ZbiContainer::parse(&mut load_buffer[..]).unwrap();
        let mut items_iter = zbi_container.iter();
        // Skip first kernel item
        items_iter.next();
        zbi_items.extend_items(items_iter).unwrap();

        let (kernel, _) = zbi_split_unused_buffer_mut(&mut load_buffer[..]).unwrap();
        zircon_verify_kernel_internal(
            ops,
            Some(SlotIndex::A),
            slot_booted_successfully,
            kernel,
            &mut zbi_items,
        )
        .inspect_err(|_| {
            // On verify failure, the load buffer contents should be unmodified.
            // This isn't critical for functionality, but if it ever changes
            // we should update the function documentation.
            assert_eq!(&original_load_buffer[..], &load_buffer[..]);

            // Similarly, the ZBI item buffer should still be empty.
            assert!(!zbi_contains_vbmeta_items(&zbi_items_buffer));

            // On verify failure, the rollbacks must remain unmodified. This is
            // critical and must never be violated.
            assert_eq!(original_rollbacks, ops.avb_ops.rollbacks);
        })?;

        Ok((load_buffer, zbi_items_buffer))
    }

    #[test]
    fn verify_on_nonsuccessful_slot() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let expect_rollback = ops.avb_ops.rollbacks.clone();

        let (load_buffer, zbi_items_buffer) =
            test_verify_zircon(&mut ops, false, KernelState::Valid).unwrap();

        // The load buffer should contain the kernel ZBI at the beginning.
        assert!(&load_buffer[..].starts_with(&read_test_data(ZIRCON_A_ZBI_FILE)));

        // Successful verification: vbmeta embedded ZBI items should be present.
        assert!(zbi_contains_vbmeta_items(&zbi_items_buffer));

        // Slot is not successful, rollback index should not be updated.
        assert_eq!(expect_rollback, ops.avb_ops.rollbacks);
    }

    #[test]
    fn verify_on_successful_slot() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        let (load_buffer, zbi_items_buffer) =
            test_verify_zircon(&mut ops, true, KernelState::Valid).unwrap();

        // The load buffer should contain the kernel ZBI at the beginning.
        assert!(&load_buffer[..].starts_with(&read_test_data(ZIRCON_A_ZBI_FILE)));

        // Successful verification: vbmeta embedded ZBI items should be present.
        assert!(zbi_contains_vbmeta_items(&zbi_items_buffer));

        // Slot is successful, rollback index should be updated.
        // vbmeta_a has rollback index value 2 at location 1.
        assert_eq!(
            ops.avb_ops.rollbacks,
            [
                (1, Ok(2)),
                (usize::try_from(CERT_PSK_VERSION_LOCATION).unwrap(), Ok(TEST_CERT_PSK_VERSION)),
                (usize::try_from(CERT_PIK_VERSION_LOCATION).unwrap(), Ok(TEST_CERT_PIK_VERSION))
            ]
            .into()
        );
    }

    #[test]
    fn verify_with_corrupted_kernel_fails() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        assert!(test_verify_zircon(&mut ops, true, KernelState::Corrupted).is_err());
    }

    #[test]
    fn verify_with_corrupted_vbmetadata_fails() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        // Corrupts vbmetadata
        corrupt_data(&mut ops, "vbmeta_a");

        assert!(test_verify_zircon(&mut ops, true, KernelState::Valid).is_err());
    }

    #[test]
    fn verify_with_rollback_violation_fails() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        // vbmeta_a has rollback index value 2 at location 1. Setting min
        // rollback value of 3 should cause rollback protection failure.
        ops.avb_ops.rollbacks.insert(1, Ok(3));

        assert!(test_verify_zircon(&mut ops, true, KernelState::Valid).is_err());
    }

    #[test]
    fn verify_with_corrupted_kernel_unlocked_succeeds() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        ops.avb_device_status.is_unlocked = true;
        let expect_rollback = ops.avb_ops.rollbacks.clone();

        let (_, zbi_items_buffer) =
            test_verify_zircon(&mut ops, true, KernelState::Corrupted).unwrap();

        // Unlocked: vbmeta embedded ZBI items should be present even on
        // verification failure.
        assert!(zbi_contains_vbmeta_items(&zbi_items_buffer));
        // Rollback index should not be updated in any failure cases, even when unlocked.
        assert_eq!(expect_rollback, ops.avb_ops.rollbacks);
    }

    #[test]
    fn verify_with_corrupted_vbmetadata_unlocked_succeeds() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        // Unlock and corrupt vbmeta.
        ops.avb_device_status.is_unlocked = true;
        let expect_rollback = ops.avb_ops.rollbacks.clone();

        corrupt_data(&mut ops, "vbmeta_a");

        let (_, zbi_items_buffer) = test_verify_zircon(&mut ops, true, KernelState::Valid).unwrap();

        // Vbmetadata is invalid so no ZBI items should be appended.
        assert!(!zbi_contains_vbmeta_items(&zbi_items_buffer));
        // Rollback index should not be updated since the vbmeta was corrupt.
        assert_eq!(expect_rollback, ops.avb_ops.rollbacks);
    }

    #[test]
    fn verify_with_io_error_unlocked_fails() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        // Unlocked, but some verification callback returns I/O error.
        ops.avb_device_status.is_unlocked = true;
        ops.avb_ops.rollbacks.insert(TEST_ROLLBACK_INDEX_LOCATION, Err(IoError::Io));

        // Even when unlocked, I/O error represents a critical failure and
        // should refuse to verify.
        assert!(test_verify_zircon(&mut ops, true, KernelState::Valid).is_err());
    }

    #[cfg(feature = "gbl_dev")]
    #[test]
    fn dev_verify_with_unimplemented_ops_succeeds() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        // Set all AVB ops to return `NotImplemented`.
        ops.avb_device_status.set_err(IoError::NotImplemented);
        ops.avb_cert_read_permanent_attributes_not_implemented = true;
        ops.avb_cert_read_permanent_attributes_hash_not_implemented = true;
        ops.avb_ops.rollbacks.insert(TEST_ROLLBACK_INDEX_LOCATION, Err(IoError::NotImplemented));
        ops.avb_ops.rollbacks.insert(CERT_PIK_VERSION_LOCATION, Err(IoError::NotImplemented));
        ops.avb_ops.rollbacks.insert(CERT_PSK_VERSION_LOCATION, Err(IoError::NotImplemented));
        let expect_rollback = ops.avb_ops.rollbacks.clone();

        let result = test_verify_zircon(&mut ops, true, KernelState::Valid);

        // On dev builds, unimplemented ops should allow booting by default.
        assert!(result.is_ok());

        // Defaults to unlocked, so vbmeta embedded ZBI items should be present.
        let (_, zbi_items_buffer) = result.unwrap();
        assert!(zbi_contains_vbmeta_items(&zbi_items_buffer));

        // Unimplemented rollback indices should not attempt to update.
        assert_eq!(expect_rollback, ops.avb_ops.rollbacks);
    }

    #[cfg(not(feature = "gbl_dev"))]
    #[test]
    fn prod_verify_with_unimplemented_unlock_fails() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        ops.avb_device_status.set_err(IoError::NotImplemented);

        assert!(test_verify_zircon(&mut ops, true, KernelState::Valid).is_err());
    }

    #[cfg(not(feature = "gbl_dev"))]
    #[test]
    fn prod_verify_with_unimplemented_permanent_attributes_fails() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        ops.avb_cert_read_permanent_attributes_not_implemented = true;

        assert!(test_verify_zircon(&mut ops, true, KernelState::Valid).is_err());
    }

    #[cfg(not(feature = "gbl_dev"))]
    #[test]
    fn prod_verify_with_unimplemented_permanent_attributes_hash_fails() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        ops.avb_cert_read_permanent_attributes_hash_not_implemented = true;

        assert!(test_verify_zircon(&mut ops, true, KernelState::Valid).is_err());
    }

    #[cfg(not(feature = "gbl_dev"))]
    #[test]
    fn prod_verify_with_unimplemented_vbmeta_rollback_fails() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        ops.avb_ops.rollbacks.insert(TEST_ROLLBACK_INDEX_LOCATION, Err(IoError::NotImplemented));

        assert!(test_verify_zircon(&mut ops, true, KernelState::Valid).is_err());
    }

    #[cfg(not(feature = "gbl_dev"))]
    #[test]
    fn prod_verify_with_unimplemented_pik_rollback_fails() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        ops.avb_ops.rollbacks.insert(CERT_PIK_VERSION_LOCATION, Err(IoError::NotImplemented));

        assert!(test_verify_zircon(&mut ops, true, KernelState::Valid).is_err());
    }

    #[cfg(not(feature = "gbl_dev"))]
    #[test]
    fn prod_verify_with_unimplemented_psk_rollback_fails() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        ops.avb_ops.rollbacks.insert(CERT_PSK_VERSION_LOCATION, Err(IoError::NotImplemented));

        assert!(test_verify_zircon(&mut ops, true, KernelState::Valid).is_err());
    }

    #[test]
    fn verify_ignores_zbi_props_from_chained_vbmeta() {
        let zbi = read_test_data(ZIRCON_A_ZBI_FILE);

        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"vbmeta_a", read_test_data("vbmeta_top.bin"));
        storage.add_raw_device(c"chained_part_a", read_test_data("vbmeta_chained.bin"));
        storage.add_raw_device(c"zircon_a", &zbi);

        let mut ops = create_gbl_ops(&storage);
        ops.avb_ops.rollbacks.insert(2, Ok(0));

        let mut load_buffer = AlignedBuffer::new(zbi.len(), ZIRCON_KERNEL_ALIGNMENT);
        load_buffer[..zbi.len()].clone_from_slice(&zbi);

        let mut zbi_items_buffer = AlignedBuffer::new(1024, ZBI_ALIGNMENT_USIZE);
        let mut zbi_items = ZbiContainer::new(&mut zbi_items_buffer[..]).unwrap();

        let (kernel, _) = zbi_split_unused_buffer_mut(&mut load_buffer[..]).unwrap();

        zircon_verify_kernel_internal(&mut ops, Some(SlotIndex::A), false, kernel, &mut zbi_items)
            .unwrap();

        let normalized = normalize_zbi(&zbi_items_buffer);

        let mut expected_zbi = AlignedBuffer::new(1024, ZBI_ALIGNMENT_USIZE);
        ZbiContainer::new(&mut expected_zbi[..]).unwrap();
        append_cmd_line(&mut expected_zbi, b"vb_prop_top=val\0");
        // Chained vbmeta tries to add `vb_prop_chained=val` which should not exist here.

        assert_eq!(normalized, normalize_zbi(&expected_zbi));
    }
}
