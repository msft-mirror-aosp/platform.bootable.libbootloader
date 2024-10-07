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
    avb_ops::GblAvbOps,
    fuchsia_boot::{zbi_split_unused_buffer, zircon_part_name, SlotIndex},
    gbl_print, GblOps, Result as GblResult,
};
use avb::{slot_verify, Descriptor, HashtreeErrorMode, Ops as _, SlotVerifyError, SlotVerifyFlags};
use core::ffi::CStr;
use zbi::{merge_within, ZbiContainer};

/// Helper for getting the A/B/R suffix.
fn slot_suffix(slot: Option<SlotIndex>) -> Option<&'static CStr> {
    Some(match slot? {
        SlotIndex::A => c"_a",
        SlotIndex::B => c"_b",
        SlotIndex::R => c"_r",
    })
}

/// Verifies a loaded ZBI kernel.
pub(crate) fn zircon_verify_kernel<'a, 'b>(
    gbl_ops: &mut impl GblOps<'b>,
    slot: Option<SlotIndex>,
    slot_booted_successfully: bool,
    zbi_kernel: &'a mut [u8],
) -> GblResult<()> {
    let (kernel, desc_buf) = zbi_split_unused_buffer(&mut zbi_kernel[..])?;
    let desc_zbi_off = kernel.len();

    // Determines verify flags and error mode.
    let unlocked = gbl_ops.avb_read_is_device_unlocked()?;
    let mode = HashtreeErrorMode::AVB_HASHTREE_ERROR_MODE_EIO; // Don't care for fuchsia
    let flag = match unlocked {
        true => SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_ALLOW_VERIFICATION_ERROR,
        _ => SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_NONE,
    };

    {
        // Verifies the kernel.
        let part = zircon_part_name(slot);
        let preloaded = [(part, &kernel[..])];
        let mut avb_ops = GblAvbOps::new(gbl_ops, &preloaded[..], true);
        // TODO(b/334962583): Supports optional additional partitions to verify.
        let verify_res = slot_verify(&mut avb_ops, &[c"zircon"], slot_suffix(slot), flag, mode);
        let verified_success = verify_res.is_ok();
        let verify_data = match verify_res {
            Ok(v) => {
                gbl_print!(avb_ops.gbl_ops, "{} successfully verified.\r\n", part);
                v
            }
            Err(SlotVerifyError::Verification(Some(v))) if unlocked => {
                gbl_print!(avb_ops.gbl_ops, "Verification failed. Device is unlocked. Ignore.\r\n");
                v
            }
            Err(_) if unlocked => {
                gbl_print!(
                    avb_ops.gbl_ops,
                    "Verification failed. No valid verify metadata. \
                    Device is unlocked. Ignore.\r\n"
                );
                return Ok(());
            }
            Err(e) => {
                gbl_print!(avb_ops.gbl_ops, "Verification failed {:?}.\r\n", e);
                return Err(e.without_verify_data().into());
            }
        };

        // Collects ZBI items from vbmetadata and appends to the `desc_buf` buffer.
        let mut desc_container = ZbiContainer::new(&mut desc_buf[..])?;
        for vbmeta_data in verify_data.vbmeta_data() {
            for prop in vbmeta_data.descriptors()?.iter().filter_map(|d| match d {
                Descriptor::Property(p) if p.key.starts_with("zbi") => Some(p),
                _ => None,
            }) {
                desc_container.extend_unaligned(prop.value)?;
            }
        }

        // Increases rollback indices if the slot has successfully booted.
        if verified_success && slot_booted_successfully {
            for (loc, val) in verify_data.rollback_indexes().iter().enumerate() {
                if *val > 0 && avb_ops.read_rollback_index(loc)? != *val {
                    avb_ops.write_rollback_index(loc, *val)?;
                }
            }

            // Increases rollback index values for Fuchsia key version locations.
            for key_version in avb_ops.key_versions {
                match key_version {
                    Some((loc, rollback)) if avb_ops.read_rollback_index(loc)? != rollback => {
                        avb_ops.write_rollback_index(loc, rollback)?;
                    }
                    _ => {}
                }
            }
        }
    }

    // Merges the vbmeta descriptor ZBI container into the ZBI kernel container.
    Ok(merge_within(zbi_kernel, desc_zbi_off).map(|_| ())?)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::fuchsia_boot::{
        test::{
            append_cmd_line, corrupt_data, create_gbl_ops, create_storage, normalize_zbi,
            read_test_data, AlignedBuffer, ZIRCON_A_ZBI_FILE,
        },
        ZIRCON_KERNEL_ALIGN,
    };
    use avb_bindgen::{AVB_CERT_PIK_VERSION_LOCATION, AVB_CERT_PSK_VERSION_LOCATION};

    // The cert test keys were both generated with rollback version 42.
    const TEST_CERT_PIK_VERSION: u64 = 42;
    const TEST_CERT_PSK_VERSION: u64 = 42;

    #[test]
    fn test_verify_success() {
        let mut storage = create_storage();
        let partitions = storage.as_partition_block_devices();
        let mut ops = create_gbl_ops(&partitions);

        let expect_rollback = ops.avb_ops.rollbacks.clone();
        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        // Adds extra bytes for device ZBI items.
        let mut load_buffer = AlignedBuffer::new(zbi.len() + 1024, ZIRCON_KERNEL_ALIGN);
        load_buffer[..zbi.len()].clone_from_slice(zbi);
        zircon_verify_kernel(&mut ops, Some(SlotIndex::A), false, &mut load_buffer).unwrap();

        // Verifies that vbmeta ZBI items are appended. Non-zbi items are ignored.
        let mut expected_zbi_items = AlignedBuffer::new(zbi.len() + 1024, 8);
        expected_zbi_items[..zbi.len()].clone_from_slice(zbi);
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_0=val\0");
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_1=val\0");
        assert_eq!(normalize_zbi(&load_buffer), normalize_zbi(&expected_zbi_items));

        // Slot is not successful, rollback index should not be updated.
        assert_eq!(expect_rollback, ops.avb_ops.rollbacks);
    }

    #[test]
    fn test_verify_update_rollback_index_for_successful_slot() {
        let mut storage = create_storage();
        let partitions = storage.as_partition_block_devices();
        let mut ops = create_gbl_ops(&partitions);

        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        // Adds extra bytes for device ZBI items.
        let mut load_buffer = AlignedBuffer::new(zbi.len() + 1024, ZIRCON_KERNEL_ALIGN);
        load_buffer[..zbi.len()].clone_from_slice(zbi);
        zircon_verify_kernel(&mut ops, Some(SlotIndex::A), true, &mut load_buffer).unwrap();

        // Slot is successful, rollback index should be updated.
        // vbmeta_a has rollback index value 2 at location 1.
        assert_eq!(
            ops.avb_ops.rollbacks,
            [
                (1, 2),
                (usize::try_from(AVB_CERT_PSK_VERSION_LOCATION).unwrap(), TEST_CERT_PIK_VERSION),
                (usize::try_from(AVB_CERT_PIK_VERSION_LOCATION).unwrap(), TEST_CERT_PIK_VERSION)
            ]
            .into()
        );
    }

    #[test]
    fn test_verify_failed_on_corrupted_image() {
        let mut storage = create_storage();
        let partitions = storage.as_partition_block_devices();
        let mut ops = create_gbl_ops(&partitions);

        let expect_rollback = ops.avb_ops.rollbacks.clone();
        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        // Adds extra bytes for device ZBI items.
        let mut load_buffer = AlignedBuffer::new(zbi.len() + 1024, ZIRCON_KERNEL_ALIGN);
        load_buffer[..zbi.len()].clone_from_slice(zbi);
        // Corrupts a random kernel bytes. Skips pass two ZBI headers.
        load_buffer[64] = !load_buffer[64];
        let expect_load = load_buffer.to_vec();
        assert!(zircon_verify_kernel(&mut ops, Some(SlotIndex::A), true, &mut load_buffer).is_err());
        // Failed while device is locked. ZBI items should not be appended.
        assert_eq!(expect_load, &load_buffer[..]);
        // Rollback index should not be updated on verification failure.
        assert_eq!(expect_rollback, ops.avb_ops.rollbacks);
    }

    #[test]
    fn test_verify_failed_on_corrupted_vbmetadata() {
        let mut storage = create_storage();
        let partitions = storage.as_partition_block_devices();
        let mut ops = create_gbl_ops(&partitions);

        let expect_rollback = ops.avb_ops.rollbacks.clone();
        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        // Adds extra bytes for device ZBI items.
        let mut load = AlignedBuffer::new(zbi.len() + 1024, ZIRCON_KERNEL_ALIGN);
        load[..zbi.len()].clone_from_slice(zbi);
        let expect_load = load.to_vec();
        // Corrupts vbmetadata
        corrupt_data(&mut ops, "vbmeta_a");
        assert!(zircon_verify_kernel(&mut ops, Some(SlotIndex::A), true, &mut load).is_err());
        // Failed while device is locked. ZBI items should not be appended.
        assert_eq!(expect_load, &load[..]);
        // Rollback index should not be updated on verification failure.
        assert_eq!(expect_rollback, ops.avb_ops.rollbacks);
    }

    #[test]
    fn test_verify_failed_on_rollback_protection() {
        let mut storage = create_storage();
        let partitions = storage.as_partition_block_devices();
        let mut ops = create_gbl_ops(&partitions);

        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        // Adds extra bytes for device ZBI items.
        let mut load_buffer = AlignedBuffer::new(zbi.len() + 1024, ZIRCON_KERNEL_ALIGN);
        load_buffer[..zbi.len()].clone_from_slice(zbi);
        let expect_load = load_buffer.to_vec();
        // vbmeta_a has rollback index value 2 at location 1. Setting min rollback value of 3 should
        // cause rollback protection failure.
        ops.avb_ops.rollbacks.insert(1, 3);
        let expect_rollback = ops.avb_ops.rollbacks.clone();
        assert!(zircon_verify_kernel(&mut ops, Some(SlotIndex::A), true, &mut load_buffer).is_err());
        // Failed while device is locked. ZBI items should not be appended.
        assert_eq!(expect_load, &load_buffer[..]);
        // Rollback index should not be updated on verification failure.
        assert_eq!(expect_rollback, ops.avb_ops.rollbacks);
    }

    #[test]
    fn test_verify_failure_when_unlocked() {
        let mut storage = create_storage();
        let partitions = storage.as_partition_block_devices();
        let mut ops = create_gbl_ops(&partitions);

        ops.avb_ops.unlock_state = Ok(true);
        let expect_rollback = ops.avb_ops.rollbacks.clone();

        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        // Adds extra bytes for device ZBI items.
        let mut load_buffer = AlignedBuffer::new(zbi.len() + 1024, ZIRCON_KERNEL_ALIGN);
        load_buffer[..zbi.len()].clone_from_slice(zbi);
        // Corrupts a random kernel bytes. Skips pass two ZBI headers.
        load_buffer[64] = !load_buffer[64];
        // Verification should proceeds OK.
        zircon_verify_kernel(&mut ops, Some(SlotIndex::A), true, &mut load_buffer).unwrap();
        // Verifies that vbmeta ZBI items are appended as long as unlocked.
        let mut expected_zbi_items = AlignedBuffer::new(load_buffer.len(), 8);
        expected_zbi_items[..load_buffer.len()].clone_from_slice(&load_buffer);
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_0=val\0");
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_1=val\0");
        assert_eq!(normalize_zbi(&load_buffer), normalize_zbi(&expected_zbi_items));
        // Rollback index should not be updated in any failure cases, even when unlocked.
        assert_eq!(expect_rollback, ops.avb_ops.rollbacks);
    }

    #[test]
    fn test_verify_failure_by_corrupted_vbmetadata_unlocked() {
        let mut storage = create_storage();
        let partitions = storage.as_partition_block_devices();
        let mut ops = create_gbl_ops(&partitions);

        ops.avb_ops.unlock_state = Ok(true);
        let expect_rollback = ops.avb_ops.rollbacks.clone();
        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        // Adds extra bytes for device ZBI items.
        let mut load_buffer = AlignedBuffer::new(zbi.len() + 1024, ZIRCON_KERNEL_ALIGN);
        load_buffer[..zbi.len()].clone_from_slice(zbi);
        let expect_load = load_buffer.to_vec();
        // Corrupts vbmetadata
        corrupt_data(&mut ops, "vbmeta_a");
        zircon_verify_kernel(&mut ops, Some(SlotIndex::A), true, &mut load_buffer).unwrap();
        // Unlocked but vbmetadata is invalid so no ZBI items should be appended.
        assert_eq!(expect_load, &load_buffer[..]);
        // Rollback index should not be updated on verification failure.
        assert_eq!(expect_rollback, ops.avb_ops.rollbacks);
    }
}
