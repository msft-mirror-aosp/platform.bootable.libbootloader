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
    fuchsia_boot::{zbi_split_unused_buffer, zircon_part_name, SlotIndex},
    gbl_avb::ops::GblAvbOps,
    gbl_print, GblOps, Result as GblResult,
};
use avb::{slot_verify, Descriptor, HashtreeErrorMode, Ops as _, SlotVerifyError, SlotVerifyFlags};
use core::ffi::CStr;
use zbi::ZbiContainer;
use zerocopy::ByteSliceMut;

/// Helper for getting the A/B/R suffix.
fn slot_suffix(slot: Option<SlotIndex>) -> Option<&'static CStr> {
    Some(match slot? {
        SlotIndex::A => c"_a",
        SlotIndex::B => c"_b",
        SlotIndex::R => c"_r",
    })
}

/// Verifies a loaded ZBI kernel.
///
/// # Arguments
///
/// * glb_ops - GblOps implementation
/// * slot - slot to verify
/// * slot_booted_successfully - if true, roll back indexes will be increased
/// * zbi_kernel - preloaded kernel to verify
/// * zbi_items - vbmeta items will be appended to this ZbiContainer
pub(crate) fn zircon_verify_kernel<'a, 'b, 'c, B: ByteSliceMut + PartialEq>(
    gbl_ops: &mut impl GblOps<'b, 'c>,
    slot: Option<SlotIndex>,
    slot_booted_successfully: bool,
    zbi_kernel: &'a mut [u8],
    zbi_items: &mut ZbiContainer<B>,
) -> GblResult<()> {
    // Copy ZBI items after kernel first. Because ordering matters, and new items should override
    // older ones.
    // TODO(b/379778252) It is not as efficient as moving kernel since ZBI items would contain file
    // system and be bigger than kernel.
    copy_items_after_kernel(zbi_kernel, zbi_items)?;

    let (kernel, _) = zbi_split_unused_buffer(&mut zbi_kernel[..])?;

    // Verifies the kernel.
    let part = zircon_part_name(slot);
    let preloaded = [(part, &kernel[..])];
    let mut avb_ops = GblAvbOps::new(gbl_ops, &preloaded[..], true);

    // Determines verify flags and error mode.
    let unlocked = avb_ops.read_is_device_unlocked()?;
    let mode = HashtreeErrorMode::AVB_HASHTREE_ERROR_MODE_EIO; // Don't care for fuchsia
    let flag = match unlocked {
        true => SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_ALLOW_VERIFICATION_ERROR,
        _ => SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_NONE,
    };

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

    // Collects ZBI items from vbmetadata and appends to the `zbi_items`.
    for vbmeta_data in verify_data.vbmeta_data() {
        for prop in vbmeta_data.descriptors()?.iter().filter_map(|d| match d {
            Descriptor::Property(p) if p.key.starts_with("zbi") => Some(p),
            _ => None,
        }) {
            zbi_items.extend_unaligned(prop.value)?;
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

    Ok(())
}

/// Copy ZBI items following kernel to separate container.
pub fn copy_items_after_kernel<'a, B: ByteSliceMut + PartialEq>(
    zbi_kernel: &'a mut [u8],
    zbi_items: &mut ZbiContainer<B>,
) -> GblResult<()> {
    let zbi_container = ZbiContainer::parse(&mut zbi_kernel[..])?;
    let mut items_iter = zbi_container.iter();
    items_iter.next(); // Skip first kernel item
    zbi_items.extend_items(items_iter)?;
    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        fuchsia_boot::{
            test::{
                append_cmd_line, corrupt_data, create_gbl_ops, create_storage, normalize_zbi,
                read_test_data, ZIRCON_A_ZBI_FILE,
            },
            ZIRCON_KERNEL_ALIGN,
        },
        tests::AlignedBuffer,
    };
    use avb_bindgen::{AVB_CERT_PIK_VERSION_LOCATION, AVB_CERT_PSK_VERSION_LOCATION};
    use zbi::ZBI_ALIGNMENT_USIZE;

    // The cert test keys were both generated with rollback version 42.
    const TEST_CERT_PIK_VERSION: u64 = 42;
    const TEST_CERT_PSK_VERSION: u64 = 42;

    #[test]
    fn test_verify_success() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        let expect_rollback = ops.avb_ops.rollbacks.clone();
        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        let mut load_buffer = AlignedBuffer::new(zbi.len(), ZIRCON_KERNEL_ALIGN);
        let mut zbi_items_buffer = AlignedBuffer::new(1024, ZBI_ALIGNMENT_USIZE);
        let mut zbi_items = ZbiContainer::new(&mut zbi_items_buffer[..]).unwrap();
        load_buffer[..zbi.len()].clone_from_slice(zbi);
        zircon_verify_kernel(&mut ops, Some(SlotIndex::A), false, &mut load_buffer, &mut zbi_items)
            .unwrap();

        // Verifies that vbmeta ZBI items are appended. Non-zbi items are ignored.
        let mut expected_zbi_items = AlignedBuffer::new(zbi.len() + 1024, 8);
        let _ = ZbiContainer::new(&mut expected_zbi_items[..]).unwrap();
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_0=val\0");
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_1=val\0");
        assert_eq!(normalize_zbi(&zbi_items_buffer), normalize_zbi(&expected_zbi_items));

        // Slot is not successful, rollback index should not be updated.
        assert_eq!(expect_rollback, ops.avb_ops.rollbacks);
    }

    #[test]
    fn test_verify_update_rollback_index_for_successful_slot() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        let mut load_buffer = AlignedBuffer::new(zbi.len(), ZIRCON_KERNEL_ALIGN);
        load_buffer[..zbi.len()].clone_from_slice(zbi);
        let mut zbi_items_buffer = AlignedBuffer::new(1024, ZBI_ALIGNMENT_USIZE);
        let mut zbi_items = ZbiContainer::new(&mut zbi_items_buffer[..]).unwrap();
        zircon_verify_kernel(&mut ops, Some(SlotIndex::A), true, &mut load_buffer, &mut zbi_items)
            .unwrap();

        // Slot is successful, rollback index should be updated.
        // vbmeta_a has rollback index value 2 at location 1.
        assert_eq!(
            ops.avb_ops.rollbacks,
            [
                (1, Ok(2)),
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

    #[test]
    fn test_verify_failed_on_corrupted_image() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        let expect_rollback = ops.avb_ops.rollbacks.clone();
        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        let mut load_buffer = AlignedBuffer::new(zbi.len(), ZIRCON_KERNEL_ALIGN);
        load_buffer[..zbi.len()].clone_from_slice(zbi);
        let mut zbi_items_buffer = AlignedBuffer::new(1024, ZBI_ALIGNMENT_USIZE);
        let mut zbi_items = ZbiContainer::new(&mut zbi_items_buffer[..]).unwrap();
        // Corrupts a random kernel bytes. Skips pass two ZBI headers.
        load_buffer[64] = !load_buffer[64];
        let expect_load = load_buffer.to_vec();
        assert!(zircon_verify_kernel(
            &mut ops,
            Some(SlotIndex::A),
            true,
            &mut load_buffer,
            &mut zbi_items
        )
        .is_err());
        // Failed while device is locked. ZBI items should not be appended.
        assert_eq!(expect_load, &load_buffer[..]);
        // Rollback index should not be updated on verification failure.
        assert_eq!(expect_rollback, ops.avb_ops.rollbacks);
    }

    #[test]
    fn test_verify_failed_on_corrupted_vbmetadata() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        let expect_rollback = ops.avb_ops.rollbacks.clone();
        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        let mut load = AlignedBuffer::new(zbi.len(), ZIRCON_KERNEL_ALIGN);
        load[..zbi.len()].clone_from_slice(zbi);
        let mut zbi_items_buffer = AlignedBuffer::new(1024, ZBI_ALIGNMENT_USIZE);
        let mut zbi_items = ZbiContainer::new(&mut zbi_items_buffer[..]).unwrap();
        let expect_load = load.to_vec();
        // Corrupts vbmetadata
        corrupt_data(&mut ops, "vbmeta_a");
        assert!(zircon_verify_kernel(
            &mut ops,
            Some(SlotIndex::A),
            true,
            &mut load,
            &mut zbi_items
        )
        .is_err());
        // Failed while device is locked. ZBI items should not be appended.
        assert_eq!(expect_load, &load[..]);
        // Rollback index should not be updated on verification failure.
        assert_eq!(expect_rollback, ops.avb_ops.rollbacks);
    }

    #[test]
    fn test_verify_failed_on_rollback_protection() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        let mut load_buffer = AlignedBuffer::new(zbi.len(), ZIRCON_KERNEL_ALIGN);
        load_buffer[..zbi.len()].clone_from_slice(zbi);
        let mut zbi_items_buffer = AlignedBuffer::new(1024, ZBI_ALIGNMENT_USIZE);
        let mut zbi_items = ZbiContainer::new(&mut zbi_items_buffer[..]).unwrap();
        let expect_load = load_buffer.to_vec();
        // vbmeta_a has rollback index value 2 at location 1. Setting min rollback value of 3 should
        // cause rollback protection failure.
        ops.avb_ops.rollbacks.insert(1, Ok(3));
        let expect_rollback = ops.avb_ops.rollbacks.clone();
        assert!(zircon_verify_kernel(
            &mut ops,
            Some(SlotIndex::A),
            true,
            &mut load_buffer,
            &mut zbi_items
        )
        .is_err());
        // Failed while device is locked. ZBI items should not be appended.
        assert_eq!(expect_load, &load_buffer[..]);
        // Rollback index should not be updated on verification failure.
        assert_eq!(expect_rollback, ops.avb_ops.rollbacks);
    }

    #[test]
    fn test_verify_failure_when_unlocked() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        ops.avb_ops.unlock_state = Ok(true);
        let expect_rollback = ops.avb_ops.rollbacks.clone();

        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        let mut load_buffer = AlignedBuffer::new(zbi.len(), ZIRCON_KERNEL_ALIGN);
        load_buffer[..zbi.len()].clone_from_slice(zbi);
        let mut zbi_items_buffer = AlignedBuffer::new(1024, ZBI_ALIGNMENT_USIZE);
        let mut zbi_items = ZbiContainer::new(&mut zbi_items_buffer[..]).unwrap();
        // Corrupts a random kernel bytes. Skips pass two ZBI headers.
        load_buffer[64] = !load_buffer[64];
        // Verification should proceeds OK.
        zircon_verify_kernel(&mut ops, Some(SlotIndex::A), true, &mut load_buffer, &mut zbi_items)
            .unwrap();
        // Verifies that vbmeta ZBI items are appended as long as unlocked.
        let mut expected_zbi_items = AlignedBuffer::new(load_buffer.len(), ZBI_ALIGNMENT_USIZE);
        let _ = ZbiContainer::new(&mut expected_zbi_items[..]).unwrap();
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_0=val\0");
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_1=val\0");
        assert_eq!(normalize_zbi(&zbi_items_buffer), normalize_zbi(&expected_zbi_items));
        // Rollback index should not be updated in any failure cases, even when unlocked.
        assert_eq!(expect_rollback, ops.avb_ops.rollbacks);
    }

    #[test]
    fn test_copy_items_after_kernel() {
        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        let mut load_buffer = AlignedBuffer::new(zbi.len() + 1024, ZIRCON_KERNEL_ALIGN);
        load_buffer[..zbi.len()].clone_from_slice(zbi);
        // Add items that will be copied
        append_cmd_line(&mut load_buffer, b"vb_prop_0=val\0");
        append_cmd_line(&mut load_buffer, b"vb_prop_1=val\0");

        // Create ZBI items container that contain 1 element
        let mut zbi_items_buffer = AlignedBuffer::new(1024, ZBI_ALIGNMENT_USIZE);
        let _ = ZbiContainer::new(&mut zbi_items_buffer[..]).unwrap();
        append_cmd_line(&mut zbi_items_buffer, b"vb_prop_2=val\0");
        let mut zbi_items = ZbiContainer::parse(&mut zbi_items_buffer[..]).unwrap();

        // Verifies that ZBI items are appended
        let mut expected_zbi_items = AlignedBuffer::new(load_buffer.len(), ZBI_ALIGNMENT_USIZE);
        let _ = ZbiContainer::new(&mut expected_zbi_items[..]).unwrap();
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_2=val\0");
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_0=val\0");
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_1=val\0");

        copy_items_after_kernel(&mut load_buffer, &mut zbi_items).unwrap();
        assert_eq!(normalize_zbi(&zbi_items_buffer), normalize_zbi(&expected_zbi_items));
    }

    #[test]
    fn test_verify_failure_by_corrupted_vbmetadata_unlocked() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        ops.avb_ops.unlock_state = Ok(true);
        let expect_rollback = ops.avb_ops.rollbacks.clone();
        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        let mut load_buffer = AlignedBuffer::new(zbi.len(), ZIRCON_KERNEL_ALIGN);
        load_buffer[..zbi.len()].clone_from_slice(zbi);
        let mut zbi_items_buffer = AlignedBuffer::new(1024, ZBI_ALIGNMENT_USIZE);
        let mut zbi_items = ZbiContainer::new(&mut zbi_items_buffer[..]).unwrap();
        let expect_load = load_buffer.to_vec();
        // Corrupts vbmetadata
        corrupt_data(&mut ops, "vbmeta_a");
        zircon_verify_kernel(&mut ops, Some(SlotIndex::A), true, &mut load_buffer, &mut zbi_items)
            .unwrap();
        // Unlocked but vbmetadata is invalid so no ZBI items should be appended.
        assert_eq!(expect_load, &load_buffer[..]);
        // Rollback index should not be updated on verification failure.
        assert_eq!(expect_rollback, ops.avb_ops.rollbacks);
    }
}
