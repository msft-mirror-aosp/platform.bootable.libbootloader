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

use crate::{gbl_print, gbl_println, image_buffer::ImageBuffer, GblOps, Result as GblResult};
pub use abr::{get_and_clear_one_shot_bootloader, get_boot_slot, Ops as AbrOps, SlotIndex};
use core::{fmt::Write, mem::MaybeUninit, num::NonZeroUsize};
use liberror::{Error, Result};
use libutils::aligned_subslice;
use safemath::SafeNum;
use zbi::{ZbiContainer, ZbiFlags, ZbiHeader, ZbiType};
use zerocopy::IntoBytes;

mod vboot;
use vboot::zircon_verify_kernel;

/// Kernel load address alignment. Value taken from
/// https://fuchsia.googlesource.com/fuchsia/+/4f204d8a0243e84a86af4c527a8edcc1ace1615f/zircon/kernel/target/arm64/boot-shim/BUILD.gn#38
pub const ZIRCON_KERNEL_ALIGN: usize = 64 * 1024;

const DURABLE_BOOT_PARTITION: &str = "durable_boot";
const MISC_PARTITION: &str = "misc";
const ABR_PARTITION_ALIASES: &[&str] = &[DURABLE_BOOT_PARTITION, MISC_PARTITION];

/// Helper function to find partition given a list of possible aliases.
fn find_part_aliases<'a, 'b, 'c>(
    ops: &mut (impl GblOps<'a, 'c> + ?Sized),
    aliases: &'b [&str],
) -> Result<&'b str> {
    Ok(*aliases
        .iter()
        .find(|v| matches!(ops.partition_size(v), Ok(Some(_))))
        .ok_or(Error::NotFound)?)
}

/// `GblAbrOps` wraps an object implementing `GblOps` and implements the `abr::Ops` trait.
pub(crate) struct GblAbrOps<'a, T: ?Sized>(pub &'a mut T);

impl<'b, 'c, T: GblOps<'b, 'c> + ?Sized> AbrOps for GblAbrOps<'_, T> {
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
fn zbi_split_unused_buffer(zbi: &mut [u8]) -> GblResult<(&mut [u8], &mut [u8])> {
    Ok(zbi.split_at_mut(ZbiContainer::parse(&zbi[..])?.container_size()?))
}

/// Relocates a ZBI kernel to a different buffer.
///
/// * `dest` must be aligned to `ZIRCON_KERNEL_ALIGN`.
/// * `dest` will be a ZBI container containing only the kernel item.
pub fn relocate_kernel(kernel: &[u8], dest: &mut [u8]) -> GblResult<()> {
    if (dest.as_ptr() as usize % ZIRCON_KERNEL_ALIGN) != 0 {
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
    let (_, reserved_memory_size) = relocated.get_kernel_entry_and_reserved_memory_size()?;
    let buf_len = u64::try_from(zbi_split_unused_buffer(dest)?.1.len()).map_err(Error::from)?;
    match reserved_memory_size > buf_len {
        true => Err(Error::BufferTooSmall(None).into()),
        _ => Ok(()),
    }
}

/// Relocate a ZBI kernel to the trailing unused buffer.
///
/// Returns the original kernel subslice and relocated kernel subslice.
pub fn relocate_to_tail(kernel: &mut [u8]) -> GblResult<(&mut [u8], &mut [u8])> {
    let reloc_size = ZbiContainer::parse(&kernel[..])?.get_buffer_size_for_kernel_relocation()?;
    let (original, relocated) = zbi_split_unused_buffer(kernel)?;
    let relocated = aligned_subslice(relocated, ZIRCON_KERNEL_ALIGN)?;
    let off = (SafeNum::from(relocated.len()) - reloc_size)
        .round_down(ZIRCON_KERNEL_ALIGN)
        .try_into()
        .map_err(Error::from)?;
    let relocated = &mut relocated[off..];
    relocate_kernel(original, relocated)?;
    let reloc_addr = relocated.as_ptr() as usize;
    Ok(kernel.split_at_mut(reloc_addr.checked_sub(kernel.as_ptr() as usize).unwrap()))
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

/// Loads and verifies a kernel of the given slot or slotless.
///
/// # Args
///
/// * `ops`: A reference to an object that implements `GblOps`.
/// * `slot`: None if slotless. Otherwise the target slot to boot.
/// * `slot_booted_successfully`: whether the slot is known-successful boot, and if so then this
/// function will update the anti-rollbacks.
///
/// On success returns a pair containing: 1. the slice of the ZBI container with device ZBI items
/// and 2. the slice of container containing the kernel.
pub fn zircon_load_verify<'a, 'd>(
    ops: &mut impl GblOps<'a, 'd>,
    slot: Option<SlotIndex>,
    slot_booted_successfully: bool,
) -> GblResult<(ImageBuffer<'d>, ImageBuffer<'d>)> {
    // TODO(b/379778252): use single `zbi_zircon` buffer for container to store both kernel and
    // arguments/items
    let mut zbi_items_img =
        ops.get_image_buffer("zbi_items", NonZeroUsize::new(64 * 1024 * 1024).unwrap()).unwrap();

    let init_len = zbi_items_img.tail().len();
    // TODO(b/379787423): it is possible to optimize this initialisation by treating
    // `zbi_items_img` same as kernel image (&[MaybeUninit]).
    MaybeUninit::fill(zbi_items_img.tail(), 0);

    // SAFETY: buffer was fully filled with 0 which is valid init value for u8
    unsafe {
        zbi_items_img.advance_used(init_len).unwrap();
    }
    let mut zbi_items = ZbiContainer::new(zbi_items_img.used_mut())?;

    let zircon_part = find_part_aliases(ops, zircon_part_name_aliases(slot))?;

    // Reads ZBI header to computes the total size of kernel.
    let mut zbi_header: ZbiHeader = Default::default();
    ops.read_from_partition_sync(zircon_part, 0, zbi_header.as_bytes_mut())?;
    let image_length = (SafeNum::from(zbi_header.as_bytes_mut().len()) + zbi_header.length)
        .try_into()
        .map_err(Error::from)?;

    // Reads the entire kernel
    // TODO(b/379778252): as part of an attempt to use single container for kernel and arguments,
    // it would be necessary to read kernel header first to figure out how much space needed
    // (kernel size + scratch space)
    let mut kernel_img =
        ops.get_image_buffer("zbi_zircon", NonZeroUsize::new(128 * 1024 * 1024).unwrap()).unwrap();
    let kernel_uninit = kernel_img
        .as_mut()
        .get_mut(..image_length)
        .ok_or(Error::BufferTooSmall(Some(image_length)))?;
    ops.read_from_partition_sync(zircon_part, 0, kernel_uninit)?;
    // SAFETY: buffer was successfully filled from partition
    unsafe {
        kernel_img.advance_used(image_length).unwrap();
    }
    let load = kernel_img.used_mut();

    // Performs AVB verification.
    // TODO(b/379789161) verify that kernel buffer is big enough for the image and scratch buffer.
    zircon_verify_kernel(ops, slot, slot_booted_successfully, load, &mut zbi_items)?;

    // Append additional ZBI items.
    match slot {
        Some(slot) => {
            // Appends current slot item.
            zbi_items.create_entry_with_payload(
                ZbiType::CmdLine,
                0,
                ZbiFlags::default(),
                slot_cmd_line(slot).as_bytes(),
            )?;
        }
        _ => {}
    }

    // Appends device specific ZBI items.
    ops.zircon_add_device_zbi_items(&mut zbi_items)?;

    // Appends staged bootloader file if present.
    match ops.get_zbi_bootloader_files_buffer_aligned().map(|v| ZbiContainer::parse(v)) {
        Some(Ok(v)) => zbi_items.extend(&v)?,
        _ => {}
    }

    Ok((zbi_items_img, kernel_img))
}

/// Loads and verifies the active slot kernel according to A/B/R.
///
/// On disk A/B/R metadata will be updated.
///
/// # Args
///
/// * `ops`: A reference to an object that implements `GblOps`.
///
/// Returns a tuple containing: 1. the slice of the ZBI container with device ZBI items, 2. the
/// slice of the relocated kernel, and 3. the selected slot index.
pub fn zircon_load_verify_abr<'a, 'd>(
    ops: &mut impl GblOps<'a, 'd>,
) -> GblResult<(ImageBuffer<'d>, ImageBuffer<'d>, SlotIndex)> {
    let (slot, successful) = get_boot_slot(&mut GblAbrOps(ops), true);
    gbl_println!(ops, "Loading kernel from {}...", zircon_part_name(Some(slot)));
    let (zbi_items_img, kernel_img) = zircon_load_verify(ops, Some(slot), successful)?;
    gbl_println!(ops, "Successfully loaded slot: {}", zircon_part_name(Some(slot)));
    Ok((zbi_items_img, kernel_img, slot))
}

/// Checks whether platform or A/B/R metadata instructs GBL to boot into fastboot mode.
///
/// # Returns
///
/// Returns true if fastboot mode is enabled, false if not.
pub fn zircon_check_enter_fastboot<'a, 'b>(ops: &mut impl GblOps<'a, 'b>) -> bool {
    match get_and_clear_one_shot_bootloader(&mut GblAbrOps(ops)) {
        Ok(true) => {
            gbl_println!(ops, "A/B/R one-shot-bootloader is set");
            return true;
        }
        Err(e) => {
            gbl_println!(ops, "Warning: error while checking A/B/R one-shot-bootloader ({:?})", e);
            gbl_println!(ops, "Ignoring error and considered not set");
        }
        _ => {}
    };

    match ops.should_stop_in_fastboot() {
        Ok(true) => {
            gbl_println!(ops, "Platform instructs GBL to enter fastboot mode");
            return true;
        }
        Err(e) => {
            gbl_println!(ops, "Warning: error while checking platform fastboot trigger ({:?})", e);
            gbl_println!(ops, "Ignoring error and considered not triggered");
        }
        _ => {}
    };
    false
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        ops::{
            test::{FakeGblOps, FakeGblOpsStorage, TestGblDisk},
            CertPermanentAttributes,
        },
        tests::AlignedBuffer,
    };
    use abr::{
        mark_slot_active, mark_slot_unbootable, set_one_shot_bootloader, ABR_MAX_TRIES_REMAINING,
    };
    use avb_bindgen::{AVB_CERT_PIK_VERSION_LOCATION, AVB_CERT_PSK_VERSION_LOCATION};
    use gbl_storage::as_uninit_mut;
    use std::{
        collections::{BTreeSet, HashMap, LinkedList},
        fs,
        path::Path,
    };
    use zbi::ZBI_ALIGNMENT_USIZE;
    use zerocopy::FromBytes;

    // The cert test keys were both generated with rollback version 42.
    const TEST_CERT_PIK_VERSION: u64 = 42;
    const TEST_CERT_PSK_VERSION: u64 = 42;

    // The `reserve_memory_size` value in the test ZBI kernel.
    // See `gen_zircon_test_images()` in libgbl/testdata/gen_test_data.py.
    const TEST_KERNEL_RESERVED_MEMORY_SIZE: usize = 1024;

    // The rollback index value and location in the generated test vbmetadata.
    // See `gen_zircon_test_images()` in libgbl/testdata/gen_test_data.py.
    const TEST_ROLLBACK_INDEX_LOCATION: usize = 1;
    const TEST_ROLLBACK_INDEX_VALUE: u64 = 2;

    pub(crate) const ZIRCON_A_ZBI_FILE: &str = "zircon_a.zbi";
    pub(crate) const ZIRCON_B_ZBI_FILE: &str = "zircon_b.zbi";
    pub(crate) const ZIRCON_R_ZBI_FILE: &str = "zircon_r.zbi";
    pub(crate) const ZIRCON_SLOTLESS_ZBI_FILE: &str = "zircon_slotless.zbi";
    pub(crate) const VBMETA_A_FILE: &str = "vbmeta_a.bin";
    pub(crate) const VBMETA_B_FILE: &str = "vbmeta_b.bin";
    pub(crate) const VBMETA_R_FILE: &str = "vbmeta_r.bin";
    pub(crate) const VBMETA_SLOTLESS_FILE: &str = "vbmeta_slotless.bin";

    /// Reads a data file under libgbl/testdata/
    pub(crate) fn read_test_data(file: &str) -> Vec<u8> {
        fs::read(Path::new(format!("external/gbl/libgbl/testdata/{}", file).as_str())).unwrap()
    }

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

    pub(crate) fn create_gbl_ops<'a>(partitions: &'a [TestGblDisk]) -> FakeGblOps<'a, 'static> {
        let mut ops = FakeGblOps::new(&partitions);
        ops.avb_ops.unlock_state = Ok(false);
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

    /// Helper for testing `zircon_load_verify`.
    fn test_load_verify(
        ops: &mut FakeGblOps,
        slot: Option<SlotIndex>,
        expected_zbi_items: &[u8],
        expected_kernel: &[u8],
    ) {
        let original_rb = ops.avb_ops.rollbacks.clone();
        // Loads and verifies with unsuccessful slot flag first.
        let (mut zbi_items, mut kernel) = zircon_load_verify(ops, slot, false).unwrap();
        // Verifies loaded ZBI kernel/items
        assert_eq!(normalize_zbi(expected_zbi_items), normalize_zbi(zbi_items.used_mut()));
        // Verifies kernel
        assert_eq!(normalize_zbi(expected_kernel), normalize_zbi(kernel.used_mut()));
        // Kernel is at aligned address
        assert_eq!(kernel.used_mut().as_ptr() as usize % ZIRCON_KERNEL_ALIGN, 0);

        // Verifies that the slot successful flag is passed correctly.
        // Unsuccessful slot, rollback not updated.
        assert_eq!(ops.avb_ops.rollbacks, original_rb);
        // Loads and verifies with successful slot flag.
        zircon_load_verify(ops, slot, true).unwrap();
        // Successful slot, rollback updated.
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

    // Helper to create local buffers and convert them to be used as ImageBuffers
    // This struct owns the buffers, and returns ImageBuffers maps that reference them.
    //
    // Tests should make sure to provide enough buffers for all `get_image_buffer()` calls.
    //
    struct ImageBuffersPool(LinkedList<(String, Vec<AlignedBuffer>)>);

    impl ImageBuffersPool {
        pub fn builder() -> ImageBuffersBuilder {
            ImageBuffersBuilder::new()
        }

        // number - number of expected get_image_buffer calls. Each call consumes buffers from the
        // list. If there are not enough it will start returning errors.
        //
        // size - size for the buffers
        fn new(number: usize, size: usize) -> Self {
            let mut zbi_items_buffer_vec = Vec::<AlignedBuffer>::new();
            let mut zbi_zircon_buffer_vec = Vec::<AlignedBuffer>::new();
            for _ in 0..number {
                zbi_zircon_buffer_vec.push(AlignedBuffer::new(size, ZIRCON_KERNEL_ALIGN));
                zbi_items_buffer_vec.push(AlignedBuffer::new(size, ZBI_ALIGNMENT_USIZE));
            }

            Self(
                [
                    (String::from("zbi_zircon"), zbi_zircon_buffer_vec),
                    (String::from("zbi_items"), zbi_items_buffer_vec),
                ]
                .into(),
            )
        }

        pub fn get(&mut self) -> HashMap<String, LinkedList<ImageBuffer>> {
            self.0
                .iter_mut()
                .map(|(key, val_vec)| {
                    (
                        key.clone(),
                        val_vec
                            .iter_mut()
                            .map(|e| ImageBuffer::new(as_uninit_mut(e.as_mut())))
                            .collect(),
                    )
                })
                .collect()
        }
    }

    struct ImageBuffersBuilder {
        // Number of buffers for each image name
        number: usize,
        // Size of the buffers
        size: usize,
    }

    /// Tests should make sure to provide enough buffers for all `get_image_buffer()` calls.
    /// Default number of calls is 1, if more expected use `builder().number(N).build()`
    /// Default buffer sizes are 2KiB, if different size required use `builder().size(1MiB).build()`
    impl ImageBuffersBuilder {
        pub fn new() -> ImageBuffersBuilder {
            Self { number: 1, size: 2 * 1024 }
        }

        /// If more than 1 `get_image_buffer()` call expected `number(N)` should be used to create
        /// big enough pool of buffers.
        pub fn number(mut self, number: usize) -> ImageBuffersBuilder {
            self.number = number;
            self
        }

        /// To change size of buffers use `builder(). size(S).build()`.
        pub fn size(mut self, size: usize) -> ImageBuffersBuilder {
            self.size = size;
            self
        }

        pub fn build(self) -> ImageBuffersPool {
            ImageBuffersPool::new(self.number, self.size)
        }
    }

    #[test]
    fn test_zircon_load_verify_slotless() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut image_buffers_pool = ImageBuffersPool::builder().number(2).build();
        ops.image_buffers = image_buffers_pool.get();

        let zbi = &read_test_data(ZIRCON_SLOTLESS_ZBI_FILE);
        let expected_kernel = AlignedBuffer::new_with_data(zbi, ZBI_ALIGNMENT_USIZE);
        // Adds extra bytes for device ZBI items.
        let mut expected_zbi_items = AlignedBuffer::new(1024, ZBI_ALIGNMENT_USIZE);
        let _ = ZbiContainer::new(&mut expected_zbi_items[..]).unwrap();
        append_cmd_line(&mut expected_zbi_items, FakeGblOps::ADDED_ZBI_COMMANDLINE_CONTENTS);
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_0=val\0");
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_1=val\0");
        append_zbi_file(&mut expected_zbi_items, FakeGblOps::TEST_BOOTLOADER_FILE_1);
        append_zbi_file(&mut expected_zbi_items, FakeGblOps::TEST_BOOTLOADER_FILE_2);
        test_load_verify(&mut ops, None, &expected_zbi_items, &expected_kernel);
    }

    /// Helper for testing `zircon_load_verify` using A/B/R.
    fn test_load_verify_slotted_helper(
        ops: &mut FakeGblOps,
        slot: SlotIndex,
        zbi: &[u8],
        slot_item: &str,
    ) {
        let expected_kernel = AlignedBuffer::new_with_data(zbi, ZBI_ALIGNMENT_USIZE);
        // Adds extra bytes for device ZBI items.
        let mut expected_zbi_items = AlignedBuffer::new(1024, ZBI_ALIGNMENT_USIZE);
        let _ = ZbiContainer::new(&mut expected_zbi_items[..]).unwrap();
        append_cmd_line(&mut expected_zbi_items, FakeGblOps::ADDED_ZBI_COMMANDLINE_CONTENTS);
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_0=val\0");
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_1=val\0");
        append_cmd_line(&mut expected_zbi_items, slot_item.as_bytes());
        append_zbi_file(&mut expected_zbi_items, FakeGblOps::TEST_BOOTLOADER_FILE_1);
        append_zbi_file(&mut expected_zbi_items, FakeGblOps::TEST_BOOTLOADER_FILE_2);
        test_load_verify(ops, Some(slot), &expected_zbi_items, &expected_kernel);
    }

    #[test]
    fn test_load_verify_slot_a() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut image_buffers_pool = ImageBuffersPool::builder().number(2).build();
        ops.image_buffers = image_buffers_pool.get();

        let zircon_a_zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        test_load_verify_slotted_helper(&mut ops, SlotIndex::A, zircon_a_zbi, "zvb.current_slot=a");
    }

    #[test]
    fn test_load_verify_slot_b() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut image_buffers_pool = ImageBuffersPool::builder().number(2).build();
        ops.image_buffers = image_buffers_pool.get();

        let zircon_b_zbi = &read_test_data(ZIRCON_B_ZBI_FILE);
        test_load_verify_slotted_helper(&mut ops, SlotIndex::B, zircon_b_zbi, "zvb.current_slot=b");
    }

    #[test]
    fn test_load_verify_slot_r() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut image_buffers_pool = ImageBuffersPool::builder().number(2).build();
        ops.image_buffers = image_buffers_pool.get();

        let zircon_r_zbi = &read_test_data(ZIRCON_R_ZBI_FILE);
        test_load_verify_slotted_helper(&mut ops, SlotIndex::R, zircon_r_zbi, "zvb.current_slot=r");
    }

    #[test]
    fn test_not_enough_buffer_for_reserved_memory() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut image_buffers_pool = ImageBuffersPool::builder().size(1024).build();
        ops.image_buffers = image_buffers_pool.get();

        assert!(zircon_load_verify(&mut ops, Some(SlotIndex::A), true).is_err());
    }

    /// A helper for assembling a set of test needed data. These include:
    ///
    /// * The original ZBI kernel image on partition `part` in the given `FakeGblOps`.
    /// * A buffer for loading and verifying the kernel.
    /// * The expected ZBI item buffer, if successfully loaded as slot index `slot`.
    /// * The expected ZBI kernel buffer, if successfully loaded.
    fn load_verify_test_data(
        ops: &mut FakeGblOps,
        slot: SlotIndex,
        part: &str,
    ) -> (Vec<u8>, AlignedBuffer, AlignedBuffer, AlignedBuffer) {
        // Read the (possibly modified) ZBI from disk.
        let zbi = ops.copy_partition(part);
        let sz = ZIRCON_KERNEL_ALIGN + zbi.len() + TEST_KERNEL_RESERVED_MEMORY_SIZE;
        let load_buffer = AlignedBuffer::new(sz, ZIRCON_KERNEL_ALIGN);
        let expected_kernel = AlignedBuffer::new_with_data(&zbi, ZBI_ALIGNMENT_USIZE);
        // Adds extra bytes for device ZBI items.
        let mut expected_zbi_items = AlignedBuffer::new(1024, ZBI_ALIGNMENT_USIZE);
        let _ = ZbiContainer::new(&mut expected_zbi_items[..]).unwrap();
        append_cmd_line(&mut expected_zbi_items, FakeGblOps::ADDED_ZBI_COMMANDLINE_CONTENTS);
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_0=val\0");
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_1=val\0");
        append_cmd_line(
            &mut expected_zbi_items,
            format!("zvb.current_slot={}", char::from(slot)).as_bytes(),
        );
        append_zbi_file(&mut expected_zbi_items, FakeGblOps::TEST_BOOTLOADER_FILE_1);
        append_zbi_file(&mut expected_zbi_items, FakeGblOps::TEST_BOOTLOADER_FILE_2);
        (zbi, load_buffer, expected_zbi_items, expected_kernel)
    }

    // Calls `zircon_load_verify_abr` and checks that the specified slot is loaded.
    fn expect_load_verify_abr_ok(ops: &mut FakeGblOps, slot: SlotIndex, part: &str) {
        let (_, _load, expected_items, expected_kernel) = load_verify_test_data(ops, slot, part);
        let (mut zbi_items, mut kernel, active) = zircon_load_verify_abr(ops).unwrap();
        assert_eq!(normalize_zbi(&expected_items), normalize_zbi(zbi_items.used_mut()));
        assert_eq!(normalize_zbi(&expected_kernel), normalize_zbi(kernel.used_mut()));
        assert_eq!(active, slot);
    }

    #[test]
    fn test_load_verify_abr_slot_a() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut image_buffers_pool = ImageBuffersPool::builder().build();
        ops.image_buffers = image_buffers_pool.get();

        expect_load_verify_abr_ok(&mut ops, SlotIndex::A, "zircon_a");
    }

    #[test]
    fn test_load_verify_abr_slot_b() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut image_buffers_pool = ImageBuffersPool::builder().build();
        ops.image_buffers = image_buffers_pool.get();

        mark_slot_active(&mut GblAbrOps(&mut ops), SlotIndex::B).unwrap();
        expect_load_verify_abr_ok(&mut ops, SlotIndex::B, "zircon_b");
    }

    #[test]
    fn test_load_verify_abr_slot_r() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut image_buffers_pool = ImageBuffersPool::builder().build();
        ops.image_buffers = image_buffers_pool.get();

        mark_slot_unbootable(&mut GblAbrOps(&mut ops), SlotIndex::A).unwrap();
        mark_slot_unbootable(&mut GblAbrOps(&mut ops), SlotIndex::B).unwrap();
        expect_load_verify_abr_ok(&mut ops, SlotIndex::R, "zircon_r");
    }

    #[test]
    fn test_load_verify_abr_exhaust_retries() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut image_buffers_pool =
            ImageBuffersPool::builder().number((1 + 2 * ABR_MAX_TRIES_REMAINING).into()).build();
        ops.image_buffers = image_buffers_pool.get();

        for _ in 0..ABR_MAX_TRIES_REMAINING {
            expect_load_verify_abr_ok(&mut ops, SlotIndex::A, "zircon_a");
        }
        for _ in 0..ABR_MAX_TRIES_REMAINING {
            expect_load_verify_abr_ok(&mut ops, SlotIndex::B, "zircon_b");
        }
        // Tests that load falls back to R eventually.
        expect_load_verify_abr_ok(&mut ops, SlotIndex::R, "zircon_r");
    }

    /// Modifies data in the given partition.
    pub(crate) fn corrupt_data(ops: &mut FakeGblOps, part_name: &str) {
        let mut data = [0u8];
        assert!(ops.read_from_partition_sync(part_name, 64, &mut data[..]).is_ok());
        data[0] ^= 0x01;
        assert!(ops.write_to_partition_sync(part_name, 64, &mut data[..]).is_ok());
    }

    #[test]
    fn test_load_verify_abr_verify_failure_a_b() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut image_buffers_pool =
            ImageBuffersPool::builder().number((1 + 2 * ABR_MAX_TRIES_REMAINING).into()).build();
        ops.image_buffers = image_buffers_pool.get();

        corrupt_data(&mut ops, "zircon_a");
        corrupt_data(&mut ops, "zircon_b");

        let (_, _load, _, _) = load_verify_test_data(&mut ops, SlotIndex::A, "zircon_a");
        for _ in 0..ABR_MAX_TRIES_REMAINING {
            assert!(zircon_load_verify_abr(&mut ops).is_err());
        }
        let (_, _load, _, _) = load_verify_test_data(&mut ops, SlotIndex::B, "zircon_b");
        for _ in 0..ABR_MAX_TRIES_REMAINING {
            assert!(zircon_load_verify_abr(&mut ops).is_err());
        }
        // Tests that load falls back to R eventually.
        expect_load_verify_abr_ok(&mut ops, SlotIndex::R, "zircon_r");
    }

    #[test]
    fn test_load_verify_abr_verify_failure_unlocked() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut image_buffers_pool =
            ImageBuffersPool::builder().number((1 + 2 * ABR_MAX_TRIES_REMAINING).into()).build();
        ops.image_buffers = image_buffers_pool.get();

        ops.avb_ops.unlock_state = Ok(true);
        corrupt_data(&mut ops, "zircon_a");
        corrupt_data(&mut ops, "zircon_b");

        for _ in 0..ABR_MAX_TRIES_REMAINING {
            expect_load_verify_abr_ok(&mut ops, SlotIndex::A, "zircon_a");
        }
        for _ in 0..ABR_MAX_TRIES_REMAINING {
            expect_load_verify_abr_ok(&mut ops, SlotIndex::B, "zircon_b");
        }
        expect_load_verify_abr_ok(&mut ops, SlotIndex::R, "zircon_r");
    }

    #[test]
    fn test_check_enter_fastboot_stop_in_fastboot() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);

        ops.stop_in_fastboot = Ok(false).into();
        assert!(!zircon_check_enter_fastboot(&mut ops));

        ops.stop_in_fastboot = Ok(true).into();
        assert!(zircon_check_enter_fastboot(&mut ops));

        ops.stop_in_fastboot = Err(Error::NotImplemented).into();
        assert!(!zircon_check_enter_fastboot(&mut ops));
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
        ops.stop_in_fastboot = Ok(true).into();
        assert!(zircon_check_enter_fastboot(&mut ops));
        ops.stop_in_fastboot = Ok(false).into();
        // A/B/R metadata should be prioritized in the previous check and thus one-shot-booloader
        // flag should be cleared.
        assert!(!zircon_check_enter_fastboot(&mut ops));
    }
    #[test]
    fn test_load_verify_abr_legacy_naming() {
        let storage = create_storage_legacy_names();
        let mut ops = create_gbl_ops(&storage);
        let mut image_buffers_pool =
            ImageBuffersPool::builder().number((1 + 2 * ABR_MAX_TRIES_REMAINING).into()).build();
        ops.image_buffers = image_buffers_pool.get();

        // Tests by exhausting all slots retries so it exercises all legacy name matching code
        // paths.
        for _ in 0..ABR_MAX_TRIES_REMAINING {
            expect_load_verify_abr_ok(&mut ops, SlotIndex::A, "zircon-a");
        }
        for _ in 0..ABR_MAX_TRIES_REMAINING {
            expect_load_verify_abr_ok(&mut ops, SlotIndex::B, "zircon-b");
        }
        // Tests that load falls back to R eventually.
        expect_load_verify_abr_ok(&mut ops, SlotIndex::R, "zircon-r");
    }

    #[test]
    fn test_zircon_load_verify_no_bootloader_file() {
        let storage = create_storage();
        let mut ops = create_gbl_ops(&storage);
        let mut image_buffers_pool = ImageBuffersPool::builder().number(2).build();
        ops.image_buffers = image_buffers_pool.get();
        ops.get_zbi_bootloader_files_buffer().unwrap().fill(0);

        let zbi = &read_test_data(ZIRCON_SLOTLESS_ZBI_FILE);
        let expected_kernel = AlignedBuffer::new_with_data(zbi, ZBI_ALIGNMENT_USIZE);
        // Adds extra bytes for device ZBI items.
        let mut expected_zbi_items = AlignedBuffer::new(1024, ZBI_ALIGNMENT_USIZE);
        let _ = ZbiContainer::new(&mut expected_zbi_items[..]).unwrap();
        append_cmd_line(&mut expected_zbi_items, FakeGblOps::ADDED_ZBI_COMMANDLINE_CONTENTS);
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_0=val\0");
        append_cmd_line(&mut expected_zbi_items, b"vb_prop_1=val\0");
        test_load_verify(&mut ops, None, &expected_zbi_items, &expected_kernel);
    }
}
