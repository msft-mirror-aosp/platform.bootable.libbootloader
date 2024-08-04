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

use crate::{Error as GblError, GblOps, Result as GblResult};
pub use abr::SlotIndex;
use safemath::SafeNum;
use zbi::{ZbiContainer, ZbiFlags, ZbiHeader, ZbiType};
use zerocopy::AsBytes;

mod vboot;

/// Kernel load address alignment. Value taken from
/// https://fuchsia.googlesource.com/fuchsia/+/4f204d8a0243e84a86af4c527a8edcc1ace1615f/zircon/kernel/target/arm64/boot-shim/BUILD.gn#38
pub const ZIRCON_KERNEL_ALIGN: usize = 64 * 1024;

/// A helper for getting a subslice with an aligned address.
fn aligned_subslice(buffer: &mut [u8], alignment: usize) -> GblResult<&mut [u8]> {
    let addr = SafeNum::from(buffer.as_ptr() as usize);
    let aligned_offset = addr.round_up(alignment) - addr;
    Ok(buffer.get_mut(aligned_offset.try_into()?..).ok_or(GblError::BufferTooSmall)?)
}

/// A helper for splitting the trailing unused portion of a ZBI container buffer.
///
/// Returns a tuple of used subslice and unused subslice
fn zbi_split_unused_buffer(zbi: &mut [u8]) -> GblResult<(&mut [u8], &mut [u8])> {
    Ok(zbi.split_at_mut(ZbiContainer::parse(&zbi[..])?.container_size()))
}

/// Relocates a ZBI kernel to a different buffer.
///
/// * `dest` must be aligned to `ZIRCON_KERNEL_ALIGN`.
/// * `dest` will be a ZBI container containing only the kernel item.
pub fn relocate_kernel(kernel: &[u8], dest: &mut [u8]) -> GblResult<()> {
    if (dest.as_ptr() as usize % ZIRCON_KERNEL_ALIGN) != 0 {
        return Err(GblError::InvalidAlignment.into());
    }

    let kernel = ZbiContainer::parse(&kernel[..])?;
    let kernel_item = kernel.is_bootable()?;
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
    match reserved_memory_size > u64::try_from(zbi_split_unused_buffer(dest)?.1.len())? {
        true => Err(GblError::BufferTooSmall.into()),
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
    let off = (SafeNum::from(relocated.len()) - reloc_size).round_down(ZIRCON_KERNEL_ALIGN);
    let relocated = &mut relocated[off.try_into()?..];
    relocate_kernel(original, relocated)?;
    let reloc_addr = relocated.as_ptr() as usize;
    Ok(kernel.split_at_mut(reloc_addr.checked_sub(kernel.as_ptr() as usize).unwrap()))
}

/// Helper for getting the slotted/slotless standard zircon partition name.
fn zircon_part_name(slot: Option<SlotIndex>) -> &'static str {
    match slot {
        Some(slot) => match slot {
            SlotIndex::A => "zircon_a",
            SlotIndex::B => "zircon_b",
            SlotIndex::R => "zircon_r",
        },
        _ => "zircon",
    }
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
/// * `load`: Buffer for loading the kernel.
///
/// On success returns a pair containing: 1. the slice of the ZBI container with device ZBI items
/// and 2. the slice of the relocated kernel at the tail.
pub fn zircon_load_verify<'a>(
    ops: &mut impl GblOps,
    slot: Option<SlotIndex>,
    load: &'a mut [u8],
) -> GblResult<(&'a mut [u8], &'a mut [u8])> {
    let load = aligned_subslice(load, ZIRCON_KERNEL_ALIGN)?;
    let zircon_part = zircon_part_name(slot);

    // Reads ZBI header to computes the total size of kernel.
    let mut zbi_header: ZbiHeader = Default::default();
    ops.read_from_partition_sync(zircon_part, 0, zbi_header.as_bytes_mut())?;
    let image_length = SafeNum::from(zbi_header.as_bytes_mut().len()) + zbi_header.length;

    // Reads the entire kernel
    let kernel = load.get_mut(..image_length.try_into()?).ok_or(GblError::BufferTooSmall)?;
    ops.read_from_partition_sync(zircon_part, 0, kernel)?;

    // TODO(b/334962583): Perform AVB verification.

    // Append additional ZBI items.
    let mut zbi_kernel = ZbiContainer::parse(&mut load[..])?;

    match slot {
        Some(slot) => {
            // Appends current slot item.
            zbi_kernel.create_entry_with_payload(
                ZbiType::CmdLine,
                0,
                ZbiFlags::default(),
                slot_cmd_line(slot).as_bytes(),
            )?;
        }
        _ => {}
    }

    // Relocates the kernel to the tail to reserved extra memory that the kernel may require.
    let (zbi_items, relocated) = relocate_to_tail(&mut load[..])?;

    // Appends device specific ZBI items.
    ops.zircon_add_device_zbi_items(&mut ZbiContainer::parse(&mut zbi_items[..])?)?;

    Ok((zbi_items, relocated))
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        ops::{AvbIoResult, CertPermanentAttributes, GblAvbOps, SHA256_DIGEST_SIZE},
        slots, BootImages, GblOpsError,
    };
    use std::{
        collections::{BTreeSet, HashMap},
        fmt::Write,
        fs,
        path::Path,
    };

    // The `reserve_memory_size` value in the test ZBI kernel.
    // See `gen_zircon_test_images()` in libgbl/testdata/gen_test_data.py.
    const TEST_KERNEL_RESERVED_MEMORY_SIZE: usize = 1024;

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

    /// `TestZirconBootGblOps` implements `GblOps` for test.
    pub(crate) struct TestZirconBootGblOps {
        pub(crate) partitions: HashMap<&'static str, Vec<u8>>,
        pub(crate) avb_unlocked: bool,
        pub(crate) rollback_index: HashMap<usize, u64>,
    }

    impl Default for TestZirconBootGblOps {
        fn default() -> Self {
            let partitions = HashMap::from([
                ("zircon_a", read_test_data(ZIRCON_A_ZBI_FILE)),
                ("zircon_b", read_test_data(ZIRCON_B_ZBI_FILE)),
                ("zircon_r", read_test_data(ZIRCON_R_ZBI_FILE)),
                ("zircon", read_test_data(ZIRCON_SLOTLESS_ZBI_FILE)),
                ("vbmeta_a", read_test_data(VBMETA_A_FILE)),
                ("vbmeta_b", read_test_data(VBMETA_B_FILE)),
                ("vbmeta_r", read_test_data(VBMETA_R_FILE)),
                ("vbmeta", read_test_data(VBMETA_SLOTLESS_FILE)),
            ]);
            Self { partitions, avb_unlocked: false, rollback_index: Default::default() }
        }
    }

    impl GblOps for TestZirconBootGblOps {
        fn console_out(&mut self) -> Option<&mut dyn Write> {
            unimplemented!();
        }

        fn should_stop_in_fastboot(&mut self) -> Result<bool, GblOpsError> {
            unimplemented!();
        }

        fn preboot(&mut self, boot_images: BootImages) -> Result<(), GblOpsError> {
            unimplemented!();
        }

        async fn read_from_partition(
            &mut self,
            part: &str,
            off: u64,
            out: &mut [u8],
        ) -> Result<(), GblOpsError> {
            match self.partitions.get_mut(part) {
                Some(v) => Ok(out.clone_from_slice(&v[off.try_into().unwrap()..][..out.len()])),
                _ => Err(GblOpsError(Some("Test: No such partition"))),
            }
        }

        async fn write_to_partition(
            &mut self,
            part: &str,
            off: u64,
            data: &mut [u8],
        ) -> Result<(), GblOpsError> {
            match self.partitions.get_mut(part) {
                Some(v) => Ok(v[off.try_into().unwrap()..][..data.len()].clone_from_slice(data)),
                _ => Err(GblOpsError(Some("Test: No such partition"))),
            }
        }

        fn partition_size(&mut self, part: &str) -> Result<Option<u64>, GblOpsError> {
            Ok(self.partitions.get_mut(part).map(|v| v.len().try_into().unwrap()))
        }

        fn zircon_add_device_zbi_items(
            &mut self,
            container: &mut ZbiContainer<&mut [u8]>,
        ) -> Result<(), GblOpsError> {
            container
                .create_entry_with_payload(
                    ZbiType::CmdLine,
                    0,
                    ZbiFlags::default(),
                    b"test_zbi_item",
                )
                .unwrap();
            Ok(())
        }

        fn do_fastboot<B: gbl_storage::AsBlockDevice>(
            &self,
            cursor: &mut slots::Cursor<B>,
        ) -> GblResult<()> {
            unimplemented!();
        }

        fn load_slot_interface<'a, B: gbl_storage::AsBlockDevice>(
            &'a mut self,
            block_device: &'a mut B,
            boot_token: slots::BootToken,
        ) -> GblResult<slots::Cursor<'a, B>> {
            unimplemented!();
        }

        fn avb_ops(&mut self) -> Option<impl GblAvbOps> {
            Some(self)
        }
    }

    // `avb::test_op:TestOps` provides a more comprehensive a set of mocks. Consider using it when
    // we add more mocks.
    impl GblAvbOps for &mut TestZirconBootGblOps {
        fn avb_read_is_device_unlocked(&mut self) -> AvbIoResult<bool> {
            Ok(self.avb_unlocked)
        }

        fn avb_read_rollback_index(&mut self, rollback_index_location: usize) -> AvbIoResult<u64> {
            Ok(*self.rollback_index.get(&rollback_index_location).unwrap_or(&0))
        }

        fn avb_write_rollback_index(
            &mut self,
            rollback_index_location: usize,
            index: u64,
        ) -> AvbIoResult<()> {
            self.rollback_index.insert(rollback_index_location, index);
            Ok(())
        }

        fn avb_cert_read_permanent_attributes(
            &mut self,
            attributes: &mut CertPermanentAttributes,
        ) -> AvbIoResult<()> {
            let perm_attr = read_test_data("cert_permanent_attributes.bin");
            Ok(attributes.as_bytes_mut().clone_from_slice(&perm_attr))
        }

        fn avb_cert_read_permanent_attributes_hash(
            &mut self,
        ) -> AvbIoResult<[u8; SHA256_DIGEST_SIZE]> {
            Ok(read_test_data("cert_permanent_attributes.hash").try_into().unwrap())
        }
    }

    // Helper object for allocating aligned buffer.
    pub(crate) struct AlignedBuffer {
        buffer: Vec<u8>,
        size: usize,
        alignment: usize,
    }

    impl AlignedBuffer {
        /// Allocates a buffer.
        pub(crate) fn new(size: usize, alignment: usize) -> Self {
            Self { buffer: vec![0u8; alignment + size - 1], size, alignment }
        }

        /// Allocates a buffer and initializes with data.
        pub(crate) fn new_with_data(data: &[u8], alignment: usize) -> Self {
            let mut res = Self::new(data.len(), alignment);
            res.get().clone_from_slice(data);
            res
        }

        /// Gets the buffer
        pub(crate) fn get(&mut self) -> &mut [u8] {
            &mut aligned_subslice(&mut self.buffer[..], self.alignment).unwrap()[..self.size]
        }
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

    /// Helper for testing `zircon_load_verify`.
    fn test_load_verify(
        ops: &mut impl GblOps,
        slot: Option<SlotIndex>,
        expected_zbi_items: &[u8],
        expected_kernel: &[u8],
    ) {
        // Test load buffer layout:
        // |  zircon_x.zbi + items| ~~ |~64k~| relocated kernel + reserved |
        // | ---------- 64K -----------|~~~~~| ----------------------------|
        let sz = 2 * ZIRCON_KERNEL_ALIGN + expected_kernel.len() + TEST_KERNEL_RESERVED_MEMORY_SIZE;
        let mut load = AlignedBuffer::new(sz, ZIRCON_KERNEL_ALIGN);
        let (zbi_items, relocated) = zircon_load_verify(ops, slot, load.get()).unwrap();
        // Verifies loaded ZBI kernel/items
        assert_eq!(normalize_zbi(expected_zbi_items), normalize_zbi(zbi_items));
        // Verifies relocated kernel
        assert_eq!(normalize_zbi(expected_kernel), normalize_zbi(relocated));
        // Relocated kernel is at the latest aligned address
        let off = (relocated.as_ptr() as usize) - (load.get().as_ptr() as usize);
        assert_eq!(off, 2 * ZIRCON_KERNEL_ALIGN);
    }

    #[test]
    fn test_zircon_load_verify_slotless() {
        let mut ops = TestZirconBootGblOps::default();
        let zbi = &read_test_data(ZIRCON_SLOTLESS_ZBI_FILE);
        let mut expected_kernel = AlignedBuffer::new_with_data(zbi, 8);
        // Adds extra bytes for device ZBI items.
        let mut expected_zbi_items = AlignedBuffer::new(zbi.len() + 1024, 8);
        expected_zbi_items.get()[..zbi.len()].clone_from_slice(zbi);
        append_cmd_line(expected_zbi_items.get(), b"test_zbi_item");
        test_load_verify(&mut ops, None, expected_zbi_items.get(), expected_kernel.get());
    }

    /// Helper for testing `zircon_load_verify` using A/B/R.
    fn test_load_verify_slotted_helper(
        ops: &mut impl GblOps,
        slot: SlotIndex,
        zbi: &[u8],
        slot_item: &str,
    ) {
        let mut expected_kernel = AlignedBuffer::new_with_data(zbi, 8);
        // Adds extra bytes for device ZBI items.
        let mut expected_zbi_items = AlignedBuffer::new(zbi.len() + 1024, 8);
        expected_zbi_items.get()[..zbi.len()].clone_from_slice(zbi);
        append_cmd_line(expected_zbi_items.get(), b"test_zbi_item");
        append_cmd_line(expected_zbi_items.get(), slot_item.as_bytes());
        test_load_verify(ops, Some(slot), expected_zbi_items.get(), expected_kernel.get());
    }

    #[test]
    fn test_load_verify_slot_a() {
        let mut ops = TestZirconBootGblOps::default();
        let zircon_a_zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        test_load_verify_slotted_helper(&mut ops, SlotIndex::A, zircon_a_zbi, "zvb.current_slot=a");
    }

    #[test]
    fn test_load_verify_slot_b() {
        let mut ops = TestZirconBootGblOps::default();
        let zircon_b_zbi = &read_test_data(ZIRCON_B_ZBI_FILE);
        test_load_verify_slotted_helper(&mut ops, SlotIndex::B, zircon_b_zbi, "zvb.current_slot=b");
    }

    #[test]
    fn test_load_verify_slot_r() {
        let mut ops = TestZirconBootGblOps::default();
        let zircon_r_zbi = &read_test_data(ZIRCON_R_ZBI_FILE);
        test_load_verify_slotted_helper(&mut ops, SlotIndex::R, zircon_r_zbi, "zvb.current_slot=r");
    }

    #[test]
    fn test_not_enough_buffer_for_reserved_memory() {
        let mut ops = TestZirconBootGblOps::default();
        let zbi = &read_test_data(ZIRCON_A_ZBI_FILE);
        let sz = ZIRCON_KERNEL_ALIGN + zbi.len() + TEST_KERNEL_RESERVED_MEMORY_SIZE - 1;
        let mut load = AlignedBuffer::new(sz, ZIRCON_KERNEL_ALIGN);
        assert!(zircon_load_verify(&mut ops, Some(SlotIndex::A), load.get()).is_err());
    }
}
