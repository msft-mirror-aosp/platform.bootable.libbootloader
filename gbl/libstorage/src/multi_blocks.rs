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

use crate::{AsBlockDevice, BlockIo, Partition, Result, StorageError};

/// `AsMultiBlockDevices` provides APIs for finding/reading/writing raw data or GPT partitions from
/// multiple block devices.
pub trait AsMultiBlockDevices {
    /// Calls closure `f` for each `AsBlockDevice` object and its unique `id` until reaching end.
    fn for_each(
        &mut self,
        f: &mut dyn FnMut(&mut dyn AsBlockDevice, u64),
    ) -> core::result::Result<(), Option<&'static str>>;

    /// Calls closure `f` for each `AsBlockDevice` object and its unique `id` until reaching end of
    /// returnning true.
    fn for_each_until(
        &mut self,
        f: &mut dyn FnMut(&mut dyn AsBlockDevice, u64) -> bool,
    ) -> Result<()> {
        let mut stop = false;
        self.for_each(&mut |io, id| {
            stop = stop || f(io, id);
        })
        .map_err(|v| StorageError::FailedGettingBlockDevices(v))
    }

    /// Gets the block device with the given id.
    fn get(&mut self, id: u64) -> Result<SelectedBlockDevice>
    where
        Self: Sized,
    {
        with_id(self, id, |_| {})?;
        Ok(SelectedBlockDevice { devs: self, id: id })
    }

    /// Syncs gpt for all block devices. Caller provides a callback for handling sync error for
    /// each block device.
    fn sync_gpt_all(&mut self, f: &mut dyn FnMut(&mut dyn AsBlockDevice, u64, StorageError)) {
        let _ = self.for_each_until(&mut |v, id| {
            match v.sync_gpt() {
                Err(e) => f(v, id, e),
                _ => {}
            }
            false
        });
    }

    /// Checks that a partition exists and is unique among all block devices with GPT.
    ///
    /// Returns the block device ID for the partition.
    fn check_part(&mut self, part: &str) -> Result<(u64, Partition)> {
        let mut res = Err(StorageError::NotExist);
        self.for_each_until(&mut |v, id| {
            res = match v.find_partition(part).map(|v| (id, v)) {
                Ok(_) if res.is_ok() => Err(StorageError::PartitionNotUnique),
                v => v.or(res),
            };
            res.err() == Some(StorageError::PartitionNotUnique)
        })?;
        res
    }

    /// Returns the block size and `GptEntry` for a partition.
    ///
    /// Returns Ok(()) if the partition is found and unique among all block devices.
    fn find_partition(&mut self, part: &str) -> Result<Partition> {
        self.check_part(part)?;
        until_ok(self, |dev, _| dev.find_partition(part))
    }

    /// Reads a GPT partition.
    ///
    /// Returns Ok(()) if the partition is unique among all block devices and read is successful.
    fn read_gpt_partition(&mut self, part_name: &str, offset: u64, out: &mut [u8]) -> Result<()> {
        self.check_part(part_name)?;
        until_ok(self, |dev, _| dev.read_gpt_partition(part_name, offset, out))
    }

    /// Writes a GPT partition with mutable input buffer.
    ///
    /// Returns Ok(()) if the partition is unique among all block devices and write is successful.
    fn write_gpt_partition_mut(
        &mut self,

        part_name: &str,
        offset: u64,
        data: &mut [u8],
    ) -> Result<()> {
        self.check_part(part_name)?;
        until_ok(self, |dev, _| dev.write_gpt_partition_mut(part_name, offset, &mut data[..]))
    }

    /// Writes a GPT partition with const input buffer.
    ///
    /// Returns Ok(()) if the partition is unique among all block devices and write is successful.
    fn write_gpt_partition(&mut self, part_name: &str, offset: u64, data: &mut [u8]) -> Result<()> {
        self.check_part(part_name)?;
        until_ok(self, |dev, _| dev.write_gpt_partition(part_name, offset, &mut data[..]))
    }
}

impl<T: ?Sized + AsMultiBlockDevices> AsMultiBlockDevices for &mut T {
    fn for_each(
        &mut self,
        f: &mut dyn FnMut(&mut dyn AsBlockDevice, u64),
    ) -> core::result::Result<(), Option<&'static str>> {
        (*self).for_each(&mut |io, id| f(io, id))
    }
}

/// Iterates and runs a closure on each block device until `Ok(R)` is returned.
fn until_ok<F, R>(devs: &mut (impl AsMultiBlockDevices + ?Sized), mut f: F) -> Result<R>
where
    F: FnMut(&mut dyn AsBlockDevice, u64) -> Result<R>,
{
    let mut res: Result<R> = Err(StorageError::BlockDeviceNotFound);
    devs.for_each_until(&mut |v, id| {
        res = f(v, id);
        res.is_ok()
    })?;
    res
}

/// Finds the first block device with the given ID and runs a closure with it.
fn with_id<F, R>(devs: &mut (impl AsMultiBlockDevices + ?Sized), dev_id: u64, mut f: F) -> Result<R>
where
    F: FnMut(&mut dyn AsBlockDevice) -> R,
{
    until_ok(devs, |dev, id| match dev_id == id {
        true => Ok(f(dev)),
        _ => Err(StorageError::BlockDeviceNotFound),
    })
}

/// `SelectedBlockDevice` is returned by `AsMultiBlockDevices::get()` and provides access to
/// the `AsBlockDevice` object of the given id.
pub struct SelectedBlockDevice<'a> {
    devs: &'a mut dyn AsMultiBlockDevices,
    id: u64,
}

impl AsBlockDevice for SelectedBlockDevice<'_> {
    fn with(&mut self, f: &mut dyn FnMut(&mut dyn BlockIo, &mut [u8], u64)) {
        let _ = with_id(self.devs, self.id, |dev| dev.with(f));
    }
}

#[cfg(test)]
mod test {
    use gbl_storage_testlib::{
        AsBlockDevice, AsMultiBlockDevices, TestBlockDeviceBuilder, TestMultiBlockDevices,
    };

    #[test]
    fn test_get() {
        let mut devs: TestMultiBlockDevices = TestMultiBlockDevices(vec![
            include_bytes!("../test/gpt_test_1.bin").as_slice().into(),
            include_bytes!("../test/gpt_test_2.bin").as_slice().into(),
        ]);
        devs.sync_gpt_all(&mut |_, _, _| panic!("GPT sync failed"));
        devs.get(0).unwrap();
        devs.get(1).unwrap();
        assert!(devs.get(2).is_err());
    }

    #[test]
    fn test_multi_block_read() {
        let off = 512; // Randomly selected offset.
        let blk_0 = include_bytes!("../test/gpt_test_1.bin");
        let blk_1 = include_bytes!("../test/gpt_test_2.bin");
        let mut devs =
            TestMultiBlockDevices(vec![blk_0.as_slice().into(), blk_1.as_slice().into()]);

        let mut out = vec![0u8; blk_0[off..].len()];
        devs.get(0).unwrap().read(u64::try_from(off).unwrap(), &mut out[..]).unwrap();
        assert_eq!(out, blk_0[off..]);

        let mut out = vec![0u8; blk_1[off..].len()];
        devs.get(1).unwrap().read(u64::try_from(off).unwrap(), &mut out[..]).unwrap();
        assert_eq!(out, blk_1[off..]);
    }

    #[test]
    fn test_multi_block_write() {
        let off = 512; // Randomly selected offset.
        let mut blk_0 = include_bytes!("../test/gpt_test_1.bin").to_vec();
        let mut blk_1 = include_bytes!("../test/gpt_test_2.bin").to_vec();
        let mut devs = TestMultiBlockDevices(vec![
            TestBlockDeviceBuilder::new().set_size(blk_0.len()).build(),
            TestBlockDeviceBuilder::new().set_size(blk_1.len()).build(),
        ]);

        devs.get(0).unwrap().write(u64::try_from(off).unwrap(), &mut blk_0[off..]).unwrap();
        assert_eq!(blk_0[off..], devs.0[0].io.storage[off..]);

        devs.get(1).unwrap().write(u64::try_from(off).unwrap(), &mut blk_1[off..]).unwrap();
        assert_eq!(blk_1[off..], devs.0[1].io.storage[off..]);
    }

    #[test]
    fn test_multi_block_gpt_partition_size() {
        let mut devs = TestMultiBlockDevices(vec![
            include_bytes!("../test/gpt_test_1.bin").as_slice().into(),
            include_bytes!("../test/gpt_test_2.bin").as_slice().into(),
        ]);
        devs.sync_gpt_all(&mut |_, _, _| panic!("GPT sync failed"));

        assert_eq!(devs.find_partition("boot_a").map(|v| v.size()).unwrap(), Ok(8 * 1024));
        assert_eq!(
            devs.get(0).unwrap().find_partition("boot_a").map(|v| v.size()).unwrap(),
            Ok(8 * 1024)
        );

        assert_eq!(devs.find_partition("boot_b").map(|v| v.size()).unwrap(), Ok(12 * 1024));
        assert_eq!(
            devs.get(0).unwrap().find_partition("boot_b").map(|v| v.size()).unwrap(),
            Ok(12 * 1024)
        );

        assert_eq!(devs.find_partition("vendor_boot_a").map(|v| v.size()).unwrap(), Ok(4 * 1024));
        assert_eq!(
            devs.get(1).unwrap().find_partition("vendor_boot_a").map(|v| v.size()).unwrap(),
            Ok(4 * 1024)
        );

        assert_eq!(devs.find_partition("vendor_boot_b").map(|v| v.size()).unwrap(), Ok(6 * 1024));
        assert_eq!(
            devs.get(1).unwrap().find_partition("vendor_boot_b").map(|v| v.size()).unwrap(),
            Ok(6 * 1024)
        );
    }

    /// A test helper for `AsMultiBlockDevices::read_gpt_partition`
    /// It verifies that data read partition `part` at offset `off` is the same as
    /// `expected[off..]`.
    fn check_read_partition(
        devs: &mut TestMultiBlockDevices,
        part: &str,
        off: u64,
        part_data: &[u8],
    ) {
        let expected = &part_data[off.try_into().unwrap()..];
        let mut out = vec![0u8; expected.len()];
        devs.read_gpt_partition(part, off, &mut out[..]).unwrap();
        assert_eq!(out, expected.to_vec());
    }

    #[test]
    fn test_multi_block_gpt_read() {
        let off = 512u64; // Randomly selected offset.

        let mut devs = TestMultiBlockDevices(vec![
            include_bytes!("../test/gpt_test_1.bin").as_slice().into(),
            include_bytes!("../test/gpt_test_2.bin").as_slice().into(),
        ]);
        devs.sync_gpt_all(&mut |_, _, _| panic!("GPT sync failed"));

        let expect_boot_a = include_bytes!("../test/boot_a.bin");
        let expect_boot_b = include_bytes!("../test/boot_b.bin");

        check_read_partition(&mut devs, "boot_a", off, expect_boot_a);
        check_read_partition(&mut devs, "boot_b", off, expect_boot_b);

        let expect_vendor_boot_a = include_bytes!("../test/vendor_boot_a.bin");
        let expect_vendor_boot_b = include_bytes!("../test/vendor_boot_b.bin");

        check_read_partition(&mut devs, "vendor_boot_a", off, expect_vendor_boot_a);
        check_read_partition(&mut devs, "vendor_boot_b", off, expect_vendor_boot_b);
    }

    /// A test helper for `AsMultiBlockDevices::write_gpt_partition`
    /// It verifies that `data[off..]` is correctly written to partition `part` at offset `off`.
    fn check_write_partition(
        devs: &mut TestMultiBlockDevices,
        part: &str,
        off: u64,
        data: &mut [u8],
    ) {
        let to_write = &mut data[off.try_into().unwrap()..];

        let mut out = vec![0u8; to_write.len()];
        devs.write_gpt_partition_mut(part, off, to_write).unwrap();
        devs.read_gpt_partition(part, off, &mut out[..]).unwrap();
        assert_eq!(out, to_write.to_vec());

        to_write.reverse();
        devs.write_gpt_partition_mut(part, off, to_write).unwrap();
        devs.read_gpt_partition(part, off, &mut out[..]).unwrap();
        assert_eq!(out, to_write.to_vec());
    }

    #[test]
    fn test_multi_block_gpt_write() {
        let off = 512u64; // Randomly selected offset.

        let mut devs = TestMultiBlockDevices(vec![
            include_bytes!("../test/gpt_test_1.bin").as_slice().into(),
            include_bytes!("../test/gpt_test_2.bin").as_slice().into(),
        ]);
        devs.sync_gpt_all(&mut |_, _, _| panic!("GPT sync failed"));

        let expect_boot_a = &mut include_bytes!("../test/boot_a.bin").to_vec();
        let expect_boot_b = &mut include_bytes!("../test/boot_b.bin").to_vec();

        expect_boot_a.reverse();
        expect_boot_b.reverse();
        check_write_partition(&mut devs, "boot_a", off, expect_boot_a);
        check_write_partition(&mut devs, "boot_b", off, expect_boot_b);

        let expect_vendor_boot_a = &mut include_bytes!("../test/vendor_boot_a.bin").to_vec();
        let expect_vendor_boot_b = &mut include_bytes!("../test/vendor_boot_b.bin").to_vec();

        expect_boot_a.reverse();
        expect_boot_b.reverse();
        check_write_partition(&mut devs, "vendor_boot_a", off, expect_vendor_boot_a);
        check_write_partition(&mut devs, "vendor_boot_b", off, expect_vendor_boot_b);
    }

    #[test]
    fn test_none_block_id_fail_with_non_unique_partition() {
        let mut devs = TestMultiBlockDevices(vec![
            include_bytes!("../test/gpt_test_1.bin").as_slice().into(),
            include_bytes!("../test/gpt_test_1.bin").as_slice().into(),
        ]);
        devs.sync_gpt_all(&mut |_, _, _| panic!("GPT sync failed"));
        assert!(devs.read_gpt_partition("boot_a", 0, &mut []).is_err());
        assert!(devs.write_gpt_partition_mut("boot_a", 0, &mut []).is_err());
        assert!(devs.write_gpt_partition("boot_a", 0, &mut []).is_err());
        assert!(devs.find_partition("boot_a").is_err());
    }
}
