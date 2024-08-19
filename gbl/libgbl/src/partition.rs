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

use crate::fastboot::sparse::{is_sparse_image, write_sparse_image, SparseRawWriter};
use core::mem::swap;
use fastboot::CommandError;
use gbl_storage::{AsyncBlockDevice, BlockInfo, BlockIoAsync, GptCache, Partition as GptPartition};
use liberror::Error;
use safemath::SafeNum;
use spin::mutex::{Mutex, MutexGuard};

/// Represents a GBL partition.
pub enum Partition<'a> {
    Raw(&'a str, u64),
    Gpt(GptPartition),
}

impl Partition<'_> {
    /// Returns the size.
    pub fn size(&self) -> Result<u64, Error> {
        let (start, end) = self.absolute_range()?;
        Ok((SafeNum::from(end) - start).try_into()?)
    }

    /// Returns the name.
    pub fn name(&self) -> Result<&str, Error> {
        Ok(match self {
            Partition::Gpt(gpt) => gpt.name().ok_or(Error::InvalidInput)?,
            Partition::Raw(name, _) => name,
        })
    }

    /// Computes the absolute start and end offset for the partition in the whole block device.
    pub fn absolute_range(&self) -> Result<(u64, u64), Error> {
        Ok(match self {
            Partition::Gpt(gpt) => gpt.absolute_range()?,
            Partition::Raw(_, size) => (0, *size),
        })
    }
}

/// Represents the partition table for a block device. It can either be a GPT partition table or a
/// single whole device raw partition.
enum PartitionTable<'a> {
    Raw(&'a str, u64),
    Gpt(GptCache<'a>),
}

/// Represents a block device that contains either GPT partitions or a single whole raw storage
/// partition.
pub struct PartitionBlockDevice<'a, B: BlockIoAsync> {
    // Contains an `AsyncBlockDevice` for block IO and `Result` to track the most recent error.
    // Wraps in `Mutex` as it will be used in parallel fastboot task.
    blk: Mutex<(AsyncBlockDevice<'a, B>, Result<(), Error>)>,
    partitions: PartitionTable<'a>,
    info_cache: BlockInfo,
}

impl<'a, B: BlockIoAsync> PartitionBlockDevice<'a, B> {
    /// Creates a new instance as a GPT device.
    pub fn new_gpt(mut blk: AsyncBlockDevice<'a, B>, gpt: GptCache<'a>) -> Self {
        let info_cache = blk.io().info();
        Self { blk: (blk, Ok(())).into(), info_cache, partitions: PartitionTable::Gpt(gpt) }
    }

    /// Creates a new instance as a raw storage partition.
    pub fn new_raw(mut blk: AsyncBlockDevice<'a, B>, name: &'a str) -> Result<Self, Error> {
        let info_cache = blk.io().info();
        Ok(Self {
            blk: (blk, Ok(())).into(),
            info_cache,
            partitions: PartitionTable::Raw(name, info_cache.total_size()?),
        })
    }

    /// Gets an instance of `PartitionIo` for a partition.
    ///
    /// If `part` is `None`, an IO for the whole block device is returned.
    pub fn partition_io(&self, part: Option<&str>) -> Result<PartitionIo<'a, '_, B>, Error> {
        let (part_start, part_end) = self.find_partition(part)?.absolute_range()?;
        Ok(PartitionIo { blk: self.blk.try_lock().ok_or(Error::NotReady)?, part_start, part_end })
    }

    /// Finds a partition.
    ///
    /// * If `part` is none, the method returns an unnamed `Partition` that represents the whole
    //    raw storage.
    pub fn find_partition(&self, part: Option<&str>) -> Result<Partition<'a>, Error> {
        let Some(part) = part else {
            return Ok(Partition::Raw("", self.info_cache.total_size()?));
        };

        match &self.partitions {
            PartitionTable::Gpt(gpt) => Ok(Partition::Gpt(gpt.find_partition(part)?)),
            PartitionTable::Raw(name, size) if *name == part => Ok(Partition::Raw(name, *size)),
            _ => Err(Error::NotFound),
        }
    }

    /// Syncs GPT if the partition type is GPT.
    ///
    /// # Returns
    ///
    /// * Returns `Ok(true)` if partition type is GPT and sync is successful.
    /// * Returns `Ok(false)` if partition type is not GPT.
    /// * Returns `Err` in other cases.
    pub async fn sync_gpt(&mut self) -> Result<bool, Error> {
        match &mut self.partitions {
            PartitionTable::Raw(name, _) => Ok(false),
            PartitionTable::Gpt(ref mut gpt) => {
                let mut blk = self.blk.try_lock().ok_or(Error::NotReady)?;
                blk.0.sync_gpt(gpt).await?;
                Ok(true)
            }
        }
    }
}

/// `PartitionIo` provides read/write APIs to a partition.
pub struct PartitionIo<'a, 'b, B: BlockIoAsync> {
    blk: MutexGuard<'b, (AsyncBlockDevice<'a, B>, Result<(), Error>)>,
    part_start: u64,
    part_end: u64,
}

impl<B: BlockIoAsync> PartitionIo<'_, '_, B> {
    /// Returns the size of the partition.
    pub fn size(&self) -> u64 {
        // Corrects by construction. Should not fail.
        self.part_end.checked_sub(self.part_start).unwrap()
    }

    /// Checks the read/write parameters and returns the absolute offset in the block.
    fn check_rw_range(&self, off: u64, size: impl Into<SafeNum>) -> Result<u64, Error> {
        let ab_range_end = SafeNum::from(self.part_start) + off + size.into();
        // Checks overflow by computing the difference between range end and partition end and
        // making sure it succeeds.
        let _end_diff: u64 = (SafeNum::from(self.part_end) - ab_range_end).try_into()?;
        Ok((SafeNum::from(self.part_start) + off).try_into()?)
    }

    /// A helper to do write for simplifying error handling.
    async fn do_write(&mut self, off: u64, data: &mut [u8]) -> Result<(), Error> {
        self.check_rw_range(off, data.len()).map(|v| self.blk.0.write(v, data))?.await
    }

    /// Writes to the partition.
    pub async fn write(&mut self, off: u64, data: &mut [u8]) -> Result<(), Error> {
        let res = self.do_write(off, data).await;
        self.blk.1 = res.and(self.blk.1);
        res
    }

    /// A helper to do read for simplifying error handling.
    async fn do_read(&mut self, off: u64, out: &mut [u8]) -> Result<(), Error> {
        self.check_rw_range(off, out.len()).map(|v| self.blk.0.read(v, out))?.await
    }

    /// Reads from the partition.
    pub async fn read(&mut self, off: u64, out: &mut [u8]) -> Result<(), Error> {
        let res = self.do_read(off, out).await;
        self.blk.1 = res.and(self.blk.1);
        res
    }

    /// A helper to do sparse write for simplifying error handling.
    async fn do_write_sparse(&mut self, off: u64, img: &mut [u8]) -> Result<(), Error> {
        self.check_rw_range(
            off,
            is_sparse_image(img).map_err(|_| Error::InvalidInput)?.data_size(),
        )?;
        write_sparse_image(img, &mut (off, &mut self.blk.0))
            .await
            .map_err(|_| "Sparse write failed")?;
        Ok(())
    }

    /// Writes sparse image to the partition.
    pub async fn write_sparse(&mut self, off: u64, img: &mut [u8]) -> Result<(), Error> {
        let res = self.do_write_sparse(off, img).await;
        self.blk.1 = res.and(self.blk.1);
        res
    }

    /// Turns this IO into one for a subrange in the partition.
    pub fn sub(self, off: u64, sz: u64) -> Result<Self, Error> {
        self.check_rw_range(off, sz)?;
        let mut sub = self;
        sub.part_start += off;
        sub.part_end = sub.part_start + sz;
        Ok(sub)
    }

    /// Returns the most recent error.
    pub fn last_err(&self) -> Result<(), Error> {
        self.blk.1
    }

    /// Takes the error and resets it.
    pub fn take_err(&mut self) -> Result<(), Error> {
        let mut err = Ok(());
        swap(&mut self.blk.1, &mut err);
        err
    }
}

// Implements `SparseRawWriter` for tuple (<flash offset>, <block device>)
impl<B: BlockIoAsync> SparseRawWriter for (u64, &mut AsyncBlockDevice<'_, B>) {
    async fn write(&mut self, off: u64, data: &mut [u8]) -> Result<(), CommandError> {
        Ok(self.1.write((SafeNum::from(off) + self.0).try_into()?, data).await?)
    }
}

/// Checks that a partition is unique.
///
/// Returns a pair `(<block device index>, `Partition`)` if the partition exists and is unique.
pub fn check_part_unique<'a>(
    devs: &'a [PartitionBlockDevice<'_, impl BlockIoAsync>],
    part: &str,
) -> Result<(usize, Partition<'a>), Error> {
    let mut filtered = devs
        .iter()
        .enumerate()
        .filter_map(|(i, v)| v.find_partition(Some(part)).ok().map(|v| (i, v)));
    match (filtered.next(), filtered.next()) {
        (Some(v), None) => Ok(v),
        (Some(_), Some(_)) => Err(Error::NotUnique),
        _ => Err(Error::NotFound),
    }
}

/// Checks that a partition is unique among all block devices and reads from it.
pub async fn read_unique_partition(
    devs: &'_ [PartitionBlockDevice<'_, impl BlockIoAsync>],
    part: &str,
    off: u64,
    out: &mut [u8],
) -> Result<(), Error> {
    devs[check_part_unique(devs, part)?.0].partition_io(Some(part))?.read(off, out).await
}

/// Checks that a partition is unique among all block devices and writes to it.
pub async fn write_unique_partition(
    devs: &'_ [PartitionBlockDevice<'_, impl BlockIoAsync>],
    part: &str,
    off: u64,
    data: &mut [u8],
) -> Result<(), Error> {
    devs[check_part_unique(devs, part)?.0].partition_io(Some(part))?.write(off, data).await
}

/// Syncs all GPT type partition devices.
pub async fn sync_gpt(
    devs: &'_ mut [PartitionBlockDevice<'_, impl BlockIoAsync>],
) -> Result<(), Error> {
    for ele in &mut devs[..] {
        ele.sync_gpt().await?;
    }
    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;
    use core::fmt::Debug;
    use gbl_async::block_on;
    use gbl_storage_testlib::{TestBlockDevice, TestBlockIo};

    /// Absolute start/end offset and size of "boot_a/b" partitions in
    /// "../../libstorage/test/gpt_test_1.bin"
    const BOOT_A_OFF: u64 = 17 * 1024;
    const BOOT_A_END: u64 = 25 * 1024;
    const BOOT_A_SZ: u64 = BOOT_A_END - BOOT_A_OFF;
    const BOOT_B_OFF: u64 = 25 * 1024;
    const BOOT_B_END: u64 = 37 * 1024;
    const BOOT_B_SZ: u64 = BOOT_B_END - BOOT_B_OFF;
    /// Total size of disk "../../libstorage/test/gpt_test_1.bin"
    const GPT_DISK_1_SZ: u64 = 64 * 1024;

    /// A helper to convert an integer into usize and panics on error.
    fn to_usize(val: impl TryInto<usize, Error = impl Debug>) -> usize {
        val.try_into().unwrap()
    }

    /// A helper to convert a `TestBlockDevice` into a raw partition device.
    pub fn as_raw_part<'a>(
        test_blk: &'a mut TestBlockDevice,
        name: &'a str,
    ) -> PartitionBlockDevice<'a, &'a mut TestBlockIo> {
        PartitionBlockDevice::new_raw(test_blk.as_blk_dev(), name).unwrap()
    }

    /// A helper to convert a `TestBlockDevice` into a gpt partition device.
    pub fn as_gpt_part<'a>(
        test_blk: &'a mut TestBlockDevice,
    ) -> PartitionBlockDevice<'a, &'a mut TestBlockIo> {
        let (gpt_blk, gpt) = test_blk.as_gpt_dev().into_blk_and_gpt();
        PartitionBlockDevice::new_gpt(gpt_blk, gpt)
    }

    #[test]
    fn test_find_partition_gpt() {
        let mut gpt = (&include_bytes!("../../libstorage/test/gpt_test_1.bin")[..]).into();
        let mut gpt = as_gpt_part(&mut gpt);
        assert!(block_on(gpt.sync_gpt()).unwrap());

        let boot_a = gpt.find_partition(Some("boot_a")).unwrap();
        assert_eq!(boot_a.name().unwrap(), "boot_a");
        assert_eq!(boot_a.size().unwrap(), BOOT_A_SZ);
        assert_eq!(boot_a.absolute_range().unwrap(), (BOOT_A_OFF, BOOT_A_END));

        let boot_b = gpt.find_partition(Some("boot_b")).unwrap();
        assert_eq!(boot_b.name().unwrap(), "boot_b");
        assert_eq!(boot_b.size().unwrap(), BOOT_B_SZ);
        assert_eq!(boot_b.absolute_range().unwrap(), (BOOT_B_OFF, BOOT_B_END));

        let unnamed_whole = gpt.find_partition(None).unwrap();
        assert_eq!(unnamed_whole.name().unwrap(), "");
        assert_eq!(unnamed_whole.size().unwrap(), GPT_DISK_1_SZ);
        assert_eq!(unnamed_whole.absolute_range().unwrap(), (0, GPT_DISK_1_SZ));

        assert!(gpt.find_partition(Some("not-exist")).is_err());
    }

    #[test]
    fn test_find_partition_raw() {
        let disk = include_bytes!("../../libstorage/test/gpt_test_1.bin");
        let mut raw = (&disk[..]).into();
        let raw = as_raw_part(&mut raw, "raw");

        let raw_part = raw.find_partition(Some("raw")).unwrap();
        assert_eq!(raw_part.name().unwrap(), "raw");
        assert_eq!(raw_part.size().unwrap(), GPT_DISK_1_SZ);
        assert_eq!(raw_part.absolute_range().unwrap(), (0, GPT_DISK_1_SZ));

        let unnamed_whole = raw.find_partition(None).unwrap();
        assert_eq!(unnamed_whole.name().unwrap(), "");
        assert_eq!(unnamed_whole.size().unwrap(), GPT_DISK_1_SZ);
        assert_eq!(unnamed_whole.absolute_range().unwrap(), (0, GPT_DISK_1_SZ));

        assert!(raw.find_partition(Some("boot_a")).is_err());
    }

    /// A helper for testing partition read.
    ///
    /// Tests that the content read at `off..off+sz` is the same as `part_content[off..off+sz]`.
    fn test_part_read(
        blk: &PartitionBlockDevice<impl BlockIoAsync>,
        part: Option<&str>,
        part_content: &[u8],
        off: u64,
        sz: u64,
    ) {
        let mut out = vec![0u8; to_usize(sz)];
        block_on(blk.partition_io(part).unwrap().read(off, &mut out)).unwrap();
        assert_eq!(out, part_content[to_usize(off)..][..out.len()].to_vec());

        // Reads using the `sub()` and then read approach.
        let mut out = vec![0u8; to_usize(sz)];
        let mut io = blk.partition_io(part).unwrap().sub(off, sz).unwrap();
        block_on(io.read(0, &mut out)).unwrap();
        assert_eq!(out, part_content[to_usize(off)..][..out.len()].to_vec());
    }

    #[test]
    fn test_read_partition_gpt() {
        let disk = include_bytes!("../../libstorage/test/gpt_test_1.bin");
        let mut gpt = (&disk[..]).into();
        let mut gpt = as_gpt_part(&mut gpt);
        assert!(block_on(gpt.sync_gpt()).unwrap());

        let expect_boot_a = include_bytes!("../../libstorage/test/boot_a.bin");
        test_part_read(&gpt, Some("boot_a"), expect_boot_a, 1, 1024);
        let expect_boot_b = include_bytes!("../../libstorage/test/boot_b.bin");
        test_part_read(&gpt, Some("boot_b"), expect_boot_b, 1, 1024);
        // Whole block read.
        test_part_read(&gpt, None, disk, 1, 1024);
    }

    #[test]
    fn test_read_partition_raw() {
        let disk = include_bytes!("../../libstorage/test/gpt_test_1.bin");
        let mut raw = (&disk[..]).into();
        let raw = as_raw_part(&mut raw, "raw");
        test_part_read(&raw, Some("raw"), disk, 1, 1024);
        test_part_read(&raw, None, disk, 1, 1024);
    }

    /// A helper for testing partition write.
    fn test_part_write(
        blk: &PartitionBlockDevice<impl BlockIoAsync>,
        part: Option<&str>,
        off: u64,
        sz: u64,
    ) {
        // Reads the current partition content
        let mut part_content = vec![0u8; to_usize(blk.partition_io(part).unwrap().size())];
        block_on(blk.partition_io(part).unwrap().read(0, &mut part_content)).unwrap();

        // Flips all the bits in the target range and writes back.
        let seg = &mut part_content[to_usize(off)..][..to_usize(sz)];
        seg.iter_mut().for_each(|v| *v = !(*v));
        block_on(blk.partition_io(part).unwrap().write(off, seg)).unwrap();
        // Checks that data is written.
        test_part_read(blk, part, &part_content, off, sz);

        // Writes using the `sub()` and then write approach.
        let seg = &mut part_content[to_usize(off)..][..to_usize(sz)];
        seg.iter_mut().for_each(|v| *v = !(*v));
        block_on(blk.partition_io(part).unwrap().sub(off, sz).unwrap().write(0, seg)).unwrap();
        test_part_read(blk, part, &part_content, off, sz);
    }

    #[test]
    fn test_write_partition_gpt() {
        let mut gpt = (&include_bytes!("../../libstorage/test/gpt_test_1.bin")[..]).into();
        let mut gpt = as_gpt_part(&mut gpt);
        assert!(block_on(gpt.sync_gpt()).unwrap());
        test_part_write(&gpt, Some("boot_a"), 1, 1024);
        test_part_write(&gpt, Some("boot_b"), 1, 1024);
        test_part_write(&gpt, None, 1, 1024);
    }

    #[test]
    fn test_write_partition_raw() {
        let mut raw = (&include_bytes!("../../libstorage/test/gpt_test_1.bin")[..]).into();
        let mut raw = as_raw_part(&mut raw, "raw");
        test_part_write(&mut raw, Some("raw"), 1, 1024);
        test_part_write(&mut raw, None, 1, 1024);
    }

    #[test]
    fn test_read_write_partition_overflow() {
        let disk = include_bytes!("../../libstorage/test/gpt_test_1.bin");
        let mut gpt = (&disk[..]).into();
        let mut gpt = as_gpt_part(&mut gpt);
        assert!(block_on(gpt.sync_gpt()).unwrap());

        let mut part_io = gpt.partition_io(Some("boot_a")).unwrap();
        assert!(block_on(part_io.read(BOOT_A_END, &mut vec![0u8; 1])).is_err());
        assert!(
            block_on(part_io.read(BOOT_A_OFF, &mut vec![0u8; to_usize(BOOT_A_SZ) + 1])).is_err()
        );
        assert!(block_on(part_io.write(BOOT_A_END, &mut vec![0u8; 1])).is_err());
        assert!(
            block_on(part_io.write(BOOT_A_OFF, &mut vec![0u8; to_usize(BOOT_A_SZ) + 1])).is_err()
        );

        let mut raw = (&disk[..]).into();
        let raw = as_raw_part(&mut raw, "raw");
        let mut part_io = raw.partition_io(Some("raw")).unwrap();
        assert!(block_on(part_io.read(GPT_DISK_1_SZ, &mut vec![0u8; 1])).is_err());
        assert!(block_on(part_io.read(0, &mut vec![0u8; to_usize(GPT_DISK_1_SZ) + 1])).is_err());
        assert!(block_on(part_io.write(GPT_DISK_1_SZ, &mut vec![0u8; 1])).is_err());
        assert!(block_on(part_io.write(0, &mut vec![0u8; to_usize(GPT_DISK_1_SZ) + 1])).is_err());
    }

    #[test]
    fn test_sub_overflow() {
        let disk = include_bytes!("../../libstorage/test/gpt_test_1.bin");
        let mut gpt = (&disk[..]).into();
        let mut gpt = as_gpt_part(&mut gpt);
        assert!(block_on(gpt.sync_gpt()).unwrap());
        assert!(gpt.partition_io(Some("boot_a")).unwrap().sub(0, BOOT_A_SZ + 1).is_err());
        assert!(gpt.partition_io(Some("boot_a")).unwrap().sub(1, BOOT_A_SZ).is_err());

        let mut raw = (&disk[..]).into();
        let raw = as_raw_part(&mut raw, "raw");
        assert!(raw.partition_io(Some("raw")).unwrap().sub(0, GPT_DISK_1_SZ + 1).is_err());
        assert!(raw.partition_io(Some("raw")).unwrap().sub(1, GPT_DISK_1_SZ).is_err());
    }

    #[test]
    fn test_write_sparse() {
        let sparse_raw = include_bytes!("../testdata/sparse_test_raw.bin");
        let mut sparse = include_bytes!("../testdata/sparse_test.bin").to_vec();
        let mut raw = (&vec![0u8; sparse_raw.len() + 512][..]).into();
        let raw = as_raw_part(&mut raw, "raw");
        block_on(raw.partition_io(Some("raw")).unwrap().write_sparse(1, &mut sparse)).unwrap();
        let mut expected = vec![0u8; sparse_raw.len() + 512];
        expected[1..][..sparse_raw.len()].clone_from_slice(sparse_raw);
        test_part_read(&raw, Some("raw"), &expected, 1, sparse_raw.len().try_into().unwrap());
    }

    #[test]
    fn test_write_sparse_not_sparse_image() {
        let sparse_raw = include_bytes!("../testdata/sparse_test_raw.bin");
        let mut sparse = include_bytes!("../testdata/sparse_test.bin").to_vec();
        sparse[0] = !sparse[0]; // Corrupt image.
        let mut raw = (&vec![0u8; sparse_raw.len() + 512][..]).into();
        let raw = as_raw_part(&mut raw, "raw");
        assert!(
            block_on(raw.partition_io(Some("raw")).unwrap().write_sparse(1, &mut sparse)).is_err()
        );
        assert!(raw.partition_io(Some("raw")).unwrap().last_err().is_err());
    }

    #[test]
    fn test_write_sparse_overflow_size() {
        let sparse_raw = include_bytes!("../testdata/sparse_test_raw.bin");
        let mut sparse = include_bytes!("../testdata/sparse_test.bin").to_vec();
        let mut raw = (&vec![0u8; sparse_raw.len()][..]).into();
        let raw = as_raw_part(&mut raw, "raw");
        assert!(
            block_on(raw.partition_io(Some("raw")).unwrap().write_sparse(1, &mut sparse)).is_err()
        );
        assert!(raw.partition_io(Some("raw")).unwrap().last_err().is_err());
    }

    #[test]
    fn test_partiton_last_err_read() {
        let mut raw = (&vec![0u8; 1024][..]).into();
        let raw = as_raw_part(&mut raw, "raw");
        let mut part_io = raw.partition_io(Some("raw")).unwrap();
        // Causes some error by read
        assert!(block_on(part_io.read(1024, &mut [0])).is_err());
        assert!(part_io.last_err().is_err());
    }

    #[test]
    fn test_partiton_last_err_write() {
        let mut raw = (&vec![0u8; 1024][..]).into();
        let raw = as_raw_part(&mut raw, "raw");
        let mut part_io = raw.partition_io(Some("raw")).unwrap();
        // Causes some error by write
        assert!(block_on(part_io.write(1024, &mut [0])).is_err());
        assert!(part_io.last_err().is_err());
    }

    #[test]
    fn test_partiton_last_err_persist_through_operation() {
        let mut raw = (&vec![0u8; 1024][..]).into();
        let raw = as_raw_part(&mut raw, "raw");
        // Causes some error by read
        assert!(block_on(raw.partition_io(Some("raw")).unwrap().read(1024, &mut [0])).is_err());
        // Tracked error should persist regardless of how many times we get partition io.
        assert!(raw.partition_io(Some("raw")).unwrap().last_err().is_err());
        assert!(raw.partition_io(None).unwrap().last_err().is_err());
        // Should persist even after successful operations.
        block_on(raw.partition_io(Some("raw")).unwrap().read(1023, &mut [0])).unwrap();
        assert!(raw.partition_io(Some("raw")).unwrap().last_err().is_err());
        block_on(raw.partition_io(Some("raw")).unwrap().write(1023, &mut [0])).unwrap();
        assert!(raw.partition_io(Some("raw")).unwrap().last_err().is_err());
        assert!(raw.partition_io(None).unwrap().last_err().is_err());
        // Taking error should reset it.
        assert!(raw.partition_io(None).unwrap().take_err().is_err());
        assert!(raw.partition_io(None).unwrap().last_err().is_ok());
    }

    /// A test helper for `read_unique_partition`
    /// It verifies that data read from partition `part` at offset `off` is the same as
    /// `part_content[off..off+sz]`.
    fn check_read_partition(
        devs: &[PartitionBlockDevice<impl BlockIoAsync>],
        part: &str,
        part_content: &[u8],
        off: u64,
        sz: u64,
    ) {
        let mut out = vec![0u8; to_usize(sz)];
        block_on(read_unique_partition(devs, part, off, &mut out)).unwrap();
        assert_eq!(out, part_content[to_usize(off)..][..out.len()]);
    }

    #[test]
    fn test_read_unique_partition() {
        let mut gpt_0 = (&include_bytes!("../../libstorage/test/gpt_test_1.bin")[..]).into();
        let mut gpt_1 = (&include_bytes!("../../libstorage/test/gpt_test_2.bin")[..]).into();
        let mut raw_0 = [0xaau8; 4 * 1024].as_slice().into();
        let mut raw_1 = [0x55u8; 4 * 1024].as_slice().into();
        let mut devs = vec![
            as_gpt_part(&mut gpt_0),
            as_gpt_part(&mut gpt_1),
            as_raw_part(&mut raw_0, "raw_0"),
            as_raw_part(&mut raw_1, "raw_1"),
        ];
        block_on(sync_gpt(&mut devs)).unwrap();

        let boot_a = include_bytes!("../../libstorage/test/boot_a.bin");
        let boot_b = include_bytes!("../../libstorage/test/boot_b.bin");

        let off = 512u64;
        let sz = 1024u64;
        check_read_partition(&mut devs, "boot_a", boot_a, off, sz);
        check_read_partition(&mut devs, "boot_b", boot_b, off, sz);

        let vendor_boot_a = include_bytes!("../../libstorage/test/vendor_boot_a.bin");
        let vendor_boot_b = include_bytes!("../../libstorage/test/vendor_boot_b.bin");

        check_read_partition(&mut devs, "vendor_boot_a", vendor_boot_a, off, sz);
        check_read_partition(&mut devs, "vendor_boot_b", vendor_boot_b, off, sz);

        check_read_partition(&mut devs, "raw_0", &[0xaau8; 4 * 1024][..], off, sz);
        check_read_partition(&mut devs, "raw_1", &[0x55u8; 4 * 1024][..], off, sz);
    }

    /// A test helper for `write_unique_partition`
    fn check_write_partition(
        devs: &[PartitionBlockDevice<impl BlockIoAsync>],
        part: &str,
        off: u64,
        sz: u64,
    ) {
        // Reads the current partition content
        let (_, p) = check_part_unique(devs, part).unwrap();
        let mut part_content = vec![0u8; to_usize(p.size().unwrap())];
        block_on(read_unique_partition(devs, part, 0, &mut part_content)).unwrap();

        // Flips all the bits in the target range and writes back.
        let seg = &mut part_content[to_usize(off)..][..to_usize(sz)];
        seg.iter_mut().for_each(|v| *v = !(*v));
        block_on(write_unique_partition(devs, part, off, seg)).unwrap();
        // Checks that data is written.
        check_read_partition(devs, part, &part_content, off, sz);
    }

    #[test]
    fn test_write_unique_partition() {
        let mut gpt_0 = (&include_bytes!("../../libstorage/test/gpt_test_1.bin")[..]).into();
        let mut gpt_1 = (&include_bytes!("../../libstorage/test/gpt_test_2.bin")[..]).into();
        let mut raw_0 = [0xaau8; 4 * 1024].as_slice().into();
        let mut raw_1 = [0x55u8; 4 * 1024].as_slice().into();
        let mut devs = vec![
            as_gpt_part(&mut gpt_0),
            as_gpt_part(&mut gpt_1),
            as_raw_part(&mut raw_0, "raw_0"),
            as_raw_part(&mut raw_1, "raw_1"),
        ];
        block_on(sync_gpt(&mut devs)).unwrap();

        let off = 512u64;
        let sz = 1024u64;
        check_write_partition(&mut devs, "boot_a", off, sz);
        check_write_partition(&mut devs, "boot_b", off, sz);
        check_write_partition(&mut devs, "vendor_boot_a", off, sz);
        check_write_partition(&mut devs, "vendor_boot_b", off, sz);
        check_write_partition(&mut devs, "raw_0", off, sz);
        check_write_partition(&mut devs, "raw_1", off, sz);
    }

    #[test]
    fn test_rw_fail_with_non_unique_partition() {
        let mut gpt_0 = (&include_bytes!("../../libstorage/test/gpt_test_1.bin")[..]).into();
        let mut gpt_1 = (&include_bytes!("../../libstorage/test/gpt_test_1.bin")[..]).into();
        let mut raw_0 = [0xaau8; 4 * 1024].as_slice().into();
        let mut raw_1 = [0x55u8; 4 * 1024].as_slice().into();
        let mut devs = vec![
            as_gpt_part(&mut gpt_0),
            as_gpt_part(&mut gpt_1),
            as_raw_part(&mut raw_0, "raw"),
            as_raw_part(&mut raw_1, "raw"),
        ];
        block_on(sync_gpt(&mut devs)).unwrap();
        assert!(block_on(read_unique_partition(&devs, "boot_a", 0, &mut [],)).is_err());
        assert!(block_on(write_unique_partition(&devs, "boot_a", 0, &mut [],)).is_err());
        assert!(block_on(read_unique_partition(&devs, "raw", 0, &mut [],)).is_err());
        assert!(block_on(write_unique_partition(&devs, "raw", 0, &mut [],)).is_err());
    }
}
