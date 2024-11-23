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

//! This file implements storage and partition logic for libgbl.

use crate::fastboot::sparse::{is_sparse_image, write_sparse_image, SparseRawWriter};
use core::cell::{RefCell, RefMut};
use core::{
    ffi::CStr,
    mem::swap,
    ops::{Deref, DerefMut},
};
use gbl_storage::{BlockInfo, BlockIo, Disk, Gpt, GptSyncResult, Partition as GptPartition};
use liberror::Error;
use safemath::SafeNum;

/// Maximum name length for raw partition.
const RAW_PARTITION_NAME_LEN: usize = 72;

/// Wraps a bytes buffer containing a null-terminated C string
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct RawName([u8; RAW_PARTITION_NAME_LEN]);

impl RawName {
    fn new(name: &CStr) -> Result<Self, Error> {
        let mut buf = [0u8; RAW_PARTITION_NAME_LEN];
        name.to_str().map_err(|_| Error::InvalidInput)?;
        let name = name.to_bytes_with_nul();
        buf.get_mut(..name.len()).ok_or(Error::InvalidInput)?.clone_from_slice(name);
        Ok(Self(buf))
    }

    /// Decodes to a string.
    pub fn to_str(&self) -> &str {
        CStr::from_bytes_until_nul(&self.0[..]).unwrap().to_str().unwrap()
    }
}

/// Represents a GBL partition.
#[derive(Copy, Clone, PartialEq, Debug)]
pub enum Partition {
    /// Raw storage partition.
    Raw(RawName, u64),
    /// Gpt Partition.
    Gpt(GptPartition),
}

impl Partition {
    /// Returns the size.
    pub fn size(&self) -> Result<u64, Error> {
        let (start, end) = self.absolute_range()?;
        Ok((SafeNum::from(end) - start).try_into()?)
    }

    /// Returns the name.
    pub fn name(&self) -> Result<&str, Error> {
        Ok(match self {
            Partition::Gpt(gpt) => gpt.name().ok_or(Error::InvalidInput)?,
            Partition::Raw(name, _) => name.to_str(),
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
enum PartitionTable<G> {
    Raw(RawName, u64),
    Gpt(G),
}

/// The status of block device
pub enum BlockStatus {
    /// Idle,
    Idle,
    /// An IO in progress.
    Pending,
    /// Error.
    Error(Error),
}

impl BlockStatus {
    /// Converts to str.
    pub fn to_str(&self) -> &'static str {
        match self {
            BlockStatus::Idle => "idle",
            BlockStatus::Pending => "IO pending",
            BlockStatus::Error(_) => "error",
        }
    }

    /// Converts to result.
    pub fn result(&self) -> Result<(), Error> {
        match self {
            Self::Error(e) => Err(*e),
            _ => Ok(()),
        }
    }
}

/// Represents a disk device that contains either GPT partitions or a single whole raw storage
/// partition.
pub struct GblDisk<D, G> {
    // Contains a `Disk` for block IO and `Result` to track the most recent error.
    // Wraps in `Mutex` as it will be used in parallel fastboot task.
    //
    // `blk` and `partitions` are wrapped in RefCell because they may be shared by multiple async
    // blocks for operations such as parallel fastboot download/flashing. They are also wrapped
    // separately in order to make operations on each independent and parallel for use cases such
    // as getting partition info for `fastboot getvar` when disk IO is busy.
    disk: RefCell<(D, Result<(), Error>)>,
    partitions: RefCell<PartitionTable<G>>,
    info_cache: BlockInfo,
}

impl<B, S, T> GblDisk<Disk<B, S>, Gpt<T>>
where
    B: BlockIo,
    S: DerefMut<Target = [u8]>,
    T: DerefMut<Target = [u8]>,
{
    /// Creates a new instance as a GPT device.
    pub fn new_gpt(mut disk: Disk<B, S>, gpt: Gpt<T>) -> Self {
        let info_cache = disk.io().info();
        Self {
            disk: (disk, Ok(())).into(),
            info_cache,
            partitions: PartitionTable::Gpt(gpt).into(),
        }
    }

    /// Creates a new instance as a raw storage partition.
    pub fn new_raw(mut disk: Disk<B, S>, name: &CStr) -> Result<Self, Error> {
        let info_cache = disk.io().info();
        Ok(Self {
            disk: (disk, Ok(())).into(),
            info_cache,
            partitions: PartitionTable::Raw(RawName::new(name)?, info_cache.total_size()?).into(),
        })
    }

    /// Gets the cached `BlockInfo`.
    pub fn block_info(&self) -> BlockInfo {
        self.info_cache
    }

    /// Gets the block status.
    pub fn status(&self) -> BlockStatus {
        match self.disk.try_borrow_mut().ok() {
            None => BlockStatus::Pending,
            Some(v) if v.1.is_err() => BlockStatus::Error(v.1.unwrap_err()),
            _ => BlockStatus::Idle,
        }
    }

    /// Gets an instance of `PartitionIo` for a partition.
    ///
    /// If `part` is `None`, an IO for the whole block device is returned.
    pub fn partition_io(&self, part: Option<&str>) -> Result<PartitionIo<'_, B>, Error> {
        let (part_start, part_end) = self.find_partition(part)?.absolute_range()?;
        let (disk, last_err) =
            RefMut::map_split(self.disk.try_borrow_mut().map_err(|_| Error::NotReady)?, |v| {
                (&mut v.0, &mut v.1)
            });
        Ok(PartitionIo { disk: Disk::from_ref_mut(disk), last_err, part_start, part_end })
    }

    /// Finds a partition.
    ///
    /// * If `part` is none, the method returns an unnamed `Partition` that represents the whole
    //    raw storage.
    pub fn find_partition(&self, part: Option<&str>) -> Result<Partition, Error> {
        let Some(part) = part else {
            return Ok(Partition::Raw(RawName::new(c"").unwrap(), self.info_cache.total_size()?));
        };

        match self.partitions.try_borrow_mut().map_err(|_| Error::NotReady)?.deref() {
            PartitionTable::Gpt(gpt) => Ok(Partition::Gpt(gpt.find_partition(part)?)),
            PartitionTable::Raw(name, size) if name.to_str() == part => {
                Ok(Partition::Raw(*name, *size))
            }
            _ => Err(Error::NotFound),
        }
    }

    /// Get total number of partitions.
    pub fn num_partitions(&self) -> Result<usize, Error> {
        match self.partitions.try_borrow_mut().map_err(|_| Error::NotReady)?.deref() {
            PartitionTable::Raw(_, _) => Ok(1),
            PartitionTable::Gpt(gpt) => gpt.num_partitions(),
        }
    }

    /// Gets a partition by index.
    pub fn get_partition_by_idx(&self, idx: usize) -> Result<Partition, Error> {
        match self.partitions.try_borrow_mut().map_err(|_| Error::NotReady)?.deref() {
            PartitionTable::Raw(name, v) if idx == 0 => Ok(Partition::Raw(*name, *v)),
            PartitionTable::Gpt(gpt) => Ok(Partition::Gpt(gpt.get_partition(idx)?)),
            _ => Err(Error::InvalidInput),
        }
    }

    /// Syncs GPT if the partition type is GPT.
    ///
    /// # Returns
    ///
    /// * Returns `Ok(Some(sync_res))` if partition type is GPT and disk access is successful, where
    ///  `sync_res` contains the GPT verification and restoration result.
    /// * Returns `Ok(None)` if partition type is not GPT.
    /// * Returns `Err` in other cases.
    pub async fn sync_gpt(&self) -> Result<Option<GptSyncResult>, Error> {
        match self.partitions.try_borrow_mut().map_err(|_| Error::NotReady)?.deref_mut() {
            PartitionTable::Raw(_, _) => Ok(None),
            PartitionTable::Gpt(ref mut gpt) => {
                let mut blk = self.disk.try_borrow_mut().map_err(|_| Error::NotReady)?;
                Ok(Some(blk.0.sync_gpt(gpt).await?))
            }
        }
    }

    /// Updates GPT to the block device and sync primary and secondary GPT.
    ///
    /// # Args
    ///
    /// * `mbr_primary`: A buffer containing the MBR block, primary GPT header and entries.
    /// * `resize`: If set to true, the method updates the last partition to cover the rest of the
    ///    storage.
    ///
    /// # Returns
    ///
    /// * Return `Err(Error::NotReady)` if device is busy.
    /// * Return `Err(Error::Unsupported)` if partition type is not GPT.
    /// * Return `Ok(())` new GPT is valid and device is updated and synced successfully.
    pub async fn update_gpt(&self, mbr_primary: &mut [u8], resize: bool) -> Result<(), Error> {
        match self.partitions.try_borrow_mut().map_err(|_| Error::NotReady)?.deref_mut() {
            PartitionTable::Raw(_, _) => Err(Error::Unsupported),
            PartitionTable::Gpt(ref mut gpt) => {
                let mut blk = self.disk.try_borrow_mut().map_err(|_| Error::NotReady)?;
                blk.0.update_gpt(mbr_primary, resize, gpt).await
            }
        }
    }

    /// Erases GPT on the disk.
    ///
    /// # Returns
    ///
    /// * Return `Err(Error::NotReady)` if device is busy.
    /// * Return `Err(Error::Unsupported)` if partition type is not GPT.
    pub async fn erase_gpt(&self) -> Result<(), Error> {
        match self.partitions.try_borrow_mut().map_err(|_| Error::NotReady)?.deref_mut() {
            PartitionTable::Raw(_, _) => Err(Error::Unsupported),
            PartitionTable::Gpt(ref mut gpt) => {
                let mut disk = self.disk.try_borrow_mut().map_err(|_| Error::NotReady)?;
                disk.0.erase_gpt(gpt).await
            }
        }
    }
}

/// `PartitionIo` provides read/write APIs to a partition.
pub struct PartitionIo<'a, B: BlockIo> {
    disk: Disk<RefMut<'a, B>, RefMut<'a, [u8]>>,
    last_err: RefMut<'a, Result<(), Error>>,
    part_start: u64,
    part_end: u64,
}

impl<'a, B: BlockIo> PartitionIo<'a, B> {
    /// Returns the size of the partition.
    pub fn size(&self) -> u64 {
        // Corrects by construction. Should not fail.
        self.part_end.checked_sub(self.part_start).unwrap()
    }

    /// Gets the block device.
    pub fn dev(&mut self) -> &mut Disk<RefMut<'a, B>, RefMut<'a, [u8]>> {
        &mut self.disk
    }

    /// Checks the read/write parameters and returns the absolute offset in the block.
    fn check_rw_range(&self, off: u64, size: impl Into<SafeNum>) -> Result<u64, Error> {
        let ab_range_end = SafeNum::from(self.part_start) + off + size.into();
        // Checks overflow by computing the difference between range end and partition end and
        // making sure it succeeds.
        let _end_diff: u64 = (SafeNum::from(self.part_end) - ab_range_end).try_into()?;
        Ok((SafeNum::from(self.part_start) + off).try_into()?)
    }

    /// Writes to the partition.
    pub async fn write(&mut self, off: u64, data: &mut [u8]) -> Result<(), Error> {
        let res =
            async { self.disk.write(self.check_rw_range(off, data.len())?, data).await }.await;
        *self.last_err = res.and(*self.last_err);
        res
    }

    /// Reads from the partition.
    pub async fn read(&mut self, off: u64, out: &mut [u8]) -> Result<(), Error> {
        let res = async { self.disk.read(self.check_rw_range(off, out.len())?, out).await }.await;
        *self.last_err = res.and(*self.last_err);
        res
    }

    /// Writes zeroes to the partition.
    pub async fn zeroize(&mut self, scratch: &mut [u8]) -> Result<(), Error> {
        let res = async { self.disk.fill(self.part_start, self.size(), 0, scratch).await }.await;
        *self.last_err = res.and(*self.last_err);
        *self.last_err
    }

    /// Writes sparse image to the partition.
    pub async fn write_sparse(&mut self, off: u64, img: &mut [u8]) -> Result<(), Error> {
        let res = async {
            let sz = is_sparse_image(img).map_err(|_| Error::InvalidInput)?.data_size();
            write_sparse_image(img, &mut (self.check_rw_range(off, sz)?, &mut self.disk)).await
        }
        .await;
        *self.last_err = res.map(|_| ()).and(*self.last_err);
        *self.last_err
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
        *self.last_err
    }

    /// Takes the error and resets it.
    pub fn take_err(&mut self) -> Result<(), Error> {
        let mut err = Ok(());
        swap(&mut self.last_err as _, &mut err);
        err
    }
}

// Implements `SparseRawWriter` for tuple (<flash offset>, <block device>)
impl<B, S> SparseRawWriter for (u64, &mut Disk<B, S>)
where
    B: BlockIo,
    S: DerefMut<Target = [u8]>,
{
    async fn write(&mut self, off: u64, data: &mut [u8]) -> Result<(), Error> {
        Ok(self.1.write((SafeNum::from(off) + self.0).try_into()?, data).await?)
    }
}

/// Checks that a partition is unique.
///
/// Returns a pair `(<block device index>, `Partition`)` if the partition exists and is unique.
pub fn check_part_unique(
    devs: &'_ [GblDisk<
        Disk<impl BlockIo, impl DerefMut<Target = [u8]>>,
        Gpt<impl DerefMut<Target = [u8]>>,
    >],
    part: &str,
) -> Result<(usize, Partition), Error> {
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
    devs: &'_ [GblDisk<
        Disk<impl BlockIo, impl DerefMut<Target = [u8]>>,
        Gpt<impl DerefMut<Target = [u8]>>,
    >],
    part: &str,
    off: u64,
    out: &mut [u8],
) -> Result<(), Error> {
    devs[check_part_unique(devs, part)?.0].partition_io(Some(part))?.read(off, out).await
}

/// Checks that a partition is unique among all block devices and writes to it.
pub async fn write_unique_partition(
    devs: &'_ [GblDisk<
        Disk<impl BlockIo, impl DerefMut<Target = [u8]>>,
        Gpt<impl DerefMut<Target = [u8]>>,
    >],
    part: &str,
    off: u64,
    data: &mut [u8],
) -> Result<(), Error> {
    devs[check_part_unique(devs, part)?.0].partition_io(Some(part))?.write(off, data).await
}

/// Syncs all GPT type partition devices.
pub async fn sync_gpt(
    devs: &'_ [GblDisk<
        Disk<impl BlockIo, impl DerefMut<Target = [u8]>>,
        Gpt<impl DerefMut<Target = [u8]>>,
    >],
) -> Result<(), Error> {
    for ele in &devs[..] {
        ele.sync_gpt().await?;
    }
    Ok(())
}

#[cfg(test)]
pub(crate) mod test {
    use super::*;
    use crate::ops::test::{FakeGblOpsStorage, TestGblDisk};
    use core::fmt::Debug;
    use gbl_async::block_on;

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

    /// A helper to create a GPT type TestGblDisk
    fn gpt_disk(data: impl AsRef<[u8]>) -> TestGblDisk {
        let mut res = FakeGblOpsStorage::default();
        res.add_gpt_device(data);
        res.0.pop().unwrap()
    }

    /// A helper to create a raw disk partition type TestGblDisk
    fn raw_disk(name: &CStr, data: impl AsRef<[u8]>) -> TestGblDisk {
        let mut res = FakeGblOpsStorage::default();
        res.add_raw_device(name, data);
        res.0.pop().unwrap()
    }

    #[test]
    fn test_find_partition_gpt() {
        let gpt = gpt_disk(include_bytes!("../../libstorage/test/gpt_test_1.bin"));
        assert_eq!(block_on(gpt.sync_gpt()).unwrap(), Some(GptSyncResult::BothValid));

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
        let raw = raw_disk(c"raw", &disk);

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
        blk: &TestGblDisk,
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
        let gpt = gpt_disk(&disk[..]);
        assert_eq!(block_on(gpt.sync_gpt()).unwrap(), Some(GptSyncResult::BothValid));

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
        let raw = raw_disk(c"raw", &disk);
        test_part_read(&raw, Some("raw"), disk, 1, 1024);
        test_part_read(&raw, None, disk, 1, 1024);
    }

    /// A helper for testing partition write.
    fn test_part_write(blk: &TestGblDisk, part: Option<&str>, off: u64, sz: u64) {
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
        let gpt = gpt_disk(include_bytes!("../../libstorage/test/gpt_test_1.bin"));
        assert_eq!(block_on(gpt.sync_gpt()).unwrap(), Some(GptSyncResult::BothValid));
        test_part_write(&gpt, Some("boot_a"), 1, 1024);
        test_part_write(&gpt, Some("boot_b"), 1, 1024);
        test_part_write(&gpt, None, 1, 1024);
    }

    #[test]
    fn test_write_partition_raw() {
        let mut raw = raw_disk(c"raw", include_bytes!("../../libstorage/test/gpt_test_1.bin"));
        test_part_write(&mut raw, Some("raw"), 1, 1024);
        test_part_write(&mut raw, None, 1, 1024);
    }

    #[test]
    fn test_read_write_partition_overflow() {
        let disk = include_bytes!("../../libstorage/test/gpt_test_1.bin");
        let gpt = gpt_disk(&disk[..]);
        assert_eq!(block_on(gpt.sync_gpt()).unwrap(), Some(GptSyncResult::BothValid));

        let mut part_io = gpt.partition_io(Some("boot_a")).unwrap();
        assert!(block_on(part_io.read(BOOT_A_END, &mut vec![0u8; 1])).is_err());
        assert!(
            block_on(part_io.read(BOOT_A_OFF, &mut vec![0u8; to_usize(BOOT_A_SZ) + 1])).is_err()
        );
        assert!(block_on(part_io.write(BOOT_A_END, &mut vec![0u8; 1])).is_err());
        assert!(
            block_on(part_io.write(BOOT_A_OFF, &mut vec![0u8; to_usize(BOOT_A_SZ) + 1])).is_err()
        );

        let raw = raw_disk(c"raw", &disk);
        let mut part_io = raw.partition_io(Some("raw")).unwrap();
        assert!(block_on(part_io.read(GPT_DISK_1_SZ, &mut vec![0u8; 1])).is_err());
        assert!(block_on(part_io.read(0, &mut vec![0u8; to_usize(GPT_DISK_1_SZ) + 1])).is_err());
        assert!(block_on(part_io.write(GPT_DISK_1_SZ, &mut vec![0u8; 1])).is_err());
        assert!(block_on(part_io.write(0, &mut vec![0u8; to_usize(GPT_DISK_1_SZ) + 1])).is_err());
    }

    #[test]
    fn test_sub_overflow() {
        let disk = include_bytes!("../../libstorage/test/gpt_test_1.bin");
        let gpt = gpt_disk(&disk[..]);
        assert_eq!(block_on(gpt.sync_gpt()).unwrap(), Some(GptSyncResult::BothValid));
        assert!(gpt.partition_io(Some("boot_a")).unwrap().sub(0, BOOT_A_SZ + 1).is_err());
        assert!(gpt.partition_io(Some("boot_a")).unwrap().sub(1, BOOT_A_SZ).is_err());

        let raw = raw_disk(c"raw", &disk);
        assert!(raw.partition_io(Some("raw")).unwrap().sub(0, GPT_DISK_1_SZ + 1).is_err());
        assert!(raw.partition_io(Some("raw")).unwrap().sub(1, GPT_DISK_1_SZ).is_err());
    }

    #[test]
    fn test_write_sparse() {
        let sparse_raw = include_bytes!("../testdata/sparse_test_raw.bin");
        let mut sparse = include_bytes!("../testdata/sparse_test.bin").to_vec();
        let raw = &vec![0u8; sparse_raw.len() + 512][..];
        let blk = raw_disk(c"raw", raw);
        block_on(
            blk.partition_io(Some("raw"))
                .unwrap()
                .sub(1, u64::try_from(raw.len() - 1).unwrap())
                .unwrap()
                .write_sparse(1, &mut sparse),
        )
        .unwrap();
        let mut expected = vec![0u8; raw.len()];
        expected[1 + 1..][..sparse_raw.len()].clone_from_slice(sparse_raw);
        test_part_read(&blk, Some("raw"), &expected, 1, sparse_raw.len().try_into().unwrap());
    }

    #[test]
    fn test_write_sparse_not_sparse_image() {
        let sparse_raw = include_bytes!("../testdata/sparse_test_raw.bin");
        let mut sparse = include_bytes!("../testdata/sparse_test.bin").to_vec();
        sparse[0] = !sparse[0]; // Corrupt image.
        let raw = raw_disk(c"raw", vec![0u8; sparse_raw.len() + 512]);
        assert!(
            block_on(raw.partition_io(Some("raw")).unwrap().write_sparse(1, &mut sparse)).is_err()
        );
        assert!(raw.partition_io(Some("raw")).unwrap().last_err().is_err());
    }

    #[test]
    fn test_write_sparse_overflow_size() {
        let sparse_raw = include_bytes!("../testdata/sparse_test_raw.bin");
        let mut sparse = include_bytes!("../testdata/sparse_test.bin").to_vec();
        let raw = raw_disk(c"raw", vec![0u8; sparse_raw.len()]);
        assert!(
            block_on(raw.partition_io(Some("raw")).unwrap().write_sparse(1, &mut sparse)).is_err()
        );
        assert!(raw.partition_io(Some("raw")).unwrap().last_err().is_err());
    }

    #[test]
    fn test_partiton_last_err_read() {
        let raw = raw_disk(c"raw", vec![0u8; 1024]);
        let mut part_io = raw.partition_io(Some("raw")).unwrap();
        // Causes some error by read
        assert!(block_on(part_io.read(1024, &mut [0])).is_err());
        assert!(part_io.last_err().is_err());
    }

    #[test]
    fn test_partiton_last_err_write() {
        let raw = raw_disk(c"raw", vec![0u8; 1024]);
        let mut part_io = raw.partition_io(Some("raw")).unwrap();
        // Causes some error by write
        assert!(block_on(part_io.write(1024, &mut [0])).is_err());
        assert!(part_io.last_err().is_err());
    }

    #[test]
    fn test_partiton_last_err_persist_through_operation() {
        let raw = raw_disk(c"raw", vec![0u8; 1024]);
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

    #[test]
    fn test_partition_iter() {
        let raw = raw_disk(c"raw", vec![0u8; 1024]);
        assert_eq!(raw.num_partitions().unwrap(), 1);
        assert_eq!(raw.get_partition_by_idx(0).unwrap().name(), Ok("raw"));
        assert_eq!(raw.get_partition_by_idx(0).unwrap().size(), Ok(1024));

        let gpt = gpt_disk(include_bytes!("../../libstorage/test/gpt_test_1.bin"));
        block_on(gpt.sync_gpt()).unwrap();
        assert_eq!(gpt.num_partitions().unwrap(), 2);
        assert_eq!(gpt.get_partition_by_idx(0).unwrap().name().unwrap(), "boot_a");
        assert_eq!(gpt.get_partition_by_idx(0).unwrap().size().unwrap(), 0x2000);
        assert_eq!(gpt.get_partition_by_idx(1).unwrap().name().unwrap(), "boot_b");
        assert_eq!(gpt.get_partition_by_idx(1).unwrap().size().unwrap(), 0x3000);
    }

    /// A test helper for `read_unique_partition`
    /// It verifies that data read from partition `part` at offset `off` is the same as
    /// `part_content[off..off+sz]`.
    fn check_read_partition(
        devs: &[TestGblDisk],
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
        let mut devs = FakeGblOpsStorage::default();
        devs.add_gpt_device(include_bytes!("../../libstorage/test/gpt_test_1.bin"));
        devs.add_gpt_device(include_bytes!("../../libstorage/test/gpt_test_2.bin"));
        devs.add_raw_device(c"raw_0", [0xaau8; 4 * 1024]);
        devs.add_raw_device(c"raw_1", [0x55u8; 4 * 1024]);

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
    fn check_write_partition(devs: &[TestGblDisk], part: &str, off: u64, sz: u64) {
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
        let mut devs = FakeGblOpsStorage::default();
        devs.add_gpt_device(include_bytes!("../../libstorage/test/gpt_test_1.bin"));
        devs.add_gpt_device(include_bytes!("../../libstorage/test/gpt_test_2.bin"));
        devs.add_raw_device(c"raw_0", [0xaau8; 4 * 1024]);
        devs.add_raw_device(c"raw_1", [0x55u8; 4 * 1024]);

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
        let mut devs = FakeGblOpsStorage::default();
        devs.add_gpt_device(include_bytes!("../../libstorage/test/gpt_test_1.bin"));
        devs.add_gpt_device(include_bytes!("../../libstorage/test/gpt_test_1.bin"));
        devs.add_raw_device(c"raw", [0xaau8; 4 * 1024]);
        devs.add_raw_device(c"raw", [0x55u8; 4 * 1024]);

        assert!(block_on(read_unique_partition(&devs, "boot_a", 0, &mut [],)).is_err());
        assert!(block_on(write_unique_partition(&devs, "boot_a", 0, &mut [],)).is_err());
        assert!(block_on(read_unique_partition(&devs, "raw", 0, &mut [],)).is_err());
        assert!(block_on(write_unique_partition(&devs, "raw", 0, &mut [],)).is_err());
    }
}
