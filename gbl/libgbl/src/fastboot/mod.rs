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

//! Fastboot backend for libgbl.

use crate::{partition::check_part_unique, GblOps};
use core::{
    cmp::min,
    fmt::Write,
    future::Future,
    marker::PhantomData,
    mem::take,
    str::{from_utf8, Split},
};
use fastboot::{
    next_arg, next_arg_u64, snprintf, CommandError, CommandResult, FastbootImplementation,
    FormattedBytes, InfoSender, OkaySender, RebootMode, UploadBuilder, Uploader, VarInfoSender,
};
use gbl_async::yield_now;
use safemath::SafeNum;
use spin::{Mutex, MutexGuard};

mod vars;
use vars::{fb_vars_get, fb_vars_get_all};

pub(crate) mod sparse;
use sparse::is_sparse_image;

/// `TasksExecutor` provides interfaces for spawning and scheduling async tasks.
pub trait TasksExecutor<'a> {
    /// Spawns a new task.
    fn spawn_task(&self, task: impl Future<Output = ()> + 'a) -> CommandResult<()>;
}

/// `GblFastboot` implements fastboot commands in the GBL context.
///
/// # Lifetimes
/// * `'a`: Lifetime of the `blk_io_executor` and `gbl_ops` objects borrowed.
/// * `'b`: [GblOps] partition lifetime.
/// * `'c`: Download buffer lifetime.
/// * `'d`: Represents the lifetime of any data borrowed by the spawned tasks running on
///     `blk_io_executor`. `'b` and `'c` will be constrained to outlive `d`.
pub struct GblFastboot<'a, 'b, 'c, 'd, T, G> {
    blk_io_executor: &'a T,
    pub(crate) gbl_ops: &'a mut G,
    download_buffers: &'c [Mutex<&'c mut [u8]>],
    current_download_buffer: Option<MutexGuard<'c, &'c mut [u8]>>,
    current_download_size: usize,
    enable_async_block_io: bool,
    default_block: Option<usize>,
    // Introduces marker type so that we can enforce constraint 'd <= min('b, 'c).
    // The constraint is expressed in the implementation block for the `FastbootImplementation`
    // trait.
    _gbl_ops_parts_lifetime: PhantomData<&'b G>,
    _blk_io_executor_context_lifetime: PhantomData<&'d T>,
}

impl<'a, 'b, 'c, T, G: GblOps<'b>> GblFastboot<'a, 'b, 'c, '_, T, G> {
    /// Creates a new instance.
    pub fn new(
        blk_io_executor: &'a T,
        gbl_ops: &'a mut G,
        download_buffers: &'c [Mutex<&'c mut [u8]>],
    ) -> Self {
        Self {
            blk_io_executor,
            gbl_ops,
            download_buffers,
            current_download_buffer: None,
            current_download_size: 0,
            enable_async_block_io: false,
            default_block: None,
            _gbl_ops_parts_lifetime: PhantomData,
            _blk_io_executor_context_lifetime: PhantomData,
        }
    }

    /// Returns the block IO task executor.
    pub fn blk_io_executor(&self) -> &'a T {
        self.blk_io_executor
    }

    /// Parses and checkds the partition argument and returns the partition name, block device
    /// index, start offset and size.
    pub(crate) fn parse_partition<'s>(
        &self,
        part: &'s str,
    ) -> CommandResult<(Option<&'s str>, usize, u64, u64)> {
        let devs = self.gbl_ops.partitions()?;
        let mut args = part.split('/');
        // Parses partition name.
        let part = next_arg(&mut args, Err("".into())).ok();
        // Parses block device ID.
        let blk_id = next_arg_u64(&mut args, Err("".into())).ok();
        let blk_id = blk_id.map(|v| usize::try_from(v)).transpose()?;
        let blk_id = blk_id.or(self.default_block);
        // Parses sub window offset.
        let window_offset = next_arg_u64(&mut args, Ok(0))?;
        // Parses sub window size.
        let window_size = next_arg_u64(&mut args, Err("".into())).ok();
        // Checks and resolves blk_id and partition size
        let (blk_id, partition) = match blk_id {
            None => check_part_unique(devs, part.ok_or("Must provide a partition")?)?,
            Some(v) => (v, devs.get(v).ok_or("Invalid block ID")?.find_partition(part)?),
        };
        let part_sz = SafeNum::from(partition.size()?);
        let window_size = window_size.unwrap_or((part_sz - window_offset).try_into()?);
        u64::try_from(part_sz - window_size - window_offset)?;
        Ok((part, blk_id, window_offset, window_size))
    }

    /// Checks and waits until a download buffer is allocated.
    async fn ensure_download_buffer(&mut self) -> &mut [u8] {
        while self.current_download_buffer.is_none() {
            self.current_download_buffer = self.download_buffers.iter().find_map(|v| v.try_lock());
            match self.current_download_buffer.is_some() {
                true => break,
                _ => yield_now().await,
            }
        }
        self.current_download_buffer.as_mut().unwrap()
    }

    /// Waits for all block devices to be ready.
    async fn sync_all_blocks(&self) -> CommandResult<()> {
        for ele in self.gbl_ops.partitions()? {
            let _ = ele.wait_partition_io(None).await;
        }
        Ok(())
    }

    /// Implementation for "fastboot oem gbl-sync-blocks".
    async fn oem_sync_blocks<'s>(
        &self,
        mut responder: impl InfoSender,
        res: &'s mut [u8],
    ) -> CommandResult<&'s [u8]> {
        self.sync_all_blocks().await?;
        // Checks error.
        let mut has_error = false;
        for (i, ele) in self.gbl_ops.partitions()?.iter().enumerate() {
            match ele.partition_io(None)?.last_err() {
                Ok(_) => {}
                Err(e) => {
                    has_error = true;
                    responder.send_info(snprintf!(res, "Block #{} error: {:?}.", i, e)).await?;
                }
            }
        }
        match has_error {
            true => Err("Errors during async block IO. Please reset device.".into()),
            _ => Ok(b""),
        }
    }

    /// Syncs all storage devices and reboots.
    async fn sync_block_and_reboot(
        &mut self,
        mode: RebootMode,
        mut resp: impl InfoSender + OkaySender,
    ) -> CommandResult<()> {
        resp.send_info("Syncing storage...").await?;
        self.sync_all_blocks().await?;
        match mode {
            RebootMode::Normal => {
                resp.send_info("Rebooting...").await?;
                resp.send_okay("").await?;
                self.gbl_ops.reboot();
            }
            _ => return Err("Unsupported".into()),
        }
        Ok(())
    }
}

impl<'b: 'd, 'c: 'd, 'd, T: TasksExecutor<'d>, G: GblOps<'b>> FastbootImplementation
    for GblFastboot<'_, 'b, 'c, 'd, T, G>
{
    async fn get_var(
        &mut self,
        var: &str,
        args: Split<'_, char>,
        out: &mut [u8],
        _: impl InfoSender,
    ) -> CommandResult<usize> {
        Ok(fb_vars_get(self, var, args, out).await?.ok_or("No such variable")?)
    }

    async fn get_var_all(&mut self, mut resp: impl VarInfoSender) -> CommandResult<()> {
        fb_vars_get_all(self, &mut resp).await
    }

    async fn get_download_buffer(&mut self) -> &mut [u8] {
        self.ensure_download_buffer().await
    }

    async fn download_complete(
        &mut self,
        download_size: usize,
        _: impl InfoSender,
    ) -> CommandResult<()> {
        self.current_download_size = download_size;
        Ok(())
    }

    async fn flash(&mut self, part: &str, mut responder: impl InfoSender) -> CommandResult<()> {
        let (part, blk_idx, start, sz) = self.parse_partition(part)?;
        let partitions = self.gbl_ops.partitions()?;
        let mut part_io = partitions[blk_idx].wait_partition_io(part).await?.sub(start, sz)?;
        part_io.last_err()?;
        let mut download_buffer = self.current_download_buffer.take().ok_or("No download")?;
        let data_size = take(&mut self.current_download_size);
        let write_task = async move {
            let _ = match is_sparse_image(&download_buffer) {
                Ok(_) => part_io.write_sparse(0, &mut download_buffer).await,
                _ => part_io.write(0, &mut download_buffer[..data_size]).await,
            };
        };
        match self.enable_async_block_io {
            true => {
                self.blk_io_executor.spawn_task(write_task)?;
                let info = "An IO task is launched. To sync manually, run \"oem gbl-sync-blocks\".";
                responder.send_info(info).await?
            }
            _ => write_task.await,
        };
        // Checks if block is ready already and returns errors. This can be the case when the
        // operation is synchronous or runs into early errors.
        match partitions[blk_idx].partition_io(part) {
            Ok(v) => Ok(v.last_err()?),
            _ => Ok(()),
        }
    }

    async fn upload(&mut self, _: impl UploadBuilder) -> CommandResult<()> {
        Err("Unimplemented".into())
    }

    async fn fetch(
        &mut self,
        part: &str,
        offset: u64,
        size: u64,
        mut responder: impl UploadBuilder + InfoSender,
    ) -> CommandResult<()> {
        let (part, blk_idx, start, sz) = self.parse_partition(part)?;
        let partitions = self.gbl_ops.partitions()?;
        let mut part_io = partitions[blk_idx].wait_partition_io(part).await?.sub(start, sz)?;
        part_io.last_err()?;
        let buffer = self.ensure_download_buffer().await;
        let end = u64::try_from(SafeNum::from(offset) + size)?;
        let mut curr = offset;
        responder
            .send_formatted_info(|v| write!(v, "Uploading {} bytes...", size).unwrap())
            .await?;
        let mut uploader = responder.initiate_upload(size).await?;
        while curr < end {
            let to_send = min(usize::try_from(end - curr)?, buffer.len());
            part_io.read(curr, &mut buffer[..to_send]).await?;
            uploader.upload(&mut buffer[..to_send]).await?;
            curr += u64::try_from(to_send)?;
        }
        Ok(())
    }

    async fn reboot(
        &mut self,
        mode: RebootMode,
        resp: impl InfoSender + OkaySender,
    ) -> CommandError {
        match self.sync_block_and_reboot(mode, resp).await {
            Err(e) => e,
            _ => "Unknown".into(),
        }
    }

    async fn oem<'s>(
        &mut self,
        cmd: &str,
        responder: impl InfoSender,
        res: &'s mut [u8],
    ) -> CommandResult<&'s [u8]> {
        match cmd {
            "gbl-sync-blocks" => self.oem_sync_blocks(responder, res).await,
            "gbl-enable-async-block-io" => {
                self.enable_async_block_io = true;
                Ok(b"")
            }
            "gbl-disable-async-block-io" => {
                self.enable_async_block_io = false;
                Ok(b"")
            }
            "gbl-unset-default-block" => {
                self.default_block = None;
                Ok(b"")
            }
            _ if cmd.starts_with("gbl-set-default-block ") => {
                let mut args = cmd.split(' ');
                let _ = args.next();
                let id = next_arg_u64(&mut args, Err("Missing block device ID".into()))?;
                self.default_block = Some(id.try_into()?);
                Ok(b"")
            }
            _ => Err("Unknown oem command".into()),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        ops::test::{FakeGblOps, FakeGblOpsStorage},
        partition::PartitionBlockDevice,
    };
    use core::{cmp::max, pin::pin};
    use fastboot::{test_utils::TestUploadBuilder, MAX_RESPONSE_SIZE};
    use gbl_async::{block_on, poll};
    use gbl_cyclic_executor::CyclicExecutor;
    use gbl_storage_testlib::{BackingStore, TestBlockDeviceBuilder, TestBlockIo};
    use spin::Mutex;

    /// A test implementation of [InfoSender] and [OkaySender].
    #[derive(Default)]
    struct TestResponder {
        okay_sent: Mutex<bool>,
        info_messages: Mutex<Vec<String>>,
    }

    impl InfoSender for &TestResponder {
        async fn send_formatted_info<F: FnOnce(&mut dyn Write)>(
            &mut self,
            cb: F,
        ) -> CommandResult<()> {
            let mut msg: String = "".into();
            cb(&mut msg);
            self.info_messages.try_lock().unwrap().push(msg);
            Ok(())
        }
    }

    impl OkaySender for &TestResponder {
        /// Sends a Fastboot "INFO<`msg`>" packet.
        async fn send_formatted_okay<F: FnOnce(&mut dyn Write)>(self, _: F) -> CommandResult<()> {
            *self.okay_sent.try_lock().unwrap() = true;
            Ok(())
        }
    }

    type TestGblFastboot<'a, 'b> =
        GblFastboot<'a, 'b, 'b, 'b, TestGblFbExecutor<'b>, FakeGblOps<'b>>;

    /// Helper to test fastboot variable value.
    fn check_var(gbl_fb: &mut TestGblFastboot<'_, '_>, var: &str, args: &str, expected: &str) {
        let resp: TestResponder = Default::default();
        let mut out = vec![0u8; MAX_RESPONSE_SIZE];
        let val =
            block_on(gbl_fb.get_var_as_str(var, args.split(':'), &resp, &mut out[..])).unwrap();
        assert_eq!(val, expected, "var {}:{} = {} != {}", var, args, val, expected,);
    }

    /// A helper to set the download content.
    fn set_download(gbl_fb: &mut TestGblFastboot, data: &[u8]) {
        block_on(gbl_fb.ensure_download_buffer());
        gbl_fb.current_download_buffer.as_mut().unwrap()[..data.len()].clone_from_slice(data);
        gbl_fb.current_download_size = data.len();
    }

    /// `TestGblFbExecutor` wraps a `CyclicExecutor` and implements `TasksExecutor` trait.
    #[derive(Default)]
    struct TestGblFbExecutor<'a>(Mutex<CyclicExecutor<'a>>);

    impl<'a> TasksExecutor<'a> for TestGblFbExecutor<'a> {
        fn spawn_task(&self, task: impl Future<Output = ()> + 'a) -> CommandResult<()> {
            Ok(self.0.try_lock().unwrap().spawn_task(task))
        }
    }

    /// A Helper type for preparing test data such as block devices AND download buffers for
    /// Fastboot tests.
    struct TestData {
        /// Fake backing storage.
        storage: FakeGblOpsStorage,
        /// Download buffers.
        download: Vec<Vec<u8>>,
    }

    impl TestData {
        /// Creates a new instance.
        ///
        /// Initializes `dl_n` number of download buffers with size `dl_sz`.
        fn new(dl_sz: usize, dl_n: usize) -> Self {
            Self { storage: Default::default(), download: vec![vec![0u8; dl_sz]; dl_n] }
        }

        /// Creates an array of `PartitionBlockDevice` and fastboot download buffers.
        fn get(&mut self) -> (Vec<PartitionBlockDevice<&mut TestBlockIo>>, Vec<Mutex<&mut [u8]>>) {
            (
                self.storage.as_partition_block_devices(),
                self.download.iter_mut().map(|v| (&mut v[..]).into()).collect::<Vec<_>>(),
            )
        }
    }

    #[test]
    fn test_get_var_partition_info() {
        let mut test_data = TestData::new(128 * 1024, 1);
        test_data.storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        test_data.storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_2.bin"));
        test_data.storage.add_raw_device("raw_0", [0xaau8; 4 * 1024]);
        test_data.storage.add_raw_device("raw_1", [0x55u8; 8 * 1024]);
        let (partitions, dl_buffers) = test_data.get();
        let mut gbl_ops = FakeGblOps::new(&partitions);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &mut gbl_ops, &dl_buffers);

        // Check different semantics
        check_var(&mut gbl_fb, "partition-size", "boot_a", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a/", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a//", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a///", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a/0", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a/0/", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a//0", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a/0/0", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a//0x1000", "0x1000");

        check_var(&mut gbl_fb, "partition-size", "boot_b/0", "0x3000");
        check_var(&mut gbl_fb, "partition-size", "vendor_boot_a/1", "0x1000");
        check_var(&mut gbl_fb, "partition-size", "vendor_boot_b/1", "0x1800");
        check_var(&mut gbl_fb, "partition-size", "boot_a//0x1000", "0x1000");
        check_var(&mut gbl_fb, "partition-size", "raw_0", "0x1000");
        check_var(&mut gbl_fb, "partition-size", "raw_1", "0x2000");

        let resp: TestResponder = Default::default();
        let mut out = vec![0u8; MAX_RESPONSE_SIZE];
        assert!(block_on(gbl_fb.get_var_as_str(
            "partition",
            "non-existent".split(':'),
            &resp,
            &mut out[..],
        ))
        .is_err());
    }

    /// `TestVarSender` implements `TestVarSender`. It stores outputs in a vector of string.
    struct TestVarSender(Vec<String>);

    impl VarInfoSender for &mut TestVarSender {
        async fn send_var_info(
            &mut self,
            name: &str,
            args: &[&str],
            val: &str,
        ) -> CommandResult<()> {
            self.0.push(format!("{}:{}: {}", name, args.join(":"), val));
            Ok(())
        }
    }

    #[test]
    fn test_get_var_all() {
        let mut test_data = TestData::new(128 * 1024, 1);
        test_data.storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        test_data.storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_2.bin"));
        test_data.storage.add_raw_device("raw_0", [0xaau8; 4 * 1024]);
        test_data.storage.add_raw_device("raw_1", [0x55u8; 8 * 1024]);
        let (partitions, dl_buffers) = test_data.get();
        let mut gbl_ops = FakeGblOps::new(&partitions);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &mut gbl_ops, &dl_buffers);

        let mut logger = TestVarSender(vec![]);
        block_on(gbl_fb.get_var_all(&mut logger)).unwrap();
        assert_eq!(
            logger.0,
            [
                "version-bootloader:: 1.0",
                "max-fetch-size:: 0xffffffffffffffff",
                "block-device:0:total-blocks: 0x80",
                "block-device:0:block-size: 0x200",
                "block-device:0:status: idle",
                "block-device:1:total-blocks: 0x100",
                "block-device:1:block-size: 0x200",
                "block-device:1:status: idle",
                "block-device:2:total-blocks: 0x8",
                "block-device:2:block-size: 0x200",
                "block-device:2:status: idle",
                "block-device:3:total-blocks: 0x10",
                "block-device:3:block-size: 0x200",
                "block-device:3:status: idle",
                "gbl-default-block:: None",
                "partition-size:boot_a/0: 0x2000",
                "partition-type:boot_a/0: raw",
                "partition-size:boot_b/0: 0x3000",
                "partition-type:boot_b/0: raw",
                "partition-size:vendor_boot_a/1: 0x1000",
                "partition-type:vendor_boot_a/1: raw",
                "partition-size:vendor_boot_b/1: 0x1800",
                "partition-type:vendor_boot_b/1: raw",
                "partition-size:raw_0/2: 0x1000",
                "partition-type:raw_0/2: raw",
                "partition-size:raw_1/3: 0x2000",
                "partition-type:raw_1/3: raw"
            ]
        );
    }

    /// A helper for fetching partition from a `GblFastboot`
    fn fetch<EOff: core::fmt::Debug, ESz: core::fmt::Debug>(
        fb: &mut TestGblFastboot,
        part: String,
        off: impl TryInto<u64, Error = EOff>,
        size: impl TryInto<u64, Error = ESz>,
    ) -> CommandResult<Vec<u8>> {
        let off = off.try_into().unwrap();
        let size = size.try_into().unwrap();
        // Forces upload in two batches for testing.
        let download_buffer = vec![0u8; max(1, usize::try_from(size).unwrap() / 2usize)];
        let mut upload_out = vec![0u8; usize::try_from(size).unwrap()];
        let test_uploader = TestUploadBuilder(&mut upload_out[..]);
        block_on(fb.fetch(part.as_str(), off, size, test_uploader))?;
        Ok(upload_out)
    }

    #[test]
    fn test_fetch_invalid_partition_arg() {
        let mut test_data = TestData::new(128 * 1024, 1);
        test_data.storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        test_data.storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_2.bin"));
        test_data.storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_2.bin"));
        let (partitions, dl_buffers) = test_data.get();
        let mut gbl_ops = FakeGblOps::new(&partitions);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &mut gbl_ops, &dl_buffers);

        // Missing mandatory block device ID for raw block partition.
        assert!(fetch(&mut gbl_fb, "//0/0".into(), 0, 0).is_err());

        // GPT partition does not exist.
        assert!(fetch(&mut gbl_fb, "non///".into(), 0, 0).is_err());

        // GPT Partition is not unique.
        assert!(fetch(&mut gbl_fb, "vendor_boot_a///".into(), 0, 0).is_err());

        // Offset overflows.
        assert!(fetch(&mut gbl_fb, "boot_a//0x2001/".into(), 0, 1).is_err());
        assert!(fetch(&mut gbl_fb, "boot_a".into(), 0x2000, 1).is_err());

        // Size overflows.
        assert!(fetch(&mut gbl_fb, "boot_a///0x2001".into(), 0, 0).is_err());
        assert!(fetch(&mut gbl_fb, "boot_a".into(), 0, 0x2001).is_err());
    }

    /// A helper for testing raw block upload. It verifies that data read from block device
    /// `blk_id` in range [`off`, `off`+`size`) is the same as `disk[off..][..size]`
    fn check_blk_upload(fb: &mut TestGblFastboot, blk_id: u64, off: u64, size: u64, disk: &[u8]) {
        let expected = disk[off.try_into().unwrap()..][..size.try_into().unwrap()].to_vec();
        // offset/size as part of the partition string.
        let part = format!("/{:#x}/{:#x}/{:#x}", blk_id, off, size);
        assert_eq!(fetch(fb, part, 0, size).unwrap(), expected);
        // offset/size as separate fetch arguments.
        let part = format!("/{:#x}", blk_id);
        assert_eq!(fetch(fb, part, off, size).unwrap(), expected);
    }

    #[test]
    fn test_fetch_raw_block() {
        let mut test_data = TestData::new(128 * 1024, 1);
        let disk_0 = include_bytes!("../../../libstorage/test/gpt_test_1.bin");
        let disk_1 = include_bytes!("../../../libstorage/test/gpt_test_2.bin");
        test_data.storage.add_gpt_device(disk_0);
        test_data.storage.add_gpt_device(disk_1);
        let (parts, dl_buffers) = test_data.get();
        let mut gbl_ops = FakeGblOps::new(&parts);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &mut gbl_ops, &dl_buffers);

        let off = 512;
        let size = 512;
        check_blk_upload(&mut gbl_fb, 0, off, size, disk_0);
        check_blk_upload(&mut gbl_fb, 1, off, size, disk_1);
    }

    /// A helper for testing uploading GPT partition. It verifies that data read from GPT partition
    /// `part` at disk `blk_id` in range [`off`, `off`+`size`) is the same as
    /// `partition_data[off..][..size]`.
    fn check_part_upload(
        fb: &mut TestGblFastboot,
        part: &str,
        off: u64,
        size: u64,
        blk_id: Option<u64>,
        partition_data: &[u8],
    ) {
        let expected =
            partition_data[off.try_into().unwrap()..][..size.try_into().unwrap()].to_vec();
        let blk_id = blk_id.map_or("".to_string(), |v| format!("{:#x}", v));
        // offset/size as part of the partition string.
        let gpt_part = format!("{}/{}/{:#x}/{:#x}", part, blk_id, off, size);
        assert_eq!(fetch(fb, gpt_part, 0, size).unwrap(), expected);
        // offset/size as separate fetch arguments.
        let gpt_part = format!("{}/{}", part, blk_id);
        assert_eq!(fetch(fb, gpt_part, off, size).unwrap(), expected);
    }

    #[test]
    fn test_fetch_partition() {
        let mut test_data = TestData::new(128 * 1024, 1);
        test_data.storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        test_data.storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_2.bin"));
        test_data.storage.add_raw_device("raw_0", [0xaau8; 4 * 1024]);
        test_data.storage.add_raw_device("raw_1", [0x55u8; 8 * 1024]);
        let (partitions, dl_buffers) = test_data.get();
        let mut gbl_ops = FakeGblOps::new(&partitions);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &mut gbl_ops, &dl_buffers);

        let expect_boot_a = include_bytes!("../../../libstorage/test/boot_a.bin");
        let expect_boot_b = include_bytes!("../../../libstorage/test/boot_b.bin");
        let expect_vendor_boot_a = include_bytes!("../../../libstorage/test/vendor_boot_a.bin");
        let expect_vendor_boot_b = include_bytes!("../../../libstorage/test/vendor_boot_b.bin");

        let size = 512;
        let off = 512;

        check_part_upload(&mut gbl_fb, "boot_a", off, size, Some(0), expect_boot_a);
        check_part_upload(&mut gbl_fb, "boot_b", off, size, Some(0), expect_boot_b);
        check_part_upload(&mut gbl_fb, "vendor_boot_a", off, size, Some(1), expect_vendor_boot_a);
        check_part_upload(&mut gbl_fb, "vendor_boot_b", off, size, Some(1), expect_vendor_boot_b);
        check_part_upload(&mut gbl_fb, "raw_0", off, size, Some(2), &[0xaau8; 4 * 1024]);
        check_part_upload(&mut gbl_fb, "raw_1", off, size, Some(3), &[0x55u8; 8 * 1024]);

        // No block device id
        check_part_upload(&mut gbl_fb, "boot_a", off, size, None, expect_boot_a);
        check_part_upload(&mut gbl_fb, "boot_b", off, size, None, expect_boot_b);
        check_part_upload(&mut gbl_fb, "vendor_boot_a", off, size, None, expect_vendor_boot_a);
        check_part_upload(&mut gbl_fb, "vendor_boot_b", off, size, None, expect_vendor_boot_b);
        check_part_upload(&mut gbl_fb, "raw_0", off, size, None, &[0xaau8; 4 * 1024]);
        check_part_upload(&mut gbl_fb, "raw_1", off, size, None, &[0x55u8; 8 * 1024]);
    }

    /// A helper function to get a bit-flipped copy of the input data.
    fn flipped_bits(data: &[u8]) -> Vec<u8> {
        data.iter().map(|v| !(*v)).collect::<Vec<_>>()
    }

    /// A helper function to flash data to a partition
    fn flash_part(fb: &mut TestGblFastboot, part: &str, data: &[u8]) {
        // Prepare a download buffer.
        let dl_size = data.len();
        let download = data.to_vec();
        let resp: TestResponder = Default::default();
        set_download(fb, &download[..]);
        block_on(fb.flash(part, &resp)).unwrap();
        assert_eq!(fetch(fb, part.into(), 0, dl_size).unwrap(), download);
    }

    /// A helper for testing partition flashing.
    fn check_flash_part(fb: &mut TestGblFastboot, part: &str, expected: &[u8]) {
        flash_part(fb, part, expected);
        // Also flashes bit-wise reversed version in case the initial content is the same.
        flash_part(fb, part, &flipped_bits(expected));
    }

    #[test]
    fn test_flash_partition() {
        let disk_0 = include_bytes!("../../../libstorage/test/gpt_test_1.bin");
        let disk_1 = include_bytes!("../../../libstorage/test/gpt_test_2.bin");
        let mut test_data = TestData::new(128 * 1024, 1);
        test_data.storage.add_gpt_device(disk_0);
        test_data.storage.add_gpt_device(disk_1);
        test_data.storage.add_raw_device("raw_0", [0xaau8; 4 * 1024]);
        test_data.storage.add_raw_device("raw_1", [0x55u8; 8 * 1024]);
        let (partitions, dl_buffers) = test_data.get();
        let mut gbl_ops = FakeGblOps::new(&partitions);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &mut gbl_ops, &dl_buffers);

        let expect_boot_a = include_bytes!("../../../libstorage/test/boot_a.bin");
        let expect_boot_b = include_bytes!("../../../libstorage/test/boot_b.bin");
        check_flash_part(&mut gbl_fb, "boot_a", expect_boot_a);
        check_flash_part(&mut gbl_fb, "boot_b", expect_boot_b);
        check_flash_part(&mut gbl_fb, "raw_0", &[0xaau8; 4 * 1024]);
        check_flash_part(&mut gbl_fb, "raw_1", &[0x55u8; 8 * 1024]);
        check_flash_part(&mut gbl_fb, "/0", disk_0);
        check_flash_part(&mut gbl_fb, "/1", disk_1);

        // Partital flash
        let off = 0x200;
        let size = 1024;
        check_flash_part(&mut gbl_fb, "boot_a//200", &expect_boot_a[off..size]);
        check_flash_part(&mut gbl_fb, "boot_b//200", &expect_boot_b[off..size]);
        check_flash_part(&mut gbl_fb, "/0/200", &disk_0[off..size]);
        check_flash_part(&mut gbl_fb, "/1/200", &disk_1[off..size]);
    }

    #[test]
    fn test_flash_partition_sparse() {
        let raw = include_bytes!("../../testdata/sparse_test_raw.bin");
        let sparse = include_bytes!("../../testdata/sparse_test.bin");
        let mut test_data = TestData::new(128 * 1024, 1);
        test_data.storage.add_raw_device("raw", vec![0u8; raw.len()]);
        let (partitions, dl_buffers) = test_data.get();
        let mut gbl_ops = FakeGblOps::new(&partitions);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &mut gbl_ops, &dl_buffers);

        let download = sparse.to_vec();
        let resp: TestResponder = Default::default();
        set_download(&mut gbl_fb, &download[..]);
        block_on(gbl_fb.flash("/0", &resp)).unwrap();
        assert_eq!(fetch(&mut gbl_fb, "/0".into(), 0, raw.len()).unwrap(), raw);
    }

    /// A helper to invoke OEM commands.
    ///
    /// Returns the result and INFO strings.
    async fn oem(
        fb: &mut TestGblFastboot<'_, '_>,
        oem_cmd: &str,
        resp: impl InfoSender,
    ) -> CommandResult<String> {
        let mut res = [0u8; MAX_RESPONSE_SIZE];
        fb.oem(oem_cmd, resp, &mut res[..]).await?;
        Ok(from_utf8(&mut res[..]).unwrap().into())
    }

    #[test]
    fn test_async_flash() {
        // Creates two block devices for writing raw and sparse image.
        let sparse_raw = include_bytes!("../../testdata/sparse_test_raw.bin");
        let sparse = include_bytes!("../../testdata/sparse_test.bin");
        let dev_sparse = TestBlockDeviceBuilder::new()
            .add_partition("sparse", BackingStore::Size(sparse_raw.len()))
            .build();
        let mut test_data = TestData::new(128 * 1024, 2);
        test_data.storage.add_gpt_device(dev_sparse.io.storage);
        test_data.storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        let (partitions, dl_buffers) = test_data.get();
        let mut gbl_ops = FakeGblOps::new(&partitions);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &mut gbl_ops, &dl_buffers);
        let resp: TestResponder = Default::default();

        // "oem gbl-sync-blocks" should return immediately when there is no pending IOs.
        assert!(poll(&mut pin!(oem(&mut gbl_fb, "gbl-sync-blocks", &resp))).unwrap().is_ok());
        // Enable async IO.
        assert!(poll(&mut pin!(oem(&mut gbl_fb, "gbl-enable-async-block-io", &resp)))
            .unwrap()
            .is_ok());

        // Flashes "boot_a".
        let expect_boot_a = flipped_bits(include_bytes!("../../../libstorage/test/boot_a.bin"));
        set_download(&mut gbl_fb, expect_boot_a.as_slice());
        block_on(gbl_fb.flash("boot_a", &resp)).unwrap();

        // Flashes the "sparse" partition on the different block device.
        set_download(&mut gbl_fb, sparse);
        block_on(gbl_fb.flash("sparse", &resp)).unwrap();

        // The two blocks should be in the pending state.
        check_var(&mut gbl_fb, "block-device", "0:status", "IO pending");
        check_var(&mut gbl_fb, "block-device", "1:status", "IO pending");

        // There should be two disk IO tasks spawned.
        assert_eq!(blk_io_executor.0.try_lock().unwrap().num_tasks(), 2);
        {
            // "oem gbl-sync-blocks" should block.
            let oem_sync_blk_fut = &mut pin!(oem(&mut gbl_fb, "gbl-sync-blocks", &resp));
            assert!(poll(oem_sync_blk_fut).is_none());
            // Schedules the disk IO tasks to completion.
            blk_io_executor.0.try_lock().unwrap().run();
            // "oem gbl-sync-blocks" should now be able to finish.
            assert!(poll(oem_sync_blk_fut).unwrap().is_ok());
        }

        // The two blocks should be in the idle state.
        check_var(&mut gbl_fb, "block-device", "0:status", "idle");
        check_var(&mut gbl_fb, "block-device", "1:status", "idle");

        // Verifies flashed image.
        assert_eq!(
            fetch(&mut gbl_fb, "boot_a".into(), 0, expect_boot_a.len()).unwrap(),
            expect_boot_a
        );
        assert_eq!(fetch(&mut gbl_fb, "sparse".into(), 0, sparse_raw.len()).unwrap(), sparse_raw);
    }

    #[test]
    fn test_async_flash_block_on_busy_blk() {
        let mut test_data = TestData::new(128 * 1024, 2);
        test_data.storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        test_data.storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_2.bin"));
        let (partitions, dl_buffers) = test_data.get();
        let mut gbl_ops = FakeGblOps::new(&partitions);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &mut gbl_ops, &dl_buffers);
        let resp: TestResponder = Default::default();

        // Enable async IO.
        assert!(poll(&mut pin!(oem(&mut gbl_fb, "gbl-enable-async-block-io", &resp)))
            .unwrap()
            .is_ok());

        // Flashes boot_a partition.
        let expect_boot_a = flipped_bits(include_bytes!("../../../libstorage/test/boot_a.bin"));
        set_download(&mut gbl_fb, expect_boot_a.as_slice());
        block_on(gbl_fb.flash("boot_a", &resp)).unwrap();

        // Flashes boot_b partition.
        let expect_boot_b = flipped_bits(include_bytes!("../../../libstorage/test/boot_b.bin"));
        set_download(&mut gbl_fb, expect_boot_b.as_slice());
        {
            let flash_boot_b_fut = &mut pin!(gbl_fb.flash("boot_b", &resp));
            // Previous IO has not completed. Block is busy.
            assert!(poll(flash_boot_b_fut).is_none());
            // There should only be the previous disk IO task for "boot_a".
            assert_eq!(blk_io_executor.0.try_lock().unwrap().num_tasks(), 1);
            // Schedule the disk IO task for "flash boot_a" to completion.
            blk_io_executor.0.try_lock().unwrap().run();
            // The blocked "flash boot_b" should now be able to finish.
            assert!(poll(flash_boot_b_fut).is_some());
            // There should be a disk IO task spawned for "flash boot_b".
            assert_eq!(blk_io_executor.0.try_lock().unwrap().num_tasks(), 1);
            // Schedule the disk IO tasks for "flash boot_b" to completion.
            blk_io_executor.0.try_lock().unwrap().run();
        }

        // Verifies flashed image.
        assert_eq!(
            fetch(&mut gbl_fb, "boot_a".into(), 0, expect_boot_a.len()).unwrap(),
            expect_boot_a
        );
        assert_eq!(
            fetch(&mut gbl_fb, "boot_b".into(), 0, expect_boot_b.len()).unwrap(),
            expect_boot_b
        );
    }

    #[test]
    fn test_async_flash_error() {
        let mut test_data = TestData::new(128 * 1024, 2);
        test_data.storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        let (partitions, dl_buffers) = test_data.get();
        let mut gbl_ops = FakeGblOps::new(&partitions);
        // Injects an error.
        partitions[0].partition_io(None).unwrap().dev().io().errors =
            [liberror::Error::Other(None)].into();
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &mut gbl_ops, &dl_buffers);
        let resp: TestResponder = Default::default();

        // Enable async IO.
        assert!(poll(&mut pin!(oem(&mut gbl_fb, "gbl-enable-async-block-io", &resp)))
            .unwrap()
            .is_ok());
        // Flashes boot_a partition.
        let expect_boot_a = flipped_bits(include_bytes!("../../../libstorage/test/boot_a.bin"));
        set_download(&mut gbl_fb, expect_boot_a.as_slice());
        block_on(gbl_fb.flash("boot_a", &resp)).unwrap();
        // Schedules the disk IO tasks to completion.
        blk_io_executor.0.try_lock().unwrap().run();
        // New flash to "boot_a" should fail due to previous error
        set_download(&mut gbl_fb, expect_boot_a.as_slice());
        assert!(block_on(gbl_fb.flash("boot_a", &resp)).is_err());
        // "oem gbl-sync-blocks" should fail.
        assert!(block_on(oem(&mut gbl_fb, "gbl-sync-blocks", &resp)).is_err());
    }

    #[test]
    fn test_default_block() {
        let mut test_data = TestData::new(128 * 1024, 1);
        test_data.storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        let disk_dup = include_bytes!("../../../libstorage/test/gpt_test_2.bin");
        test_data.storage.add_gpt_device(disk_dup);
        test_data.storage.add_gpt_device(disk_dup);
        let raw_a = [0xaau8; 4 * 1024];
        let raw_b = [0x55u8; 8 * 1024];
        test_data.storage.add_raw_device("raw", raw_a);
        test_data.storage.add_raw_device("raw", raw_b);
        let (partitions, dl_buffers) = test_data.get();
        let mut gbl_ops = FakeGblOps::new(&partitions);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &mut gbl_ops, &dl_buffers);
        let resp: TestResponder = Default::default();

        let boot_a = include_bytes!("../../../libstorage/test/boot_a.bin");
        // Flips the bits on partition "vendor_boot_a" on block device #2 to make it different from
        // block #1.
        let vendor_boot_a =
            flipped_bits(include_bytes!("../../../libstorage/test/vendor_boot_a.bin"));
        flash_part(&mut gbl_fb, "vendor_boot_a/2", &vendor_boot_a);

        let size = 512;
        let off = 512;

        check_var(&mut gbl_fb, "gbl-default-block", "", "None");
        // Sets default block to #2
        block_on(oem(&mut gbl_fb, "gbl-set-default-block 2", &resp)).unwrap();
        check_var(&mut gbl_fb, "gbl-default-block", "", "0x2");
        // The following fetch should succeed and fetch from "vendor_boot_a" on block 2.
        check_part_upload(&mut gbl_fb, "vendor_boot_a", off, size, None, &vendor_boot_a);

        // Sets default block to #4 (raw_b)
        block_on(oem(&mut gbl_fb, "gbl-set-default-block 4", &resp)).unwrap();
        check_var(&mut gbl_fb, "gbl-default-block", "", "0x4");
        // The following fetch should succeed and fetch from "raw" on block 4.
        check_part_upload(&mut gbl_fb, "raw", off, size, None, &raw_b);

        // Fetches with explicit storage ID shouldn't be affected.
        check_part_upload(&mut gbl_fb, "boot_a", off, size, Some(0), boot_a);
        check_part_upload(&mut gbl_fb, "raw", off, size, Some(3), &raw_a);
        check_blk_upload(&mut gbl_fb, 1, off, size, disk_dup);

        // Fetching without storage ID should use default ID and thus the following should fail.
        assert!(fetch(&mut gbl_fb, "boot_a".into(), 0, boot_a.len()).is_err());

        // Sets default block to #1 (unmodified `disk_dup`)
        block_on(oem(&mut gbl_fb, "gbl-set-default-block 1", &resp)).unwrap();
        check_var(&mut gbl_fb, "gbl-default-block", "", "0x1");
        // Fetches whole raw block but without block ID should use the default block.
        check_part_upload(&mut gbl_fb, "", off, size, None, disk_dup);

        // Unset default block
        block_on(oem(&mut gbl_fb, "gbl-unset-default-block", &resp)).unwrap();
        check_var(&mut gbl_fb, "gbl-default-block", "", "None");
        // Fetching non-unique partitions should now fail.
        assert!(fetch(&mut gbl_fb, "raw".into(), 0, raw_a.len()).is_err());
        assert!(fetch(&mut gbl_fb, "vendor_boot_a".into(), 0, vendor_boot_a.len()).is_err());
        assert!(fetch(&mut gbl_fb, "/".into(), 0, 512).is_err());
    }

    #[test]
    fn test_set_default_block_invalid_arg() {
        let mut test_data = TestData::new(128 * 1024, 2);
        let (partitions, dl_buffers) = test_data.get();
        let mut gbl_ops = FakeGblOps::new(&partitions);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &mut gbl_ops, &dl_buffers);
        let resp: TestResponder = Default::default();
        // Missing block device ID.
        assert!(block_on(oem(&mut gbl_fb, "gbl-set-default-block ", &resp)).is_err());
        // Invalid block device ID.
        assert!(block_on(oem(&mut gbl_fb, "gbl-set-default-block zzz", &resp)).is_err());
    }

    #[test]
    fn test_reboot_sync_all_blocks() {
        let mut test_data = TestData::new(128 * 1024, 2);
        test_data.storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        let (partitions, dl_buffers) = test_data.get();
        let mut gbl_ops = FakeGblOps::new(&partitions);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &mut gbl_ops, &dl_buffers);
        let resp: TestResponder = Default::default();

        block_on(oem(&mut gbl_fb, "gbl-enable-async-block-io", &resp)).unwrap();

        // Flashes "boot_a".
        let expect_boot_a = flipped_bits(include_bytes!("../../../libstorage/test/boot_a.bin"));
        set_download(&mut gbl_fb, expect_boot_a.as_slice());
        block_on(gbl_fb.flash("boot_a", &resp)).unwrap();
        // Checks initial state, okay_sent=false.
        assert!(!(*resp.okay_sent.try_lock().unwrap()));
        // Performs a reboot.
        let mut reboot_fut = pin!(gbl_fb.reboot(RebootMode::Normal, &resp));
        // There is a pending flash task. Reboot should wait.
        assert!(poll(&mut reboot_fut).is_none());
        assert!(!(*resp.okay_sent.try_lock().unwrap()));
        assert_eq!(resp.info_messages.try_lock().unwrap()[1], "Syncing storage...");
        // Schedules the disk IO tasks to completion.
        blk_io_executor.0.try_lock().unwrap().run();
        // The reboot can now complete.
        assert!(poll(&mut reboot_fut).is_some());
        assert!((*resp.okay_sent.try_lock().unwrap()));
        assert_eq!(resp.info_messages.try_lock().unwrap()[2], "Rebooting...");
    }
}
