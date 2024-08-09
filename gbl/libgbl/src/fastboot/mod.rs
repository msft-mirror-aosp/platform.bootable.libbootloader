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

use core::{
    cmp::min,
    fmt::Write,
    future::Future,
    mem::take,
    str::{from_utf8, Split},
};
use fastboot::{
    next_arg, next_arg_u64, snprintf, CommandError, FastbootImplementation, FastbootUtils,
    FormattedBytes, UploadBuilder, Uploader, VarSender,
};
use gbl_async::yield_now;
use gbl_storage::{AsyncBlockDevice, BlockIoAsync, GPT_NAME_LEN_U16};
use safemath::SafeNum;

mod vars;
use vars::{fb_vars_get, fb_vars_get_all};

mod sparse;
use sparse::{is_sparse_image, write_sparse_image};

mod shared_resource;
pub use shared_resource::{GblFbBlockDevice, GblFbResource};
use shared_resource::{ScopedGblFbBlockDevice, ScopedGblFbDownloadBuffer};

pub(crate) const GPT_NAME_LEN_U8: usize = GPT_NAME_LEN_U16 * 2;

/// `GblFbPartition` represents any sub window of a block device..
#[derive(Debug, Copy, Clone)]
pub(crate) struct GblFbPartition {
    // The offset where the window starts.
    window_start: u64,
    // The size of the window.
    window_size: u64,
}

impl GblFbPartition {
    /// Returns the partition size
    pub fn size(&self) -> u64 {
        self.window_size
    }

    /// Checks a given subrange and returns the absolute offset.
    fn get_subrange_offset(&self, off: u64, size: usize) -> Result<u64, CommandError> {
        let off = SafeNum::from(off);
        match u64::try_from(off + size)? > self.window_size {
            true => Err("Out of range".into()),
            _ => Ok((off + self.window_start).try_into().unwrap()),
        }
    }
}

/// Writes to a GBL Fastboot partition.
async fn write_fb_partition<T: BlockIoAsync>(
    blk: &mut AsyncBlockDevice<'_, T>,
    part: GblFbPartition,
    off: u64,
    data: &mut [u8],
) -> Result<(), CommandError> {
    Ok(blk.write(part.get_subrange_offset(off, data.len())?, data).await?)
}

/// Reads from a GBL Fastboot partition.
async fn read_fb_partition<T: BlockIoAsync>(
    blk: &mut AsyncBlockDevice<'_, T>,
    part: GblFbPartition,
    off: u64,
    out: &mut [u8],
) -> Result<(), CommandError> {
    Ok(blk.read(part.get_subrange_offset(off, out.len())?, out).await?)
}

/// `TasksExecutor` provides interfaces for spawning and scheduling async tasks.
pub trait TasksExecutor<'a> {
    /// Spawns a new task.
    fn spawn_task(&self, task: impl Future<Output = ()> + 'a) -> Result<(), CommandError>;
}

/// `GblFastboot` implements fastboot commands in the GBL context.
pub struct GblFastboot<'a, 'b, T: TasksExecutor<'b>, B: BlockIoAsync> {
    blk_io_executor: &'a T,
    shared_resource: &'b GblFbResource<'b, B>,
    current_download_buffer: Option<ScopedGblFbDownloadBuffer<'b, 'b, B>>,
    current_download_size: usize,
    enable_async_block_io: bool,
}

impl<'a, 'b, T: TasksExecutor<'b>, B: BlockIoAsync> GblFastboot<'a, 'b, T, B> {
    /// Creates a new instance.
    pub fn new(blk_io_executor: &'a T, shared_resource: &'b GblFbResource<'b, B>) -> Self {
        Self {
            blk_io_executor,
            shared_resource,
            current_download_buffer: None,
            current_download_size: 0,
            enable_async_block_io: false,
        }
    }

    /// Returns the shared resource.
    pub fn shared_resource(&self) -> &'b GblFbResource<'b, B> {
        self.shared_resource
    }

    /// Returns the block IO task executor.
    pub fn blk_io_executor(&self) -> &'a T {
        self.blk_io_executor
    }

    /// Parses and checks the partition argument and returns the block device index and a
    /// `GblFbPartition`.
    pub(crate) fn parse_partition(
        &mut self,
        mut args: Split<char>,
    ) -> Result<(usize, GblFbPartition), CommandError> {
        let part = next_arg(&mut args, Ok(""))?;
        // Parses block device ID.
        let blk_id = next_arg_u64(&mut args, Err("".into())).ok();
        let blk_id = blk_id.map(|v| usize::try_from(v)).transpose()?;
        // Parses offset.
        let window_start = next_arg_u64(&mut args, Ok(0))?;
        // Resolves blk_id and computes absolute offset and maximum end position.
        let (blk_id, window_start, max_end) = match part {
            "" => {
                // Raw block.
                let blk_id = blk_id.ok_or("Must provide a block device ID")?;
                (blk_id, window_start, self.shared_resource.blk_info(blk_id).total_size()?)
            }
            gpt => {
                // GPT partition.
                let (blk_id, ptn) = match blk_id {
                    Some(id) => (id, self.shared_resource.find_partition(id, gpt)?),
                    _ => self.shared_resource.check_part(gpt)?,
                };
                (blk_id, ptn.check_range(window_start, 0)?, ptn.absolute_range()?.1)
            }
        };
        // Parses size. If not given, use the max size computed from max end position.
        let max_window_size = (SafeNum::from(max_end) - window_start).try_into()?;
        let window_size = next_arg_u64(&mut args, Ok(max_window_size))?;
        match window_size > max_window_size {
            true => Err("Out of range".into()),
            _ => Ok((blk_id, GblFbPartition { window_start, window_size })),
        }
    }

    /// Checks and waits until a download buffer is allocated.
    async fn ensure_download_buffer(&mut self) -> &mut [u8] {
        while self.current_download_buffer.is_none() {
            self.current_download_buffer = self.shared_resource.find_download_buffer();
            match self.current_download_buffer.is_some() {
                true => break,
                _ => yield_now().await,
            }
        }
        self.current_download_buffer.as_mut().unwrap()
    }

    /// Waits until a block device is ready and taken.
    async fn sync_block(
        &self,
        blk_idx: usize,
    ) -> Result<ScopedGblFbBlockDevice<'b, 'b, B>, CommandError> {
        loop {
            match self.shared_resource.blk_take(blk_idx)? {
                None => yield_now().await,
                Some(v) => return Ok(v),
            }
        }
    }

    /// Waits for all block devices to be ready.
    async fn sync_all_blocks(&self) {
        for i in 0..self.shared_resource.num_blks() {
            let _ = self.sync_block(i).await;
        }
    }

    /// Implementation for "fastboot oem gbl-sync-blocks".
    async fn oem_sync_blocks<'c>(
        &self,
        utils: &mut impl FastbootUtils,
        res: &'c mut [u8],
    ) -> Result<&'c [u8], CommandError> {
        self.sync_all_blocks().await;
        // Checks error.
        let mut has_error = false;
        for i in 0..self.shared_resource.num_blks() {
            match self.shared_resource.blk_get_err(i) {
                Ok(_) => {}
                Err(e) => {
                    has_error = true;
                    utils.send_info(snprintf!(res, "Block #{} error: {:?}.", i, e)).await?;
                }
            }
        }
        match has_error {
            true => Err("Errors during async block IO. Please reset device.".into()),
            _ => Ok(b""),
        }
    }
}

impl<'b, T: TasksExecutor<'b>, B: BlockIoAsync> FastbootImplementation
    for GblFastboot<'_, 'b, T, B>
{
    async fn get_var(
        &mut self,
        var: &str,
        args: Split<'_, char>,
        out: &mut [u8],
        _utils: &mut impl FastbootUtils,
    ) -> Result<usize, CommandError> {
        Ok(fb_vars_get(self, var, args, out).await?.ok_or("No such variable")?)
    }

    async fn get_var_all(
        &mut self,
        var_logger: &mut impl VarSender,
        _utils: &mut impl FastbootUtils,
    ) -> Result<(), CommandError> {
        fb_vars_get_all(self, var_logger).await
    }

    async fn get_download_buffer(&mut self) -> &mut [u8] {
        self.ensure_download_buffer().await
    }

    async fn download_complete(&mut self, download_size: usize) -> Result<(), CommandError> {
        self.current_download_size = download_size;
        Ok(())
    }

    async fn flash(
        &mut self,
        part: &str,
        utils: &mut impl FastbootUtils,
    ) -> Result<(), CommandError> {
        let (blk_idx, part) = self.parse_partition(part.split(':'))?;
        let mut blk = self.sync_block(blk_idx).await?;
        let mut download_buffer = self.current_download_buffer.take().ok_or("No download")?;
        let download_data_size = take(&mut self.current_download_size);
        let write_task = async move {
            match is_sparse_image(&download_buffer) {
                Ok(_) => {
                    let mut writer = (part, &mut blk);
                    // Passes the entire download buffer so that more can be used as fill buffer.
                    let res =
                        write_sparse_image(&mut download_buffer, &mut writer).await.map(|_| ());
                    blk.set_error(res);
                }
                _ => {
                    let data = &mut download_buffer[..download_data_size];
                    let res = write_fb_partition(&mut blk, part, 0, data).await;
                    blk.set_error(res);
                }
            }
        };
        match self.enable_async_block_io {
            true => {
                self.blk_io_executor.spawn_task(write_task)?;
                let info = "An IO task is launched. To sync manually, run \"oem gbl-sync-blocks\".";
                utils.send_info(info).await?
            }
            _ => write_task.await,
        };
        // Checks if block is ready already and returns errors. This can be the case when the
        // operation is synchronous or runs into early errors.
        match self.shared_resource.blk_take(blk_idx) {
            Err(_) => self.shared_resource.blk_get_err(blk_idx),
            _ => Ok(()),
        }
    }

    async fn upload(
        &mut self,
        _: impl UploadBuilder,
        _: &mut impl FastbootUtils,
    ) -> Result<(), CommandError> {
        Err("Unimplemented".into())
    }

    async fn fetch(
        &mut self,
        part: &str,
        offset: u64,
        size: u64,
        upload_builder: impl UploadBuilder,
        utils: &mut impl FastbootUtils,
    ) -> Result<(), CommandError> {
        let (blk_id, part) = self.parse_partition(part.split(':'))?;
        // Waits until the block device and a download buffer is ready.
        let mut blk = self.sync_block(blk_id).await?;
        let buffer = self.ensure_download_buffer().await;
        let buffer_len = u64::try_from(buffer.len())
            .map_err::<CommandError, _>(|_| "buffer size overflow".into())?;
        let end = add(offset, size)?;
        let mut curr = offset;
        let mut uploader = upload_builder.start(size).await?;
        while curr < end {
            let to_send = min(end - curr, buffer_len);
            read_fb_partition(&mut blk, part, curr, &mut buffer[..to_usize(to_send)?]).await?;
            uploader.upload(&mut buffer[..to_usize(to_send)?]).await?;
            curr += to_send;
        }
        Ok(())
    }

    async fn oem<'a>(
        &mut self,
        cmd: &str,
        utils: &mut impl FastbootUtils,
        res: &'a mut [u8],
    ) -> Result<&'a [u8], CommandError> {
        match cmd {
            "gbl-sync-blocks" => self.oem_sync_blocks(utils, res).await,
            "gbl-enable-async-block-io" => {
                self.enable_async_block_io = true;
                Ok(b"")
            }
            "gbl-disable-async-block-io" => {
                self.enable_async_block_io = false;
                Ok(b"")
            }
            _ => Err("Unknown oem command".into()),
        }
    }
}

/// Check and convert u64 into usize
fn to_usize(val: u64) -> Result<usize, CommandError> {
    val.try_into().map_err(|_| "Overflow".into())
}

/// Add two u64 integers and check overflow
fn add(lhs: u64, rhs: u64) -> Result<u64, CommandError> {
    lhs.checked_add(rhs).ok_or("Overflow".into())
}

/// Subtracts two u64 integers and check overflow
fn sub(lhs: u64, rhs: u64) -> Result<u64, CommandError> {
    lhs.checked_sub(rhs).ok_or("Overflow".into())
}

#[cfg(test)]
mod test {
    use super::*;
    use core::{cmp::max, pin::pin};
    use fastboot::{test_utils::TestUploadBuilder, TransportError, MAX_RESPONSE_SIZE};
    use gbl_async::{block_on, poll};
    use gbl_cyclic_executor::CyclicExecutor;
    use gbl_storage_testlib::{
        AsyncGptDevice, BackingStore, TestBlockDeviceBuilder, TestBlockIo, TestMultiBlockDevices,
    };
    use std::{string::String, sync::Mutex};
    use Vec;

    /// A test implementation of FastbootUtils.
    #[derive(Default)]
    struct TestFastbootUtils {}

    impl FastbootUtils for TestFastbootUtils {
        /// Sends a Fastboot "INFO<`msg`>" packet.
        async fn send_info(&mut self, _: &str) -> Result<(), CommandError> {
            Ok(())
        }

        /// Returns transport errors if there are any.
        fn transport_error(&self) -> Result<(), TransportError> {
            Ok(())
        }
    }

    /// A helper to create an array of `GblFbBlockDevice` and `&mut [u8]` for creating
    /// `GblFbResource`.
    fn create_shared_resource<'a>(
        blks: Vec<AsyncGptDevice<'a, &'a mut TestBlockIo>>,
        dl_buffers: &'a mut Vec<Vec<u8>>,
    ) -> (Vec<GblFbBlockDevice<'a, &'a mut TestBlockIo>>, Vec<&'a mut [u8]>) {
        let mut fb_blks = vec![];
        for ele in blks {
            fb_blks.push(ele.into())
        }
        (fb_blks, dl_buffers.iter_mut().map(|v| v.as_mut_slice().into()).collect::<Vec<_>>())
    }

    /// A helper to sync all GPTs
    fn sync_gpt_all(blks: &mut [AsyncGptDevice<&mut TestBlockIo>]) {
        blks.iter_mut().for_each(|v| block_on(v.sync_gpt()).unwrap())
    }

    type TestGblFastboot<'a, 'b> = GblFastboot<'a, 'b, TestGblFbExecutor<'b>, &'b mut TestBlockIo>;

    /// Helper to test fastboot variable value.
    fn check_var(gbl_fb: &mut TestGblFastboot, var: &str, args: &str, expected: &str) {
        let mut utils: TestFastbootUtils = Default::default();
        let mut out = vec![0u8; fastboot::MAX_RESPONSE_SIZE];
        let val = block_on(gbl_fb.get_var_as_str(var, args.split(':'), &mut out[..], &mut utils))
            .unwrap();
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
        fn spawn_task(&self, task: impl Future<Output = ()> + 'a) -> Result<(), CommandError> {
            Ok(self.0.try_lock().unwrap().spawn_task(task))
        }
    }

    #[test]
    fn test_get_var_partition_info() {
        let mut devs = TestMultiBlockDevices(vec![
            include_bytes!("../../../libstorage/test/gpt_test_1.bin").as_slice().into(),
            include_bytes!("../../../libstorage/test/gpt_test_2.bin").as_slice().into(),
        ]);
        let mut devs = devs.as_gpt_devs();
        sync_gpt_all(&mut devs[..]);
        let mut dl_buffers = vec![vec![0u8; 128 * 1024]; 1];
        let (mut blks, mut dl_buffers) = create_shared_resource(devs, &mut dl_buffers);
        let shared_resource = GblFbResource::new(&mut blks[..], &mut dl_buffers[..]);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &shared_resource);

        // Check different semantics
        check_var(&mut gbl_fb, "partition-size", "boot_a", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a:", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a::", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a:::", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a:0", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a:0:", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a::0", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a:0:0", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a::0x1000", "0x1000");

        check_var(&mut gbl_fb, "partition-size", "boot_b:0", "0x3000");
        check_var(&mut gbl_fb, "partition-size", "vendor_boot_a:1", "0x1000");
        check_var(&mut gbl_fb, "partition-size", "vendor_boot_b:1", "0x1800");

        let mut utils: TestFastbootUtils = Default::default();
        let mut out = vec![0u8; fastboot::MAX_RESPONSE_SIZE];
        assert!(block_on(gbl_fb.get_var_as_str(
            "partition",
            "non-existent".split(':'),
            &mut out[..],
            &mut utils
        ))
        .is_err());
    }

    /// `TestVarSender` implements `TestVarSender`. It stores outputs in a vector of string.
    struct TestVarSender(Vec<String>);

    impl VarSender for TestVarSender {
        async fn send(&mut self, name: &str, args: &[&str], val: &str) -> Result<(), CommandError> {
            self.0.push(format!("{}:{}: {}", name, args.join(":"), val));
            Ok(())
        }
    }

    #[test]
    fn test_get_var_all() {
        let mut devs = TestMultiBlockDevices(vec![
            include_bytes!("../../../libstorage/test/gpt_test_1.bin").as_slice().into(),
            include_bytes!("../../../libstorage/test/gpt_test_2.bin").as_slice().into(),
        ]);
        let mut devs = devs.as_gpt_devs();
        sync_gpt_all(&mut devs[..]);
        let mut dl_buffers = vec![vec![0u8; 128 * 1024]; 1];
        let (mut blks, mut dl_buffers) = create_shared_resource(devs, &mut dl_buffers);
        let shared_resource = GblFbResource::new(&mut blks[..], &mut dl_buffers[..]);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &shared_resource);

        let mut utils: TestFastbootUtils = Default::default();
        let mut logger = TestVarSender(vec![]);
        block_on(gbl_fb.get_var_all(&mut logger, &mut utils)).unwrap();
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
                "partition-size:boot_a:0: 0x2000",
                "partition-type:boot_a:0: raw",
                "partition-size:boot_b:0: 0x3000",
                "partition-type:boot_b:0: raw",
                "partition-size:vendor_boot_a:1: 0x1000",
                "partition-type:vendor_boot_a:1: raw",
                "partition-size:vendor_boot_b:1: 0x1800",
                "partition-type:vendor_boot_b:1: raw"
            ]
        );
    }

    /// A helper for fetching partition from a `GblFastboot`
    fn fetch(
        fb: &mut TestGblFastboot,
        part: String,
        off: u64,
        size: u64,
    ) -> Result<Vec<u8>, CommandError> {
        // Forces upload in two batches for testing.
        let download_buffer = vec![0u8; max(1, usize::try_from(size).unwrap() / 2usize)];
        let mut utils: TestFastbootUtils = Default::default();
        let mut upload_out = vec![0u8; usize::try_from(size).unwrap()];
        let test_uploader = TestUploadBuilder(&mut upload_out[..]);
        block_on(fb.fetch(part.as_str(), off, size, test_uploader, &mut utils))?;
        Ok(upload_out)
    }

    #[test]
    fn test_fetch_invalid_partition_arg() {
        let mut devs = TestMultiBlockDevices(vec![
            include_bytes!("../../../libstorage/test/gpt_test_1.bin").as_slice().into(),
            include_bytes!("../../../libstorage/test/gpt_test_2.bin").as_slice().into(),
            include_bytes!("../../../libstorage/test/gpt_test_2.bin").as_slice().into(),
        ]);
        let mut devs = devs.as_gpt_devs();
        sync_gpt_all(&mut devs[..]);
        let mut dl_buffers = vec![vec![0u8; 128 * 1024]; 1];
        let (mut blks, mut dl_buffers) = create_shared_resource(devs, &mut dl_buffers);
        let shared_resource = GblFbResource::new(&mut blks[..], &mut dl_buffers[..]);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &shared_resource);

        // Missing mandatory block device ID for raw block partition.
        assert!(fetch(&mut gbl_fb, "::0:0".into(), 0, 0).is_err());

        // GPT partition does not exist.
        assert!(fetch(&mut gbl_fb, "non:::".into(), 0, 0).is_err());

        // GPT Partition is not unique.
        assert!(fetch(&mut gbl_fb, "vendor_boot_a:::".into(), 0, 0).is_err());

        // Offset overflows.
        assert!(fetch(&mut gbl_fb, "boot_a::0x2001:".into(), 0, 1).is_err());
        assert!(fetch(&mut gbl_fb, "boot_a".into(), 0x2000, 1).is_err());

        // Size overflows.
        assert!(fetch(&mut gbl_fb, "boot_a:::0x2001".into(), 0, 0).is_err());
        assert!(fetch(&mut gbl_fb, "boot_a".into(), 0, 0x2001).is_err());
    }

    /// A helper for testing raw block upload. It verifies that data read from block device
    /// `blk_id` in range [`off`, `off`+`size`) is the same as `disk[off..][..size]`
    fn check_blk_upload(fb: &mut TestGblFastboot, blk_id: u64, off: u64, size: u64, disk: &[u8]) {
        let expected = disk[off.try_into().unwrap()..][..size.try_into().unwrap()].to_vec();
        // offset/size as part of the partition string.
        let part = format!(":{:#x}:{:#x}:{:#x}", blk_id, off, size);
        assert_eq!(fetch(fb, part, 0, size).unwrap(), expected);
        // offset/size as separate fetch arguments.
        let part = format!(":{:#x}", blk_id);
        assert_eq!(fetch(fb, part, off, size).unwrap(), expected);
    }

    #[test]
    fn test_fetch_raw_block() {
        let disk_0 = include_bytes!("../../../libstorage/test/gpt_test_1.bin");
        let disk_1 = include_bytes!("../../../libstorage/test/gpt_test_2.bin");
        let mut devs =
            TestMultiBlockDevices(vec![disk_0.as_slice().into(), disk_1.as_slice().into()]);
        let mut devs = devs.as_gpt_devs();
        sync_gpt_all(&mut devs[..]);
        let mut dl_buffers = vec![vec![0u8; 128 * 1024]; 1];
        let (mut blks, mut dl_buffers) = create_shared_resource(devs, &mut dl_buffers);
        let shared_resource = GblFbResource::new(&mut blks[..], &mut dl_buffers[..]);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &shared_resource);

        let off = 512;
        let size = 512;
        check_blk_upload(&mut gbl_fb, 0, off, size, disk_0);
        check_blk_upload(&mut gbl_fb, 1, off, size, disk_1);
    }

    /// A helper for testing uploading GPT partition. It verifies that data read from GPT partition
    /// `part` at disk `blk_id` in range [`off`, `off`+`size`) is the same as
    /// `partition_data[off..][..size]`.
    fn check_gpt_upload(
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
        let gpt_part = format!("{}:{}:{:#x}:{:#x}", part, blk_id, off, size);
        assert_eq!(fetch(fb, gpt_part, 0, size).unwrap(), expected);
        // offset/size as separate fetch arguments.
        let gpt_part = format!("{}:{}", part, blk_id);
        assert_eq!(fetch(fb, gpt_part, off, size).unwrap(), expected);
    }

    #[test]
    fn test_fetch_gpt_partition() {
        let mut devs = TestMultiBlockDevices(vec![
            include_bytes!("../../../libstorage/test/gpt_test_1.bin").as_slice().into(),
            include_bytes!("../../../libstorage/test/gpt_test_2.bin").as_slice().into(),
        ]);
        let mut devs = devs.as_gpt_devs();
        sync_gpt_all(&mut devs[..]);
        let mut dl_buffers = vec![vec![0u8; 128 * 1024]; 1];
        let (mut blks, mut dl_buffers) = create_shared_resource(devs, &mut dl_buffers);
        let shared_resource = GblFbResource::new(&mut blks[..], &mut dl_buffers[..]);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &shared_resource);

        let expect_boot_a = include_bytes!("../../../libstorage/test/boot_a.bin");
        let expect_boot_b = include_bytes!("../../../libstorage/test/boot_b.bin");
        let expect_vendor_boot_a = include_bytes!("../../../libstorage/test/vendor_boot_a.bin");
        let expect_vendor_boot_b = include_bytes!("../../../libstorage/test/vendor_boot_b.bin");

        let size = 512;
        let off = 512;

        check_gpt_upload(&mut gbl_fb, "boot_a", off, size, Some(0), expect_boot_a);
        check_gpt_upload(&mut gbl_fb, "boot_b", off, size, Some(0), expect_boot_b);
        check_gpt_upload(&mut gbl_fb, "vendor_boot_a", off, size, Some(1), expect_vendor_boot_a);
        check_gpt_upload(&mut gbl_fb, "vendor_boot_b", off, size, Some(1), expect_vendor_boot_b);

        // No block device id
        check_gpt_upload(&mut gbl_fb, "boot_a", off, size, None, expect_boot_a);
        check_gpt_upload(&mut gbl_fb, "boot_b", off, size, None, expect_boot_b);
        check_gpt_upload(&mut gbl_fb, "vendor_boot_a", off, size, None, expect_vendor_boot_a);
        check_gpt_upload(&mut gbl_fb, "vendor_boot_b", off, size, None, expect_vendor_boot_b);
    }

    /// A helper function to get a bit-flipped copy of the input data.
    fn flipped_bits(data: &[u8]) -> Vec<u8> {
        data.iter().map(|v| !(*v)).collect::<Vec<_>>()
    }

    /// A helper for testing GPT partition flashing.
    fn check_flash_part(fb: &mut TestGblFastboot, part: &str, expected: &[u8]) {
        // Prepare a download buffer.
        let dl_size = expected.len();
        let download = expected.to_vec();
        let mut utils: TestFastbootUtils = Default::default();
        set_download(fb, &download[..]);
        block_on(fb.flash(part, &mut utils)).unwrap();
        assert_eq!(fetch(fb, part.into(), 0, dl_size.try_into().unwrap()).unwrap(), download);

        // Also flashes bit-wise reversed version in case the initial content is the same.
        let download = flipped_bits(expected);
        set_download(fb, &download[..]);
        block_on(fb.flash(part, &mut utils)).unwrap();
        assert_eq!(fetch(fb, part.into(), 0, dl_size.try_into().unwrap()).unwrap(), download);
    }

    #[test]
    fn test_flash_partition() {
        let disk_0 = include_bytes!("../../../libstorage/test/gpt_test_1.bin");
        let disk_1 = include_bytes!("../../../libstorage/test/gpt_test_2.bin");
        let mut devs =
            TestMultiBlockDevices(vec![disk_0.as_slice().into(), disk_1.as_slice().into()]);
        let mut devs = devs.as_gpt_devs();
        sync_gpt_all(&mut devs[..]);
        let mut dl_buffers = vec![vec![0u8; 128 * 1024]; 1];
        let (mut blks, mut dl_buffers) = create_shared_resource(devs, &mut dl_buffers);
        let shared_resource = GblFbResource::new(&mut blks[..], &mut dl_buffers[..]);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &shared_resource);

        let expect_boot_a = include_bytes!("../../../libstorage/test/boot_a.bin");
        let expect_boot_b = include_bytes!("../../../libstorage/test/boot_b.bin");
        check_flash_part(&mut gbl_fb, "boot_a", expect_boot_a);
        check_flash_part(&mut gbl_fb, "boot_b", expect_boot_b);
        check_flash_part(&mut gbl_fb, ":0", disk_0);
        check_flash_part(&mut gbl_fb, ":1", disk_1);

        // Partital flash
        let off = 0x200;
        let size = 1024;
        check_flash_part(&mut gbl_fb, "boot_a::200", &expect_boot_a[off..size]);
        check_flash_part(&mut gbl_fb, "boot_b::200", &expect_boot_b[off..size]);
        check_flash_part(&mut gbl_fb, ":0:200", &disk_0[off..size]);
        check_flash_part(&mut gbl_fb, ":1:200", &disk_1[off..size]);
    }

    #[test]
    fn test_flash_partition_sparse() {
        let raw = include_bytes!("../../testdata/sparse_test_raw.bin");
        let sparse = include_bytes!("../../testdata/sparse_test.bin");
        let mut devs =
            TestMultiBlockDevices(vec![TestBlockDeviceBuilder::new().set_size(raw.len()).build()]);
        let mut dl_buffers = vec![vec![0u8; 128 * 1024]; 1];
        let (mut blks, mut dl_buffers) =
            create_shared_resource(devs.as_gpt_devs(), &mut dl_buffers);
        let shared_resource = GblFbResource::new(&mut blks[..], &mut dl_buffers[..]);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &shared_resource);

        let download = sparse.to_vec();
        let mut utils: TestFastbootUtils = Default::default();
        set_download(&mut gbl_fb, &download[..]);
        block_on(gbl_fb.flash(":0", &mut utils)).unwrap();
        assert_eq!(fetch(&mut gbl_fb, ":0".into(), 0, raw.len().try_into().unwrap()).unwrap(), raw);
    }

    /// A helper to invoke OEM commands.
    ///
    /// Returns the result and INFO strings.
    async fn oem(
        fb: &mut TestGblFastboot<'_, '_>,
        oem_cmd: &str,
        utils: &mut impl FastbootUtils,
    ) -> Result<String, CommandError> {
        let mut res = [0u8; MAX_RESPONSE_SIZE];
        fb.oem(oem_cmd, utils, &mut res[..]).await?;
        Ok(from_utf8(&mut res[..]).unwrap().into())
    }

    #[test]
    fn test_async_flash() {
        // Creates two block devices for writing raw and sparse image.
        let disk = include_bytes!("../../../libstorage/test/gpt_test_1.bin");
        let sparse_raw = include_bytes!("../../testdata/sparse_test_raw.bin");
        let sparse = include_bytes!("../../testdata/sparse_test.bin");
        let dev_sparse = TestBlockDeviceBuilder::new()
            .add_partition("sparse", BackingStore::Size(sparse_raw.len()))
            .build();
        let mut devs = TestMultiBlockDevices(vec![disk.as_slice().into(), dev_sparse]);
        let mut devs = devs.as_gpt_devs();
        sync_gpt_all(&mut devs[..]);

        let mut dl_buffers = vec![vec![0u8; 128 * 1024]; 2];
        let (mut blks, mut dl_buffers) = create_shared_resource(devs, &mut dl_buffers);
        let shared_resource = GblFbResource::new(&mut blks[..], &mut dl_buffers[..]);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &shared_resource);
        let mut utils: TestFastbootUtils = Default::default();

        // "oem gbl-sync-blocks" should return immediately when there is no pending IOs.
        assert!(poll(&mut pin!(oem(&mut gbl_fb, "gbl-sync-blocks", &mut utils))).unwrap().is_ok());
        // Enable async IO.
        assert!(poll(&mut pin!(oem(&mut gbl_fb, "gbl-enable-async-block-io", &mut utils)))
            .unwrap()
            .is_ok());

        // Flashes "boot_a".
        let expect_boot_a = flipped_bits(include_bytes!("../../../libstorage/test/boot_a.bin"));
        set_download(&mut gbl_fb, expect_boot_a.as_slice());
        block_on(gbl_fb.flash("boot_a", &mut utils)).unwrap();

        // Flashes the "sparse" partition on the different block device.
        set_download(&mut gbl_fb, sparse);
        block_on(gbl_fb.flash("sparse", &mut utils)).unwrap();

        // The two blocks should be in the pending state.
        check_var(&mut gbl_fb, "block-device", "0:status", "IO pending");
        check_var(&mut gbl_fb, "block-device", "1:status", "IO pending");

        // There should be two disk IO tasks spawned.
        assert_eq!(blk_io_executor.0.lock().unwrap().num_tasks(), 2);
        {
            // "oem gbl-sync-blocks" should block.
            let oem_sync_blk_fut = &mut pin!(oem(&mut gbl_fb, "gbl-sync-blocks", &mut utils));
            assert!(poll(oem_sync_blk_fut).is_none());
            // Schedules the disk IO tasks to completion.
            blk_io_executor.0.lock().unwrap().run();
            // "oem gbl-sync-blocks" should now be able to finish.
            assert!(poll(oem_sync_blk_fut).unwrap().is_ok());
        }

        // The two blocks should be in the idle state.
        check_var(&mut gbl_fb, "block-device", "0:status", "idle");
        check_var(&mut gbl_fb, "block-device", "1:status", "idle");

        // Verifies flashed image.
        assert_eq!(
            fetch(&mut gbl_fb, "boot_a".into(), 0, expect_boot_a.len().try_into().unwrap())
                .unwrap(),
            expect_boot_a
        );
        assert_eq!(
            fetch(&mut gbl_fb, "sparse".into(), 0, sparse_raw.len().try_into().unwrap()).unwrap(),
            sparse_raw
        );
    }

    #[test]
    fn test_async_flash_block_on_busy_blk() {
        let disk_0 = include_bytes!("../../../libstorage/test/gpt_test_1.bin");
        let disk_1 = include_bytes!("../../../libstorage/test/gpt_test_2.bin");
        let mut devs =
            TestMultiBlockDevices(vec![disk_0.as_slice().into(), disk_1.as_slice().into()]);
        let mut devs = devs.as_gpt_devs();
        sync_gpt_all(&mut devs[..]);

        let mut dl_buffers = vec![vec![0u8; 128 * 1024]; 2];
        let (mut blks, mut dl_buffers) = create_shared_resource(devs, &mut dl_buffers);
        let shared_resource = GblFbResource::new(&mut blks[..], &mut dl_buffers[..]);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &shared_resource);
        let mut utils: TestFastbootUtils = Default::default();

        // Enable async IO.
        assert!(poll(&mut pin!(oem(&mut gbl_fb, "gbl-enable-async-block-io", &mut utils)))
            .unwrap()
            .is_ok());

        // Flashes boot_a partition.
        let expect_boot_a = flipped_bits(include_bytes!("../../../libstorage/test/boot_a.bin"));
        set_download(&mut gbl_fb, expect_boot_a.as_slice());
        block_on(gbl_fb.flash("boot_a", &mut utils)).unwrap();

        // Flashes boot_b partition.
        let expect_boot_b = flipped_bits(include_bytes!("../../../libstorage/test/boot_b.bin"));
        set_download(&mut gbl_fb, expect_boot_b.as_slice());
        {
            let flash_boot_b_fut = &mut pin!(gbl_fb.flash("boot_b", &mut utils));
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
            fetch(&mut gbl_fb, "boot_a".into(), 0, expect_boot_a.len().try_into().unwrap())
                .unwrap(),
            expect_boot_a
        );
        assert_eq!(
            fetch(&mut gbl_fb, "boot_b".into(), 0, expect_boot_b.len().try_into().unwrap())
                .unwrap(),
            expect_boot_b
        );
    }

    #[test]
    fn test_async_flash_error() {
        let disk = include_bytes!("../../../libstorage/test/gpt_test_1.bin");
        let mut devs = TestMultiBlockDevices(vec![disk.as_slice().into()]);
        let mut devs = devs.as_gpt_devs();
        sync_gpt_all(&mut devs[..]);
        // Injects an error.
        devs[0].blk().io().errors = [liberror::Error::Other(None)].into();

        let mut dl_buffers = vec![vec![0u8; 128 * 1024]; 2];
        let (mut blks, mut dl_buffers) = create_shared_resource(devs, &mut dl_buffers);
        let shared_resource = GblFbResource::new(&mut blks[..], &mut dl_buffers[..]);
        let blk_io_executor: TestGblFbExecutor = Default::default();
        let mut gbl_fb = GblFastboot::new(&blk_io_executor, &shared_resource);
        let mut utils: TestFastbootUtils = Default::default();

        // Enable async IO.
        assert!(poll(&mut pin!(oem(&mut gbl_fb, "gbl-enable-async-block-io", &mut utils)))
            .unwrap()
            .is_ok());
        // Flashes boot_a partition.
        let expect_boot_a = flipped_bits(include_bytes!("../../../libstorage/test/boot_a.bin"));
        set_download(&mut gbl_fb, expect_boot_a.as_slice());
        block_on(gbl_fb.flash("boot_a", &mut utils)).unwrap();
        // Schedules the disk IO tasks to completion.
        blk_io_executor.0.lock().unwrap().run();
        // New flash to "boot_a" should fail due to previous error
        set_download(&mut gbl_fb, expect_boot_a.as_slice());
        assert!(block_on(gbl_fb.flash("boot_a", &mut utils)).is_err());
        // "oem gbl-sync-blocks" should fail.
        assert!(block_on(oem(&mut gbl_fb, "gbl-sync-blocks", &mut utils)).is_err());
    }
}
