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

use core::cmp::min;
use core::ffi::CStr;
use core::str::Split;
use fastboot::{
    next_arg, next_arg_u64, CommandError, FastbootImplementation, FastbootUtils, UploadBuilder,
};
use gbl_async::block_on;
use gbl_storage::{AsBlockDevice, AsMultiBlockDevices, GPT_NAME_LEN_U16};

mod vars;
use vars::{BlockDevice, Partition, Variable};

mod sparse;
use sparse::{is_sparse_image, write_sparse_image, SparseRawWriter};

pub(crate) const GPT_NAME_LEN_U8: usize = GPT_NAME_LEN_U16 * 2;

/// `GblFbPartition` represents a GBL Fastboot partition, which is defined as any sub window of a
/// GPT partition or raw storage.
#[derive(Debug, Copy, Clone)]
pub(crate) struct GblFbPartition {
    // GPT partition if it is a non-null string, raw block otherwise.
    part: [u8; GPT_NAME_LEN_U8],
    blk_id: u64,
    // The offset where the window starts.
    window_start: u64,
    // The size of the window.
    window_size: u64,
}

impl GblFbPartition {
    pub fn part(&self) -> &str {
        // The construction is guaranteed to give a valid UTF8 string.
        CStr::from_bytes_until_nul(&self.part[..]).unwrap().to_str().unwrap()
    }

    /// Returns the partition size
    pub fn size(&self) -> u64 {
        self.window_size
    }
}

/// `GblFbPartitionIo` provides read/write/size methods for a GBL Fastboot partition.
pub(crate) struct GblFbPartitionIo<'a> {
    part: GblFbPartition,
    devs: &'a mut dyn AsMultiBlockDevices,
}

impl<'a> GblFbPartitionIo<'a> {
    fn new(part: GblFbPartition, devs: &'a mut dyn AsMultiBlockDevices) -> Self {
        Self { part, devs }
    }

    /// Checks read/write offset/size and returns the absolute offset.
    fn check_range(&self, rw_off: u64, rw_size: usize) -> Result<u64, CommandError> {
        if add(rw_off, u64::try_from(rw_size)?)? > self.part.window_size {
            return Err("Read/Write range overflow".into());
        }
        Ok(add(rw_off, self.part.window_start)?)
    }

    /// Reads from the GBL Fastboot partition.
    pub fn read(&mut self, offset: u64, out: &mut [u8]) -> Result<(), CommandError> {
        let offset = self.check_range(offset, out.len())?;
        let mut dev = (&mut self.devs).get(self.part.blk_id)?;
        Ok(match self.part.part() {
            "" => dev.read(offset, out),
            part => dev.read_gpt_partition(part, offset, out),
        }?)
    }

    /// Writes to the GBL Fastboot partition.
    pub fn write(&mut self, offset: u64, data: &mut [u8]) -> Result<(), CommandError> {
        let offset = self.check_range(offset, data.len())?;
        let mut dev = (&mut self.devs).get(self.part.blk_id)?;
        Ok(match self.part.part() {
            "" => dev.write(offset, data),
            part => dev.write_gpt_partition(part, offset, data),
        }?)
    }

    /// Returns the size of the GBL Fastboot partition.
    pub fn size(&mut self) -> u64 {
        self.part.window_size
    }
}

impl SparseRawWriter for GblFbPartitionIo<'_> {
    /// Writes bytes from `data` to the destination storage at offset `off`
    async fn write(&mut self, off: u64, data: &mut [u8]) -> Result<(), CommandError> {
        self.write(off, data)
    }
}

/// `GblFastboot` implements fastboot commands in the GBL context.
pub struct GblFastboot<'a> {
    pub storage: &'a mut dyn AsMultiBlockDevices,
    download_buffer: &'a mut [u8],
}

impl<'a> GblFastboot<'a> {
    /// Native GBL fastboot variables.
    const NATIVE_VARS: &'static [&'static dyn Variable] = &[
        &("version-bootloader", "1.0"), // Placeholder for now.
        // GBL Fastboot can internally handle uploading in batches, thus there is no limit on
        // max-fetch-size.
        &("max-fetch-size", "0xffffffffffffffff"),
        &BlockDevice {},
        &Partition {},
    ];

    /// Creates a new instance.
    pub fn new(storage: &'a mut dyn AsMultiBlockDevices, download_buffer: &'a mut [u8]) -> Self {
        Self { storage, download_buffer }
    }

    /// Returns the storage object.
    ///
    /// `AsMultiBlockDevices` has methods with `Self: Sized` constraint. Thus we return a
    /// `&mut &mut dyn AsMultiBlockDevices` which also implements `AsMultiBlockDevices` but meets
    /// the `Sized` bound.
    pub fn storage(&mut self) -> &mut &'a mut dyn AsMultiBlockDevices {
        &mut self.storage
    }

    /// Parses and checks partition name, block device ID and offset from the arguments and
    /// returns an instance of `GblFbPartition`.
    pub(crate) fn parse_partition<'b>(
        &mut self,
        mut args: Split<'b, char>,
    ) -> Result<GblFbPartition, CommandError> {
        let devs = self.storage();
        // Copies over partition name string
        let part = next_arg(&mut args, Ok(""))?;
        let mut part_str = [0u8; GPT_NAME_LEN_U8];
        part_str
            .get_mut(..part.len())
            .ok_or("Partition name too long")?
            .clone_from_slice(part.as_bytes());
        // Parses block device ID.
        let blk_id = next_arg_u64(&mut args, Err("".into())).ok();
        // Parses offset
        let window_start = next_arg_u64(&mut args, Ok(0))?;
        // Checks blk_id and computes maximum partition size.
        let (blk_id, max_size) = match part {
            "" => {
                let blk_id = blk_id.ok_or("Must provide a block device ID")?;
                (blk_id, devs.get(blk_id)?.info().total_size()?)
            }
            gpt => match blk_id {
                Some(id) => (id, devs.get(id)?.find_partition(gpt)?.size()?),
                _ => {
                    devs.check_part(gpt).map(|(id, p)| Ok::<_, CommandError>((id, p.size()?)))??
                }
            },
        };
        let max_size = max_size.checked_sub(window_start).ok_or("Offset overflows")?;
        // Parses size or uses `max_size`
        let window_size = next_arg_u64(&mut args, Ok(max_size))?;
        match window_size > max_size {
            true => Err("Size overflows".into()),
            _ => Ok(GblFbPartition {
                part: part_str,
                blk_id: blk_id,
                window_start: window_start,
                window_size: window_size,
            }),
        }
    }
}

impl FastbootImplementation for GblFastboot<'_> {
    fn get_var(
        &mut self,
        var: &str,
        args: Split<char>,
        out: &mut [u8],
        _utils: &mut dyn FastbootUtils,
    ) -> Result<usize, CommandError> {
        Self::NATIVE_VARS
            .iter()
            .find_map(|v| v.get(self, var, args.clone(), out).transpose())
            .ok_or::<CommandError>("No such variable".into())?
    }

    fn get_var_all(
        &mut self,
        f: &mut dyn FnMut(&str, &[&str], &str) -> Result<(), CommandError>,
        _utils: &mut dyn FastbootUtils,
    ) -> Result<(), CommandError> {
        Self::NATIVE_VARS.iter().find_map(|v| v.get_all(self, f).err()).map_or(Ok(()), |e| Err(e))
    }

    /// Backend for getting download buffer
    fn get_download_buffer(&mut self) -> &mut [u8] {
        self.download_buffer
    }

    fn flash(&mut self, part: &str, utils: &mut dyn FastbootUtils) -> Result<(), CommandError> {
        let part = self.parse_partition(part.split(':'))?;
        match is_sparse_image(self.download_buffer) {
            // Passes the entire download buffer so that more can be used as fill buffer.
            Ok(_) => block_on(write_sparse_image(
                self.download_buffer,
                &mut GblFbPartitionIo::new(part, self.storage),
            ))
            .map(|_| ()),
            _ => GblFbPartitionIo::new(part, self.storage)
                .write(0, &mut self.download_buffer[..utils.download_data_size()]),
        }
    }

    fn upload(
        &mut self,
        _upload_builder: UploadBuilder,
        _utils: &mut dyn FastbootUtils,
    ) -> Result<(), CommandError> {
        Err("Unimplemented".into())
    }

    fn fetch(
        &mut self,
        part: &str,
        offset: u64,
        size: u64,
        upload_builder: UploadBuilder,
        utils: &mut dyn FastbootUtils,
    ) -> Result<(), CommandError> {
        let part = self.parse_partition(part.split(':'))?;
        let buffer = &mut self.download_buffer[..];
        let buffer_len = u64::try_from(buffer.len())
            .map_err::<CommandError, _>(|_| "buffer size overflow".into())?;
        let end = add(offset, size)?;
        let mut curr = offset;
        let mut uploader = upload_builder.start(size)?;
        while curr < end {
            let to_send = min(end - curr, buffer_len);
            GblFbPartitionIo::new(part, self.storage)
                .read(curr, &mut buffer[..to_usize(to_send)?])?;
            uploader.upload(&mut buffer[..to_usize(to_send)?])?;
            curr += to_send;
        }
        Ok(())
    }

    fn oem<'a>(
        &mut self,
        _cmd: &str,
        utils: &mut dyn FastbootUtils,
        _res: &'a mut [u8],
    ) -> Result<&'a [u8], CommandError> {
        let _ = utils.send_info("GBL OEM not implemented yet")?;
        Err("Unimplemented".into())
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
    use fastboot::{test_utils::with_mock_upload_builder, TransportError};
    use gbl_storage_testlib::{TestBlockDeviceBuilder, TestMultiBlockDevices};
    use std::string::String;
    use Vec;

    /// A test implementation of FastbootUtils.
    #[derive(Default)]
    struct TestFastbootUtils {
        download_data_size: usize,
    }

    impl TestFastbootUtils {
        pub fn new(download_data_size: usize) -> Self {
            Self { download_data_size }
        }
    }

    impl FastbootUtils for TestFastbootUtils {
        // Returns the size of the most recent download.
        fn download_data_size(&self) -> usize {
            self.download_data_size
        }

        /// Sends a Fastboot "INFO<`msg`>" packet.
        fn send_info(&mut self, _: &str) -> Result<(), CommandError> {
            Ok(())
        }

        /// Returns transport errors if there are any.
        fn transport_error(&self) -> Result<(), TransportError> {
            Ok(())
        }
    }

    /// Helper to test fastboot variable value.
    fn check_var(gbl_fb: &mut GblFastboot, var: &str, args: &str, expected: &str) {
        let mut utils: TestFastbootUtils = Default::default();
        let mut out = vec![0u8; fastboot::MAX_RESPONSE_SIZE];
        assert_eq!(
            gbl_fb.get_var_as_str(var, args.split(':'), &mut out[..], &mut utils).unwrap(),
            expected
        );
    }

    /// A helper to set the download content.
    fn set_download(gbl_fb: &mut GblFastboot, data: &[u8], utils: &mut TestFastbootUtils) {
        gbl_fb.download_buffer[..data.len()].clone_from_slice(data);
        utils.download_data_size = data.len();
    }

    #[test]
    fn test_get_var_partition_info() {
        let mut devs = TestMultiBlockDevices(vec![
            include_bytes!("../../../libstorage/test/gpt_test_1.bin").as_slice().into(),
            include_bytes!("../../../libstorage/test/gpt_test_2.bin").as_slice().into(),
        ]);
        devs.sync_gpt_all(&mut |_, _, _| panic!("GPT sync failed"));
        let download_buffer = &mut vec![0u8; 128 * 1024][..];
        let mut gbl_fb = GblFastboot::new(&mut devs, download_buffer);

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
        assert!(gbl_fb
            .get_var_as_str("partition", "non-existent".split(':'), &mut out[..], &mut utils)
            .is_err());
    }

    #[test]
    fn test_get_var_all() {
        let mut devs = TestMultiBlockDevices(vec![
            include_bytes!("../../../libstorage/test/gpt_test_1.bin").as_slice().into(),
            include_bytes!("../../../libstorage/test/gpt_test_2.bin").as_slice().into(),
        ]);
        devs.sync_gpt_all(&mut |_, _, _| panic!("GPT sync failed"));
        let download_buffer = &mut vec![0u8; 128 * 1024][..];
        let mut gbl_fb = GblFastboot::new(&mut devs, download_buffer);

        let mut utils: TestFastbootUtils = Default::default();
        let mut out: Vec<String> = Default::default();
        gbl_fb
            .get_var_all(
                &mut |name, args, val| {
                    out.push(format!("{}:{}: {}", name, args.join(":"), val));
                    Ok(())
                },
                &mut utils,
            )
            .unwrap();
        assert_eq!(
            out,
            [
                "version-bootloader:: 1.0",
                "max-fetch-size:: 0xffffffffffffffff",
                "block-device:0:total-blocks: 0x80",
                "block-device:0:block-size: 0x200",
                "block-device:1:total-blocks: 0x100",
                "block-device:1:block-size: 0x200",
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
        fb: &mut GblFastboot,
        part: String,
        off: u64,
        size: u64,
    ) -> Result<Vec<u8>, CommandError> {
        // Forces upload in two batches for testing.
        let download_buffer = vec![0u8; core::cmp::max(1, usize::try_from(size).unwrap() / 2usize)];
        let mut utils: TestFastbootUtils = Default::default();
        let mut upload_out = vec![0u8; usize::try_from(size).unwrap()];
        let mut res = Ok(());
        let (uploaded, _) = with_mock_upload_builder(&mut upload_out[..], |upload_builder| {
            res = fb.fetch(part.as_str(), off, size, upload_builder, &mut utils)
        });
        assert!(res.is_err() || uploaded == usize::try_from(size).unwrap());
        res.map(|_| upload_out)
    }

    #[test]
    fn test_fetch_invalid_partition_arg() {
        let mut devs = TestMultiBlockDevices(vec![
            include_bytes!("../../../libstorage/test/gpt_test_1.bin").as_slice().into(),
            include_bytes!("../../../libstorage/test/gpt_test_2.bin").as_slice().into(),
            include_bytes!("../../../libstorage/test/gpt_test_2.bin").as_slice().into(),
        ]);
        devs.sync_gpt_all(&mut |_, _, _| panic!("GPT sync failed"));
        let download_buffer = &mut vec![0u8; 128 * 1024][..];
        let mut gbl_fb = GblFastboot::new(&mut devs, download_buffer);

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
    fn check_blk_upload(fb: &mut GblFastboot, blk_id: u64, off: u64, size: u64, disk: &[u8]) {
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
        devs.sync_gpt_all(&mut |_, _, _| panic!("GPT sync failed"));
        let download_buffer = &mut vec![0u8; 128 * 1024][..];
        let mut gbl_fb = GblFastboot::new(&mut devs, download_buffer);

        let off = 512;
        let size = 512;
        check_blk_upload(&mut gbl_fb, 0, off, size, disk_0);
        check_blk_upload(&mut gbl_fb, 1, off, size, disk_1);
    }

    /// A helper for testing uploading GPT partition. It verifies that data read from GPT partition
    /// `part` at disk `blk_id` in range [`off`, `off`+`size`) is the same as
    /// `partition_data[off..][..size]`.
    fn check_gpt_upload(
        fb: &mut GblFastboot,
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
        devs.sync_gpt_all(&mut |_, _, _| panic!("GPT sync failed"));
        let download_buffer = &mut vec![0u8; 128 * 1024][..];
        let mut gbl_fb = GblFastboot::new(&mut devs, download_buffer);

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

    /// A helper for testing GPT partition flashing.
    fn check_flash_part(fb: &mut GblFastboot, part: &str, expected: &[u8]) {
        // Prepare a download buffer.
        let dl_size = expected.len();
        let download = expected.to_vec();
        let mut utils: TestFastbootUtils = Default::default();
        set_download(fb, &download[..], &mut utils);
        fb.flash(part, &mut utils).unwrap();
        assert_eq!(fetch(fb, part.into(), 0, dl_size.try_into().unwrap()).unwrap(), download);

        // Also flashes bit-wise reversed version in case the initial content is the same.
        let download = expected.iter().map(|v| !(*v)).collect::<Vec<_>>();
        set_download(fb, &download[..], &mut utils);
        fb.flash(part, &mut utils).unwrap();
        assert_eq!(fetch(fb, part.into(), 0, dl_size.try_into().unwrap()).unwrap(), download);
    }

    #[test]
    fn test_flash_partition() {
        let disk_0 = include_bytes!("../../../libstorage/test/gpt_test_1.bin");
        let disk_1 = include_bytes!("../../../libstorage/test/gpt_test_2.bin");
        let mut devs =
            TestMultiBlockDevices(vec![disk_0.as_slice().into(), disk_1.as_slice().into()]);
        devs.sync_gpt_all(&mut |_, _, _| panic!("GPT sync failed"));

        let download_buffer = &mut vec![0u8; 128 * 1024][..];
        let mut gbl_fb = GblFastboot::new(&mut devs, download_buffer);

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
        let download_buffer = &mut vec![0u8; 128 * 1024][..];
        let mut gbl_fb = GblFastboot::new(&mut devs, download_buffer);

        let download = sparse.to_vec();
        let mut utils: TestFastbootUtils = Default::default();
        set_download(&mut gbl_fb, &download[..], &mut utils);
        gbl_fb.flash(":0", &mut utils).unwrap();
        assert_eq!(fetch(&mut gbl_fb, ":0".into(), 0, raw.len().try_into().unwrap()).unwrap(), raw);
    }
}
