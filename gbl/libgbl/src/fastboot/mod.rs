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

use core::str::Split;
use fastboot::{CommandError, FastbootImplementation};
use gbl_storage::AsMultiBlockDevices;

mod vars;
use vars::{BlockDevice, Partition, Variable};

/// `GblFastboot` implements fastboot commands in the GBL context.
pub struct GblFastboot<'a> {
    pub storage: &'a mut dyn AsMultiBlockDevices,
}

impl<'a> GblFastboot<'a> {
    /// Native GBL fastboot variables.
    const NATIVE_VARS: &'static [&'static dyn Variable] = &[
        &("version-bootloader", "1.0"), // Placeholder for now.
        &BlockDevice {},
        &Partition {},
    ];

    /// Creates a new instance.
    pub fn new(storage: &'a mut dyn AsMultiBlockDevices) -> Self {
        Self { storage: storage }
    }

    /// Returns the storage object.
    ///
    /// `AsMultiBlockDevices` has methods with `Self: Sized` constraint. Thus we return a
    /// `&mut &mut dyn AsMultiBlockDevices` which also implements `AsMultiBlockDevices` but meets
    /// the `Sized` bound.
    pub fn storage(&mut self) -> &mut &'a mut dyn AsMultiBlockDevices {
        &mut self.storage
    }
}

impl FastbootImplementation for GblFastboot<'_> {
    fn get_var(
        &mut self,
        var: &str,
        args: Split<char>,
        out: &mut [u8],
    ) -> Result<usize, CommandError> {
        Self::NATIVE_VARS
            .iter()
            .find_map(|v| v.get(self, var, args.clone(), out).transpose())
            .ok_or::<CommandError>("No such variable".into())?
    }

    fn get_var_all(
        &mut self,
        f: &mut dyn FnMut(&str, &[&str], &str) -> Result<(), CommandError>,
    ) -> Result<(), CommandError> {
        Self::NATIVE_VARS.iter().find_map(|v| v.get_all(self, f).err()).map_or(Ok(()), |e| Err(e))
    }
}

/// A helper to convert a hex string into u64.
pub(crate) fn hex_str_to_u64(s: &str) -> Result<u64, CommandError> {
    Ok(u64::from_str_radix(s.strip_prefix("0x").unwrap_or(s), 16)?)
}

/// A helper to check and fetch the next argument from a `Split` or fail with given message.
pub(crate) fn next_arg<'a>(args: &mut Split<'a, char>, err: &str) -> Result<&'a str, CommandError> {
    args.next().ok_or(err.into())
}

#[cfg(test)]
mod test {
    use super::*;
    use gbl_storage::{required_scratch_size, AsBlockDevice, BlockIo};
    use Vec;

    const BLOCK_SIZE: u64 = 512;
    const MAX_GPT_ENTRIES: u64 = 128;

    // TODO(b/329138620): Migrate to common storage test library once available.
    struct TestBlockIo(Vec<u8>);

    impl BlockIo for TestBlockIo {
        fn block_size(&mut self) -> u64 {
            BLOCK_SIZE
        }

        fn num_blocks(&mut self) -> u64 {
            u64::try_from(self.0.len()).unwrap() / BLOCK_SIZE
        }

        fn alignment(&mut self) -> u64 {
            BLOCK_SIZE
        }

        fn read_blocks(&mut self, blk_offset: u64, out: &mut [u8]) -> bool {
            out.clone_from_slice(
                &self.0[usize::try_from(blk_offset * BLOCK_SIZE).unwrap()..][..out.len()],
            );
            true
        }

        fn write_blocks(&mut self, blk_offset: u64, data: &[u8]) -> bool {
            self.0[usize::try_from(blk_offset * BLOCK_SIZE).unwrap()..][..data.len()]
                .clone_from_slice(data);
            true
        }
    }

    struct TestBlockDevice((TestBlockIo, Vec<u8>));

    impl AsBlockDevice for TestBlockDevice {
        fn with(&mut self, f: &mut dyn FnMut(&mut dyn BlockIo, &mut [u8], u64)) {
            f(&mut self.0 .0, &mut self.0 .1[..], MAX_GPT_ENTRIES)
        }
    }

    fn test_block_device(storage: &[u8]) -> TestBlockDevice {
        let mut io = TestBlockIo(Vec::from(storage));
        let scratch_size = required_scratch_size(&mut io, MAX_GPT_ENTRIES).unwrap();
        TestBlockDevice((io, vec![0u8; scratch_size]))
    }

    struct TestMultiBlockDevices(Vec<TestBlockDevice>);

    impl AsMultiBlockDevices for TestMultiBlockDevices {
        fn for_each_until(&mut self, f: &mut dyn FnMut(&mut dyn AsBlockDevice, u64) -> bool) {
            let _ = self
                .0
                .iter_mut()
                .enumerate()
                .find_map(|(idx, ele)| f(ele, u64::try_from(idx).unwrap()).then_some(()));
        }
    }

    /// Helper to test fastboot variable value.
    fn check_var(gbl_fb: &mut GblFastboot, var: &str, args: &str, expected: &str) {
        let mut out = vec![0u8; fastboot::MAX_RESPONSE_SIZE];
        assert_eq!(gbl_fb.get_var_as_str(var, args.split(':'), &mut out[..]).unwrap(), expected);
    }

    #[test]
    fn test_get_var_partition_info() {
        let mut devs = TestMultiBlockDevices(vec![
            test_block_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin")),
            test_block_device(include_bytes!("../../../libstorage/test/gpt_test_2.bin")),
        ]);
        devs.sync_gpt_all(&mut |_, _, _| panic!("GPT sync failed"));

        let mut gbl_fb = GblFastboot::new(&mut devs);
        check_var(&mut gbl_fb, "partition-size", "boot_a:0", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_b:0", "0x3000");
        check_var(&mut gbl_fb, "partition-size", "vendor_boot_a:1", "0x1000");
        check_var(&mut gbl_fb, "partition-size", "vendor_boot_b:1", "0x1800");

        let mut out = vec![0u8; fastboot::MAX_RESPONSE_SIZE];
        assert!(gbl_fb
            .get_var_as_str("partition", "non-existent".split(':'), &mut out[..])
            .is_err());
    }

    #[test]
    fn test_get_var_all() {
        let mut devs = TestMultiBlockDevices(vec![
            test_block_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin")),
            test_block_device(include_bytes!("../../../libstorage/test/gpt_test_2.bin")),
        ]);
        devs.sync_gpt_all(&mut |_, _, _| panic!("GPT sync failed"));
        let mut gbl_fb = GblFastboot::new(&mut devs);

        let mut out: Vec<String> = Default::default();
        gbl_fb
            .get_var_all(&mut |name, args, val| {
                out.push(format!("{}:{}: {}", name, args.join(":"), val));
                Ok(())
            })
            .unwrap();
        assert_eq!(
            out,
            [
                "version-bootloader:: 1.0",
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
}
