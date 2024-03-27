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

use crate::fastboot::{GblFastboot, GPT_NAME_LEN_U8};
use core::fmt::Write;
use core::str::{from_utf8, Split};
use fastboot::{next_arg, next_arg_u64, snprintf, CommandError, FormattedBytes};
use gbl_storage::{AsBlockDevice, AsMultiBlockDevices};

/// Internal trait that provides methods for getting and enumerating values for one or multiple
/// related fastboot variables.
pub(crate) trait Variable {
    /// Get the variable value given variable name and arguments.
    ///
    /// Return Ok(Some(`size`)) where `size` is the number of bytes written to `out`. Return
    /// `Ok(None)` if the variable is not supported.
    fn get(
        &self,
        gbl_fb: &mut GblFastboot,
        name: &str,
        args: Split<char>,
        out: &mut [u8],
    ) -> Result<Option<usize>, CommandError>;

    /// Iterates and calls `f` on all values/arguments combinations.
    fn get_all(
        &self,
        gbl_fb: &mut GblFastboot,
        f: &mut dyn FnMut(&str, &[&str], &str) -> Result<(), CommandError>,
    ) -> Result<(), CommandError>;
}

// Constant fastboot variable
impl Variable for (&'static str, &'static str) {
    fn get(
        &self,
        _: &mut GblFastboot,
        name: &str,
        _: Split<char>,
        out: &mut [u8],
    ) -> Result<Option<usize>, CommandError> {
        Ok((name == self.0).then_some(snprintf!(out, "{}", self.1).len()))
    }

    fn get_all(
        &self,
        _: &mut GblFastboot,
        f: &mut dyn FnMut(&str, &[&str], &str) -> Result<(), CommandError>,
    ) -> Result<(), CommandError> {
        f(self.0, &[], self.1)
    }
}

/// `Partition` variable provides information of GPT partitions
///
/// `fastboot getvar partition-size:<GBL Fastboot partition>`
/// `fastboot getvar partition-type:<GBL Fastboot partition>`
pub(crate) struct Partition {}

const PARTITION_SIZE: &str = "partition-size";
const PARTITION_TYPE: &str = "partition-type";
impl Variable for Partition {
    fn get(
        &self,
        gbl_fb: &mut GblFastboot,
        name: &str,
        args: Split<char>,
        out: &mut [u8],
    ) -> Result<Option<usize>, CommandError> {
        let part = gbl_fb.parse_partition(args)?;
        Ok(match name {
            PARTITION_SIZE => Some(snprintf!(out, "{:#x}", gbl_fb.partition_io(part).size()).len()),
            PARTITION_TYPE => Some(snprintf!(out, "raw").len()), // Image type not supported yet.
            _ => None,
        })
    }

    fn get_all(
        &self,
        gbl_fb: &mut GblFastboot,
        f: &mut dyn FnMut(&str, &[&str], &str) -> Result<(), CommandError>,
    ) -> Result<(), CommandError> {
        // Though any sub range of a GPT partition or raw block counts as a partition in GBL
        // Fastboot, for "getvar all" we only enumerate whole range GPT partitions.
        let mut res: Result<(), CommandError> = Ok(());
        let part_name = &mut [0u8; GPT_NAME_LEN_U8][..];
        let mut size_str = [0u8; 32];
        gbl_fb.storage().for_each_until(&mut |mut v, id| {
            // `AsBlockDevice::partition_iter()` has `Self:Sized` constraint thus we make it into a
            // `&mut &mut dyn AsBlockDevice` to meet the bound requirement.
            let v = &mut v;
            let mut id_str = [0u8; 32];
            let id = snprintf!(id_str, "{:x}", id);
            res = (|| {
                for ptn in v.partition_iter() {
                    let sz = ptn.size()?;
                    let part = ptn.gpt_entry().name_to_str(part_name)?;
                    f(PARTITION_SIZE, &[part, id], snprintf!(size_str, "{:#x}", sz))?;
                    // Image type is not supported yet.
                    f(PARTITION_TYPE, &[part, id], snprintf!(size_str, "raw"))?;
                }
                Ok(())
            })();
            res.is_err()
        });
        res
    }
}

/// `BlockDevice` variable provides information of block devices.
///
/// `fastboot getvar block-device:<id>:total-blocks`
/// `fastboot getvar block-device:<id>:block-size`
pub(crate) struct BlockDevice {}

const BLOCK_DEVICE: &str = "block-device";
const TOTAL_BLOCKS: &str = "total-blocks";
const BLOCK_SIZE: &str = "block-size";
impl Variable for BlockDevice {
    fn get(
        &self,
        gbl_fb: &mut GblFastboot,
        name: &str,
        mut args: Split<char>,
        out: &mut [u8],
    ) -> Result<Option<usize>, CommandError> {
        Ok(match name {
            BLOCK_DEVICE => {
                let id = next_arg_u64(&mut args, Err("Missing block device ID".into()))?;
                let val_type = next_arg(&mut args, Err("Missing value type".into()))?;
                let val = match val_type {
                    TOTAL_BLOCKS => gbl_fb.storage().get(id)?.num_blocks()?,
                    BLOCK_SIZE => gbl_fb.storage().get(id)?.block_size()?,
                    _ => return Err("Invalid type".into()),
                };
                Some(snprintf!(out, "{:#x}", val).len())
            }
            _ => None,
        })
    }

    fn get_all(
        &self,
        gbl_fb: &mut GblFastboot,
        f: &mut dyn FnMut(&str, &[&str], &str) -> Result<(), CommandError>,
    ) -> Result<(), CommandError> {
        let mut val = [0u8; 32];
        let mut res: Result<(), CommandError> = Ok(());
        gbl_fb.storage().for_each_until(&mut |blk, id| {
            let mut id_str = [0u8; 32];
            let id = snprintf!(id_str, "{:x}", id);
            res = (|| {
                f(BLOCK_DEVICE, &[id, "total-blocks"], snprintf!(val, "{:#x}", blk.num_blocks()?))?;
                f(BLOCK_DEVICE, &[id, "block-size"], snprintf!(val, "{:#x}", blk.block_size()?))
            })();
            res.is_err()
        });
        res
    }
}
