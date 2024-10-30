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

use crate::{
    fastboot::{BufferPool, GblFastboot},
    GblOps,
};
use core::fmt::Write;
use core::str::{from_utf8, Split};
use fastboot::{next_arg, next_arg_u64, snprintf, CommandError, FormattedBytes, VarInfoSender};

/// Internal trait that provides methods for getting and enumerating values for one or multiple
/// related fastboot variables.
pub(crate) trait Variable {
    /// Get the variable value given variable name and arguments.
    ///
    /// Return Ok(Some(`size`)) where `size` is the number of bytes written to `out`. Return
    /// `Ok(None)` if the variable is not supported.
    async fn get<'a, P, F>(
        &self,
        gbl_fb: &mut GblFastboot<'a, '_, '_, '_, impl GblOps<'a>, impl BufferPool, P, F>,
        name: &str,
        args: Split<'_, char>,
        out: &mut [u8],
    ) -> Result<Option<usize>, CommandError>;

    /// Iterates and calls `f` on all values/arguments combinations.
    async fn get_all<'a, P, F>(
        &self,
        gbl_fb: &mut GblFastboot<'a, '_, '_, '_, impl GblOps<'a>, impl BufferPool, P, F>,
        responder: &mut impl VarInfoSender,
    ) -> Result<(), CommandError>;
}

// Constant fastboot variable
impl Variable for (&'static str, &'static str) {
    async fn get<'a, P, F>(
        &self,
        _: &mut GblFastboot<'a, '_, '_, '_, impl GblOps<'a>, impl BufferPool, P, F>,
        name: &str,
        _: Split<'_, char>,
        out: &mut [u8],
    ) -> Result<Option<usize>, CommandError> {
        Ok((name == self.0).then_some(snprintf!(out, "{}", self.1).len()))
    }

    async fn get_all<'a, P, F>(
        &self,
        _: &mut GblFastboot<'a, '_, '_, '_, impl GblOps<'a>, impl BufferPool, P, F>,
        responder: &mut impl VarInfoSender,
    ) -> Result<(), CommandError> {
        responder.send_var_info(self.0, &[], self.1).await
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
    async fn get<'a, P, F>(
        &self,
        gbl_fb: &mut GblFastboot<'a, '_, '_, '_, impl GblOps<'a>, impl BufferPool, P, F>,
        name: &str,
        mut args: Split<'_, char>,
        out: &mut [u8],
    ) -> Result<Option<usize>, CommandError> {
        let (_, _, start, sz) = gbl_fb.parse_partition(args.next().ok_or("Missing var")?)?;
        Ok(match name {
            PARTITION_SIZE => Some(snprintf!(out, "{:#x}", sz).len()),
            PARTITION_TYPE => Some(snprintf!(out, "raw").len()), // Image type not supported yet.
            _ => None,
        })
    }

    async fn get_all<'a, P, F>(
        &self,
        gbl_fb: &mut GblFastboot<'a, '_, '_, '_, impl GblOps<'a>, impl BufferPool, P, F>,
        responder: &mut impl VarInfoSender,
    ) -> Result<(), CommandError> {
        // Though any sub range of a GPT partition or raw block counts as a partition in GBL
        // Fastboot, for "getvar all" we only enumerate whole range GPT partitions.
        let partitions = gbl_fb.gbl_ops.partitions()?;
        let mut size_str = [0u8; 32];
        for (idx, blk) in partitions.iter().enumerate() {
            for ptn_idx in 0..blk.num_partitions().unwrap_or(0) {
                let ptn = blk.get_partition_by_idx(ptn_idx)?;
                let sz: u64 = ptn.size()?;
                let part = ptn.name()?;
                // Assumes max partition name length of 72 plus max u64 hex string length 18.
                let mut part_id_buf = [0u8; 128];
                let part = snprintf!(part_id_buf, "{}/{:x}", part, idx);
                responder
                    .send_var_info(PARTITION_SIZE, &[part], snprintf!(size_str, "{:#x}", sz))
                    .await?;
                // Image type is not supported yet.
                responder
                    .send_var_info(PARTITION_TYPE, &[part], snprintf!(size_str, "raw"))
                    .await?;
            }
        }
        Ok(())
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
const BLOCK_DEVICE_STATUS: &str = "status";

impl Variable for BlockDevice {
    async fn get<'a, P, F>(
        &self,
        gbl_fb: &mut GblFastboot<'a, '_, '_, '_, impl GblOps<'a>, impl BufferPool, P, F>,
        name: &str,
        mut args: Split<'_, char>,
        out: &mut [u8],
    ) -> Result<Option<usize>, CommandError> {
        Ok(match name {
            BLOCK_DEVICE => {
                let id = next_arg_u64(&mut args)?.ok_or("Missing block device ID")?;
                let id = usize::try_from(id)?;
                let val_type = next_arg(&mut args).ok_or("Missing value type")?;
                let blk = &gbl_fb.gbl_ops.partitions()?[id];
                let info = blk.block_info();
                Some(
                    match val_type {
                        TOTAL_BLOCKS => snprintf!(out, "{:#x}", info.num_blocks),
                        BLOCK_SIZE => snprintf!(out, "{:#x}", info.block_size),
                        BLOCK_DEVICE_STATUS => {
                            snprintf!(out, "{}", blk.status().to_str())
                        }
                        _ => return Err("Invalid type".into()),
                    }
                    .len(),
                )
            }
            _ => None,
        })
    }

    async fn get_all<'a, P, F>(
        &self,
        gbl_fb: &mut GblFastboot<'a, '_, '_, '_, impl GblOps<'a>, impl BufferPool, P, F>,
        responder: &mut impl VarInfoSender,
    ) -> Result<(), CommandError> {
        let mut val = [0u8; 32];
        for (idx, blk) in gbl_fb.gbl_ops.partitions()?.iter().enumerate() {
            let mut id_str = [0u8; 32];
            let id = snprintf!(id_str, "{:x}", idx);
            let info = blk.block_info();
            responder
                .send_var_info(
                    BLOCK_DEVICE,
                    &[id, TOTAL_BLOCKS],
                    snprintf!(val, "{:#x}", info.num_blocks),
                )
                .await?;
            responder
                .send_var_info(
                    BLOCK_DEVICE,
                    &[id, BLOCK_SIZE],
                    snprintf!(val, "{:#x}", info.block_size),
                )
                .await?;
            responder
                .send_var_info(
                    BLOCK_DEVICE,
                    &[id, BLOCK_DEVICE_STATUS],
                    snprintf!(val, "{}", blk.status().to_str()),
                )
                .await?;
        }
        Ok(())
    }
}

/// Gives the value of current default block device ID set by "oem gbl-set-default-block".
///
/// `fastboot getvar gbl-default-block`
pub(crate) struct DefaultBlock {}

const DEFAULT_BLOCK: &str = "gbl-default-block";

impl Variable for DefaultBlock {
    async fn get<'a, P, F>(
        &self,
        gbl_fb: &mut GblFastboot<'a, '_, '_, '_, impl GblOps<'a>, impl BufferPool, P, F>,
        name: &str,
        _: Split<'_, char>,
        out: &mut [u8],
    ) -> Result<Option<usize>, CommandError> {
        Ok(match name {
            DEFAULT_BLOCK => Some(
                match gbl_fb.default_block {
                    Some(v) => snprintf!(out, "{:#x}", v),
                    _ => snprintf!(out, "None"),
                }
                .len(),
            ),
            _ => None,
        })
    }

    async fn get_all<'a, P, F>(
        &self,
        gbl_fb: &mut GblFastboot<'a, '_, '_, '_, impl GblOps<'a>, impl BufferPool, P, F>,
        responder: &mut impl VarInfoSender,
    ) -> Result<(), CommandError> {
        let mut val = [0u8; 32];
        match gbl_fb.default_block {
            Some(v) => {
                responder.send_var_info(DEFAULT_BLOCK, &[], snprintf!(val, "{:#x}", v)).await
            }
            _ => responder.send_var_info(DEFAULT_BLOCK, &[], snprintf!(val, "None")).await,
        }
    }
}

/// `fb_vars_api` generates a `fn fb_vars_get()` and `fn fb_vars_get_all()` helper API for all
/// registered Fastboot variables.
macro_rules! fb_vars_api {
    ($($vars:expr),+ $(,)?) => {
        /// Gets a Fastboot variable.
        ///
        /// The macro simply generates `var.get()` calls for each variable. i.e.:
        ///
        ///   pub(crate) async fn fb_vars_get<'a, P, F>(
        ///       gbl_fb: &mut GblFastboot<...>,
        ///       name: &str,
        ///       args: Split<'_, char>,
        ///       out: &mut [u8],
        ///   ) -> Result<Option<usize>, CommandError> {
        ///       match ("version-bootloader", "1.0").get(gbl_fb, name, args, out).await? {
        ///           Some(v) => return Ok(Some(v)),
        ///           _ => {}
        ///       }
        ///
        ///       match BlockDevice {}.get(gbl_fb, name, args, out).await? {
        ///           Some(v) => return Ok(Some(v)),
        ///           _ => {}
        ///       }
        ///
        ///       Ok(None)
        ///   }
        pub(crate) async fn fb_vars_get<'a, P, F> (
            gbl_fb: &mut GblFastboot<'a, '_, '_, '_, impl GblOps<'a>, impl BufferPool, P, F>,
            name: &str,
            args: Split<'_, char>,
            out: &mut [u8],
        ) -> Result<Option<usize>, CommandError> {
            fb_vars_get_body!(gbl_fb, name, args.clone(), out, $($vars),*);
            Ok(None)
        }

        /// Gets all Fastboot variable values.
        ///
        /// The macro simply generates `var.get_all()` calls for each variable.
        ///
        ///   pub(crate) async fn fb_vars_get_all<'a, P, F>(
        ///       gbl_fb: &mut GblFastboot<...>,
        ///       responder: &mut impl VarInfoSender,
        ///   ) -> Result<(), CommandError> {
        ///       ("version-bootloader", "1.0").get_all(gbl_fb, responder).await?;
        ///       ("max-fetch-size", "0xffffffffffffffff").get_all(gbl_fb, responder).await?;
        ///       BlockDevice {}.get_all(gbl_fb, responder).await?;
        ///       Partition {}.get_all(gbl_fb, responder).await?;
        ///       Ok(())
        ///   }
        pub(crate) async fn fb_vars_get_all<'a, P, F>(
            gbl_fb: &mut GblFastboot<'a, '_, '_, '_, impl GblOps<'a>, impl BufferPool, P, F>,
            responder: &mut impl VarInfoSender,
        ) -> Result<(), CommandError> {
            fb_vars_get_all_body!(gbl_fb, responder, $($vars),*);
            Ok(())
        }
    }
}

// `fb_vars_get_body` generates the body for `fn fb_vars_get()`
macro_rules! fb_vars_get_body {
    ($gbl_fb:expr, $name:expr, $args:expr, $out:expr, $var:expr) => {
        match $var.get($gbl_fb, $name, $args, $out).await? {
            Some(v) => return Ok(Some(v)),
            _ => {}
        }
    };
    ($gbl_fb:expr, $name:expr, $args:expr, $out:expr, $var:expr, $($remains:expr),+ $(,)?) => {
        fb_vars_get_body!($gbl_fb, $name, $args, $out, $var);
        fb_vars_get_body!($gbl_fb, $name, $args, $out, $($remains),*)
    };
}

// `fb_vars_get_all_body` generates the body for `fn fb_vars_get_all()`
macro_rules! fb_vars_get_all_body {
    ($gbl_fb:expr, $responder:expr, $var:expr) => {
        $var.get_all($gbl_fb, $responder).await?
    };
    ($gbl_fb:expr, $responder:expr, $var:expr, $($remains:expr),+ $(,)?) => {
        fb_vars_get_all_body!($gbl_fb, $responder, $var);
        fb_vars_get_all_body!($gbl_fb, $responder, $($remains),*)
    };
}

fb_vars_api! {
    ("version-bootloader", "1.0"),
    // GBL Fastboot can internally handle uploading in batches, thus there is no limit on
    // max-fetch-size.
    ("max-fetch-size", "0xffffffffffffffff"),
    BlockDevice {},
    DefaultBlock {},
    Partition {},
}
