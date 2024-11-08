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

use crate::fastboot::PinFutContainerTyped;
use crate::{
    fastboot::{BufferPool, GblFastboot},
    GblOps,
};
use core::fmt::Write;
use core::future::Future;
use core::str::{from_utf8, Split};
use fastboot::{next_arg, next_arg_u64, snprintf, CommandResult, FormattedBytes, VarInfoSender};

impl<'a: 'c, 'b: 'c, 'c, 'd, G, B, P, F> GblFastboot<'a, 'b, 'c, 'd, G, B, P, F>
where
    G: GblOps<'a>,
    B: BufferPool,
    F: Future<Output = ()> + 'c,
    P: PinFutContainerTyped<'c, F>,
{
    const VERSION_BOOTLOADER: &'static str = "version-bootloader";
    const VERSION_BOOTLOADER_VAL: &'static str = "1.0";

    const MAX_FETCH_SIZE: &'static str = "max-fetch-size";
    const MAX_FETCH_SIZE_VAL: &'static str = "0xffffffffffffffff";

    /// Entry point for "fastboot getvar <variable>..."
    pub(crate) fn get_var_internal<'s>(
        &mut self,
        name: &str,
        args: Split<'_, char>,
        out: &'s mut [u8],
    ) -> CommandResult<&'s str> {
        Ok(match name {
            Self::VERSION_BOOTLOADER => snprintf!(out, "{}", Self::VERSION_BOOTLOADER_VAL),
            Self::MAX_FETCH_SIZE => snprintf!(out, "{}", Self::MAX_FETCH_SIZE_VAL),
            Self::PARTITION_SIZE => self.get_var_partition_size(args, out)?,
            Self::PARTITION_TYPE => self.get_var_partition_type(args, out)?,
            Self::BLOCK_DEVICE => self.get_var_block_device(args, out)?,
            Self::DEFAULT_BLOCK => self.get_var_default_block(out)?,
            _ => Err("Not found")?,
        })
    }

    /// Entry point for "fastboot getvar all..."
    pub(crate) async fn get_var_all_internal(
        &mut self,
        send: &mut impl VarInfoSender,
    ) -> CommandResult<()> {
        send.send_var_info(Self::VERSION_BOOTLOADER, &[], Self::VERSION_BOOTLOADER_VAL).await?;
        send.send_var_info(Self::MAX_FETCH_SIZE, &[], Self::MAX_FETCH_SIZE_VAL).await?;
        self.get_all_block_device(send).await?;
        let mut buf = [0u8; 32];
        send.send_var_info(Self::DEFAULT_BLOCK, &[], self.get_var_default_block(&mut buf)?).await?;
        self.get_all_partition_size_type(send).await
    }

    const PARTITION_SIZE: &'static str = "partition-size";
    const PARTITION_TYPE: &'static str = "partition-type";

    /// "fastboot getvar partition-size"
    fn get_var_partition_size<'s>(
        &mut self,
        mut args: Split<'_, char>,
        out: &'s mut [u8],
    ) -> CommandResult<&'s str> {
        let (_, _, _, sz) = self.parse_partition(args.next().ok_or("Missing var")?)?;
        Ok(snprintf!(out, "{:#x}", sz))
    }

    /// "fastboot getvar partition-type"
    fn get_var_partition_type<'s>(
        &mut self,
        mut args: Split<'_, char>,
        out: &'s mut [u8],
    ) -> CommandResult<&'s str> {
        self.parse_partition(args.next().ok_or("Missing var")?)?;
        Ok(snprintf!(out, "raw"))
    }

    /// Gets all "partition-size/partition-type"
    async fn get_all_partition_size_type(
        &mut self,
        responder: &mut impl VarInfoSender,
    ) -> CommandResult<()> {
        // Though any sub range of a GPT partition or raw block counts as a partition in GBL
        // Fastboot, for "getvar all" we only enumerate whole range GPT partitions.
        let partitions = self.gbl_ops.partitions()?;
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
                    .send_var_info(Self::PARTITION_SIZE, &[part], snprintf!(size_str, "{:#x}", sz))
                    .await?;
                // Image type is not supported yet.
                responder
                    .send_var_info(Self::PARTITION_TYPE, &[part], snprintf!(size_str, "raw"))
                    .await?;
            }
        }
        Ok(())
    }

    const BLOCK_DEVICE: &'static str = "block-device";
    const TOTAL_BLOCKS: &'static str = "total-blocks";
    const BLOCK_SIZE: &'static str = "block-size";
    const BLOCK_DEVICE_STATUS: &'static str = "status";

    /// Block device related information.
    ///
    /// `fastboot getvar block-device:<id>:total-blocks`
    /// `fastboot getvar block-device:<id>:block-size`
    /// `fastboot getvar block-device:<id>:status`
    fn get_var_block_device<'s>(
        &mut self,
        mut args: Split<'_, char>,
        out: &'s mut [u8],
    ) -> CommandResult<&'s str> {
        let id = next_arg_u64(&mut args)?.ok_or("Missing block device ID")?;
        let id = usize::try_from(id)?;
        let val_type = next_arg(&mut args).ok_or("Missing value type")?;
        let blk = &self.gbl_ops.partitions()?[id];
        let info = blk.block_info();
        Ok(match val_type {
            Self::TOTAL_BLOCKS => snprintf!(out, "{:#x}", info.num_blocks),
            Self::BLOCK_SIZE => snprintf!(out, "{:#x}", info.block_size),
            Self::BLOCK_DEVICE_STATUS => {
                snprintf!(out, "{}", blk.status().to_str())
            }
            _ => return Err("Invalid type".into()),
        })
    }

    /// Gets all "block-device" variables
    async fn get_all_block_device(
        &mut self,
        responder: &mut impl VarInfoSender,
    ) -> CommandResult<()> {
        let mut val = [0u8; 32];
        for (idx, blk) in self.gbl_ops.partitions()?.iter().enumerate() {
            let mut id_str = [0u8; 32];
            let id = snprintf!(id_str, "{:x}", idx);
            let info = blk.block_info();
            responder
                .send_var_info(
                    Self::BLOCK_DEVICE,
                    &[id, Self::TOTAL_BLOCKS],
                    snprintf!(val, "{:#x}", info.num_blocks),
                )
                .await?;
            responder
                .send_var_info(
                    Self::BLOCK_DEVICE,
                    &[id, Self::BLOCK_SIZE],
                    snprintf!(val, "{:#x}", info.block_size),
                )
                .await?;
            responder
                .send_var_info(
                    Self::BLOCK_DEVICE,
                    &[id, Self::BLOCK_DEVICE_STATUS],
                    snprintf!(val, "{}", blk.status().to_str()),
                )
                .await?;
        }
        Ok(())
    }

    const DEFAULT_BLOCK: &'static str = "gbl-default-block";

    /// "fastboot getvar gbl-default-block"
    fn get_var_default_block<'s>(&mut self, out: &'s mut [u8]) -> CommandResult<&'s str> {
        Ok(match self.default_block {
            Some(v) => snprintf!(out, "{:#x}", v),
            None => snprintf!(out, "None"),
        })
    }
}
