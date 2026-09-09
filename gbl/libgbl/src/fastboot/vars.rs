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
    android_boot::hasher::{Hasher, Sha256},
    fastboot::{BufferPool, GblFastboot, PinFutContainerTyped, ResolveMode},
    gbl_println,
    partition::{check_part_unique, split_partition_suffix, Partition, RawName},
    slots::{Bootability, Slot},
    GblOps,
};
use core::{
    ffi::CStr,
    future::Future,
    mem::size_of,
    ops::{Deref, DerefMut},
    str::from_utf8,
};
use fastboot::{CommandError, CommandResult, VarInfoSender};
use gbl_async::{block_on, select, yield_now};
use gbl_storage::BlockIo;
use libbuild_number::BUILD_NUMBER;
use liberror::Error;
use liblp::LpMetadataPartition;
use libutils::{next_arg, snprintf, FromHexStr};
use zerocopy::{error::SizeError, FromBytes, IntoBytes, Unaligned};

const MAX_DOWNLOAD_SIZE: &'static str = "max-download-size";

const IS_USERSPACE: &'static str = "is-userspace";
const VERSION_BOOTLOADER: &'static str = "version-bootloader";

const SLOT_COUNT: &'static str = "slot-count";
const CURRENT_SLOT: &'static str = "current-slot";
const SLOT_SUCCESSFUL: &'static str = "slot-successful";
const SLOT_UNBOOTABLE: &'static str = "slot-unbootable";
const SLOT_RETRY_COUNT: &'static str = "slot-retry-count";
const HAS_SLOT: &'static str = "has-slot";

const MAX_FETCH_SIZE: &'static str = "max-fetch-size";
// Limited by DATA message which only allows 8 hex digits.
// Additionally fastboot upstream parses this value as int, so we only have 31 bits.
// Defensively capped to 512 MiB (block-aligned) to avoid scratch buffer copying
// in libstorage, provide regular progress reporting during `fastboot fetch`, and
// guard against buggy firmware that misreports IoAlign.
const MAX_FETCH_SIZE_VAL: &'static str = "0x20000000";

const PARTITION_SIZE: &'static str = "partition-size";
const PARTITION_TYPE: &'static str = "partition-type";
const PARTITION_GUID: &'static str = "partition-guid";
const PARTITION_START: &'static str = "partition-start";

const BLOCK_DEVICE: &'static str = "block-device";
const TOTAL_BLOCKS: &'static str = "total-blocks";
const BLOCK_SIZE: &'static str = "block-size";

const DEFAULT_BLOCK: &'static str = "gbl-default-block";

const UNLOCKED: &'static str = "unlocked";
const UNLOCKED_CRITICAL: &'static str = "unlocked-critical";

const STREAM_SEGMENT_SIZE: &'static str = "stream-segment-size";

pub(crate) const GETVAR_ALL_FILTER: &'static [&'static str] = &[
    IS_USERSPACE,
    VERSION_BOOTLOADER,
    SLOT_COUNT,
    CURRENT_SLOT,
    SLOT_SUCCESSFUL,
    SLOT_UNBOOTABLE,
    SLOT_RETRY_COUNT,
    HAS_SLOT,
    PARTITION_START,
    MAX_FETCH_SIZE,
    PARTITION_SIZE,
    PARTITION_TYPE,
    PARTITION_GUID,
    BLOCK_DEVICE,
    DEFAULT_BLOCK,
    MAX_DOWNLOAD_SIZE,
    UNLOCKED,
    UNLOCKED_CRITICAL,
    STREAM_SEGMENT_SIZE,
];

#[derive(FromBytes, IntoBytes, Unaligned)]
#[repr(packed)]
struct PartHasSlot(RawName, u8);

/// Query result of `getvar has-slot`.
///
/// If `PartHasSlot(part, NO)`, then `part` is the name of an unslotted partition.
/// If `PartHasSlot(name, YES)`, then `name` is the name-without-suffix of a slotted partition.
impl PartHasSlot {
    const NO: u8 = 0;
    const YES: u8 = 1;
}

/// Extracts the partition name from `LpMetadataPartition`.
///
/// # Safety
/// The `partition.name` field is `[i8; 36]` (C char array). We reinterpret it as `[u8; 36]`
/// to parse as UTF-8. This is safe because we only read the bytes and the representation
/// of `i8` and `u8` is identical for ASCII characters used in partition names.
fn lp_partition_name(partition: &LpMetadataPartition) -> Option<&str> {
    let name_bytes: &[u8] = unsafe {
        core::slice::from_raw_parts(partition.name.as_ptr() as *const u8, partition.name.len())
    };
    let end = name_bytes.iter().position(|&b| b == 0).unwrap_or(name_bytes.len());
    core::str::from_utf8(&name_bytes[..end]).ok()
}

/// A vector backed by a borrowed slice.
struct SliceVec<'a, T> {
    buf: &'a mut [T],
    len: usize,
}

impl<'a, T> SliceVec<'a, T> {
    fn new(buf: &'a mut [T]) -> Self {
        Self { buf, len: 0 }
    }

    fn push(&mut self, v: T) {
        if self.len >= self.buf.len() {
            panic!("SliceVec capacity exceeded: cap={}", self.buf.len());
        }
        self.buf[self.len] = v;
        self.len += 1;
    }
}

impl<T> Deref for SliceVec<'_, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        &self.buf[..self.len]
    }
}

impl<T> DerefMut for SliceVec<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.buf[..self.len]
    }
}

impl<'a, T> From<SliceVec<'a, T>> for &'a [T] {
    fn from(v: SliceVec<'a, T>) -> Self {
        &v.buf[..v.len]
    }
}

struct FastbootSlotInfo {
    successful: &'static str,
    unbootable: &'static str,
    retry_count: usize,
}

impl From<Slot> for FastbootSlotInfo {
    fn from(slot: Slot) -> Self {
        match slot.bootability {
            Bootability::Successful(t) => {
                FastbootSlotInfo { successful: "yes", unbootable: "no", retry_count: t.0 }
            }
            Bootability::Unbootable(_) => {
                FastbootSlotInfo { successful: "no", unbootable: "yes", retry_count: 0 }
            }
            Bootability::Retriable(t) => {
                FastbootSlotInfo { successful: "no", unbootable: "no", retry_count: t.0 }
            }
        }
    }
}

/// Returns "yes" if true, "no" if false.
fn yes_no_str(value: bool) -> &'static str {
    match value {
        true => "yes",
        false => "no",
    }
}

// See definition of [GblFastboot] for docs on lifetimes and generics parameters.
impl<'a: 'c, 'b: 'c, 'c, 'd, G, B, P2, T, P, C, F> GblFastboot<'a, 'b, 'c, 'd, G, B, P2, T, P, C, F>
where
    G: GblOps<'a>,
    B: BlockIo,
    P2: BufferPool,
    T: DerefMut<Target = [u8]>,
    P: BufferPool,
    C: PinFutContainerTyped<'c, F>,
    F: Future<Output = ()> + 'c,
{
    /// Entry point for "fastboot getvar <variable>..."
    pub(crate) async fn get_var_internal<'s, 't>(
        &mut self,
        name: &CStr,
        args: impl Iterator<Item = &'t CStr> + Clone,
        out: &'s mut [u8],
    ) -> CommandResult<&'s str> {
        let args_str = args.clone().map(|v| v.to_str());
        // Checks that all arguments are valid str first.
        args_str.clone().find(|v| v.is_err()).unwrap_or(Ok(""))?;
        let args_str = args_str.map(|v| v.unwrap());
        Ok(match name.to_str()? {
            MAX_DOWNLOAD_SIZE => snprintf!(out, "{:#x}", self.max_download_size().await),
            IS_USERSPACE => snprintf!(out, "no"),
            VERSION_BOOTLOADER => snprintf!(out, "gbl.{}", BUILD_NUMBER),
            SLOT_COUNT => snprintf!(out, "{}", self.gbl_ops.get_slot_count()?),
            CURRENT_SLOT => snprintf!(out, "{}", self.gbl_ops.get_current_slot()?.suffix.as_char()),
            SLOT_SUCCESSFUL => {
                snprintf!(out, "{}", self.get_fastboot_slot_info(args_str)?.successful)
            }
            SLOT_UNBOOTABLE => {
                snprintf!(out, "{}", self.get_fastboot_slot_info(args_str)?.unbootable)
            }
            SLOT_RETRY_COUNT => {
                snprintf!(out, "{}", self.get_fastboot_slot_info(args_str)?.retry_count)
            }
            HAS_SLOT => self.get_var_has_slot(args_str, out).await?,
            MAX_FETCH_SIZE => snprintf!(out, "{}", MAX_FETCH_SIZE_VAL),
            PARTITION_START => self.get_var_partition_start(args_str, out)?,
            PARTITION_SIZE => self.get_var_partition_size(args_str, out)?,
            PARTITION_TYPE => self.get_var_partition_type(args_str, out)?,
            PARTITION_GUID => self.get_var_partition_guid(args_str, out)?,
            STREAM_SEGMENT_SIZE => self.get_var_stream_segment_size(out)?,
            BLOCK_DEVICE => self.get_var_block_device(args_str, out)?,
            DEFAULT_BLOCK => self.get_var_default_block(out)?,
            UNLOCKED => self.get_var_unlocked(fastboot::LockType::Device, out)?,
            UNLOCKED_CRITICAL => self.get_var_unlocked(fastboot::LockType::Critical, out)?,
            _ => {
                let sz = self.gbl_ops.fastboot_variable(name, args, out)?;
                from_utf8(out.get(..sz).ok_or("Invalid variable value size")?)?
            }
        })
    }

    /// Entry point for "fastboot getvar all..."
    ///
    /// TODO(b/465769208): Reuse code between `getvar` and `getvar all`.
    pub(crate) async fn get_var_all_internal(
        &mut self,
        send: &mut impl VarInfoSender,
    ) -> CommandResult<()> {
        let mut buf = [0u8; 32];
        let dl_sz = snprintf!(buf, "{:#x}", self.max_download_size().await);
        send.send_var_info(MAX_DOWNLOAD_SIZE, [], dl_sz).await?;
        send.send_var_info(IS_USERSPACE, [], "no").await?;
        send.send_var_info(VERSION_BOOTLOADER, [], snprintf!(buf, "gbl.{BUILD_NUMBER}")).await?;
        match self.gbl_ops.get_slot_count() {
            Ok(slot_count) => {
                send.send_var_info(SLOT_COUNT, [], snprintf!(buf, "{slot_count}")).await?;

                // Variable may be optional. Continues instead of erroring out.
                match self.gbl_ops.get_current_slot().map(|v| v.suffix.as_char()) {
                    Ok(v) => send.send_var_info(CURRENT_SLOT, [], snprintf!(buf, "{v}")).await?,
                    Err(e) => gbl_println!(self.gbl_ops, "Failed to get current_slot {e}"),
                };

                for idx in 0..slot_count {
                    // Variable may be optional. Continues instead of erroring out.
                    let Ok(slot) = self.gbl_ops.get_slot_info(idx).inspect_err(|e| {
                        gbl_println!(self.gbl_ops, "Failed to get slot_info for slot {idx}, {e}");
                    }) else {
                        continue;
                    };
                    let FastbootSlotInfo { successful, unbootable, retry_count } = slot.into();
                    let mut suffix_buf = [0u8; 4];
                    let suffix = snprintf!(suffix_buf, "{}", slot.suffix.as_char());
                    send.send_var_info(SLOT_SUCCESSFUL, [suffix], successful).await?;
                    send.send_var_info(SLOT_UNBOOTABLE, [suffix], unbootable).await?;
                    send.send_var_info(SLOT_RETRY_COUNT, [suffix], snprintf!(buf, "{retry_count}"))
                        .await?;
                }
                self.get_all_partition_has_slot(send).await?;
            }
            Err(e) => gbl_println!(
                self.gbl_ops,
                "Slotting is not supported, failed to get {SLOT_COUNT}: {e}. Slot-related \
                fastboot variables cannot be provided."
            ),
        }
        send.send_var_info(MAX_FETCH_SIZE, [], MAX_FETCH_SIZE_VAL).await?;
        self.get_all_block_device(send).await?;
        send.send_var_info(DEFAULT_BLOCK, [], self.get_var_default_block(&mut buf)?).await?;
        self.get_all_partition_vars(send).await?;

        send.send_var_info(STREAM_SEGMENT_SIZE, [], self.get_var_stream_segment_size(&mut buf)?)
            .await?;

        match self.gbl_ops.avb_read_device_status() {
            Ok(device_status) => {
                send.send_var_info(UNLOCKED, [], yes_no_str(device_status.is_unlocked)).await?;
                send.send_var_info(
                    UNLOCKED_CRITICAL,
                    [],
                    yes_no_str(device_status.is_unlocked_critical),
                )
                .await?;
            }
            Err(e) => gbl_println!(self.gbl_ops, "failed to read lock state: {e}"),
        };

        // Gets platform specific variables
        let tasks = self.tasks();
        let _ = self.gbl_ops.fastboot_visit_all_variables(|ops, args, val| {
            if let Some((name, args)) = args.split_first_chunk::<1>() {
                let name = name[0].to_str().unwrap_or("?");
                // Needs to split because the interface allows backend to pass ':' concatenated
                // string as a whole.
                let var = name.split(':').next().unwrap_or(name);
                if GETVAR_ALL_FILTER.iter().find(|v| **v == var).is_some() {
                    // Its possible that backend might have its own special non-gpt/raw block
                    // partitions (i.e. virtual) and therefore needs to expose
                    // `partition-size/partition-type` vars for them. If this will be the case,
                    // allow `partition-size/partition-type` when partition doesn't exist.
                    gbl_println!(ops, "Variable {var:?} is reserved by GBL.");
                    return;
                }
                let args = args.iter().map(|v| v.to_str().unwrap_or("?"));
                let val = val.to_str().unwrap_or("?");
                // Manually polls async tasks so that we can still get parallelism while
                // running in the context of backend.
                let _ = block_on(select(send.send_var_info(name, args, val), async {
                    loop {
                        tasks.borrow_mut().poll_all();
                        yield_now().await;
                    }
                }))
                .0
                .transpose() // Option<Result<>> -> Result<Option<>>
                .inspect_err(|e| gbl_println!(ops, "Failed to get platform vars: {e}"));
            }
        });
        Ok(())
    }

    /// Gets the max-download-size variable.
    pub(crate) async fn max_download_size(&mut self) -> usize {
        self.get_download_buffer().await.len()
    }

    /// Parses and finds the size of the given partition.
    pub(crate) fn partition_size<'s>(&mut self, part: &'s str) -> CommandResult<u64> {
        let (part, blk_id, off, sz) = self.parse_partition_arg(part)?;
        // If the user just gives the partition base name, resolve to the current slot.
        let (_, parts) = self.resolve_slotted_partitions(part, blk_id, ResolveMode::CurrentSlot)?;
        // Slotted partition-size only make sense if they are all the same. Because it may be used
        // to copy AVB footer.
        for (_, p) in &parts[1..] {
            if p.size()? != parts[0].1.size()? {
                return Err(format_args!(
                    "{} and {} has different partition sizes",
                    p.name().unwrap_or("?"),
                    parts[0].1.name().unwrap_or("?")
                )
                .into());
            }
        }
        let (start, end) = parts[0].1.sub(off, sz)?;
        Ok(end - start)
    }

    /// "fastboot getvar partition-size"
    fn get_var_partition_size<'s, 't>(
        &mut self,
        mut args: impl Iterator<Item = &'t str> + Clone,
        out: &'s mut [u8],
    ) -> CommandResult<&'s str> {
        Ok(snprintf!(out, "{:#x}", self.partition_size(args.next().ok_or("Missing partition")?)?))
    }

    /// "fastboot getvar partition-type"
    fn get_var_partition_type<'s, 't>(
        &mut self,
        mut args: impl Iterator<Item = &'t str> + Clone,
        out: &'s mut [u8],
    ) -> CommandResult<&'s str> {
        let part = args.next().ok_or("Missing partition")?;
        let part = self.parse_partition_arg(part)?.0.ok_or("Missing partition")?;
        match check_part_unique(self.disks, part) {
            Ok(_) | Err(Error::NotUnique) => {
                let part_type = self.gbl_ops.fastboot_get_partition_type(part)?;
                Ok(snprintf!(out, "{part_type}"))
            }
            Err(e) => Err(e.into()),
        }
    }

    /// "fastboot getvar partition-guid"
    fn get_var_partition_guid<'s, 't>(
        &mut self,
        mut args: impl Iterator<Item = &'t str> + Clone,
        out: &'s mut [u8],
    ) -> CommandResult<&'s str> {
        let (part, blk_id, _, _) =
            self.parse_partition_arg(args.next().ok_or("Missing partition")?)?;
        let (_, ptn) = self.find_partition(part, blk_id)?;

        match ptn {
            Partition::Gpt(gpt_partition) => {
                Ok(snprintf!(out, "{}", gpt_partition.gpt_entry().guid))
            }
            _ => Err("Not a GPT partition".into()),
        }
    }

    /// "fastboot getvar partition-start"
    fn get_var_partition_start<'s, 't>(
        &mut self,
        mut args: impl Iterator<Item = &'t str> + Clone,
        out: &'s mut [u8],
    ) -> CommandResult<&'s str> {
        let (_, ptn) = args
            .next()
            .ok_or(CommandError::from("Missing partition"))
            .and_then(|arg| self.parse_partition_arg(arg))
            .and_then(|(part, blk_id, _, _)| {
                self.find_partition(part, blk_id).map_err(CommandError::from)
            })?;

        Ok(snprintf!(out, "{:#x}", ptn.absolute_range()?.0))
    }

    /// Gets all "partition-size/partition-type/partition-guid/partition-start"
    async fn get_all_partition_vars(
        &mut self,
        responder: &mut impl VarInfoSender,
    ) -> CommandResult<()> {
        // Though any sub range of a GPT partition or raw block counts as a partition in GBL
        // Fastboot, for "getvar all" we only enumerate whole range GPT partitions.
        let disks = self.disks;
        // Allocates 36 bytes to fit partition GUID.
        let mut str_buf = [0u8; 36];
        for (idx, blk) in disks.iter().enumerate() {
            for ptn_idx in 0..blk.num_partitions().unwrap_or(0) {
                let ptn = blk.get_partition_by_idx(ptn_idx)?;
                let sz: u64 = ptn.size()?;
                let part = ptn.name()?;
                let part_type = self.gbl_ops.fastboot_get_partition_type(part)?;

                // Assumes max partition name length of 72 plus max u64 hex string length 18.
                let mut part_id_buf = [0u8; 128];
                // If partition is not unique, append block ID suffix.
                let part = match crate::partition::check_part_unique(disks, part) {
                    Ok(_) => snprintf!(part_id_buf, "{}", part),
                    Err(_) => snprintf!(part_id_buf, "{}/{:x}", part, idx),
                };
                responder
                    .send_var_info(
                        PARTITION_START,
                        [part],
                        snprintf!(str_buf, "{:#x}", ptn.absolute_range()?.0),
                    )
                    .await?;
                responder
                    .send_var_info(PARTITION_SIZE, [part], snprintf!(str_buf, "{:#x}", sz))
                    .await?;
                responder
                    .send_var_info(PARTITION_TYPE, [part], snprintf!(str_buf, "{part_type}"))
                    .await?;
                if let Partition::Gpt(gpt_partition) = &ptn {
                    let guid = gpt_partition.gpt_entry().guid;
                    responder
                        .send_var_info(PARTITION_GUID, [part], snprintf!(str_buf, "{}", guid))
                        .await?;
                }
            }
        }
        Ok(())
    }

    /// Block device related information.
    ///
    /// `fastboot getvar block-device:<id>:total-blocks`
    /// `fastboot getvar block-device:<id>:block-size`
    /// `fastboot getvar block-device:<id>:status`
    fn get_var_block_device<'s, 't>(
        &mut self,
        mut args: impl Iterator<Item = &'t str> + Clone,
        out: &'s mut [u8],
    ) -> CommandResult<&'s str> {
        let id: usize = FromHexStr::try_parse_next(&mut args)
            .map_err(|_| CommandError::from("Missing block device ID"))?;
        let val_type = next_arg(&mut args).ok_or("Missing value type")?;
        let blk = &self.disks[id];
        let info = blk.block_info();
        Ok(match val_type {
            TOTAL_BLOCKS => snprintf!(out, "{:#x}", info.num_blocks),
            BLOCK_SIZE => snprintf!(out, "{:#x}", info.block_size),
            _ => return Err("Invalid type".into()),
        })
    }

    /// Gets all "block-device" variables.
    async fn get_all_block_device(
        &mut self,
        responder: &mut impl VarInfoSender,
    ) -> CommandResult<()> {
        let mut val = [0u8; 32];
        for (idx, blk) in self.gbl_ops.disks().iter().enumerate() {
            let mut id_str = [0u8; 32];
            let id = snprintf!(id_str, "{:x}", idx);
            let info = blk.block_info();
            responder
                .send_var_info(
                    BLOCK_DEVICE,
                    [id, TOTAL_BLOCKS],
                    snprintf!(val, "{:#x}", info.num_blocks),
                )
                .await?;
            responder
                .send_var_info(
                    BLOCK_DEVICE,
                    [id, BLOCK_SIZE],
                    snprintf!(val, "{:#x}", info.block_size),
                )
                .await?;
        }
        Ok(())
    }

    /// "fastboot getvar gbl-default-block"
    fn get_var_default_block<'s>(&mut self, out: &'s mut [u8]) -> CommandResult<&'s str> {
        Ok(match self.default_block {
            Some(v) => snprintf!(out, "{:#x}", v),
            None => snprintf!(out, "None"),
        })
    }

    /// "fastboot getvar stream-segment-size"
    fn get_var_stream_segment_size<'s>(&mut self, out: &'s mut [u8]) -> CommandResult<&'s str> {
        const DEFAULT_SEGMENT_SIZE: u64 = 4096;
        let segment_size_bytes = self
            .disks
            .iter()
            .map(|d| d.block_info().block_size * d.block_info().erase_blocks_num)
            .chain([DEFAULT_SEGMENT_SIZE].into_iter())
            .max()
            .unwrap_or(DEFAULT_SEGMENT_SIZE);

        Ok(snprintf!(out, "{:#x}", segment_size_bytes))
    }

    /// "fastboot getvar unlocked" and "fastboot getvar unlocked-critical"
    fn get_var_unlocked<'s>(
        &mut self,
        lock_type: fastboot::LockType,
        out: &'s mut [u8],
    ) -> CommandResult<&'s str> {
        let status =
            self.gbl_ops.avb_read_device_status().map_err(|_| "failed to read lock state")?;
        let unlocked = match lock_type {
            fastboot::LockType::Device => status.is_unlocked,
            fastboot::LockType::Critical => status.is_unlocked_critical,
        };
        Ok(snprintf!(out, "{}", yes_no_str(unlocked)))
    }

    /// "fastboot getvar slot-successful:<slot-suffix>"
    /// "fastboot getvar slot-unbootable:<slot-suffix>"
    /// "fastboot getvar slot-retry-count:<slot-suffix>"
    fn get_fastboot_slot_info<'t>(
        &mut self,
        mut args: impl Iterator<Item = &'t str> + Clone,
    ) -> CommandResult<FastbootSlotInfo> {
        let suffix_str = args.next().ok_or("Missing slot suffix")?;
        if suffix_str.chars().count() != 1 {
            return Err("Slot suffix must be a single character".into());
        }
        let suffix = suffix_str.chars().next().ok_or("Invalid slot")?;
        let slot = self
            .slots_iter()?
            .find(|slot| slot.is_ok() && slot.unwrap().suffix.as_char() == suffix)
            .ok_or("Invalid slot")??;
        Ok(slot.into())
    }

    /// Builds a lookup table that tells us whether a partition has slot or not.
    ///
    /// Returns a `&[PartHasSlot]`.
    async fn get_part_has_slot_table(&mut self) -> Result<&[PartHasSlot], Error> {
        let default_slot = self.slots_iter()?.next().ok_or("Missing slot info")??.suffix.as_char();

        let dynamic_parts = self.get_dynamic_partition_names().await.unwrap_or_default();
        let dynamic_partition_count = dynamic_parts.len();

        // The table size could theoretically be as large as the number of total partitions, so
        // stack allocation would be insufficient. We instead dynamically allocate a memory slice
        // on the boot_buffer scratch pad.
        let partition_count: usize =
            self.disks.iter().map(|b| b.num_partitions().unwrap_or_default()).sum();
        let total_partitions = partition_count + dynamic_partition_count;
        let buf = <[PartHasSlot]>::mut_from_prefix_with_elems(
            self.data.boot_buffer.scratch(),
            total_partitions,
        )
        .map_err(|e| match e.into() {
            SizeError { .. } => {
                Error::BufferTooSmall(Some(total_partitions * size_of::<PartHasSlot>()))
            }
        })?
        .0;
        let mut part_has_slot = SliceVec::new(buf);
        let gpt_parts = self.disks.iter().flat_map(|blk| {
            (0..blk.num_partitions().unwrap_or_default()).filter_map(move |idx| {
                let part = blk.get_partition_by_idx(idx).ok()?;
                let name = part.name().ok()?;
                RawName::try_from(name).ok()
            })
        });

        let all_parts = gpt_parts.chain(dynamic_parts.into_iter());
        for raw_part in all_parts {
            let part_name = raw_part.to_str();
            match split_partition_suffix(part_name) {
                None => match part_has_slot.iter().position(|p| p.0.to_str() == part_name) {
                    None => {
                        if let Ok(raw_name) = part_name.try_into() {
                            part_has_slot.push(PartHasSlot(raw_name, PartHasSlot::NO));
                        }
                    }
                    Some(pos) => part_has_slot[pos].1 = PartHasSlot::NO,
                },
                Some((name, suffix)) if suffix == default_slot => {
                    if part_has_slot.iter().all(|p| p.0.to_str() != name) {
                        if let Ok(base_name) = name.try_into() {
                            part_has_slot.push(PartHasSlot(base_name, PartHasSlot::YES));
                        }
                    }
                }
                _ => {}
            }
        }

        Ok(part_has_slot.into())
    }

    /// Reads the super partition and extracts dynamic partition names from LP metadata.
    ///
    /// Returns an empty list if super partition doesn't exist or metadata parsing fails.
    /// TODO(b/502083075) Add unit tests to check dynamic partitions names in super.
    async fn get_dynamic_partition_names(
        &mut self,
    ) -> Result<arrayvec::ArrayVec<RawName, 32>, Error> {
        // 256KB is sufficient to read LP geometry + metadata (primary + backup).
        const SUPER_METADATA_SIZE: usize = 256 * 1024;
        let mut result = arrayvec::ArrayVec::new();

        let Ok((blk_idx, _)) = check_part_unique(self.disks, "super") else {
            return Ok(result);
        };

        let (buffer, _) = <[u8]>::mut_from_prefix_with_elems(
            self.data.boot_buffer.scratch(),
            SUPER_METADATA_SIZE,
        )
        .map_err(|e| match e.into() {
            SizeError { .. } => Error::BufferTooSmall(Some(SUPER_METADATA_SIZE)),
        })?;

        let disk = &self.disks[blk_idx];

        let io;
        loop {
            match disk.partition_io(Some("super")) {
                Ok(pio) => {
                    io = pio;
                    break;
                }
                Err(Error::NotReady) => {
                    // Disk is busy, yield and retry.
                    yield_now().await;
                }
                Err(e) => {
                    gbl_println!(self.gbl_ops, "Failed to get partition_io for super: {e}");
                    return Ok(result);
                }
            }
        }

        if io.read(0, &mut buffer[..]).await.is_err() {
            gbl_println!(self.gbl_ops, "Failed to read super partition");
            return Ok(result);
        }

        let mut hasher = Sha256::new();
        let Ok(metadata) = liblp::parse(buffer, &mut hasher) else {
            return Ok(result);
        };

        for raw_name in metadata
            .partitions
            .iter()
            .filter_map(lp_partition_name)
            .filter_map(|name| RawName::try_from(name).ok())
        {
            if result.try_push(raw_name).is_err() {
                gbl_println!(
                    self.gbl_ops,
                    "Warning: dynamic partition list truncated at {} entries, more partitions exist in super",
                    result.len()
                );
                break;
            }
        }

        Ok(result)
    }

    /// "fastboot getvar has-slot:<partition-name-without-slot-suffix>"
    async fn get_var_has_slot<'t, 's>(
        &mut self,
        mut args: impl Iterator<Item = &'t str> + Clone,
        out: &'s mut [u8],
    ) -> CommandResult<&'s str> {
        let part = args.next().ok_or("Missing partition")?;
        let has_slot = self
            .get_part_has_slot_table()
            .await?
            .iter()
            .find_map(
                |PartHasSlot(name, has_slot)| {
                    if name.to_str() == part {
                        Some(has_slot)
                    } else {
                        None
                    }
                },
            )
            .copied()
            .ok_or(Error::NotFound)?;
        Ok(snprintf!(out, "{}", if has_slot == PartHasSlot::NO { "no" } else { "yes" }))
    }

    /// Gets all "has-slot"
    async fn get_all_partition_has_slot(
        &mut self,
        responder: &mut impl VarInfoSender,
    ) -> CommandResult<()> {
        let res = self.get_part_has_slot_table().await;
        // Variable may be optional. Continues instead of erroring out.
        if let Some(e) = res.clone().err() {
            gbl_println!(self.gbl_ops, "Failed to get slot_info for partitions, {e}");
            return Ok(());
        }
        for PartHasSlot(part, has_slot) in res? {
            responder
                .send_var_info(
                    HAS_SLOT,
                    [part.to_str()],
                    if *has_slot == PartHasSlot::NO { "no" } else { "yes" },
                )
                .await?;
        }
        Ok(())
    }
}
