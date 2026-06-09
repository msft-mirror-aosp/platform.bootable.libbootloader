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

use alloc::{boxed::Box, vec::Vec};
use arrayvec::ArrayVec;
use bytes::buf::UninitSlice;
use core::cmp::max;
use efi::{
    efi_println,
    profiling::EfiProfileBackend,
    protocol::{
        block_io::BlockIoProtocol, block_io2::BlockIo2Protocol, device_path::DevicePathProtocol,
        erase_block::EraseBlockProtocol, Protocol,
    },
    EfiEntry,
};
use efi_types::{defs::EFI_TPL_APPLICATION, protocol::block_io::BlockIo as _, tpl::TplLocked};
use gbl_async::block_on;
use gbl_storage::{gpt_buffer_size, BlockInfo, BlockIo, Disk, Gpt, GPT_MAX_NUM_ENTRIES};
use liberror::Error;
use libgbl::partition::GblDisk;
use libprofile_macros::profile;
use safemath::SafeNum;

/// `EfiBlockDeviceIo` wraps an EFI `BlockIoProtocol` and optionally a `BlockIo2Protocol` and
/// implements the `BlockIo` interface.
///
/// `BlockIoProtocol` is always required and used for implementation of `read_blocks_sync` and
/// `write_blocks_sync`. When `BlockIo2Protocol` is provided, it will be used to implement
/// `read_blocks` and `write_blocks`, otherwise they fall back to `BlockIoProtocol`.
pub struct EfiBlockDeviceIo<'a> {
    block_io: Protocol<'a, BlockIoProtocol>,
    block_io2: Option<Protocol<'a, BlockIo2Protocol>>,
    erase: Option<Protocol<'a, EraseBlockProtocol>>,
    /// We don't currently support hot-plugging disks so we cache the media ID
    /// upon creation; if this media ever goes away, the APIs will start
    /// failing rather than trying to switch to a new ID.
    media_id: u32,
    block_info: BlockInfo,
}

// SAFETY:
// `read_blocks()` uses EFI protocol that guarantees to read exact number of blocks that were
// requested, or return error.
// For async `read_blocks_ex()` blocking wait guarantees that read finishes.
unsafe impl BlockIo for EfiBlockDeviceIo<'_> {
    fn info(&self) -> BlockInfo {
        self.block_info
    }

    async fn read_blocks<'a>(
        &self,
        blk_offset: u64,
        out: impl Into<&'a mut UninitSlice>,
    ) -> Result<(), Error> {
        match &self.block_io2 {
            Some(v) => v.read_blocks_ex(blk_offset, out).await,
            _ => {
                // SAFETY: `read_blocks()` will only initialize the data.
                let out = unsafe { out.into().as_uninit_slice_mut() };
                self.block_io.read_blocks(self.media_id, blk_offset, out).map_err(Into::into)
            }
        }
    }

    async fn write_blocks(&self, blk_offset: u64, data: &mut [u8]) -> Result<(), Error> {
        match &self.block_io2 {
            Some(v) => v.write_blocks_ex(blk_offset, data).await,
            _ => self.block_io.write_blocks(self.media_id, blk_offset, data).map_err(Into::into),
        }
    }

    async fn erase_blocks(&self, blk_off: u64, num_blks: u64) -> Result<(), Error> {
        let protocol = self.erase.as_ref().ok_or(Error::Unsupported)?;
        let block_info = self.info();
        let erase_block_size = block_info.erase_block_size()?;
        let lba = SafeNum::from(blk_off) * erase_block_size / block_info.block_size;
        let sz = SafeNum::from(num_blks) * erase_block_size;
        protocol.erase_blocks(self.media_id, lba.try_into()?, sz.try_into()?).await
    }

    fn read_blocks_sync<'a>(
        &self,
        blk_offset: u64,
        out: impl Into<&'a mut UninitSlice>,
    ) -> Result<(), Error> {
        // SAFETY: `read_blocks()` will only initialize the data.
        let out = unsafe { out.into().as_uninit_slice_mut() };
        Ok(self.block_io.read_blocks(self.media_id, blk_offset, out)?)
    }

    fn write_blocks_sync(&self, blk_offset: u64, data: &mut [u8]) -> Result<(), Error> {
        Ok(self.block_io.write_blocks(self.media_id, blk_offset, data)?)
    }

    async fn flush(&self) -> Result<(), Error> {
        let res = match &self.block_io2 {
            Some(v) => v.flush_blocks_ex().await,
            _ => self.block_io.flush_blocks().map_err(Into::into),
        };
        match res {
            Ok(()) | Err(Error::Unsupported) | Err(Error::NotFound) => Ok(()),
            Err(e) => Err(e),
        }
    }
}

/// The [GblDisk] type in the GBL EFI context.
pub type EfiGblDisk<'a> =
    GblDisk<Disk<EfiBlockDeviceIo<'a>, ArrayVec<Option<Box<[u8]>>, 2>>, Gpt<Vec<u8>>>;

/// Finds and returns all EFI devices supporting either EFI_BLOCK_IO or EFI_BLOCK_IO2 protocol.
#[profile(backend = EfiProfileBackend::new(efi_entry))]
pub fn find_block_devices(efi_entry: &EfiEntry) -> Result<Vec<EfiGblDisk<'_>>, Error> {
    let bs = efi_entry.system_table().boot_services();
    let block_dev_handles = bs.locate_handle_buffer_by_protocol::<BlockIoProtocol>()?;
    let mut gbl_disks = vec![];
    // TODO(b/452455989) Buffer size and capacity can be configurable using vendor path.
    let gpt_buffer_size = gpt_buffer_size(GPT_MAX_NUM_ENTRIES)?;
    for (idx, handle) in block_dev_handles.handles().iter().enumerate() {
        let block_io = bs.open_protocol::<BlockIoProtocol>(*handle).unwrap();
        // SAFETY: this code always executes at `EFI_TPL_APPLICATION`.
        let media = unsafe {
            block_io.with_lock::<EFI_TPL_APPLICATION, _>(efi_entry, || {
                // SAFETY: the protocol is locked while we access `media`, we
                // clone it here for safe access outside the critical section.
                block_io.media().unwrap().clone()
            })
        };
        if media.logical_partition {
            continue;
        }
        let open_disk = || -> Result<_, Error> {
            let block_io2 = bs.open_protocol::<BlockIo2Protocol>(*handle).ok();
            let erase = bs.open_protocol::<EraseBlockProtocol>(*handle).ok();
            let erase_blocks =
                erase.as_ref().map(|v| v.erase_length_granularity()).unwrap_or_default();
            let block_info = BlockInfo {
                // `block_size` is u32 so can always convert to u64
                block_size: media.block_size as u64,
                erase_blocks_num: max(1, erase_blocks).into(),
                num_blocks: (SafeNum::from(media.last_block) + 1).try_into()?,
                // `io_align` is u32 so can always convert to u64
                alignment: max(1, media.io_align as u64),
            };
            let disk_io = Disk::new_alloc_scratch(EfiBlockDeviceIo {
                block_io,
                block_io2,
                erase,
                media_id: media.media_id,
                block_info,
            })?;
            let disk = match bs.open_protocol::<DevicePathProtocol>(*handle) {
                Ok(dpp) => {
                    if let Some(device_name) = dpp.gbl_vendor_media_device_path()? {
                        efi_println!(
                            efi_entry,
                            "Block #{idx} raw device vendor-defined name: {device_name:?}"
                        );
                        GblDisk::new_raw(disk_io, device_name)?
                    } else {
                        GblDisk::new_gpt(disk_io, Gpt::new(vec![0u8; gpt_buffer_size])?)
                    }
                }
                _ => GblDisk::new_gpt(disk_io, Gpt::new(vec![0u8; gpt_buffer_size])?),
            };
            match block_on(disk.as_sync()?.sync_gpt()) {
                Ok(Some(v)) => efi_println!(efi_entry, "Block #{idx} GPT sync result: {v}"),
                Err(e) => efi_println!(efi_entry, "Block #{idx} error while syncing GPT: {e}"),
                _ => {}
            };
            Ok(disk)
        };
        match open_disk() {
            Ok(disk) => gbl_disks.push(disk),
            Err(e) => efi_println!(efi_entry, "Block #{idx} failed to open device: {e}"),
        }
    }
    Ok(gbl_disks)
}
