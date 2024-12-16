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

use alloc::vec::Vec;
use core::{cmp::max, fmt::Write};
use efi::{
    efi_print, efi_println,
    protocol::{block_io::BlockIoProtocol, block_io2::BlockIo2Protocol, Protocol},
    EfiEntry,
};
use efi_types::EfiBlockIoMedia;
use gbl_async::block_on;
use gbl_storage::{gpt_buffer_size, BlockInfo, BlockIo, Disk, Gpt, SliceMaybeUninit};
use liberror::Error;
use libgbl::partition::GblDisk;

/// `EfiBlockDeviceIo` wraps a EFI `BlockIoProtocol` or `BlockIo2Protocol` and implements the
/// `BlockIo` interface.
pub enum EfiBlockDeviceIo<'a> {
    Sync(Protocol<'a, BlockIoProtocol>),
    Async(Protocol<'a, BlockIo2Protocol>),
}

impl<'a> EfiBlockDeviceIo<'a> {
    fn media(&self) -> EfiBlockIoMedia {
        match self {
            EfiBlockDeviceIo::Sync(v) => v.media(),
            EfiBlockDeviceIo::Async(v) => v.media(),
        }
        .unwrap()
    }

    fn info(&mut self) -> BlockInfo {
        let media = self.media();
        BlockInfo {
            block_size: media.block_size as u64,
            num_blocks: (media.last_block + 1) as u64,
            alignment: max(1, media.io_align as u64),
        }
    }
}

// SAFETY:
// `read_blocks()` usess EFI protocol that guarantees to read exact number of blocks that were
// requested, or return error.
// For async `read_blocks_ex()` blocking wait guarantees that read finishes.
unsafe impl BlockIo for EfiBlockDeviceIo<'_> {
    fn info(&mut self) -> BlockInfo {
        (*self).info()
    }

    async fn read_blocks(
        &mut self,
        blk_offset: u64,
        out: &mut (impl SliceMaybeUninit + ?Sized),
    ) -> Result<(), Error> {
        match self {
            EfiBlockDeviceIo::Sync(v) => v.read_blocks(blk_offset, out),
            EfiBlockDeviceIo::Async(v) => v.read_blocks_ex(blk_offset, out).await,
        }
        .or(Err(Error::BlockIoError))
    }

    async fn write_blocks(&mut self, blk_offset: u64, data: &mut [u8]) -> Result<(), Error> {
        match self {
            EfiBlockDeviceIo::Sync(v) => v.write_blocks(blk_offset, data),
            EfiBlockDeviceIo::Async(v) => v.write_blocks_ex(blk_offset, data).await,
        }
        .or(Err(Error::BlockIoError))
    }
}

const MAX_GPT_ENTRIES: usize = 128;

/// The [GblDisk] type in the GBL EFI context.
pub type EfiGblDisk<'a> = GblDisk<Disk<EfiBlockDeviceIo<'a>, Vec<u8>>, Gpt<Vec<u8>>>;

/// Finds and returns all EFI devices supporting either EFI_BLOCK_IO or EFI_BLOCK_IO2 protocol.
pub fn find_block_devices(efi_entry: &EfiEntry) -> Result<Vec<EfiGblDisk<'_>>, Error> {
    let bs = efi_entry.system_table().boot_services();
    let block_dev_handles = bs.locate_handle_buffer_by_protocol::<BlockIoProtocol>()?;
    let mut gbl_disks = vec![];
    let gpt_buffer_size = gpt_buffer_size(MAX_GPT_ENTRIES)?;
    for (idx, handle) in block_dev_handles.handles().iter().enumerate() {
        // Prioritizes `BlockIo2Protocol`.
        let blk_io = match bs.open_protocol::<BlockIo2Protocol>(*handle) {
            Ok(v) => EfiBlockDeviceIo::Async(v),
            _ => EfiBlockDeviceIo::Sync(bs.open_protocol::<BlockIoProtocol>(*handle)?),
        };
        if blk_io.media().logical_partition {
            continue;
        }
        // TODO(b/357688291): Support raw partition based on device path info.
        let disk = GblDisk::new_gpt(
            Disk::new_alloc_scratch(blk_io).unwrap(),
            Gpt::new(vec![0u8; gpt_buffer_size]).unwrap(),
        );
        match block_on(disk.sync_gpt()) {
            Ok(Some(v)) => efi_println!(efi_entry, "Block #{idx} GPT sync result: {v}"),
            Err(e) => efi_println!(efi_entry, "Block #{idx} error while syncing GPT: {e}"),
            _ => {}
        };
        gbl_disks.push(disk);
    }
    Ok(gbl_disks)
}
