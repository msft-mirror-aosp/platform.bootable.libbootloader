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

use crate::fastboot::{sparse::SparseRawWriter, write_fb_partition, GblFbPartition};
use core::mem::swap;
use core::ops::{Deref, DerefMut};
use fastboot::CommandError;
use gbl_storage::{
    AsyncBlockDevice, AsyncGptDevice, BlockInfo, BlockIoAsync, GptCache, Partition as GptPartition,
};
use spin::mutex::Mutex;

/// The status of block device
pub enum BlockStatus {
    Idle,
    Pending,
    Error,
}

/// `GblFbBlockDevice` represents a block device in the GBL Fastboot context.
pub struct GblFbBlockDevice<'a, B: BlockIoAsync> {
    // Wraps in an `Option`. None means the block is taken by an async blk IO task.
    blk: Option<AsyncBlockDevice<'a, B>>,
    // Cached `BlockInfo` and `GptCache` so that they can be accessed while block is taken.
    info_cache: BlockInfo,
    gpt_cache: GptCache<'a>,
    error: Result<(), CommandError>,
}

impl<'a, B: BlockIoAsync> GblFbBlockDevice<'a, B> {
    /// Creates an new instance.
    pub fn new(dev: AsyncGptDevice<'a, B>) -> Self {
        let (mut blk, gpt_cache) = dev.into_blk_and_gpt();
        let info_cache = blk.io().info();
        Self { blk: Some(blk), info_cache, gpt_cache, error: Ok(()) }
    }

    /// Returns the status of block.
    pub(crate) fn status(&self) -> BlockStatus {
        match () {
            _ if self.error.is_err() => BlockStatus::Error,
            _ if self.blk.is_none() => BlockStatus::Pending,
            _ => BlockStatus::Idle,
        }
    }
}

impl<'a, B: BlockIoAsync> From<AsyncGptDevice<'a, B>> for GblFbBlockDevice<'a, B> {
    fn from(val: AsyncGptDevice<'a, B>) -> Self {
        Self::new(val)
    }
}

/// `ResourceInternal` contains internal resources needed by GBL Fastboot.
struct ResourceInternal<'a, B: BlockIoAsync> {
    blks: &'a mut [GblFbBlockDevice<'a, B>],
    download_buffers: &'a mut [&'a mut [u8]],
}

/// `GblFbResource` contains resources needed by GBL Fastboot.
pub struct GblFbResource<'a, B: BlockIoAsync>(Mutex<ResourceInternal<'a, B>>);

impl<'a, B: BlockIoAsync> GblFbResource<'a, B> {
    /// Creates an new instance.
    pub fn new(
        blks: &'a mut [GblFbBlockDevice<'a, B>],
        download_buffers: &'a mut [&'a mut [u8]],
    ) -> Self {
        Self(ResourceInternal { blks, download_buffers }.into())
    }

    /// Returns the number of block devices.
    pub(crate) fn num_blks(&self) -> usize {
        self.0.lock().blks.len()
    }

    /// Takes a block device.
    pub(crate) fn blk_take(
        &self,
        blk_idx: usize,
    ) -> Result<Option<ScopedGblFbBlockDevice<'a, '_, B>>, CommandError> {
        let mut state = self.0.lock();
        let blk = &mut state.blks[blk_idx];
        match blk.error {
            Err(_) => Err("Block device has encountered error previously".into()),
            _ if blk.blk.is_some() => Ok(Some(ScopedGblFbBlockDevice {
                blk_idx,
                blk: Some(blk.blk.take().unwrap()),
                shared: self,
                error: Ok(()),
            })),
            _ => Ok(None),
        }
    }

    /// Checks if a block device has error
    pub(crate) fn blk_is_err(&self, blk_idx: usize) -> bool {
        self.0.lock().blks[blk_idx].error.is_err()
    }

    /// Gets the error status of a block device.
    pub(crate) fn blk_get_err(&self, blk_idx: usize) -> Result<(), CommandError> {
        match self.0.lock().blks[blk_idx].error.as_ref() {
            Ok(()) => Ok(()),
            Err(e) => Err(e.clone()),
        }
    }

    /// Checks if a block device is ready.
    pub(crate) fn blk_is_ready(&self, blk_idx: usize) -> bool {
        self.0.lock().blks[blk_idx].blk.is_some()
    }

    /// Gets the `BlockInfo` of a block device.
    pub(crate) fn blk_info(&self, blk_idx: usize) -> BlockInfo {
        self.0.lock().blks[blk_idx].info_cache
    }

    pub(crate) fn blk_status(&self, blk_idx: usize) -> BlockStatus {
        self.0.lock().blks[blk_idx].status()
    }

    /// Gets the number of partitions on a block device.
    pub(crate) fn num_partitions(&self, blk_idx: usize) -> usize {
        self.0.lock().blks[blk_idx].gpt_cache.num_partitions().unwrap_or(0)
    }

    /// Get the `ptn_idx`th partition on a block device.
    pub(crate) fn get_partition(&self, blk_idx: usize, ptn_idx: usize) -> GptPartition {
        self.0.lock().blks[blk_idx].gpt_cache.get_partition(ptn_idx).unwrap()
    }

    /// Finds a GPT partition on a block device.
    pub(crate) fn find_partition(
        &self,
        blk_idx: usize,
        part: &str,
    ) -> Result<GptPartition, CommandError> {
        Ok(self.0.lock().blks[blk_idx].gpt_cache.find_partition(part)?)
    }

    /// Checks that a partition exists and is unique among all block devices with GPT.
    ///
    /// Returns the block device index and the GPT `Partition`.
    pub(crate) fn check_part(&self, part: &str) -> Result<(usize, GptPartition), CommandError> {
        let state = self.0.lock();
        let mut res = Err("Partition does not exist".into());
        for (idx, blk) in state.blks.iter().enumerate() {
            res = match blk.gpt_cache.find_partition(part).map(|v| (idx, v)) {
                Ok(_) if res.is_ok() => return Err("Partition is not unique".into()),
                v => v.or(res),
            };
        }
        res
    }

    /// Searches and takes a download buffer.
    pub(crate) fn find_download_buffer(&self) -> Option<ScopedGblFbDownloadBuffer<'a, '_, B>> {
        let buffers = &mut self.0.lock().download_buffers[..];
        buffers.iter_mut().enumerate().find(|(_, v)| v.len() > 0).map(|(idx, v)| {
            let mut buffer = &mut [][..];
            swap(v, &mut buffer);
            ScopedGblFbDownloadBuffer { idx, buffer: buffer, shared: self }
        })
    }
}

/// `ScopedGblFbBlockDevice` wraps an `AsyncBlockDevice` obtained from `GblFbResource` and
/// automatically returns it after going out of scope.
pub(crate) struct ScopedGblFbBlockDevice<'a, 'b, B: BlockIoAsync> {
    blk_idx: usize,
    blk: Option<AsyncBlockDevice<'a, B>>,
    shared: &'b GblFbResource<'a, B>,
    error: Result<(), CommandError>,
}

impl<B: BlockIoAsync> ScopedGblFbBlockDevice<'_, '_, B> {
    // Sets error status.
    pub(crate) fn set_error(&mut self, error: Result<(), CommandError>) {
        self.error = error;
    }
}

impl<B: BlockIoAsync> SparseRawWriter for (GblFbPartition, &mut ScopedGblFbBlockDevice<'_, '_, B>) {
    /// Writes bytes from `data` to the destination storage at offset `off`
    async fn write(&mut self, off: u64, data: &mut [u8]) -> Result<(), CommandError> {
        let (part, blk) = self;
        write_fb_partition(blk, *part, off, data).await
    }
}

impl<B: BlockIoAsync> Drop for ScopedGblFbBlockDevice<'_, '_, B> {
    fn drop(&mut self) {
        assert!(!self.shared.blk_is_ready(self.blk_idx));
        // Returns the block device and error.
        let blk = &mut self.shared.0.lock().blks[self.blk_idx];
        blk.blk = self.blk.take();
        swap(&mut blk.error, &mut self.error);
    }
}

impl<'a, B: BlockIoAsync> Deref for ScopedGblFbBlockDevice<'a, '_, B> {
    type Target = AsyncBlockDevice<'a, B>;

    fn deref(&self) -> &Self::Target {
        self.blk.as_ref().unwrap()
    }
}

impl<'a, B: BlockIoAsync> DerefMut for ScopedGblFbBlockDevice<'a, '_, B> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.blk.as_mut().unwrap()
    }
}

/// `ScopedGblFbDownloadBuffer` wraps a download buffer taken from `GblFbResource` and
/// automatically returns it after going out of scope
pub(crate) struct ScopedGblFbDownloadBuffer<'a, 'b, B: BlockIoAsync> {
    idx: usize,
    buffer: &'a mut [u8],
    shared: &'b GblFbResource<'a, B>,
}

impl<'a, 'b, B: BlockIoAsync> Drop for ScopedGblFbDownloadBuffer<'a, 'b, B> {
    fn drop(&mut self) {
        let buffers = &mut self.shared.0.lock().download_buffers;
        swap(&mut self.buffer, &mut buffers[self.idx]);
    }
}

impl<'a, B: BlockIoAsync> Deref for ScopedGblFbDownloadBuffer<'a, '_, B> {
    type Target = &'a mut [u8];

    fn deref(&self) -> &Self::Target {
        &self.buffer
    }
}

impl<'a, B: BlockIoAsync> DerefMut for ScopedGblFbDownloadBuffer<'a, '_, B> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.buffer
    }
}
