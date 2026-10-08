// Copyright 2023, The Android Open Source Project
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

//! This module provides an implementation of [BlockIo] backed by RAM.

use crate::{is_aligned, is_buffer_aligned, BlockInfo, BlockIo};
use bytes::buf::UninitSlice;
use core::{
    cell::{Ref, RefCell},
    ops::DerefMut,
};
use gbl_async::yield_now;
use liberror::Error;
use safemath::SafeNum;

/// `RamBlockIo` implements [BlockIo] backed by user provided buffer.
///
/// This also exposes a few useful features for testing such as:
///
/// * read/write counters
/// * error injection
/// * blocking/non-blocking
pub struct RamBlockIo<T> {
    /// The storage block size in bytes.
    pub block_size: u64,
    /// The storage access alignment in bytes.
    pub alignment: u64,
    /// The backing storage data.
    /// Stored as a RefCell so that BlockIo methods can mutate and take &self receivers.
    pub storage: RefCell<T>,
    /// The number of successful IO calls, (reads, writes).
    ///
    /// Private to make sure that tests don't confuse which field is which.
    num_accesses: RefCell<(usize, usize)>,
    /// Injected error to be returned by the next read/write/erase IO.
    /// This is a RefCell because BlockIo methods take &self
    /// but need to call `Option::take` on the error as well.
    pub error: RefCell<Option<Error>>,
    /// Number of additional times to yield before performing I/O.
    ///
    /// This is private because tests should not depend on the exact number of yields.
    /// See [set_blocking] for more info.
    yields: usize,
}

impl<T: DerefMut<Target = [u8]>> RamBlockIo<T> {
    /// Creates a new instance.
    ///
    /// Initial state is to perform I/O operations successfully without blocking.
    pub fn new(block_size: u64, alignment: u64, storage: T) -> Self {
        assert_eq!(
            storage.len() % usize::try_from(block_size).unwrap(),
            0,
            "storage size is not multiple of block size, {}, {}",
            storage.len(),
            block_size
        );
        Self {
            block_size,
            alignment,
            storage: storage.into(),
            num_accesses: (0, 0).into(),
            error: None.into(),
            yields: 0,
        }
    }

    /// Configures the blocking behavior.
    ///
    /// When set to true, the [RamBlockIo] will yield a large number of times prior to each I/O
    /// operation. This is to allow tests to check behavior when tasks are blocked on I/O.
    ///
    /// Tests should generally not depend on the exact number of yields since they are
    /// non-deterministic. Factors like buffer alignment can influence the number of I/O operations,
    /// e.g. depending on where the allocator places a buffer, `fastboot flash` may end up issuing
    /// anywhere from 1-3 I/O operations to handle partial pages, which will result in a varying
    /// number of yields.
    ///
    /// Instead, tests should just use this API to indicate whether I/O operations should block
    /// or not, and can safely assume that a blocking operation will yield enough times that it
    /// will stay blocked until the test loops on completing it.
    pub fn set_blocking(&mut self, blocking: bool) {
        // 100 should be enough, if for some reason we have a test that does perform 100+ polls
        // but still wants tasks to remain blocked we can increase this.
        self.yields = if blocking { 100 } else { 0 };
    }

    /// Gets the underlying ramdisk storage.
    pub fn storage(&self) -> Ref<'_, [u8]> {
        Ref::map(self.storage.borrow(), |s| s.deref())
    }

    /// Helper for checking custom injected errors
    fn check_custom_error(&self) -> Result<(), Error> {
        match self.error.borrow_mut().take() {
            Some(e) => Err(e),
            _ => Ok(()),
        }
    }

    /// Checks injected error, simulates async waiting, checks read/write parameters and returns the
    /// offset in number of bytes.
    async fn checks<'a>(
        &self,
        blk_offset: u64,
        buf: impl Into<&'a mut UninitSlice>,
    ) -> Result<usize, Error> {
        let buf = buf.into();
        assert!(is_buffer_aligned(&mut *buf, self.alignment).unwrap_or(false));
        assert!(is_aligned(buf.len(), self.block_size).unwrap_or(false));
        for _ in 0..self.yields {
            yield_now().await;
        }
        self.check_custom_error()?;
        Ok((SafeNum::from(blk_offset) * self.block_size).try_into().unwrap())
    }
}

// SAFETY:
// `read_blocks` clones `out.len()` bytes to output which initializes all elements in `out`
unsafe impl<T: DerefMut<Target = [u8]>> BlockIo for RamBlockIo<T> {
    fn info(&self) -> BlockInfo {
        BlockInfo {
            block_size: self.block_size,
            erase_blocks_num: 2,
            num_blocks: u64::try_from(self.storage.borrow().len()).unwrap() / self.block_size,
            alignment: self.alignment,
        }
    }

    async fn read_blocks<'a>(
        &self,
        blk_offset: u64,
        out: impl Into<&'a mut UninitSlice>,
    ) -> Result<(), Error> {
        let out = out.into();
        let offset = self.checks(blk_offset, &mut *out).await?;
        let out_len = out.len();
        self.num_accesses.borrow_mut().0 += 1;

        Ok(out.copy_from_slice(&self.storage.borrow()[offset..][..out_len]))
    }

    async fn write_blocks(&self, blk_offset: u64, data: &mut [u8]) -> Result<(), Error> {
        let offset = self.checks(blk_offset, &mut *data).await?;
        self.num_accesses.borrow_mut().1 += 1;

        Ok(self.storage.borrow_mut()[offset..][..data.len()].copy_from_slice(data))
    }

    async fn erase_blocks(&self, blk_offset: u64, num_blks: u64) -> Result<(), Error> {
        for _ in 0..self.yields {
            yield_now().await;
        }
        self.check_custom_error()?;
        let blk_sz = self.info().erase_block_size().unwrap();
        let off = (SafeNum::from(blk_offset) * blk_sz).try_into().unwrap();
        let sz = (SafeNum::from(num_blks) * blk_sz).try_into().unwrap();

        // Erases by flipping the bits.
        Ok(self.storage.borrow_mut()[off..][..sz].iter_mut().for_each(|v| *v = !*v))
    }
}

#[cfg(test)]
pub(crate) mod test {
    use super::*;
    use core::cell::RefMut;

    impl<T: DerefMut<Target = [u8]>> RamBlockIo<T> {
        /// Gets the underlying ramdisk storage mutably.
        pub(crate) fn storage_mut(&self) -> RefMut<'_, [u8]> {
            RefMut::map(self.storage.borrow_mut(), |s| s.deref_mut())
        }

        /// Gets the number of successful read operations
        pub(crate) fn num_reads(&self) -> usize {
            self.num_accesses.borrow().0
        }

        /// Gets the number of successful write operations
        pub(crate) fn num_writes(&self) -> usize {
            self.num_accesses.borrow().1
        }
    }
}
