// Copyright (C) 2024  Google LLC
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
pub use gbl_storage::{
    alignment_scratch_size, is_aligned, is_buffer_aligned, required_scratch_size, AsBlockDevice,
    AsMultiBlockDevices, BlockIo,
};

use safemath::SafeNum;

/// Helper `gbl_storage::BlockIo` struct for TestBlockDevice.
pub struct TestBlockIo {
    /// The storage block size in bytes.
    pub block_size: u64,
    /// The storage access alignment in bytes.
    pub alignment: u64,
    /// The backing storage data.
    pub storage: Vec<u8>,
    /// The number of successful write calls.
    pub num_writes: usize,
    /// The number of successful read calls.
    pub num_reads: usize,
}

impl TestBlockIo {
    pub fn new<T: AsRef<[u8]>>(block_size: u64, alignment: u64, data: T) -> Self {
        Self {
            block_size: block_size,
            alignment: alignment,
            storage: Vec::from(data.as_ref()),
            num_writes: 0,
            num_reads: 0,
        }
    }

    fn check_alignment(&mut self, buffer: &[u8]) -> bool {
        matches!(is_buffer_aligned(buffer, self.alignment()), Ok(true))
            && matches!(is_aligned(buffer.len().into(), self.block_size().into()), Ok(true))
    }
}

impl BlockIo for TestBlockIo {
    fn block_size(&mut self) -> u64 {
        self.block_size
    }

    fn num_blocks(&mut self) -> u64 {
        self.storage.len() as u64 / self.block_size()
    }

    fn alignment(&mut self) -> u64 {
        self.alignment
    }

    fn read_blocks(&mut self, blk_offset: u64, out: &mut [u8]) -> bool {
        if !self.check_alignment(out) {
            return false;
        }

        let start = SafeNum::from(blk_offset) * self.block_size();
        let end = start + out.len();
        out.clone_from_slice(&self.storage[start.try_into().unwrap()..end.try_into().unwrap()]);
        self.num_reads += 1;
        true
    }

    fn write_blocks(&mut self, blk_offset: u64, data: &[u8]) -> bool {
        if !self.check_alignment(data) {
            return false;
        }

        let start = SafeNum::from(blk_offset) * self.block_size();
        let end = start + data.len();
        self.storage[start.try_into().unwrap()..end.try_into().unwrap()].clone_from_slice(&data);
        self.num_writes += 1;
        true
    }
}

/// Simple RAM based block device used by unit tests.
pub struct TestBlockDevice {
    /// The BlockIo helper struct.
    pub io: TestBlockIo,
    /// In-memory backing store.
    pub scratch: Vec<u8>,
    max_gpt_entries: u64,
}

impl From<&[u8]> for TestBlockDevice {
    fn from(data: &[u8]) -> Self {
        TestBlockDeviceBuilder::new().set_data(data).build()
    }
}

impl AsBlockDevice for TestBlockDevice {
    fn with(&mut self, f: &mut dyn FnMut(&mut dyn BlockIo, &mut [u8], u64)) {
        f(&mut self.io, &mut self.scratch[..], self.max_gpt_entries)
    }
}

impl Default for TestBlockDevice {
    fn default() -> Self {
        TestBlockDeviceBuilder::new().build()
    }
}

/// A description of the backing data store for a block device.
/// Can either describe explicit data the device is initialized with
/// OR a size in bytes if the device can be initialized in a blank state.
enum BackingStore<'a> {
    Data(&'a [u8]),
    Size(usize),
}

/// Builder struct for TestBlockDevice.
/// Most tests will want either:
/// 1) A blank device of a reasonable size OR
/// 2) A device with specific initial data.
/// Other customizations include block size,
/// the maximum number of GPT entries,
/// the alignment requirements,
/// and the size of the scratch buffer.
///
/// Note: setting the storage size or storage data is generally safe,
///       as long as the backing store is large enough,
///       but customizing other attributes may generate a block device
///       that cannot successfully complete any operations.
///       This may be exactly the intention, but be warned that it can be tricky
///       to customize the device and generate something that works without errors.
pub struct TestBlockDeviceBuilder<'a> {
    block_size: u64,
    max_gpt_entries: u64,
    alignment: u64,
    backing_store: BackingStore<'a>,
    scratch_size: Option<usize>,
}

impl<'a> TestBlockDeviceBuilder<'a> {
    /// The default access alignment in bytes.
    pub const DEFAULT_ALIGNMENT: u64 = 64;
    /// The default block size in bytes.
    pub const DEFAULT_BLOCK_SIZE: u64 = 512;
    /// The default maximum number of GPT entries.
    pub const MAX_GPT_ENTRIES: u64 = 128;

    /// Creates a new TestBlockDeviceBuilder with defaults for all attributes.
    pub fn new() -> Self {
        Self {
            block_size: Self::DEFAULT_BLOCK_SIZE,
            max_gpt_entries: Self::MAX_GPT_ENTRIES,
            alignment: Self::DEFAULT_ALIGNMENT,
            backing_store: BackingStore::Size((Self::DEFAULT_BLOCK_SIZE * 32) as usize),
            scratch_size: None,
        }
    }

    /// Set the block size of the block device in bytes.
    /// The default is `DEFAULT_BLOCK_SIZE`.
    pub fn set_block_size(mut self, block_size: u64) -> Self {
        self.block_size = block_size;
        self
    }

    /// Set the maximum number of GPT entries for the GPT header.
    /// The default is `MAX_GPT_ENTRIES`.
    /// Note: setting too large a number of entries will make a device
    ///       that fails to sync its GPT.
    pub fn set_max_gpt_entries(mut self, max_gpt_entries: u64) -> Self {
        self.max_gpt_entries = max_gpt_entries;
        self
    }

    /// Set the required alignment for the TestBlockDevice.
    /// An alignment of `0` means there are no alignment requirements.
    /// The default is `DEFAULT_ALIGNMENT`.
    pub fn set_alignment(mut self, alignment: u64) -> Self {
        self.alignment = alignment;
        self
    }

    /// Set the size of TestBlockDevice in bytes.
    /// When built, the TestBlockDevice will have a blank backing store of size `size`.
    /// The default is `DEFAULT_BLOCK_SIZE` * 32.
    ///
    /// Note: This option is mutually exclusive with set_data.
    ///       If set_data has been called, set_size overrides
    ///       that customization.
    pub fn set_size(mut self, size: usize) -> Self {
        self.backing_store = BackingStore::Size(size);
        self
    }

    /// Sets the block device's backing data to the provided slice.
    ///
    /// Note: This option is mutually exclusive with set_size.
    ///       If set_size has been called, set_data overrides
    ///       that customization.
    pub fn set_data(mut self, data: &'a [u8]) -> Self {
        self.backing_store = BackingStore::Data(data);
        self
    }

    /// Customize the size of the block device's scratch buffer.
    /// The default size is a known safe minimum calculated when `build()` is called.
    ///
    /// Note: Too small a scratch buffer will generate errors.
    ///       Unless a test is specifically interested in a non-default
    ///       scratch size, it's better to rely on the default size.
    pub fn set_scratch_size(mut self, scratch_size: usize) -> Self {
        self.scratch_size = Some(scratch_size);
        self
    }

    /// Consumes the builder and generates a TestBlockDevice
    /// with the desired customizations.
    pub fn build(self) -> TestBlockDevice {
        let storage = match self.backing_store {
            BackingStore::Data(slice) => Vec::from(slice),
            BackingStore::Size(size) => vec![0u8; size],
        };
        assert!(storage.len() % (self.block_size as usize) == 0);
        let mut io = TestBlockIo::new(self.block_size, self.alignment, storage);
        let scratch_size = match self.scratch_size {
            Some(s) => s,
            None => required_scratch_size(&mut io, self.max_gpt_entries).unwrap(),
        };
        TestBlockDevice {
            io,
            scratch: vec![0u8; scratch_size],
            max_gpt_entries: self.max_gpt_entries,
        }
    }
}

/// Simple RAM based multi-block device used for unit tests.
pub struct TestMultiBlockDevices(pub Vec<TestBlockDevice>);

impl AsMultiBlockDevices for TestMultiBlockDevices {
    fn for_each(
        &mut self,
        f: &mut dyn FnMut(&mut dyn AsBlockDevice, u64),
    ) -> core::result::Result<(), Option<&'static str>> {
        let _ = self
            .0
            .iter_mut()
            .enumerate()
            .for_each(|(idx, ele)| f(ele, u64::try_from(idx).unwrap()));
        Ok(())
    }
}
