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

//! Utilities for writing tests with libstorage, e.g. creating fake block devices.

use crc32fast::Hasher;
use gbl_async::yield_now;
pub use gbl_storage::*;
use liberror::{Error, Result};
use safemath::SafeNum;
use std::collections::{BTreeMap, VecDeque};
use zerocopy::AsBytes;

/// Helper `gbl_storage::BlockIoSync` struct for TestBlockDevice.
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
    /// Injected errors.
    pub errors: VecDeque<Error>,
}

impl TestBlockIo {
    /// Creates a new [TestBlockIo].
    pub fn new(block_size: u64, alignment: u64, data: Vec<u8>) -> Self {
        Self {
            block_size,
            alignment,
            storage: data,
            num_writes: 0,
            num_reads: 0,
            errors: Default::default(),
        }
    }

    fn check_alignment(&mut self, buffer: &[u8]) -> bool {
        matches!(is_buffer_aligned(buffer, self.alignment), Ok(true))
            && matches!(is_aligned(buffer.len().into(), self.block_size.into()), Ok(true))
    }
}

impl BlockIoAsync for TestBlockIo {
    /// Returns a `BlockInfo` for the block device.
    fn info(&mut self) -> BlockInfo {
        BlockInfo {
            block_size: self.block_size,
            num_blocks: u64::try_from(self.storage.len()).unwrap() / self.block_size,
            alignment: self.alignment,
        }
    }

    async fn read_blocks(&mut self, blk_offset: u64, out: &mut [u8]) -> Result<()> {
        assert!(self.check_alignment(out));
        let offset = (SafeNum::from(blk_offset) * self.block_size).try_into().unwrap();
        yield_now().await; // yield once to simulate IO pending.
        match self.errors.pop_front() {
            Some(e) => Err(e),
            _ => Ok(out.clone_from_slice(&self.storage[offset..][..out.len()])),
        }
    }

    async fn write_blocks(&mut self, blk_offset: u64, data: &mut [u8]) -> Result<()> {
        assert!(self.check_alignment(data));
        let offset = (SafeNum::from(blk_offset) * self.block_size).try_into().unwrap();
        yield_now().await; // yield once to simulate IO pending.
        match self.errors.pop_front() {
            Some(e) => Err(e),
            _ => Ok(self.storage[offset..][..data.len()].clone_from_slice(data)),
        }
    }
}

/// Simple RAM based block device used by unit tests.
pub struct TestBlockDevice {
    /// The mock block device.
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
    fn with(&mut self, f: &mut dyn FnMut(&mut dyn BlockIoSync, &mut [u8], u64)) {
        f(&mut self.io, &mut self.scratch[..], self.max_gpt_entries)
    }
}

impl Default for TestBlockDevice {
    fn default() -> Self {
        TestBlockDeviceBuilder::new().build()
    }
}

impl TestBlockDevice {
    /// Creates an instance of `AsyncGptDevice`
    pub fn as_gpt_dev(&mut self) -> AsyncGptDevice<'_, &mut TestBlockIo> {
        AsyncGptDevice::<&mut TestBlockIo>::new_from_monotonic_buffer(
            &mut self.io,
            &mut self.scratch[..],
            self.max_gpt_entries,
        )
        .unwrap()
    }

    /// Creates an instance of `AsyncBlockDevice`
    pub fn as_blk_dev(&mut self) -> AsyncBlockDevice<'_, &mut TestBlockIo> {
        self.as_gpt_dev().into_blk_and_gpt().0
    }
}

/// A description of the backing data store for a block device or partition.
/// Can either describe explicit data the device or partition is initialized with
/// OR a size in bytes if the device or partition can be initialized in a blank state.
#[derive(Copy, Clone)]
pub enum BackingStore<'a> {
    /// Exact data to use for the storage.
    Data(&'a [u8]),
    /// Data size to use, will be initialized as zeros.
    Size(usize),
}

impl<'a> BackingStore<'a> {
    fn size(&self) -> usize {
        match self {
            Self::Data(slice) => slice.len(),
            Self::Size(size) => *size,
        }
    }
}

enum DiskDescription<'a> {
    Disk(BackingStore<'a>),
    Partitions(BTreeMap<&'static str, BackingStore<'a>>),
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
    disk_description: DiskDescription<'a>,
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
            disk_description: DiskDescription::Disk(BackingStore::Size(
                (Self::DEFAULT_BLOCK_SIZE * 32) as usize,
            )),
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
    /// Note: This option is mutually exclusive with `set_data` and `add_partition`.
    ///       If `set_data` or `add_partition` have been called, `set_size` overrides
    ///       those customizations.
    pub fn set_size(mut self, size: usize) -> Self {
        self.disk_description = DiskDescription::Disk(BackingStore::Size(size));
        self
    }

    /// Sets the block device's backing data to the provided slice.
    ///
    /// Note: This option is mutually exclusive with `set_size` and `add_partition`.
    ///       If `set_size` or `add_partition` have been called, `set_data` overrides
    ///       those customizations.
    pub fn set_data(mut self, data: &'a [u8]) -> Self {
        self.disk_description = DiskDescription::Disk(BackingStore::Data(data));
        self
    }

    /// Adds a partition description.
    /// Partitions can be defined either with a specific backing store
    /// from a slice OR from a specific size in bytes.
    /// Partition sizes are rounded up to full blocks.
    /// If the same partition name is added multiple times,
    /// the last definition is used.
    ///
    /// Note: explicitly added partitions are mutually exclusive with
    ///       `set_size` and `set_data`.
    ///       If either have been called, `add_partition` overrides that customization.
    pub fn add_partition(mut self, name: &'static str, backing: BackingStore<'a>) -> Self {
        match self.disk_description {
            DiskDescription::Disk(_) => {
                let mut map = BTreeMap::new();
                map.insert(name, backing);
                self.disk_description = DiskDescription::Partitions(map);
            }
            DiskDescription::Partitions(ref mut map) => {
                map.insert(name, backing);
            }
        };
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
        let storage = match self.disk_description {
            DiskDescription::Disk(BackingStore::Data(slice)) => Vec::from(slice),
            DiskDescription::Disk(BackingStore::Size(size)) => vec![0u8; size],
            DiskDescription::Partitions(partitions) => {
                partitions_to_disk_data(&partitions, self.block_size as usize)
            }
        };
        assert_eq!(storage.len() % (self.block_size as usize), 0);
        let mut io = TestBlockIo::new(self.block_size, self.alignment, storage);
        let scratch_size = match self.scratch_size {
            Some(s) => s,
            None => {
                required_scratch_size(BlockIoSync::info(&mut io), self.max_gpt_entries).unwrap()
            }
        };
        TestBlockDevice {
            io,
            scratch: vec![0u8; scratch_size],
            max_gpt_entries: self.max_gpt_entries,
        }
    }
}

fn str_to_utf16_entry_name(name: &str) -> [u16; GPT_NAME_LEN_U16] {
    assert!(name.len() < GPT_NAME_LEN_U16);
    let mut data = [0; GPT_NAME_LEN_U16];
    let tmp: Vec<u16> = name.encode_utf16().collect();
    for (d, t) in std::iter::zip(data.iter_mut(), tmp) {
        *d = t;
    }
    data
}

fn pad_to_block_size(store: &mut Vec<u8>, block_size: usize) {
    let delta = (block_size - store.len() % block_size) % block_size;
    for _ in 0..delta {
        store.push(0);
    }
}

fn add_blocks(store: &mut Vec<u8>, data: &[u8], block_size: usize) {
    store.extend(data.iter());
    pad_to_block_size(store, block_size);
}

fn pad_bytes(store: &mut Vec<u8>, size: usize, block_size: usize) {
    for _ in 0..size {
        store.push(0);
    }
    pad_to_block_size(store, block_size);
}

fn partitions_to_disk_data(
    partitions: &BTreeMap<&'static str, BackingStore>,
    block_size: usize,
) -> Vec<u8> {
    let gpt_max_entries = 128;
    assert!(partitions.len() <= gpt_max_entries);
    let entry_blocks: u64 = ((SafeNum::from(partitions.len()) * std::mem::size_of::<GptEntry>())
        .round_up(block_size)
        / block_size)
        .try_into()
        .unwrap();
    let mut block = entry_blocks
        + 1  // Protective MBR
        + 1 // Primary GPT header
        ;
    // Leading mbr
    let mut store = vec![0; block_size];
    let mut header = GptHeader {
        magic: GPT_MAGIC,
        current: 1,
        size: std::mem::size_of::<GptHeader>() as u32,
        first: block,
        entries: 2,
        entries_count: std::cmp::min(partitions.len(), gpt_max_entries) as u32,
        entries_size: std::mem::size_of::<GptEntry>() as u32,
        ..Default::default()
    };

    // Define gpt entry structures
    let entries: Vec<GptEntry> = partitions
        .iter()
        .take(gpt_max_entries)
        .map(|(k, v)| {
            let last = (SafeNum::from(v.size()).round_up(block_size) / block_size + block - 1)
                .try_into()
                .unwrap();
            let mut entry = GptEntry {
                part_type: Default::default(),
                guid: Default::default(),
                first: block,
                last,
                flags: 0,
                name: str_to_utf16_entry_name(k),
            };
            entry.guid[0] = block as u8;
            block = last + 1;
            entry
        })
        .collect();

    // Patch last fields of header
    header.last = block - 1;
    header.backup = block + entry_blocks;
    header.entries_crc = entries
        .iter()
        .fold(Hasher::new(), |mut h, e| {
            h.update(e.as_bytes());
            h
        })
        .finalize();
    header.update_crc();

    // Primary header
    add_blocks(&mut store, header.as_bytes(), block_size);

    // Primary entries
    for e in &entries {
        store.extend(e.as_bytes());
    }
    pad_to_block_size(&mut store, block_size);

    // Partition store
    for p in partitions.values() {
        match p {
            BackingStore::Data(d) => add_blocks(&mut store, d, block_size),
            BackingStore::Size(s) => pad_bytes(&mut store, *s, block_size),
        };
    }

    // Backup entries
    let backup_entries_block = store.len() / block_size;
    for e in entries {
        store.extend(e.as_bytes());
    }
    pad_to_block_size(&mut store, block_size);
    // Tweak header to make it the backup.
    header.current = header.backup;
    header.backup = 1;
    header.entries = backup_entries_block.try_into().unwrap();
    header.update_crc();
    add_blocks(&mut store, header.as_bytes(), block_size);

    store
}

/// Simple RAM based multi-block device used for unit tests.
pub struct TestMultiBlockDevices(pub Vec<TestBlockDevice>);

impl TestMultiBlockDevices {
    /// Creates a vector of `AsyncGptDevice`;
    pub fn as_gpt_devs(&mut self) -> Vec<AsyncGptDevice<&mut TestBlockIo>> {
        self.0.iter_mut().map(|v| v.as_gpt_dev()).collect::<Vec<_>>()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_builder_partitions() {
        let data: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
        let mut actual: [u8; 8] = Default::default();
        let mut block_dev = TestBlockDeviceBuilder::new()
            .add_partition("squid", BackingStore::Data(&data))
            .add_partition("clam", BackingStore::Size(28))
            .build();

        assert!(block_dev.sync_gpt().is_ok());
        assert!(block_dev.read_gpt_partition("squid", 0, actual.as_mut_slice()).is_ok());
        assert_eq!(actual, data);

        assert!(block_dev.read_gpt_partition("clam", 0, actual.as_mut_slice()).is_ok());
        assert_eq!(actual, [0u8; 8]);
    }
}
