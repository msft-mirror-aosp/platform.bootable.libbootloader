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

//! GblOps trait that defines GBL callbacks.

pub use crate::image_buffer::ImageBuffer;
use crate::{
    error::Result as GblResult,
    partition::{check_part_unique, read_unique_partition, write_unique_partition, GblDisk},
};
use core::{ffi::CStr, fmt::Write, num::NonZeroUsize, ops::DerefMut, result::Result};
use gbl_async::block_on;
use libutils::aligned_subslice;

// Re-exports of types from other dependencies that appear in the APIs of this library.
pub use avb::{
    CertPermanentAttributes, IoError as AvbIoError, IoResult as AvbIoResult, SHA256_DIGEST_SIZE,
};
pub use gbl_storage::{BlockIo, Disk, Gpt};
use liberror::Error;
pub use zbi::{ZbiContainer, ZBI_ALIGNMENT_USIZE};

use super::device_tree;
use super::slots;

// https://stackoverflow.com/questions/41081240/idiomatic-callbacks-in-rust
// should we use traits for this? or optional/box FnMut?
//
/* TODO: b/312612203 - needed callbacks:
missing:
- validate_public_key_for_partition: None,
- key management => atx extension in callback =>  atx_ops: ptr::null_mut(), // support optional ATX.
*/
/// Trait that defines callbacks that can be provided to Gbl.
pub trait GblOps<'a> {
    /// Gets a console for logging messages.
    fn console_out(&mut self) -> Option<&mut dyn Write>;

    /// The string to use for console line termination with [gbl_println!].
    ///
    /// Defaults to "\n" if not overridden.
    fn console_newline(&self) -> &'static str {
        "\n"
    }

    /// This method can be used to implement platform specific mechanism for deciding whether boot
    /// should abort and enter Fastboot mode.
    fn should_stop_in_fastboot(&mut self) -> Result<bool, Error>;

    /// Reboots the system into the last set boot mode.
    ///
    /// The method is not expected to return. Errors should be handled internally by the
    /// implementation. In most cases, implementation should continue to reset even in the presence
    /// of errors (users can force power cycle anyway). If there are error cases where reboot
    /// absolutely can't be taken, implementation should hang and notify platform user in its own
    /// way.
    fn reboot(&mut self);

    /// Returns the list of disk devices on this platform.
    ///
    /// Notes that the return slice doesn't capture the life time of `&self`, meaning that the slice
    /// reference must be producible without borrowing `Self`. This is intended and necessary to
    /// make disk IO and the rest of GblOps methods independent and parallelizable, which is
    /// required for features such as parallell fastboot flash, download and other commands. For
    /// implementation, this typically means that the `GblOps` object should hold a reference of the
    /// array instead of owning it.
    fn disks(
        &self,
    ) -> &'a [GblDisk<
        Disk<impl BlockIo + 'a, impl DerefMut<Target = [u8]> + 'a>,
        Gpt<impl DerefMut<Target = [u8]> + 'a>,
    >];

    /// Reads data from a partition.
    async fn read_from_partition(
        &mut self,
        part: &str,
        off: u64,
        out: &mut [u8],
    ) -> Result<(), Error> {
        read_unique_partition(self.disks(), part, off, out).await
    }

    /// Reads data from a partition synchronously.
    fn read_from_partition_sync(
        &mut self,
        part: &str,
        off: u64,
        out: &mut [u8],
    ) -> Result<(), Error> {
        block_on(self.read_from_partition(part, off, out))
    }

    /// Writes data to a partition.
    async fn write_to_partition(
        &mut self,
        part: &str,
        off: u64,
        data: &mut [u8],
    ) -> Result<(), Error> {
        write_unique_partition(self.disks(), part, off, data).await
    }

    /// Writes data to a partition synchronously.
    fn write_to_partition_sync(
        &mut self,
        part: &str,
        off: u64,
        data: &mut [u8],
    ) -> Result<(), Error> {
        block_on(self.write_to_partition(part, off, data))
    }

    /// Returns the size of a partiiton. Returns Ok(None) if partition doesn't exist.
    fn partition_size(&mut self, part: &str) -> Result<Option<u64>, Error> {
        match check_part_unique(self.disks(), part) {
            Ok((_, p)) => Ok(Some(p.size()?)),
            Err(Error::NotFound) => Ok(None),
            Err(e) => Err(e),
        }
    }

    /// Adds device specific ZBI items to the given `container`
    fn zircon_add_device_zbi_items(
        &mut self,
        container: &mut ZbiContainer<&mut [u8]>,
    ) -> Result<(), Error>;

    /// Gets a buffer for staging bootloader file from fastboot.
    ///
    /// Fuchsia uses bootloader file for staging SSH key in development flow.
    ///
    /// Returns `None` if the platform does not intend to support it.
    fn get_zbi_bootloader_files_buffer(&mut self) -> Option<&mut [u8]>;

    /// Gets the aligned part of buffer returned by `get_zbi_bootloader_files_buffer()` according to
    /// ZBI alignment requirement.
    fn get_zbi_bootloader_files_buffer_aligned(&mut self) -> Option<&mut [u8]> {
        aligned_subslice(self.get_zbi_bootloader_files_buffer()?, ZBI_ALIGNMENT_USIZE).ok()
    }

    // TODO(b/334962570): figure out how to plumb ops-provided hash implementations into
    // libavb. The tricky part is that libavb hashing APIs are global with no way to directly
    // correlate the implementation to a particular [GblOps] object, so we'll probably have to
    // create a [Context] ahead of time and store it globally for the hashing APIs to access.
    // However this would mean that [Context] must be a standalone object and cannot hold a
    // reference to [GblOps], which may restrict implementations.
    // fn new_digest(&self) -> Option<Self::Context>;

    /// Load and initialize a slot manager and return a cursor over the manager on success.
    ///
    /// # Args
    ///
    /// * `persist`: A user provided closure for persisting a given slot metadata bytes to storage.
    /// * `boot_token`: A [slots::BootToken].
    fn load_slot_interface<'b>(
        &'b mut self,
        persist: &'b mut dyn FnMut(&mut [u8]) -> Result<(), Error>,
        boot_token: slots::BootToken,
    ) -> GblResult<slots::Cursor<'b>>;

    // The following is a selective subset of the interfaces in `avb::Ops` and `avb::CertOps` needed
    // by GBL's usage of AVB. The rest of the APIs are either not relevant to or are implemented and
    // managed by GBL APIs.

    /// Returns if device is in an unlocked state.
    ///
    /// The interface has the same requirement as `avb::Ops::read_is_device_unlocked`.
    fn avb_read_is_device_unlocked(&mut self) -> AvbIoResult<bool>;

    /// Reads the AVB rollback index at the given location
    ///
    /// The interface has the same requirement as `avb::Ops::read_rollback_index`.
    fn avb_read_rollback_index(&mut self, _rollback_index_location: usize) -> AvbIoResult<u64>;

    /// Writes the AVB rollback index at the given location.
    ///
    /// The interface has the same requirement as `avb::Ops::write_rollback_index`.
    fn avb_write_rollback_index(
        &mut self,
        _rollback_index_location: usize,
        _index: u64,
    ) -> AvbIoResult<()>;

    /// Reads AVB certificate extension permanent attributes.
    ///
    /// The interface has the same requirement as `avb::CertOps::read_permanent_attributes`.
    fn avb_cert_read_permanent_attributes(
        &mut self,
        attributes: &mut CertPermanentAttributes,
    ) -> AvbIoResult<()>;

    /// Reads AVB certificate extension permanent attributes hash.
    ///
    /// The interface has the same requirement as `avb::CertOps::read_permanent_attributes_hash`.
    fn avb_cert_read_permanent_attributes_hash(&mut self) -> AvbIoResult<[u8; SHA256_DIGEST_SIZE]>;

    /// Get buffer for specific image of requested size.
    fn get_image_buffer<'c>(
        &mut self,
        image_name: &str,
        size: NonZeroUsize,
    ) -> GblResult<ImageBuffer<'c>>;

    /// Returns the custom device tree to use, if any.
    ///
    /// If this returns a device tree, it will be used instead of any on-disk contents. This is
    /// currently needed for Cuttlefish, but should not be used in production devices because this
    /// data cannot be verified with libavb.
    fn get_custom_device_tree(&mut self) -> Option<&'a [u8]>;

    /// Requests an OS command line to be used alongside the one built by GBL.
    ///
    /// The returned command line will be verified and appended on top of the command line
    /// built by GBL. Refer to the behavior specified for the corresponding UEFI interface:
    /// https://cs.android.com/android/platform/superproject/main/+/main:bootable/libbootloader/gbl/docs/gbl_os_configuration_protocol.md
    fn fixup_os_commandline<'c>(
        &mut self,
        commandline: &CStr,
        fixup_buffer: &'c mut [u8],
    ) -> Result<Option<&'c str>, Error>;

    /// Requests an OS bootconfig to be used alongside the one built by GBL.
    ///
    /// The returned bootconfig will be verified and appended on top of the bootconfig
    /// built by GBL. Refer to the behavior specified for the corresponding UEFI interface:
    /// https://cs.android.com/android/platform/superproject/main/+/main:bootable/libbootloader/gbl/docs/gbl_os_configuration_protocol.md
    fn fixup_bootconfig<'c>(
        &mut self,
        bootconfig: &[u8],
        fixup_buffer: &'c mut [u8],
    ) -> Result<Option<&'c [u8]>, Error>;

    /// Selects from device tree components to build the final one.
    ///
    /// Provided components registry must be used to select one device tree (none is not allowed),
    /// and any number of overlays. Refer to the behavior specified for the corresponding UEFI
    /// interface:
    /// https://cs.android.com/android/platform/superproject/main/+/main:bootable/libbootloader/gbl/docs/gbl_os_configuration_protocol.md
    fn select_device_trees(
        &mut self,
        components: &mut device_tree::DeviceTreeComponentsRegistry,
    ) -> Result<(), Error>;

    /// Provide writtable buffer of the device tree built by GBL.
    ///
    /// Modified device tree will be verified and used to boot a device. Refer to the behavior
    /// specified for the corresponding UEFI interface:
    /// https://cs.android.com/android/platform/superproject/main/+/main:bootable/libbootloader/gbl/docs/efi_protocols.md
    /// https://github.com/U-Boot-EFI/EFI_DT_FIXUP_PROTOCOL
    fn fixup_device_tree(&mut self, device_tree: &mut [u8]) -> Result<(), Error>;
}

/// Prints with `GblOps::console_out()`.
#[macro_export]
macro_rules! gbl_print {
    ( $ops:expr, $( $x:expr ),* $(,)? ) => {
        {
            match $ops.console_out() {
                Some(v) => write!(v, $($x,)*).unwrap(),
                _ => {}
            }
        }
    };
}

/// Prints the given text plus a newline termination with `GblOps::console_out()`.
#[macro_export]
macro_rules! gbl_println {
    ( $ops:expr, $( $x:expr ),* $(,)? ) => {
        let newline = $ops.console_newline();
        gbl_print!($ops, $($x,)*);
        gbl_print!($ops, "{}", newline);
    };
}

#[cfg(test)]
pub(crate) mod test {
    use super::*;
    use crate::partition::GblDisk;
    use avb::{CertOps, Ops};
    use avb_test::TestOps as AvbTestOps;
    use core::ops::{Deref, DerefMut};
    use gbl_async::block_on;
    use gbl_storage::{new_gpt_max, Disk, GptMax, RamBlockIo};
    use zbi::{ZbiFlags, ZbiType};

    /// Type of [GblDisk] in tests.
    pub(crate) type TestGblDisk = GblDisk<Disk<RamBlockIo<Vec<u8>>, Vec<u8>>, GptMax>;

    /// Backing storage for [FakeGblOps].
    ///
    /// This needs to be a separate object because [GblOps] has designed its lifetimes to borrow
    /// the [GblDisk] objects rather than own it, so that they can outlive the ops
    /// object when necessary.
    ///
    /// # Example usage
    /// ```
    /// let storage = FakeGblOpsStorage::default();
    /// storage.add_gpt_device(&gpt_disk_contents);
    /// storage.add_raw_device(c"raw", &raw_disk_contents);
    ///
    /// let fake_ops = FakeGblOps(&storage);
    /// ```
    #[derive(Default)]
    pub(crate) struct FakeGblOpsStorage(pub Vec<TestGblDisk>);

    impl FakeGblOpsStorage {
        /// Adds a GPT disk.
        pub(crate) fn add_gpt_device(&mut self, data: impl AsRef<[u8]>) {
            // For test GPT images, all block sizes are 512.
            let ram_blk = RamBlockIo::new(512, 512, data.as_ref().to_vec());
            self.0.push(TestGblDisk::new_gpt(
                Disk::new_alloc_scratch(ram_blk).unwrap(),
                new_gpt_max(),
            ));
            let _ = block_on(self.0.last().unwrap().sync_gpt());
        }

        /// Adds a raw partition disk.
        pub(crate) fn add_raw_device(&mut self, name: &CStr, data: impl AsRef<[u8]>) {
            // For raw partition, use block_size=alignment=1 for simplicity.
            let ram_blk = RamBlockIo::new(1, 1, data.as_ref().to_vec());
            self.0.push(
                TestGblDisk::new_raw(Disk::new_alloc_scratch(ram_blk).unwrap(), name).unwrap(),
            )
        }
    }

    impl Deref for FakeGblOpsStorage {
        type Target = [TestGblDisk];

        fn deref(&self) -> &Self::Target {
            &self.0[..]
        }
    }

    /// Fake [GblOps] implementation for testing.
    #[derive(Default)]
    pub(crate) struct FakeGblOps<'a> {
        /// Partition data to expose.
        pub partitions: &'a [TestGblDisk],

        /// Test fixture for [avb::Ops] and [avb::CertOps], provided by libavb.
        ///
        /// We don't use all the available functionality here, in particular the backing storage
        /// is provided by `partitions` and our custom storage APIs rather than the [AvbTestOps]
        /// fake storage, so that we can more accurately test our storage implementation.
        pub avb_ops: AvbTestOps<'static>,

        /// Value returned by `should_stop_in_fastboot`.
        pub stop_in_fastboot: Option<Result<bool, Error>>,

        /// For returned by `fn get_zbi_bootloader_files_buffer()`
        pub zbi_bootloader_files_buffer: Vec<u8>,
    }

    /// Print `console_out` output, which can be useful for debugging.
    impl Write for FakeGblOps<'_> {
        fn write_str(&mut self, s: &str) -> Result<(), std::fmt::Error> {
            Ok(print!("{s}"))
        }
    }

    impl<'a> FakeGblOps<'a> {
        /// For now we've just hardcoded the `zircon_add_device_zbi_items()` callback to add a
        /// single commandline ZBI item with these contents; if necessary we can generalize this
        /// later and allow tests to configure the ZBI modifications.
        pub const ADDED_ZBI_COMMANDLINE_CONTENTS: &'static [u8] = b"test_zbi_item";
        pub const TEST_BOOTLOADER_FILE_1: &'static [u8] = b"\x06test_1foo";
        pub const TEST_BOOTLOADER_FILE_2: &'static [u8] = b"\x06test_2bar";

        pub fn new(partitions: &'a [TestGblDisk]) -> Self {
            let mut res = Self {
                partitions,
                zbi_bootloader_files_buffer: vec![0u8; 32 * 1024],
                ..Default::default()
            };
            let mut container =
                ZbiContainer::new(res.get_zbi_bootloader_files_buffer_aligned().unwrap()).unwrap();
            for ele in [Self::TEST_BOOTLOADER_FILE_1, Self::TEST_BOOTLOADER_FILE_2] {
                container
                    .create_entry_with_payload(ZbiType::BootloaderFile, 0, ZbiFlags::default(), ele)
                    .unwrap();
            }

            res
        }

        /// Copies an entire partition contents into a vector.
        ///
        /// This is a common enough operation in tests that it's worth a small wrapper to provide
        /// a more convenient API using [Vec].
        ///
        /// Panics if the given partition name doesn't exist.
        pub fn copy_partition(&mut self, name: &str) -> Vec<u8> {
            let mut contents =
                vec![0u8; self.partition_size(name).unwrap().unwrap().try_into().unwrap()];
            assert!(self.read_from_partition_sync(name, 0, &mut contents[..]).is_ok());
            contents
        }
    }

    impl<'a> GblOps<'a> for FakeGblOps<'a> {
        fn console_out(&mut self) -> Option<&mut dyn Write> {
            Some(self)
        }

        fn should_stop_in_fastboot(&mut self) -> Result<bool, Error> {
            self.stop_in_fastboot.unwrap_or(Ok(false))
        }

        fn reboot(&mut self) {}

        fn disks(
            &self,
        ) -> &'a [GblDisk<
            Disk<impl BlockIo + 'a, impl DerefMut<Target = [u8]> + 'a>,
            Gpt<impl DerefMut<Target = [u8]> + 'a>,
        >] {
            self.partitions
        }

        fn zircon_add_device_zbi_items(
            &mut self,
            container: &mut ZbiContainer<&mut [u8]>,
        ) -> Result<(), Error> {
            container
                .create_entry_with_payload(
                    ZbiType::CmdLine,
                    0,
                    ZbiFlags::default(),
                    Self::ADDED_ZBI_COMMANDLINE_CONTENTS,
                )
                .unwrap();
            Ok(())
        }

        fn get_zbi_bootloader_files_buffer(&mut self) -> Option<&mut [u8]> {
            Some(self.zbi_bootloader_files_buffer.as_mut_slice())
        }

        fn load_slot_interface<'b>(
            &'b mut self,
            _: &'b mut dyn FnMut(&mut [u8]) -> Result<(), Error>,
            _: slots::BootToken,
        ) -> GblResult<slots::Cursor<'b>> {
            unimplemented!();
        }

        fn avb_read_is_device_unlocked(&mut self) -> AvbIoResult<bool> {
            self.avb_ops.read_is_device_unlocked()
        }

        fn avb_read_rollback_index(&mut self, rollback_index_location: usize) -> AvbIoResult<u64> {
            self.avb_ops.read_rollback_index(rollback_index_location)
        }

        fn avb_write_rollback_index(
            &mut self,
            rollback_index_location: usize,
            index: u64,
        ) -> AvbIoResult<()> {
            self.avb_ops.write_rollback_index(rollback_index_location, index)
        }

        fn avb_cert_read_permanent_attributes(
            &mut self,
            attributes: &mut CertPermanentAttributes,
        ) -> AvbIoResult<()> {
            self.avb_ops.read_permanent_attributes(attributes)
        }

        fn avb_cert_read_permanent_attributes_hash(
            &mut self,
        ) -> AvbIoResult<[u8; SHA256_DIGEST_SIZE]> {
            self.avb_ops.read_permanent_attributes_hash()
        }

        fn get_image_buffer<'c>(&mut self, _: &str, _: NonZeroUsize) -> GblResult<ImageBuffer<'c>> {
            unimplemented!();
        }

        fn get_custom_device_tree(&mut self) -> Option<&'static [u8]> {
            None
        }

        fn fixup_os_commandline<'c>(
            &mut self,
            _commandline: &CStr,
            _fixup_buffer: &'c mut [u8],
        ) -> Result<Option<&'c str>, Error> {
            unimplemented!();
        }

        fn fixup_bootconfig<'c>(
            &mut self,
            _bootconfig: &[u8],
            _fixup_buffer: &'c mut [u8],
        ) -> Result<Option<&'c [u8]>, Error> {
            unimplemented!();
        }

        fn fixup_device_tree(&mut self, _: &mut [u8]) -> Result<(), Error> {
            unimplemented!();
        }

        fn select_device_trees(
            &mut self,
            _: &mut device_tree::DeviceTreeComponentsRegistry,
        ) -> Result<(), Error> {
            unimplemented!();
        }
    }
}
