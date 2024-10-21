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
    partition::{
        check_part_unique, read_unique_partition, write_unique_partition, PartitionBlockDevice,
    },
};
use core::ffi::CStr;
use core::{fmt::Write, num::NonZeroUsize, result::Result};
use gbl_async::block_on;
use gbl_storage::BlockIoAsync;

// Re-exports of types from other dependencies that appear in the APIs of this library.
pub use avb::{
    CertPermanentAttributes, IoError as AvbIoError, IoResult as AvbIoResult, SHA256_DIGEST_SIZE,
};
use liberror::Error;
pub use zbi::ZbiContainer;

use super::slots;

/// `AndroidBootImages` contains references to loaded images for booting Android.
pub struct AndroidBootImages<'a> {
    /// Kernel image.
    pub kernel: &'a mut [u8],
    /// Ramdisk to pass to the kernel.
    pub ramdisk: &'a mut [u8],
    /// FDT To pass to the kernel.
    pub fdt: &'a mut [u8],
}

/// `FuchsiaBootImages` contains references to loaded images for booting Zircon.
pub struct FuchsiaBootImages<'a> {
    /// Kernel image.
    pub zbi_kernel: &'a mut [u8],
    /// ZBI container with items to pass to the kernel.
    pub zbi_items: &'a mut [u8],
}

/// Images required to boot the supported kernels.
pub enum BootImages<'a> {
    /// Android boot images.
    Android(AndroidBootImages<'a>),
    /// Fuchsia boot images.
    Fuchsia(FuchsiaBootImages<'a>),
}

// https://stackoverflow.com/questions/41081240/idiomatic-callbacks-in-rust
// should we use traits for this? or optional/box FnMut?
//
/* TODO: b/312612203 - needed callbacks:
missing:
- validate_public_key_for_partition: None,
- key management => atx extension in callback =>  atx_ops: ptr::null_mut(), // support optional ATX.
*/
/// Trait that defines callbacks that can be provided to Gbl.
pub trait GblOps<'a>
where
    Self: 'a,
{
    /// Type that implements `BlockIoAsync` for the array of `PartitionBlockDevice` returned by]
    /// `partitions()`.
    type PartitionBlockIo: BlockIoAsync;

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

    /// Platform specific processing of boot images before booting.
    fn preboot(&mut self, boot_images: BootImages) -> Result<(), Error>;

    /// Reboots the system into the last set boot mode.
    ///
    /// The method is not expected to return. Errors should be handled internally by the
    /// implementation. In most cases, implementation should continue to reset even in the presence
    /// of errors (users can force power cycle anyway). If there are error cases where reboot
    /// absolutely can't be taken, implementation should hang and notify platform user in its own
    /// way.
    fn reboot(&mut self);

    /// Returns the list of partition block devices.
    ///
    /// Notes that the return slice doesn't capture the life time of `&self`, meaning that the slice
    /// reference must be producible without borrowing the `GblOps`. This is intended and necessary
    /// in order to parallelize fastboot flash, download and other commands. For implementation,
    /// this typically means that the `GblOps` object should hold a reference of the array instead
    /// of owning it.
    fn partitions(&self) -> Result<&'a [PartitionBlockDevice<'a, Self::PartitionBlockIo>], Error>;

    /// Reads data from a partition.
    async fn read_from_partition(
        &mut self,
        part: &str,
        off: u64,
        out: &mut [u8],
    ) -> Result<(), Error> {
        read_unique_partition(self.partitions()?, part, off, out).await
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
        write_unique_partition(self.partitions()?, part, off, data).await
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
        match check_part_unique(self.partitions()?, part) {
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

    // TODO(b/334962570): figure out how to plumb ops-provided hash implementations into
    // libavb. The tricky part is that libavb hashing APIs are global with no way to directly
    // correlate the implementation to a particular [GblOps] object, so we'll probably have to
    // create a [Context] ahead of time and store it globally for the hashing APIs to access.
    // However this would mean that [Context] must be a standalone object and cannot hold a
    // reference to [GblOps], which may restrict implementations.
    // fn new_digest(&self) -> Option<Self::Context>;

    /// Callback for when fastboot mode is requested.
    // Nevertype could be used here when it is stable https://github.com/serde-rs/serde/issues/812
    fn do_fastboot<B: gbl_storage::AsBlockDevice>(
        &self,
        cursor: &mut slots::Cursor<B>,
    ) -> GblResult<()>;

    /// Load and initialize a slot manager and return a cursor over the manager on success.
    fn load_slot_interface<'b, B: gbl_storage::AsBlockDevice>(
        &'b mut self,
        block_device: &'b mut B,
        boot_token: slots::BootToken,
    ) -> GblResult<slots::Cursor<'b, B>>;

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
    use crate::partition::sync_gpt;
    use avb::{CertOps, Ops};
    use avb_test::TestOps as AvbTestOps;
    use gbl_storage_testlib::{TestBlockDevice, TestBlockDeviceBuilder, TestBlockIo};
    use zbi::{ZbiFlags, ZbiType};

    /// Backing storage for [FakeGblOps].
    ///
    /// This needs to be a separate object because [GblOps] has designed its lifetimes to borrow
    /// the [PartitionBlockDevice] objects rather than own it, so that they can outlive the ops
    /// object when necessary.
    ///
    /// # Example usage
    /// ```
    /// let storage = FakeGblOpsStorage::default();
    /// storage.add_gpt_device(&gpt_disk_contents);
    /// storage.add_raw_device("raw", &raw_disk_contents);
    ///
    /// let partitions = storage.as_partition_block_devices();
    /// let fake_ops = FakeGblOps(&partitions);
    /// ```
    #[derive(Default)]
    pub(crate) struct FakeGblOpsStorage {
        /// GPT block devices.
        gpt_devices: Vec<TestBlockDevice>,
        /// Raw partition block devices.
        raw_devices: Vec<(&'static str, TestBlockDevice)>,
    }

    impl FakeGblOpsStorage {
        /// Adds a GPT block device.
        pub fn add_gpt_device(&mut self, data: impl AsRef<[u8]>) {
            self.gpt_devices.push(data.as_ref().into())
        }

        /// Adds a raw partition block device.
        pub fn add_raw_device(&mut self, name: &'static str, data: impl AsRef<[u8]>) {
            let dev =
                TestBlockDeviceBuilder::new().set_data(data.as_ref()).set_block_size(1).build();
            self.raw_devices.push((name, dev))
        }

        /// Returns a vector of [PartitionBlockDevice]s wrapping the added devices.
        pub fn as_partition_block_devices(
            &mut self,
        ) -> Vec<PartitionBlockDevice<&mut TestBlockIo>> {
            let mut parts = Vec::default();
            // Convert GPT devices.
            for device in self.gpt_devices.iter_mut() {
                let (gpt_blk, gpt) = device.as_gpt_dev().into_blk_and_gpt();
                parts.push(PartitionBlockDevice::new_gpt(gpt_blk, gpt));
            }
            // Convert raw devices.
            for (name, device) in self.raw_devices.iter_mut() {
                parts.push(PartitionBlockDevice::new_raw(device.as_blk_dev(), name).unwrap());
            }
            block_on(sync_gpt(&mut parts[..])).unwrap();
            parts
        }
    }

    /// Fake [GblOps] implementation for testing.
    #[derive(Default)]
    pub(crate) struct FakeGblOps<'a> {
        /// Partition data to expose.
        pub partitions: &'a [PartitionBlockDevice<'a, &'a mut TestBlockIo>],

        /// Test fixture for [avb::Ops] and [avb::CertOps], provided by libavb.
        ///
        /// We don't use all the available functionality here, in particular the backing storage
        /// is provided by `partitions` and our custom storage APIs rather than the [AvbTestOps]
        /// fake storage, so that we can more accurately test our storage implementation.
        pub avb_ops: AvbTestOps<'static>,

        /// Value returned by `should_stop_in_fastboot`.
        pub stop_in_fastboot: Option<Result<bool, Error>>,
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

        pub fn new(partitions: &'a [PartitionBlockDevice<'a, &'a mut TestBlockIo>]) -> Self {
            Self { partitions, ..Default::default() }
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

    impl<'a> GblOps<'a> for FakeGblOps<'a>
    where
        Self: 'a,
    {
        type PartitionBlockIo = &'a mut TestBlockIo;

        fn console_out(&mut self) -> Option<&mut dyn Write> {
            Some(self)
        }

        fn should_stop_in_fastboot(&mut self) -> Result<bool, Error> {
            self.stop_in_fastboot.unwrap_or(Ok(false))
        }

        fn preboot(&mut self, boot_images: BootImages) -> Result<(), Error> {
            unimplemented!();
        }

        fn reboot(&mut self) {}

        fn partitions(
            &self,
        ) -> Result<&'a [PartitionBlockDevice<'a, Self::PartitionBlockIo>], Error> {
            Ok(self.partitions)
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

        fn do_fastboot<B: gbl_storage::AsBlockDevice>(
            &self,
            cursor: &mut slots::Cursor<B>,
        ) -> GblResult<()> {
            unimplemented!();
        }

        fn load_slot_interface<'b, B: gbl_storage::AsBlockDevice>(
            &'b mut self,
            block_device: &'b mut B,
            boot_token: slots::BootToken,
        ) -> GblResult<slots::Cursor<'b, B>> {
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

        fn get_image_buffer<'c>(
            &mut self,
            image_name: &str,
            size: NonZeroUsize,
        ) -> GblResult<ImageBuffer<'c>> {
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

        fn fixup_device_tree(&mut self, device_tree: &mut [u8]) -> Result<(), Error> {
            unimplemented!();
        }
    }
}
