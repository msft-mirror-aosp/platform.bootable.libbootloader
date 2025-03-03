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
    fuchsia_boot::GblAbrOps,
    gbl_avb::state::{BootStateColor, KeyValidationStatus},
    partition::{check_part_unique, read_unique_partition, write_unique_partition, GblDisk},
};
pub use abr::{set_one_shot_bootloader, set_one_shot_recovery, SlotIndex};
use core::{ffi::CStr, fmt::Write, num::NonZeroUsize, ops::DerefMut, result::Result};
use gbl_async::block_on;
use gbl_storage::SliceMaybeUninit;
use libutils::aligned_subslice;

// Re-exports of types from other dependencies that appear in the APIs of this library.
pub use avb::{
    CertPermanentAttributes, IoError as AvbIoError, IoResult as AvbIoResult, SHA256_DIGEST_SIZE,
};
pub use gbl_storage::{BlockIo, Disk, Gpt};
use liberror::Error;
pub use slots::{Slot, SlotsMetadata};
pub use zbi::{ZbiContainer, ZBI_ALIGNMENT_USIZE};

use super::device_tree;
use super::slots;

/// Target Type of OS to boot.
#[derive(PartialEq, Debug, Copy, Clone)]
pub enum Os {
    /// Android
    Android,
    /// Fuchsia
    Fuchsia,
}

/// Contains reboot reasons for instructing GBL to boot to different modes.
#[derive(PartialEq, Debug, Copy, Clone)]
pub enum RebootReason {
    /// Normal boot.
    Normal,
    /// Bootloader Fastboot mode.
    Bootloader,
    /// Userspace Fastboot mode.
    FastbootD,
    /// Recovery mode.
    Recovery,
}

// https://stackoverflow.com/questions/41081240/idiomatic-callbacks-in-rust
// should we use traits for this? or optional/box FnMut?
//
/* TODO: b/312612203 - needed callbacks:
missing:
- key management => atx extension in callback =>  atx_ops: ptr::null_mut(), // support optional ATX.
*/
/// Trait that defines callbacks that can be provided to Gbl.
pub trait GblOps<'a, 'd> {
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

    /// Reboots into recovery mode
    ///
    /// On success, returns a closure that performs the reboot.
    fn reboot_recovery(&mut self) -> Result<impl FnOnce() + '_, Error> {
        if self.expected_os_is_fuchsia()? {
            // TODO(b/363075013): Checks and prioritizes platform specific `set_boot_reason()`.
            set_one_shot_recovery(&mut GblAbrOps(self), true)?;
            return Ok(|| self.reboot());
        }
        Err(Error::Unsupported)
    }

    /// Reboots into bootloader fastboot mode
    ///
    /// On success, returns a closure that performs the reboot.
    fn reboot_bootloader(&mut self) -> Result<impl FnOnce() + '_, Error> {
        if self.expected_os_is_fuchsia()? {
            // TODO(b/363075013): Checks and prioritizes platform specific `set_boot_reason()`.
            set_one_shot_bootloader(&mut GblAbrOps(self), true)?;
            return Ok(|| self.reboot());
        }
        Err(Error::Unsupported)
    }

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
        out: &mut (impl SliceMaybeUninit + ?Sized),
    ) -> Result<(), Error> {
        read_unique_partition(self.disks(), part, off, out).await
    }

    /// Reads data from a partition synchronously.
    fn read_from_partition_sync(
        &mut self,
        part: &str,
        off: u64,
        out: &mut (impl SliceMaybeUninit + ?Sized),
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

    /// Returns which OS to load, or `None` to try to auto-detect based on disk layout & contents.
    fn expected_os(&mut self) -> Result<Option<Os>, Error>;

    /// Returns if the expected_os is fuchsia
    fn expected_os_is_fuchsia(&mut self) -> Result<bool, Error> {
        // TODO(b/374776896): Implement auto detection.
        Ok(self.expected_os()?.map(|v| v == Os::Fuchsia).unwrap_or(false))
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
    fn avb_read_rollback_index(&mut self, rollback_index_location: usize) -> AvbIoResult<u64>;

    /// Writes the AVB rollback index at the given location.
    ///
    /// The interface has the same requirement as `avb::Ops::write_rollback_index`.
    fn avb_write_rollback_index(
        &mut self,
        rollback_index_location: usize,
        index: u64,
    ) -> AvbIoResult<()>;

    /// Reads the AVB persistent value for the given name.
    ///
    /// The interface has the same requirement as `avb::Ops::read_persistent_value`.
    fn avb_read_persistent_value(&mut self, name: &CStr, value: &mut [u8]) -> AvbIoResult<usize>;

    /// Writes the AVB persistent value for the given name.
    ///
    /// The interface has the same requirement as `avb::Ops::write_persistent_value`.
    fn avb_write_persistent_value(&mut self, name: &CStr, value: &[u8]) -> AvbIoResult<()>;

    /// Erases the AVB persistent value for the given name.
    ///
    /// The interface has the same requirement as `avb::Ops::erase_persistent_value`.
    fn avb_erase_persistent_value(&mut self, name: &CStr) -> AvbIoResult<()>;

    /// Validate public key used to execute AVB.
    ///
    /// Used by `avb::CertOps::read_permanent_attributes_hash` so have similar requirements.
    fn avb_validate_vbmeta_public_key(
        &self,
        public_key: &[u8],
        public_key_metadata: Option<&[u8]>,
    ) -> AvbIoResult<KeyValidationStatus>;

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

    /// Handle AVB result.
    ///
    /// Set device state (rot / version binding), show UI, etc.
    fn avb_handle_verification_result(
        &mut self,
        color: BootStateColor,
        digest: Option<&CStr>,
        boot_os_version: Option<&[u8]>,
        boot_security_patch: Option<&[u8]>,
        system_os_version: Option<&[u8]>,
        system_security_patch: Option<&[u8]>,
        vendor_os_version: Option<&[u8]>,
        vendor_security_patch: Option<&[u8]>,
    ) -> AvbIoResult<()>;

    /// Get buffer for specific image of requested size.
    fn get_image_buffer(
        &mut self,
        image_name: &str,
        size: NonZeroUsize,
    ) -> GblResult<ImageBuffer<'d>>;

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

    /// Gets platform-specific fastboot variable.
    ///
    /// # Args
    ///
    /// * `name`: Varaiable name.
    /// * `args`: Additional arguments.
    /// * `out`: The output buffer for the value of the variable. Must be a ASCII string.
    ///
    /// # Returns
    ///
    /// * Returns the number of bytes written in `out` on success.
    fn fastboot_variable<'arg>(
        &mut self,
        name: &CStr,
        args: impl Iterator<Item = &'arg CStr> + Clone,
        out: &mut [u8],
    ) -> Result<usize, Error>;

    /// Iterates all fastboot variables, arguments and values.
    ///
    /// # Args
    ///
    /// * `cb`: A closure that takes 1) an array of CStr that contains the variable name followed by
    ///   any additional arguments and 2) a CStr representing the value.
    fn fastboot_visit_all_variables(
        &mut self,
        cb: impl FnMut(&[&CStr], &CStr),
    ) -> Result<(), Error>;

    /// Returns a [SlotsMetadata] for the platform.
    fn slots_metadata(&mut self) -> Result<SlotsMetadata, Error>;

    /// Gets the currently booted bootloader slot.
    ///
    /// # Returns
    ///
    /// * Returns Ok(Some(slot index)) if bootloader is slotted.
    /// * Returns Ok(Errorr::Unsupported) if bootloader is not slotted.
    /// * Returns Err() on error.
    fn get_current_slot(&mut self) -> Result<Slot, Error>;

    /// Gets the slot for the next A/B decision.
    ///
    /// # Args
    ///
    /// * `mark_boot_attempt`: Passes true if the caller attempts to boot the returned slot and
    ///   would like implementation to perform necessary update to the state of slot such as retry
    ///   counter. Passes false if the caller only wants to query the slot decision and not cause
    ///   any state change.
    fn get_next_slot(&mut self, _mark_boot_attempt: bool) -> Result<Slot, Error>;

    /// Sets the active slot for the next A/B decision.
    ///
    /// # Args
    ///
    /// * `slot`: The numeric index of the slot.
    fn set_active_slot(&mut self, _slot: u8) -> Result<(), Error>;

    /// Sets the reboot reason for the next reboot.
    fn set_reboot_reason(&mut self, _reason: RebootReason) -> Result<(), Error>;

    /// Gets the reboot reason for this boot.
    fn get_reboot_reason(&mut self) -> Result<RebootReason, Error>;
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
        {
            let newline = $ops.console_newline();
            gbl_print!($ops, $($x,)*);
            gbl_print!($ops, "{}", newline);
        }
    };
}

#[cfg(test)]
pub(crate) mod test {
    use super::*;
    use crate::error::IntegrationError;
    use crate::partition::GblDisk;
    use abr::{get_and_clear_one_shot_bootloader, get_boot_slot};
    use avb::{CertOps, Ops};
    use avb_test::TestOps as AvbTestOps;
    use core::{
        fmt::Write,
        ops::{Deref, DerefMut},
    };
    use fdt::Fdt;
    use gbl_async::block_on;
    use gbl_storage::{new_gpt_max, Disk, GptMax, RamBlockIo};
    use libutils::snprintf;
    use std::{
        collections::{HashMap, LinkedList},
        ffi::CString,
    };
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
            self.0.push(TestGblDisk::new_gpt(
                Disk::new_ram_alloc(512, 512, data.as_ref().to_vec()).unwrap(),
                new_gpt_max(),
            ));
            let _ = block_on(self.0.last().unwrap().sync_gpt());
        }

        /// Adds a raw partition disk.
        pub(crate) fn add_raw_device(&mut self, name: &CStr, data: impl AsRef<[u8]>) {
            // For raw partition, use block_size=alignment=1 for simplicity.
            TestGblDisk::new_raw(Disk::new_ram_alloc(1, 1, data.as_ref().to_vec()).unwrap(), name)
                .and_then(|v| Ok(self.0.push(v)))
                .unwrap()
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
    pub(crate) struct FakeGblOps<'a, 'd> {
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

        /// For checking that `Self::reboot` is called.
        pub rebooted: bool,

        /// For return by `Self::expected_os()`
        pub os: Option<Os>,

        /// For return by `Self::avb_validate_vbmeta_public_key`
        pub avb_key_validation_status: Option<AvbIoResult<KeyValidationStatus>>,

        /// For return by `Self::get_image_buffer()`
        pub image_buffers: HashMap<String, LinkedList<ImageBuffer<'d>>>,

        /// Custom device tree.
        pub custom_device_tree: Option<&'a [u8]>,

        /// Custom handler for `avb_handle_verification_result`
        pub avb_handle_verification_result: Option<
            &'a mut dyn FnMut(
                BootStateColor,
                Option<&CStr>,
                Option<&[u8]>,
                Option<&[u8]>,
                Option<&[u8]>,
                Option<&[u8]>,
                Option<&[u8]>,
                Option<&[u8]>,
            ) -> AvbIoResult<()>,
        >,
    }

    /// Print `console_out` output, which can be useful for debugging.
    impl<'a, 'd> Write for FakeGblOps<'a, 'd> {
        fn write_str(&mut self, s: &str) -> Result<(), std::fmt::Error> {
            Ok(print!("{s}"))
        }
    }

    impl<'a, 'd> FakeGblOps<'a, 'd> {
        /// For now we've just hardcoded the `zircon_add_device_zbi_items()` callback to add a
        /// single commandline ZBI item with these contents; if necessary we can generalize this
        /// later and allow tests to configure the ZBI modifications.
        pub const ADDED_ZBI_COMMANDLINE_CONTENTS: &'static [u8] = b"test_zbi_item";
        pub const TEST_BOOTLOADER_FILE_1: &'static [u8] = b"\x06test_1foo";
        pub const TEST_BOOTLOADER_FILE_2: &'static [u8] = b"\x06test_2bar";
        pub const GBL_TEST_VAR: &'static str = "gbl-test-var";
        pub const GBL_TEST_VAR_VAL: &'static str = "gbl-test-var-val";
        pub const GBL_TEST_BOOTCONFIG: &'static str = "arg1=val1\x0aarg2=val2\x0a";

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

    impl<'a, 'd> GblOps<'a, 'd> for FakeGblOps<'a, 'd> {
        fn console_out(&mut self) -> Option<&mut dyn Write> {
            Some(self)
        }

        fn should_stop_in_fastboot(&mut self) -> Result<bool, Error> {
            self.stop_in_fastboot.unwrap_or(Ok(false))
        }

        fn reboot(&mut self) {
            self.rebooted = true;
        }

        fn disks(
            &self,
        ) -> &'a [GblDisk<
            Disk<impl BlockIo + 'a, impl DerefMut<Target = [u8]> + 'a>,
            Gpt<impl DerefMut<Target = [u8]> + 'a>,
        >] {
            self.partitions
        }

        fn expected_os(&mut self) -> Result<Option<Os>, Error> {
            Ok(self.os)
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

        fn avb_validate_vbmeta_public_key(
            &self,
            _public_key: &[u8],
            _public_key_metadata: Option<&[u8]>,
        ) -> AvbIoResult<KeyValidationStatus> {
            self.avb_key_validation_status.clone().unwrap()
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

        fn avb_read_persistent_value(
            &mut self,
            name: &CStr,
            value: &mut [u8],
        ) -> AvbIoResult<usize> {
            self.avb_ops.read_persistent_value(name, value)
        }

        fn avb_write_persistent_value(&mut self, name: &CStr, value: &[u8]) -> AvbIoResult<()> {
            self.avb_ops.write_persistent_value(name, value)
        }

        fn avb_erase_persistent_value(&mut self, name: &CStr) -> AvbIoResult<()> {
            self.avb_ops.erase_persistent_value(name)
        }

        fn avb_handle_verification_result(
            &mut self,
            color: BootStateColor,
            digest: Option<&CStr>,
            boot_os_version: Option<&[u8]>,
            boot_security_patch: Option<&[u8]>,
            system_os_version: Option<&[u8]>,
            system_security_patch: Option<&[u8]>,
            vendor_os_version: Option<&[u8]>,
            vendor_security_patch: Option<&[u8]>,
        ) -> AvbIoResult<()> {
            match self.avb_handle_verification_result.as_mut() {
                Some(f) => (*f)(
                    color,
                    digest,
                    boot_os_version,
                    boot_security_patch,
                    system_os_version,
                    system_security_patch,
                    vendor_os_version,
                    vendor_security_patch,
                ),
                _ => Ok(()),
            }
        }

        fn get_image_buffer(
            &mut self,
            image_name: &str,
            _size: NonZeroUsize,
        ) -> GblResult<ImageBuffer<'d>> {
            if let Some(buf_list) = self.image_buffers.get_mut(image_name) {
                if let Some(buf) = buf_list.pop_front() {
                    return Ok(buf);
                };
            };

            gbl_println!(self, "FakeGblOps.get_image_buffer({image_name}) no buffer for the image");
            Err(IntegrationError::UnificationError(Error::Other(Some(
                "No buffer provided. Add sufficient buffers to FakeGblOps.image_buffers",
            ))))
        }

        fn get_custom_device_tree(&mut self) -> Option<&'a [u8]> {
            self.custom_device_tree
        }

        fn fixup_os_commandline<'c>(
            &mut self,
            _commandline: &CStr,
            _fixup_buffer: &'c mut [u8],
        ) -> Result<Option<&'c str>, Error> {
            Ok(None)
        }

        fn fixup_bootconfig<'c>(
            &mut self,
            _bootconfig: &[u8],
            fixup_buffer: &'c mut [u8],
        ) -> Result<Option<&'c [u8]>, Error> {
            let (out, _) = fixup_buffer.split_at_mut(Self::GBL_TEST_BOOTCONFIG.len());
            out.clone_from_slice(Self::GBL_TEST_BOOTCONFIG.as_bytes());
            Ok(Some(out))
        }

        fn fixup_device_tree(&mut self, fdt: &mut [u8]) -> Result<(), Error> {
            Fdt::new_mut(fdt).unwrap().set_property("chosen", c"fixup", &[1])?;
            Ok(())
        }

        fn select_device_trees(
            &mut self,
            device_tree: &mut device_tree::DeviceTreeComponentsRegistry,
        ) -> Result<(), Error> {
            // Select the first dtbo.
            match device_tree.components_mut().find(|v| !v.is_base_device_tree()) {
                Some(v) => v.selected = true,
                _ => {}
            }
            device_tree.autoselect()
        }

        fn fastboot_variable<'arg>(
            &mut self,
            name: &CStr,
            mut args: impl Iterator<Item = &'arg CStr> + Clone,
            out: &mut [u8],
        ) -> Result<usize, Error> {
            match name.to_str()? {
                Self::GBL_TEST_VAR => {
                    Ok(snprintf!(out, "{}:{:?}", Self::GBL_TEST_VAR_VAL, args.next()).len())
                }
                _ => Err(Error::NotFound),
            }
        }

        fn fastboot_visit_all_variables(
            &mut self,
            mut cb: impl FnMut(&[&CStr], &CStr),
        ) -> Result<(), Error> {
            cb(
                &[CString::new(Self::GBL_TEST_VAR).unwrap().as_c_str(), c"1"],
                CString::new(format!("{}:1", Self::GBL_TEST_VAR_VAL)).unwrap().as_c_str(),
            );
            cb(
                &[CString::new(Self::GBL_TEST_VAR).unwrap().as_c_str(), c"2"],
                CString::new(format!("{}:2", Self::GBL_TEST_VAR_VAL)).unwrap().as_c_str(),
            );
            Ok(())
        }

        fn slots_metadata(&mut self) -> Result<SlotsMetadata, Error> {
            unimplemented!();
        }

        fn get_current_slot(&mut self) -> Result<Slot, Error> {
            unimplemented!()
        }

        fn get_next_slot(&mut self, _: bool) -> Result<Slot, Error> {
            unimplemented!()
        }

        fn set_active_slot(&mut self, _: u8) -> Result<(), Error> {
            unimplemented!()
        }

        fn set_reboot_reason(&mut self, _: RebootReason) -> Result<(), Error> {
            unimplemented!()
        }

        fn get_reboot_reason(&mut self) -> Result<RebootReason, Error> {
            unimplemented!()
        }
    }

    #[test]
    fn test_fuchsia_reboot_bootloader() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"durable_boot", [0x00u8; 4 * 1024]);
        let mut gbl_ops = FakeGblOps::new(&storage);
        gbl_ops.os = Some(Os::Fuchsia);
        (gbl_ops.reboot_bootloader().unwrap())();
        assert!(gbl_ops.rebooted);
        assert_eq!(get_and_clear_one_shot_bootloader(&mut GblAbrOps(&mut gbl_ops)), Ok(true));
    }

    #[test]
    fn test_non_fuchsia_reboot_bootloader() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"durable_boot", [0x00u8; 4 * 1024]);
        let mut gbl_ops = FakeGblOps::new(&storage);
        gbl_ops.os = Some(Os::Android);
        assert!(gbl_ops.reboot_bootloader().is_err_and(|e| e == Error::Unsupported));
        assert_eq!(get_and_clear_one_shot_bootloader(&mut GblAbrOps(&mut gbl_ops)), Ok(false));
    }

    #[test]
    fn test_fuchsia_reboot_recovery() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"durable_boot", [0x00u8; 4 * 1024]);
        let mut gbl_ops = FakeGblOps::new(&storage);
        gbl_ops.os = Some(Os::Fuchsia);
        (gbl_ops.reboot_recovery().unwrap())();
        assert!(gbl_ops.rebooted);
        // One shot recovery is set.
        assert_eq!(get_boot_slot(&mut GblAbrOps(&mut gbl_ops), true), (SlotIndex::R, false));
        assert_eq!(get_boot_slot(&mut GblAbrOps(&mut gbl_ops), true), (SlotIndex::A, false));
    }

    #[test]
    fn test_non_fuchsia_reboot_recovery() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"durable_boot", [0x00u8; 4 * 1024]);
        let mut gbl_ops = FakeGblOps::new(&storage);
        gbl_ops.os = Some(Os::Android);
        assert!(gbl_ops.reboot_recovery().is_err_and(|e| e == Error::Unsupported));
        // One shot recovery is not set.
        assert_eq!(get_boot_slot(&mut GblAbrOps(&mut gbl_ops), true), (SlotIndex::A, false));
    }
}
