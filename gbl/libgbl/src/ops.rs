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

use crate::{
    constants::FASTBOOT_PARTITION_TYPE_LEN,
    gbl_avb::{
        state::{KeyValidationStatus, VerificationStatus},
        ArrayMaxSpecializedParts, AvbDeviceStatus, AvbPartition, AvbProperty, Fdr, LoadPartition,
        SpecializedPartition,
    },
    gbl_println,
    metrics::{FirmwareVersionMetrics, GblMetrics, GblTime},
    partition::{
        check_part_unique, read_unique_partition, read_unique_partition_sync,
        write_unique_partition, write_unique_partition_sync, GblDisk,
    },
};
pub use abr::{set_one_shot_bootloader, set_one_shot_recovery, Ops as AbrOps, SlotIndex};
use arrayvec::ArrayVec;
use bytes::buf::UninitSlice;
use core::{
    ffi::CStr,
    fmt::{Display, Write},
    ops::{Deref, DerefMut},
    result::Result,
};
use libprofile::ProfileBackend;
#[cfg(feature = "fuchsia")]
use libutils::aligned_subslice;
use libutils::{buffer_pool::BufferPool, cstr_buffer};

// Re-exports of types from other dependencies that appear in the APIs of this library.
pub use avb::{
    CertPermanentAttributes, IoError as AvbIoError, IoResult as AvbIoResult, SHA256_DIGEST_SIZE,
};
pub use fastboot::{
    CommandExecType, FailSender, InfoSender, LockState, LockType, OkaySender, Unlockability,
};
pub use gbl_storage::{BlockIo, Disk, Gpt};
use liberror::Error;
pub use libutils::arch_timestamp;
pub use slots::Slot;
#[cfg(feature = "fuchsia")]
pub use zbi::{ZbiContainer, ZBI_ALIGNMENT_USIZE};

use super::device_tree::DtComponentsRegistry;
use super::slots;

/// Target Type of OS to boot.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Os {
    /// Android
    Android,
    /// Fuchsia
    Fuchsia,
}

/// One-shot boot mode override options.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum OneShotBootMode {
    /// Bootloader.
    Bootloader,
    /// Recovery.
    Recovery,
}

/// Represents a partition buffer for return by `GblOps::get_partition_buffer()`.
pub enum PartitionBuffer<T> {
    /// Buffer with preloaded partition image.
    Preloaded(T),
    /// Designated buffer for loading the partition image.
    Designated(T),
}

/// Requested random number generator algorithm.
pub enum RngAlgorithm {
    /// No specific algorithm is required. Up to implementation to decide.
    Default,
    /// Entropy directly from the source, without it going through some deterministic
    /// random bit generator.
    Raw,
}

/// Partition type to be returned for `fastboot getvar partition-type:`.
#[derive(Copy, Clone)]
pub struct FastbootPartitionType {
    len: usize,
    buf: [u8; FASTBOOT_PARTITION_TYPE_LEN],
}

impl Deref for FastbootPartitionType {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &self.buf[..self.len]
    }
}

impl From<(usize, [u8; FASTBOOT_PARTITION_TYPE_LEN])> for FastbootPartitionType {
    fn from((len, buf): (usize, [u8; FASTBOOT_PARTITION_TYPE_LEN])) -> Self {
        Self { len, buf }
    }
}

impl FastbootPartitionType {
    pub(crate) const fn from_slice(b: &[u8]) -> Option<Self> {
        let mut buf = [0u8; _];
        if b.len() > buf.len() {
            return None;
        }
        buf.split_at_mut(b.len()).0.copy_from_slice(b);
        Some(Self { len: b.len(), buf })
    }
}

impl Default for FastbootPartitionType {
    fn default() -> Self {
        const { Self::from_slice(b"raw").unwrap() }
    }
}

impl FastbootPartitionType {
    fn as_str(&self) -> &str {
        str::from_utf8(self).unwrap_or("raw")
    }
}

impl Display for FastbootPartitionType {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

// https://stackoverflow.com/questions/41081240/idiomatic-callbacks-in-rust
// should we use traits for this? or optional/box FnMut?
//
/* TODO: b/312612203 - needed callbacks:
missing:
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

    /// Reboots the system into the last set boot mode.
    ///
    /// If successful this method will not return.
    /// If an error is generated instead, the caller is expected to log the error
    /// and bring the system to a halt, usually by entering an infinite loop.
    fn reboot(&mut self) -> Result<!, Error>;

    /// Returns the list of disk devices on this platform.
    ///
    /// Notes that the return slice doesn't capture the life time of `&self`, meaning that the slice
    /// reference must be producible without borrowing `Self`. This is intended and necessary to
    /// make disk IO and the rest of GblOps methods independent and parallelizable, which is
    /// required for features such as parallel fastboot flash, download and other commands. For
    /// implementation, this typically means that the `GblOps` object should hold a reference of the
    /// array instead of owning it.
    fn disks(
        &self,
    ) -> &'a [GblDisk<
        Disk<impl BlockIo + 'a, impl BufferPool + 'a>,
        Gpt<impl DerefMut<Target = [u8]> + 'a>,
    >];

    /// Reads data from a partition.
    async fn read_from_partition<'b>(
        &mut self,
        part: &str,
        off: u64,
        out: impl Into<&'b mut UninitSlice>,
    ) -> Result<(), Error> {
        read_unique_partition(self.disks(), part, off, out).await
    }

    /// Reads data from a partition synchronously.
    fn read_from_partition_sync<'b>(
        &mut self,
        part: &str,
        off: u64,
        out: impl Into<&'b mut UninitSlice>,
    ) -> Result<(), Error> {
        read_unique_partition_sync(self.disks(), part, off, out)
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
        write_unique_partition_sync(self.disks(), part, off, data)
    }

    /// Returns the size of a partition. Returns Ok(None) if partition doesn't exist.
    fn partition_size(&mut self, part: &str) -> Result<Option<u64>, Error> {
        match check_part_unique(self.disks(), part) {
            Ok((_, p)) => Ok(Some(p.size()?)),
            Err(Error::NotFound) => Ok(None),
            Err(e) => Err(e),
        }
    }

    /// Fills `buffer` with generated random data. The entire buffer must be populated,
    /// otherwise an appropriate error is returned.
    ///
    /// # Returns
    ///
    /// `Err(Error::Unsupported)` if the requested algorithm is not supported.
    /// `Err(Error::NotReady)` if there is not enough random data available at the moment.
    /// `Err(Error::NotFound)` if RNG driver isn't available.
    /// `Err(_)` if any other error, treated as unrecoverable RNG failure.
    /// `Ok(())` if the buffer was successfully filled with random data.
    fn get_random_bytes(&self, algorithm: RngAlgorithm, buffer: &mut [u8]) -> Result<(), Error>;

    /// Returns which OS to load, or `None` to try to auto-detect based on disk layout & contents.
    fn expected_os(&mut self) -> Result<Option<Os>, Error>;

    /// Returns if the expected_os is fuchsia
    #[cfg(feature = "fuchsia")]
    fn expected_os_is_fuchsia(&mut self) -> Result<bool, Error> {
        // TODO(b/374776896): Implement auto detection.
        Ok(self.expected_os()?.map(|v| v == Os::Fuchsia).unwrap_or(false))
    }

    /// Adds device specific ZBI items to the given `container`
    #[cfg(feature = "fuchsia")]
    fn zircon_add_device_zbi_items(
        &mut self,
        container: &mut ZbiContainer<&mut [u8]>,
    ) -> Result<(), Error>;

    /// Gets a buffer for staging bootloader file from fastboot.
    ///
    /// Fuchsia uses bootloader file for staging SSH key in development flow.
    ///
    /// Returns `None` if the platform does not intend to support it.
    #[cfg(feature = "fuchsia")]
    fn get_zbi_bootloader_files_buffer(&mut self) -> Option<&mut [u8]>;

    /// Gets the aligned part of buffer returned by `get_zbi_bootloader_files_buffer()` according to
    /// ZBI alignment requirement.
    #[cfg(feature = "fuchsia")]
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

    // The following is a selective subset of the interfaces in `avb::Ops` and `avb::CertOps` needed
    // by GBL's usage of AVB. The rest of the APIs are either not relevant to or are implemented and
    // managed by GBL APIs.

    /// Returns the set of specialized partitions and their requested handling attributes.
    ///
    /// This is the raw set of attributes provided by the platform; most callers will want to use
    /// [avb_read_partition_attributes] instead which provides the defaults defined by GBL's docs.
    fn avb_read_partition_attributes_raw(
        &mut self,
    ) -> AvbIoResult<ArrayMaxSpecializedParts<SpecializedPartition>>;

    /// Returns the set of specialized partitions with GBL defaults applied.
    ///
    /// These defaults are described in the UEFI protocol documentation at
    /// `bootable/libbootloader/gbl/docs/gbl_efi_avb_protocol.md`. These are UEFI defaults so
    /// theoretically could live in the UEFI backend implementation instead of here in the
    /// platform-generic `Ops`, but it seems likely we want this behavior for all backends so
    /// for now it's here.
    ///
    /// The defaults provided are:
    /// * missing backend implementation does not return an error
    /// * "userdata" and "metadata" are marked as FDR partitions unless opted out
    ///
    /// This function does *not* provide any default partitions to verify, since these partitions
    /// may vary depending on the boot flow this is called from.
    ///
    /// Additionally, this function returns an iterator rather than an `ArrayVec` because it may
    /// append additional items which would exceed the `ArrayMaxSpecializedParts` capacity.
    fn avb_read_partition_attributes(
        &mut self,
    ) -> AvbIoResult<impl Iterator<Item = SpecializedPartition> + 'static> {
        let attributes = match self.avb_read_partition_attributes_raw() {
            Ok(attributes) => attributes,
            Err(AvbIoError::NotImplemented) => Default::default(), // Hook is optional
            Err(e) => return Err(e),
        };

        // If these partitions aren't explicitly provided, they are added to the end.
        let mut default_partitions = ArrayVec::from([
            SpecializedPartition {
                name_buffer: cstr_buffer("userdata"),
                fdr: Fdr::Yes,
                ..Default::default()
            },
            SpecializedPartition {
                name_buffer: cstr_buffer("metadata"),
                fdr: Fdr::Yes,
                ..Default::default()
            },
        ]);
        default_partitions.retain(|p| !attributes.iter().any(|a| a.name_cstr() == p.name_cstr()));

        Ok(attributes.into_iter().chain(default_partitions.into_iter()))
    }

    /// Reads the AVB device status.
    fn avb_read_device_status(&mut self) -> AvbIoResult<AvbDeviceStatus>;

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
    fn avb_handle_verification_result<'b>(
        &mut self,
        status: VerificationStatus,
        digest: Option<&CStr>,
        properties: Option<impl Iterator<Item = AvbProperty<'b>>>,
        partitions: Option<impl Iterator<Item = AvbPartition<'b>>>,
    ) -> AvbIoResult<()>;

    /// Performs a factory data reset.
    fn factory_data_reset(&mut self) -> Result<(), Error>;

    /// Check AVF vendor implementations are provided.
    fn avf_is_supported(&mut self) -> Result<bool, Error>;

    /// Returns vendor device handover.
    ///
    /// To be wrapped by GBL and provided to HLOS via the device tree.
    fn avf_read_vendor_dice_handover<'c>(
        &mut self,
        buffer: &'c mut [u8],
    ) -> Result<&'c [u8], Error>;

    /// Returns the Secret Keeper public key.
    ///
    /// To be placed into the reference DT, which is built by GBL and passed to HLOS
    /// via the device tree.
    fn avf_read_secretkeeper_public_key<'c>(
        &mut self,
        buffer: &'c mut [u8],
    ) -> Result<Option<&'c [u8]>, Error>;

    /// Gets platform reserved buffer for loading the given type of partition image.
    ///
    /// Implementation should always return the same and unique buffer for `img` until
    /// `sync_partition_buffer()` is called. If caller has not dropped a previously returned
    /// instance, implementation should return `Err(Error::NotReady)`.
    ///
    /// # Returns
    ///
    /// Returns `Err(Error::NotReady)`, if a previous returned instance is still in scope.
    /// Returns `Err(Error::NotFound)`, if buffer is not found.
    /// Returns `Ok(PartitionBuffer::Designated(..))`, if buffer is found.
    /// Returns `Ok(PartitionBuffer::Preloaded(..))`, if buffer is found and contains preloaded
    /// data.
    fn get_partition_buffer(
        &self,
        img: LoadPartition,
    ) -> Result<PartitionBuffer<impl DerefMut<Target = [u8]> + 'a>, Error>;

    /// Notifies the firmware to inspect or update buffer for return by `get_partition_buffer()`.
    ///
    /// # Args
    ///
    /// * `sync_preloaded`: Set to true to request backend to re-sync preloaded partition buffer.
    ///
    /// # Returns
    ///
    /// Returns `Err(Error::NotReady)`, if some previously returned buffer is still in use.
    fn sync_partition_buffer(&mut self, sync_preloaded: bool) -> Result<(), Error>;

    /// Requests an OS bootconfig to be used alongside the one built by GBL.
    ///
    /// The returned bootconfig will be verified and appended on top of the bootconfig
    /// built by GBL. Refer to the behavior specified for the corresponding UEFI interface:
    /// https://cs.android.com/android/kernel/superproject/+/common-android-mainline:bootable/libbootloader/gbl/docs/gbl_os_configuration_protocol.md
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
    /// https://cs.android.com/android/kernel/superproject/+/common-android-mainline:bootable/libbootloader/gbl/docs/gbl_os_configuration_protocol.md
    fn select_device_trees(&mut self, components: &mut DtComponentsRegistry) -> Result<(), Error>;

    /// Selects FIT configuration from FIT FDT.
    ///
    /// Refer to the behavior specified for the corresponding UEFI
    /// interface:
    /// https://cs.android.com/android/kernel/superproject/+/common-android-mainline:bootable/libbootloader/gbl/docs/gbl_os_configuration_protocol.md
    fn select_fit_configuration(
        &mut self,
        fit: &[u8],
        metadata: Option<&[u8]>,
    ) -> Result<Option<usize>, Error>;

    /// Provide writtable buffer of the device tree built by GBL.
    ///
    /// Modified device tree will be verified and used to boot a device. Refer to the behavior
    /// specified for the corresponding UEFI interface:
    /// https://cs.android.com/android/kernel/superproject/+/common-android-mainline:bootable/libbootloader/gbl/docs/efi_integration.md
    fn fixup_device_tree(&mut self, device_tree: &mut [u8]) -> Result<(), Error>;

    /// Gets platform-specific fastboot variable.
    ///
    /// # Args
    ///
    /// * `name`: Variable name.
    /// * `args`: Additional arguments.
    /// * `out`: The output buffer for the value of the variable. Must be an ASCII string.
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
        cb: impl FnMut(&mut Self, &[&CStr], &CStr),
    ) -> Result<(), Error>;

    /// Handler for `fastboot flashing lock|unlock` and
    /// `fastboot flashing lock_critical|unlock_critical`.
    ///
    /// # Args
    ///
    /// * `lock_type`: The type of lock to set.
    /// * `lock_state`: The target lock state to set.
    fn avb_write_lock_state(
        &mut self,
        lock_type: LockType,
        lock_state: LockState,
    ) -> Result<(), Error>;

    /// Handler for `fastboot flashing get_unlock_ability`.
    ///
    /// # Returns
    ///
    /// Ok(Unlockability::Unlockable) if device can be unlocked,
    /// Ok(Unlockability::Secured) if device cannot be unlocked.
    fn fastboot_get_unlock_ability(&mut self) -> Result<Unlockability, Error>;

    /// Reads out data staged by the platform to upload to the host during `fastboot get_staged`.
    ///
    /// # Args
    ///
    /// * `out`: The output buffer.
    ///
    /// # Returns
    ///
    /// * On success, returns the size of the actual read data and size of remaining data.
    fn fastboot_get_staged(&mut self, _out: &mut [u8]) -> Result<(usize, usize), Error>;

    /// Checks if the given fastboot command is allowed.
    ///
    /// # Args:
    ///
    /// * `args`: An iterator of CStrs. The first one is the command, followed by arguments.
    /// * `download`: The current downloaded data buffer.
    /// * `download_used`: Size of the download buffer that is used.
    /// * `sender`: An implementation that provides APIs for sending fastboot OKAY/FAIL/INFO
    ///   messages.
    ///
    /// Returns Ok((true, _)) if allowed, Ok((false, <msg>)) if disallowed.
    fn fastboot_command_exec<'arg, Sender: InfoSender + OkaySender + FailSender>(
        &mut self,
        args: impl Iterator<Item = &'arg CStr> + Clone,
        download: &mut [u8],
        download_used: usize,
        sender: Sender,
    ) -> Result<CommandExecType, Error>;

    /// Gets the partition type.
    fn fastboot_get_partition_type(&mut self, part: &str) -> Result<FastbootPartitionType, Error>;

    /// Returns the slot count.
    fn get_slot_count(&mut self) -> Result<u8, Error>;

    /// Get the slot info for provided index.
    ///
    /// # Args
    ///
    /// * `slot`: The numeric index of the slot.
    fn get_slot_info(&mut self, slot: u8) -> Result<Slot, Error>;

    /// Gets the current boot slot.
    fn get_current_slot(&mut self) -> Result<Slot, Error>;

    /// Sets the active slot for the next A/B decision.
    ///
    /// # Args
    ///
    /// * `slot`: The numeric index of the slot.
    fn set_active_slot(&mut self, _slot: u8) -> Result<(), Error>;

    /// Gets the one-shot boot mode.
    fn get_one_shot_boot_mode(&mut self) -> Result<Option<OneShotBootMode>, Error>;

    /// Returns whether GBL should pause after loading images and before booting OS .
    fn one_shot_pause_fastboot_after_load(&mut self) -> bool {
        // TODO(b/468009593): Removes and implements in all existing backends once breaking changes
        // are in.
        false
    }

    /// Handles a loaded OS before booting.
    ///
    /// # Args
    ///
    /// * `kernel`: Kernel image.
    /// * `ramdisk`: Ramdisk image.
    /// * `device_tree`: Device tree image.
    ///
    /// Returns Ok(()) if loaded OS images are successfully handled.
    /// Returns Err(Error::Unsupported) if FW doesn't need to handle OS images.
    fn handle_loaded_os(
        &mut self,
        kernel: &[u8],
        ramdisk: &[u8],
        device_tree: &[u8],
    ) -> Result<(), Error>;

    /// Returns the base stack pointer if available
    fn get_base_sp(&mut self) -> Option<usize>;

    /// Calculates the current stack usage given the stack pointer.
    ///
    /// # Returns None if Self::get_base_sp() returns None.
    /// # Returns Some(usize::MAX) if current stack address is higher than get_base_sp();
    #[inline(never)]
    fn calculate_stack_usage(&mut self, sp: usize) -> Option<usize> {
        Some(self.get_base_sp()?.checked_sub(sp).unwrap_or(usize::MAX))
    }

    /// Displays stack usage with the given stack pointer and location info.
    ///
    /// it is recommended to use macro `gbl_log_stack_usage` if displaying for the callsite.
    #[inline(never)]
    fn log_stack_usage_with_location(&mut self, sp: usize, file: &str, line: u32) {
        let buffer = &mut [0u8; 256][..];
        let s = match self.calculate_stack_usage(sp) {
            Some(v) => libutils::snprintf!(buffer, "{file}:{line}, stack usage: {}", v),
            _ => "base sp not set",
        };
        gbl_println!(self, "{s}");
    }

    /// Provides backend specific hooks for profiling.
    fn get_profiling_backend(&self) -> impl ProfileBackend;

    /// Gets the firmware api level.
    fn get_fw_api_level(&self) -> Result<u64, Error>;

    /// Returns the hardware time interface.
    fn get_time(&self) -> Option<&impl GblTime>;

    /// Returns a guard for mutable metrics access.
    ///
    /// This method implements internal mutability, so the implementation should be aware of
    /// synchronization. The caller should treat the return type as a `MutexGuard` and ensure
    /// minimal lifetime (drop as soon as possible) to avoid deadlocks.
    fn get_metrics(&self) -> Option<impl DerefMut<Target = GblMetrics> + '_>;

    /// Returns firmware version metrics.
    fn get_firmware_version_metrics(&self) -> FirmwareVersionMetrics;
}

/// Prints the stack usage at the callsite.
#[macro_export]
macro_rules! gbl_log_stack_usage {
    ($ops:expr) => {
        $crate::GblOps::log_stack_usage_with_location(
            $ops,
            libutils::get_sp(),
            core::file!(),
            core::line!(),
        )
    };
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
            // Print timestamp if supported
            let _ = $crate::ops::arch_timestamp().inspect(|v| {
                $crate::gbl_print!($ops, "[{:.4}] ", v.as_secs_f32());
            });
            let newline = $ops.console_newline();
            $crate::gbl_print!($ops, $($x,)*);
            $crate::gbl_print!($ops, "{}", newline);
        }
    };
}

/// Inherits everything from `ops` but override a few such as read boot_a from
/// bootimg_buffer, avb_write_rollback_index(), slot operation etc
pub(crate) struct RambootOps<'a, T> {
    pub(crate) ops: &'a mut T,
    pub(crate) ram_partitions: &'a [(&'a str, &'a [u8])],
}

impl<'a, T> RambootOps<'a, T> {
    /// Reads from ram partitions.
    pub fn read_from_ram_partition<'b>(
        &mut self,
        part: &str,
        off: u64,
        out: impl Into<&'b mut UninitSlice>,
    ) -> Result<(), Error> {
        let out = out.into();
        match self.ram_partitions.iter().find(|(name, _)| *name == part) {
            Some((_, data)) => {
                let buf = data
                    .get(off.try_into()?..)
                    .and_then(|v| v.get(..out.len()))
                    .ok_or(Error::OutOfRange)?;
                Ok(out.copy_from_slice(buf))
            }
            _ => Err(Error::NotFound),
        }
    }
}

impl<'r, 'a: 'r, T: GblOps<'a>> GblOps<'a> for RambootOps<'r, T> {
    fn console_out(&mut self) -> Option<&mut dyn Write> {
        self.ops.console_out()
    }

    fn reboot(&mut self) -> Result<!, Error> {
        self.ops.reboot()
    }

    fn disks(
        &self,
    ) -> &'a [GblDisk<
        Disk<impl BlockIo + 'a, impl BufferPool + 'a>,
        Gpt<impl DerefMut<Target = [u8]> + 'a>,
    >] {
        self.ops.disks()
    }

    fn expected_os(&mut self) -> Result<Option<Os>, Error> {
        self.ops.expected_os()
    }

    fn get_random_bytes(&self, algorithm: RngAlgorithm, buffer: &mut [u8]) -> Result<(), Error> {
        self.ops.get_random_bytes(algorithm, buffer)
    }

    #[cfg(feature = "fuchsia")]
    fn zircon_add_device_zbi_items(
        &mut self,
        container: &mut ZbiContainer<&mut [u8]>,
    ) -> Result<(), Error> {
        self.ops.zircon_add_device_zbi_items(container)
    }

    #[cfg(feature = "fuchsia")]
    fn get_zbi_bootloader_files_buffer(&mut self) -> Option<&mut [u8]> {
        self.ops.get_zbi_bootloader_files_buffer()
    }

    fn avb_read_partition_attributes_raw(
        &mut self,
    ) -> AvbIoResult<ArrayMaxSpecializedParts<SpecializedPartition>> {
        self.ops.avb_read_partition_attributes_raw()
    }

    fn avb_read_device_status(&mut self) -> AvbIoResult<AvbDeviceStatus> {
        self.ops.avb_read_device_status()
    }

    fn avb_read_rollback_index(&mut self, _rollback_index_location: usize) -> AvbIoResult<u64> {
        self.ops.avb_read_rollback_index(_rollback_index_location)
    }

    fn avb_write_rollback_index(&mut self, _: usize, _: u64) -> AvbIoResult<()> {
        // We don't want to persist AVB related data such as updating antirollback indices.
        Ok(())
    }

    fn avb_read_persistent_value(&mut self, name: &CStr, value: &mut [u8]) -> AvbIoResult<usize> {
        self.ops.avb_read_persistent_value(name, value)
    }

    fn avb_write_persistent_value(&mut self, _: &CStr, _: &[u8]) -> AvbIoResult<()> {
        // We don't want to persist AVB related data such as updating current VBH.
        Ok(())
    }

    fn avb_erase_persistent_value(&mut self, _: &CStr) -> AvbIoResult<()> {
        // We don't want to persist AVB related data such as updating current VBH.
        Ok(())
    }

    fn avb_cert_read_permanent_attributes(
        &mut self,
        attributes: &mut CertPermanentAttributes,
    ) -> AvbIoResult<()> {
        self.ops.avb_cert_read_permanent_attributes(attributes)
    }

    fn avb_cert_read_permanent_attributes_hash(&mut self) -> AvbIoResult<[u8; SHA256_DIGEST_SIZE]> {
        self.ops.avb_cert_read_permanent_attributes_hash()
    }

    fn get_partition_buffer(
        &self,
        img: LoadPartition,
    ) -> Result<PartitionBuffer<impl DerefMut<Target = [u8]> + 'a>, Error> {
        self.ops.get_partition_buffer(img)
    }

    fn sync_partition_buffer(&mut self, sync_preloaded: bool) -> Result<(), Error> {
        self.ops.sync_partition_buffer(sync_preloaded)
    }

    fn fixup_bootconfig<'c>(
        &mut self,
        bootconfig: &[u8],
        fixup_buffer: &'c mut [u8],
    ) -> Result<Option<&'c [u8]>, Error> {
        self.ops.fixup_bootconfig(bootconfig, fixup_buffer)
    }

    fn fixup_device_tree(&mut self, device_tree: &mut [u8]) -> Result<(), Error> {
        self.ops.fixup_device_tree(device_tree)
    }

    fn select_device_trees(
        &mut self,
        components_registry: &mut DtComponentsRegistry,
    ) -> Result<(), Error> {
        self.ops.select_device_trees(components_registry)
    }

    fn select_fit_configuration(
        &mut self,
        fit: &[u8],
        metadata: Option<&[u8]>,
    ) -> Result<Option<usize>, Error> {
        self.ops.select_fit_configuration(fit, metadata)
    }

    async fn read_from_partition<'b>(
        &mut self,
        part: &str,
        off: u64,
        out: impl Into<&'b mut UninitSlice>,
    ) -> Result<(), Error> {
        let out = out.into();
        match self.read_from_ram_partition(part, off, &mut *out) {
            Err(Error::NotFound) => self.ops.read_from_partition(part, off, out).await,
            v => v,
        }
    }

    fn read_from_partition_sync<'b>(
        &mut self,
        part: &str,
        off: u64,
        out: impl Into<&'b mut UninitSlice>,
    ) -> Result<(), Error> {
        let out = out.into();
        match self.read_from_ram_partition(part, off, &mut *out) {
            Err(Error::NotFound) => self.ops.read_from_partition_sync(part, off, out),
            v => v,
        }
    }

    /// Writes data to a partition.
    async fn write_to_partition(&mut self, _: &str, _: u64, _: &mut [u8]) -> Result<(), Error> {
        Ok(())
    }

    fn partition_size(&mut self, part: &str) -> Result<Option<u64>, Error> {
        match self.ram_partitions.iter().find(|(name, _)| *name == part) {
            Some((_, data)) => Ok(Some(data.len().try_into().unwrap())),
            _ => self.ops.partition_size(part),
        }
    }

    fn avb_handle_verification_result<'b>(
        &mut self,
        status: VerificationStatus,
        digest: Option<&CStr>,
        properties: Option<impl Iterator<Item = AvbProperty<'b>>>,
        partitions: Option<impl Iterator<Item = AvbPartition<'b>>>,
    ) -> AvbIoResult<()> {
        self.ops.avb_handle_verification_result(status, digest, properties, partitions)
    }

    fn factory_data_reset(&mut self) -> Result<(), Error> {
        // Ramboot should never call this interface.
        unreachable!();
    }

    fn avb_validate_vbmeta_public_key(
        &self,
        public_key: &[u8],
        public_key_metadata: Option<&[u8]>,
    ) -> AvbIoResult<KeyValidationStatus> {
        self.ops.avb_validate_vbmeta_public_key(public_key, public_key_metadata)
    }

    fn avf_is_supported(&mut self) -> Result<bool, Error> {
        self.ops.avf_is_supported()
    }

    fn avf_read_vendor_dice_handover<'c>(
        &mut self,
        buffer: &'c mut [u8],
    ) -> Result<&'c [u8], Error> {
        self.ops.avf_read_vendor_dice_handover(buffer)
    }

    fn avf_read_secretkeeper_public_key<'c>(
        &mut self,
        buffer: &'c mut [u8],
    ) -> Result<Option<&'c [u8]>, Error> {
        self.ops.avf_read_secretkeeper_public_key(buffer)
    }

    fn get_slot_count(&mut self) -> Result<u8, Error> {
        // Ramboot is not suppose to call this interface.
        unreachable!()
    }

    fn get_slot_info(&mut self, slot: u8) -> Result<Slot, Error> {
        self.ops.get_slot_info(slot)
    }

    fn get_current_slot(&mut self) -> Result<Slot, Error> {
        // Ramboot is slotless
        Err(Error::Unsupported)
    }

    fn set_active_slot(&mut self, _: u8) -> Result<(), Error> {
        // Ramboot is not suppose to call this interface.
        unreachable!()
    }

    fn get_one_shot_boot_mode(&mut self) -> Result<Option<OneShotBootMode>, Error> {
        // Ramboot is not suppose to call this interface.
        unreachable!()
    }

    fn handle_loaded_os(
        &mut self,
        kernel: &[u8],
        ramdisk: &[u8],
        device_tree: &[u8],
    ) -> Result<(), Error> {
        self.ops.handle_loaded_os(kernel, ramdisk, device_tree)
    }

    fn get_base_sp(&mut self) -> Option<usize> {
        self.ops.get_base_sp()
    }

    fn fastboot_variable<'arg>(
        &mut self,
        _: &CStr,
        _: impl Iterator<Item = &'arg CStr> + Clone,
        _: &mut [u8],
    ) -> Result<usize, Error> {
        // Ramboot should not need this.
        unreachable!();
    }

    fn fastboot_visit_all_variables(
        &mut self,
        _: impl FnMut(&mut Self, &[&CStr], &CStr),
    ) -> Result<(), Error> {
        // Ramboot should not need this.
        unreachable!();
    }

    fn fastboot_get_staged(&mut self, _: &mut [u8]) -> Result<(usize, usize), Error> {
        // Ramboot should not need this.
        unreachable!();
    }

    fn avb_write_lock_state(&mut self, _: LockType, _: LockState) -> Result<(), Error> {
        // Ramboot should not need this.
        unreachable!();
    }

    fn fastboot_get_unlock_ability(&mut self) -> Result<Unlockability, Error> {
        // Ramboot should not need this.
        unreachable!();
    }

    fn fastboot_command_exec<'arg, Sender: InfoSender + OkaySender + FailSender>(
        &mut self,
        _: impl Iterator<Item = &'arg CStr> + Clone,
        _: &mut [u8],
        _: usize,
        _: Sender,
    ) -> Result<CommandExecType, Error> {
        // Ramboot should not need this.
        unreachable!();
    }

    fn fastboot_get_partition_type(&mut self, _part: &str) -> Result<FastbootPartitionType, Error> {
        unreachable!();
    }

    fn get_profiling_backend(&self) -> impl ProfileBackend {
        self.ops.get_profiling_backend()
    }

    fn get_fw_api_level(&self) -> Result<u64, Error> {
        self.ops.get_fw_api_level()
    }

    fn get_time(&self) -> Option<&impl GblTime> {
        self.ops.get_time()
    }

    fn get_metrics(&self) -> Option<impl DerefMut<Target = GblMetrics> + '_> {
        self.ops.get_metrics()
    }

    fn get_firmware_version_metrics(&self) -> FirmwareVersionMetrics {
        self.ops.get_firmware_version_metrics()
    }
}

#[cfg(test)]
pub(crate) mod test {
    use super::*;
    use crate::{
        android_boot::device_tree::{PROP_BOOTARGS, RNG_SEED_SIZE_BYTES},
        device_tree::{DtComponentType, DtComponentsRegistry},
        gbl_avb::{Critical, Verification},
        partition::GblDisk,
        slots::Bootability,
    };
    use avb::{CertOps, Ops};
    use avb_test::TestOps as AvbTestOps;
    use bootparams::commandline::CommandlineBuilder;
    use fdt::Fdt;
    use gbl_async::block_on;
    use gbl_storage::{new_gpt_max, Disk, GptMax, RamBlockIo};
    use libprofile::{ProfileTimer, Reporter};
    use libutils::snprintf;
    use std::{
        cell::{Cell, RefCell, RefMut},
        collections::{HashMap, VecDeque},
        ffi::CString,
        fmt::Debug,
        fmt::Write,
        ops::{Deref, DerefMut},
        time::Duration,
    };
    #[cfg(feature = "fuchsia")]
    use zbi::{ZbiFlags, ZbiType};

    /// Type of [GblDisk] in tests.
    pub(crate) type TestGblDisk =
        GblDisk<Disk<RamBlockIo<Vec<u8>>, ArrayVec<Option<Box<[u8]>>, 2>>, GptMax>;

    /// A small test helper to invoke closures and keep a shared invocation count.
    ///
    /// Supports interior mutability so that the main test logic can access the count while async
    /// tasks that might modify it are pending.
    pub(crate) struct CounterCallback {
        count: Cell<usize>,
    }

    impl CounterCallback {
        /// Creates a new [CounterCallback] initialized to 0.
        pub fn new() -> Self {
            Self { count: Cell::new(0) }
        }

        /// Returns the current number of times the callback has been invoked.
        pub fn count(&self) -> usize {
            self.count.get()
        }

        /// Returns a closure that increments the callback count.
        pub fn handler(&self) -> impl FnMut() -> Result<(), Error> + '_ {
            move || {
                self.count.set(self.count.get() + 1);
                Ok(())
            }
        }
    }

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
            self.0.as_slice()
        }
    }

    impl DerefMut for FakeGblOpsStorage {
        fn deref_mut(&mut self) -> &mut Self::Target {
            self.0.as_mut_slice()
        }
    }

    /// Converts a RefMut of type that can dereference to &mut [u8] to RefMut<'_, [u8]>
    pub(crate) fn into_refmut_bytes<'a>(
        val: RefMut<'a, impl DerefMut<Target = [u8]>>,
    ) -> RefMut<'a, [u8]> {
        RefMut::map(val, |f| &mut f[..])
    }

    /// Default [AvbDeviceStatus] value across the tests
    impl Default for AvbDeviceStatus {
        fn default() -> Self {
            Self {
                is_unlocked: false,
                is_unlocked_critical: false,
                is_dm_verity_error: false,
                is_unlockable: false,
            }
        }
    }

    pub enum SenderMessage {
        Okay(String),
        Fail(String),
        Info(String),
    }

    /// A wrapper around [Result] for tests.
    ///
    /// Usage is similar to [Result], but adds:
    ///   * a [Default] implementation, so users can `#[derive(Default)]`
    ///   * [Deref]/[DerefMut] which automatically unwraps the [Result]
    ///
    /// The latter behavior is so that the most common test patters are simple and clear, so
    /// that modifying the contained value looks like this:
    ///
    /// ```
    /// # Automatic deref to internal type so we can modify fields directly
    /// my_result.field_a = 20;
    ///
    /// # Without this, it would look something like:
    /// my_result.0.as_mut().unwrap().field_a = 20;
    /// ```
    ///
    /// If a test attempts to deref while the [Result] is an error value, it will panic.
    pub struct DefaultOk<T, E>(pub Result<T, E>);

    impl<T: Default, E> Default for DefaultOk<T, E> {
        fn default() -> Self {
            Self(Ok(T::default()))
        }
    }

    impl<T, E> From<E> for DefaultOk<T, E> {
        fn from(value: E) -> Self {
            Self(Err(value))
        }
    }

    impl<T: Default, E> DefaultOk<T, E> {
        /// Assigns an error.
        pub fn set_err(&mut self, err: E) {
            self.0 = Err(err);
        }
    }

    impl<T: Default, E: Debug> Deref for DefaultOk<T, E> {
        type Target = T;
        fn deref(&self) -> &Self::Target {
            match &self.0 {
                Ok(val) => val,
                Err(e) => panic!("Attempted to deref an error: {:?}", e),
            }
        }
    }

    impl<T: Default, E: Debug> DerefMut for DefaultOk<T, E> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            match &mut self.0 {
                Ok(val) => val,
                Err(e) => panic!("Attempted to deref an error: {:?}", e),
            }
        }
    }

    /// A fake implementation of [GblTime].
    pub struct FakeGblTime(RefCell<FakeGblTimeState>);

    struct FakeGblTimeState {
        ticks: Vec<u64>,
        index: usize,
    }

    impl FakeGblTime {
        pub fn new(ticks: Vec<u64>) -> Self {
            Self(RefCell::new(FakeGblTimeState { ticks, index: 0 }))
        }
    }

    impl GblTime for FakeGblTime {
        fn current_tick(&self) -> Result<u64, Error> {
            let mut state = self.0.borrow_mut();
            let val = state.ticks[state.index];
            state.index += 1;
            Ok(val)
        }

        fn elapsed_ticks(&self, start: u64) -> Result<u64, Error> {
            Ok(self.current_tick()? - start)
        }

        fn ticks_to_us(&self, ticks: u64) -> u64 {
            ticks
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

        /// For returned by `fn get_zbi_bootloader_files_buffer()`
        #[cfg(feature = "fuchsia")]
        pub zbi_bootloader_files_buffer: Vec<u8>,

        /// For checking that `Self::reboot` is called.
        pub rebooted: bool,

        /// For return by `Self::expected_os()`
        pub os: Option<Os>,

        /// For return by `Self::get_random_bytes()`
        pub get_random_bytes_error: Option<Error>,

        /// For return by `Self::avb_read_partition_attributes_raw()`
        pub avb_partition_attributes: Option<AvbIoResult<Vec<SpecializedPartition>>>,

        /// For return by `Self::avb_read_device_status`
        pub avb_device_status: DefaultOk<AvbDeviceStatus, AvbIoError>,

        /// Custom handler for `factory_data_reset()`.
        /// If not set, `factory_data_reset()` will be a no-op returning `Ok(())`.
        pub factory_data_reset_handler: Option<&'a mut dyn FnMut() -> Result<(), Error>>,

        /// Custom handler for `avb_read_device_status`
        /// This allows simulating a sequence where the device appears unlocked for Fastboot
        /// but locked for AVB, which is currently needed by:
        ///    1. `test_zircon_main_fastboot_boot_fail_on_corrupted_images`
        ///    2. `test_zircon_main_fastboot_boot_fails_on_rollback_protection`
        /// TODO(b/506730736): Remove this when fastboot boot via command override is supported.
        pub avb_read_device_status_handler:
            Option<&'a mut dyn FnMut() -> AvbIoResult<AvbDeviceStatus>>,

        /// For return by `Self::avb_validate_vbmeta_public_key`
        pub avb_key_validation_status: Option<AvbIoResult<KeyValidationStatus>>,

        /// Custom handler for `avb_handle_verification_result`
        pub avb_handle_verification_result: Option<
            &'a mut dyn FnMut(
                VerificationStatus,
                Option<&CStr>,
                Option<Vec<AvbProperty<'_>>>,
                Option<Vec<AvbPartition<'_>>>,
            ) -> AvbIoResult<()>,
        >,

        /// For returned by `get_current_slot`
        //
        // We wrap it in an `Option` so that if a test exercises code paths that use it but did not
        // set it, it can panic with "unwrap()" which will give a clearer error and location
        // message than a vague error such as `Error::Unimplemented`.
        pub current_slot: Option<Result<u8, Error>>,

        /// For returned by `get_slot_info`.
        pub slot_infos: Vec<Result<Slot, Error>>,

        /// For returned by `get_one_shot_boot_mode`.
        pub one_shot_boot_mode: Option<OneShotBootMode>,

        /// For returned by `slot_count`.
        pub slot_count: Option<Result<u8, Error>>,

        /// For returned by `get_base_sp`.
        pub base_sp: Option<usize>,

        /// If true, return [IoError::NotImplemented] from
        /// [avb_cert_read_permanent_attributes].
        pub avb_cert_read_permanent_attributes_not_implemented: bool,

        /// If true, return [IoError::NotImplemented] from
        /// [avb_cert_read_permanent_attributes_hash].
        pub avb_cert_read_permanent_attributes_hash_not_implemented: bool,

        /// For return by `avf_is_supported`
        pub avf_is_supported: bool,

        /// For return by `avf_read_vendor_dice_handover`
        pub avf_vendor_dice_handover: Option<&'a [u8]>,

        /// Handler of `fastboot_get_staged`
        pub get_staged_handler:
            Option<&'a mut dyn FnMut(&mut [u8]) -> Result<(usize, usize), Error>>,

        /// Stores the inputs of `avb_write_lock_state()` call.
        pub write_lock_state_traces: Vec<(LockType, LockState)>,

        /// Handler for `get_partition_buffer`
        pub get_partition_buffer_handler:
            Option<&'a dyn Fn(LoadPartition) -> Result<PartitionBuffer<RefMut<'a, [u8]>>, Error>>,

        /// Handler for `sync_partition_buffer`
        pub sync_partition_buffer_handler:
            Option<&'a mut dyn FnMut(&mut FakeGblOps, bool) -> Result<(), Error>>,

        /// Custom FDT fixup value for property "chosen/test-fixup" set by unittest.
        pub test_custom_fdt_fixup: Option<String>,

        /// Custom bootconfig fixup value set by unittest.
        pub test_custom_bootconfig_fixup: Option<String>,

        /// Number of times `Self::fixup_bootconfig()` is called.
        fixup_bootconfig_calls: u8,

        /// Handler for `Self::fastboot_command_exec`.
        pub fastboot_command_exec_handler: Option<
            &'a mut dyn FnMut(Vec<String>, &mut [u8], usize) -> Result<CommandExecType, Error>,
        >,

        /// Download data seen by the most recent command_exec command
        pub command_exec_download: Vec<u8>,

        /// Stack to store messages that needs to be send.
        pub command_exec_send_messages: VecDeque<Vec<SenderMessage>>,

        /// For return by `fastboot_get_partition_type`.
        pub partition_type: HashMap<String, FastbootPartitionType>,

        /// For return by `get_fw_api_level`.
        pub fw_api_level: Option<Result<u64, Error>>,
    }

    /// Print `console_out` output, which can be useful for debugging.
    impl<'a> Write for FakeGblOps<'a> {
        fn write_str(&mut self, s: &str) -> Result<(), std::fmt::Error> {
            Ok(print!("{s}"))
        }
    }

    impl<'a> FakeGblOps<'a> {
        /// For now we've just hardcoded the `zircon_add_device_zbi_items()` callback to add a
        /// single commandline ZBI item with these contents; if necessary we can generalize this
        /// later and allow tests to configure the ZBI modifications.
        #[cfg(feature = "fuchsia")]
        pub const ADDED_ZBI_COMMANDLINE_CONTENTS: &'static [u8] = b"test_zbi_item";
        #[cfg(feature = "fuchsia")]
        pub const TEST_BOOTLOADER_FILE_1: &'static [u8] = b"\x06test_1foo";
        #[cfg(feature = "fuchsia")]
        pub const TEST_BOOTLOADER_FILE_2: &'static [u8] = b"\x06test_2bar";
        pub const GBL_TEST_VAR: &'static str = "gbl-test-var";
        pub const GBL_TEST_VAR_VAL: &'static str = "gbl-test-var-val";
        pub const GBL_TEST_VAR_UNSPLIT: &'static str = "gbl:test:var:unsplit";
        pub const GBL_TEST_VAR_UNSPLIT_VAL: &'static str = "gbl-test-var-val-unsplit";
        pub const GBL_TEST_BOOTCONFIG: &'static str = "arg1=val1\x0aarg2=val2\x0a";
        pub const GBL_TEST_FDT_FIXUP: &'static [u8] = &[1];
        pub const TEST_FDT_FIXUP_PADDING: usize = 4096;
        pub const GBL_TEST_RANDOM_DATA: &'static [u8] = &[b'7'; RNG_SEED_SIZE_BYTES];
        /// TODO(b/391191885): Generate real dice handover or use prebuilt
        pub const GBL_TEST_AVF_VENDOR_DICE_HANDOVER: &'static [u8] = b"fake_handover_always_fail";
        pub const GBL_TEST_AVF_SECRET_KEEPER_PUBLIC_KEY: &'static [u8] =
            b"secret_keeper_public_key";
        pub const GBL_OEM_CMD_INFO_MSG: &'static str = "oem-info";
        pub const TEST_CUSTOM_FDT_FIXUP_PROP: &'static CStr = c"test-fixup";

        pub fn new(partitions: &'a [TestGblDisk]) -> Self {
            #[cfg_attr(not(feature = "fuchsia"), allow(unused_mut))]
            let mut res = Self {
                slot_count: Some(Ok(2)),
                current_slot: Some(Ok(0)),
                slot_infos: vec![Ok(slot('a')), Ok(slot('b'))],
                partitions,
                #[cfg(feature = "fuchsia")]
                zbi_bootloader_files_buffer: vec![0u8; 32 * 1024],
                fw_api_level: Some(Ok(202604)),
                ..Default::default()
            };
            #[cfg(feature = "fuchsia")]
            let mut container =
                ZbiContainer::new(res.get_zbi_bootloader_files_buffer_aligned().unwrap()).unwrap();
            #[cfg(feature = "fuchsia")]
            for ele in [Self::TEST_BOOTLOADER_FILE_1, Self::TEST_BOOTLOADER_FILE_2] {
                container
                    .create_entry_with_payload(ZbiType::BootloaderFile, 0, ZbiFlags::default(), ele)
                    .unwrap();
            }

            res
        }

        /// Flips a range of bytes on the given partition.
        #[cfg(feature = "fuchsia")]
        pub fn flip_partition_bytes(&mut self, name: &str, off: u64, sz: usize) {
            let mut contents = vec![0u8; sz];
            self.read_from_partition_sync(name, off, &mut contents[..]).unwrap();
            contents.iter_mut().for_each(|v| *v = !*v);
            self.write_to_partition_sync(name, off, &mut contents[..]).unwrap();
        }
    }

    #[derive(Copy, Clone)]
    struct NullProfiler {}

    impl ProfileBackend for NullProfiler {
        fn new_timer(&self) -> impl ProfileTimer {
            *self
        }

        fn reporter(&self) -> impl Reporter {
            *self
        }
    }

    impl ProfileTimer for NullProfiler {
        fn elapsed(&self) -> Duration {
            Duration::ZERO
        }
    }

    impl Reporter for NullProfiler {
        fn report(&self, _: &'static str, _: &'static str, _: Duration) {}
    }

    impl<'a> GblOps<'a> for FakeGblOps<'a> {
        fn console_out(&mut self) -> Option<&mut dyn Write> {
            Some(self)
        }

        fn reboot(&mut self) -> Result<!, Error> {
            self.rebooted = true;
            Err(Error::Aborted)
        }

        fn disks(
            &self,
        ) -> &'a [GblDisk<
            Disk<impl BlockIo + 'a, impl BufferPool + 'a>,
            Gpt<impl DerefMut<Target = [u8]> + 'a>,
        >] {
            self.partitions
        }

        fn expected_os(&mut self) -> Result<Option<Os>, Error> {
            Ok(self.os)
        }

        fn get_random_bytes(
            &self,
            _algorithm: RngAlgorithm,
            buffer: &mut [u8],
        ) -> Result<(), Error> {
            if let Some(get_random_bytes_error) = self.get_random_bytes_error {
                return Err(get_random_bytes_error);
            }
            assert!(buffer.len() <= Self::GBL_TEST_RANDOM_DATA.len());
            buffer.copy_from_slice(&Self::GBL_TEST_RANDOM_DATA[..buffer.len()]);
            Ok(())
        }

        #[cfg(feature = "fuchsia")]
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

        #[cfg(feature = "fuchsia")]
        fn get_zbi_bootloader_files_buffer(&mut self) -> Option<&mut [u8]> {
            Some(self.zbi_bootloader_files_buffer.as_mut_slice())
        }

        fn avb_read_partition_attributes_raw(
            &mut self,
        ) -> AvbIoResult<ArrayMaxSpecializedParts<SpecializedPartition>> {
            Ok(self
                .avb_partition_attributes
                .clone()
                .unwrap_or(Err(AvbIoError::NotImplemented))?
                .into_iter()
                .collect())
        }

        fn avb_read_device_status(&mut self) -> AvbIoResult<AvbDeviceStatus> {
            // Use a custom handler if set to support testing restricted fastboot commands on
            // locked devices.
            // See comments on `avb_read_device_status_handler` for details.
            // TODO(b/506730736): Remove this when fastboot boot via command override is supported.
            if let Some(ref mut f) = self.avb_read_device_status_handler {
                return (*f)();
            }
            self.avb_device_status.0.clone()
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
            // [AvbTestOps] doesn't have any support for returning
            // [IoError::NotImplemented] here, so we add it separately.
            if self.avb_cert_read_permanent_attributes_not_implemented {
                return Err(AvbIoError::NotImplemented);
            }
            self.avb_ops.read_permanent_attributes(attributes)
        }

        fn avb_cert_read_permanent_attributes_hash(
            &mut self,
        ) -> AvbIoResult<[u8; SHA256_DIGEST_SIZE]> {
            // [AvbTestOps] doesn't have any support for returning
            // [IoError::NotImplemented] here, so we add it separately.
            if self.avb_cert_read_permanent_attributes_hash_not_implemented {
                return Err(AvbIoError::NotImplemented);
            }
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

        fn avb_handle_verification_result<'b>(
            &mut self,
            status: VerificationStatus,
            digest: Option<&CStr>,
            properties: Option<impl Iterator<Item = AvbProperty<'b>>>,
            partitions: Option<impl Iterator<Item = AvbPartition<'b>>>,
        ) -> AvbIoResult<()> {
            match self.avb_handle_verification_result.as_mut() {
                Some(f) => (*f)(
                    status,
                    digest,
                    properties.map(|p| p.collect()),
                    partitions.map(|p| p.collect()),
                ),
                _ => Ok(()),
            }
        }

        fn factory_data_reset(&mut self) -> Result<(), Error> {
            match self.factory_data_reset_handler {
                Some(ref mut func) => (*func)(),
                None => Ok(()),
            }
        }

        fn avf_is_supported(&mut self) -> Result<bool, Error> {
            Ok(self.avf_is_supported)
        }

        fn avf_read_vendor_dice_handover<'c>(
            &mut self,
            buffer: &'c mut [u8],
        ) -> Result<&'c [u8], Error> {
            if !self.avf_is_supported {
                return Err(Error::Unsupported);
            }
            let data =
                self.avf_vendor_dice_handover.unwrap_or(Self::GBL_TEST_AVF_VENDOR_DICE_HANDOVER);
            let (out, _) = buffer.split_at_mut(data.len());
            out.copy_from_slice(data);
            Ok(out)
        }

        fn avf_read_secretkeeper_public_key<'c>(
            &mut self,
            buffer: &'c mut [u8],
        ) -> Result<Option<&'c [u8]>, Error> {
            if !self.avf_is_supported {
                return Err(Error::Unsupported);
            }

            let (out, _) = buffer.split_at_mut(Self::GBL_TEST_AVF_SECRET_KEEPER_PUBLIC_KEY.len());
            out.copy_from_slice(Self::GBL_TEST_AVF_SECRET_KEEPER_PUBLIC_KEY);
            Ok(Some(out))
        }

        fn get_partition_buffer(
            &self,
            img: LoadPartition,
        ) -> Result<PartitionBuffer<impl DerefMut<Target = [u8]> + 'a>, Error> {
            self.get_partition_buffer_handler.as_ref().ok_or(Error::NotFound)?(img)
        }

        fn sync_partition_buffer(&mut self, sync: bool) -> Result<(), Error> {
            let mut f = self.sync_partition_buffer_handler.take();
            let res = f.as_mut().map(|v| (*v)(self, sync)).unwrap_or(Ok(()));
            self.sync_partition_buffer_handler = f;
            res
        }

        fn fixup_bootconfig<'c>(
            &mut self,
            _bootconfig: &[u8],
            fixup_buffer: &'c mut [u8],
        ) -> Result<Option<&'c [u8]>, Error> {
            let config = self
                .test_custom_bootconfig_fixup
                .clone()
                .unwrap_or(Self::GBL_TEST_BOOTCONFIG.into());
            let (out, _) = fixup_buffer.split_at_mut(config.len());
            out.copy_from_slice(config.as_bytes());
            self.fixup_bootconfig_calls += 1;
            Ok(Some(out))
        }

        fn fixup_device_tree(&mut self, fdt: &mut [u8]) -> Result<(), Error> {
            let mut fdt = Fdt::new_mut(fdt).unwrap();

            // Update kernel command line with fixup value.
            let cmd_prop_len = fdt.get_property("chosen", PROP_BOOTARGS)?.len();

            // GBL guarantees kernel command line has some extra space reserved to append.
            let cmd_prop_buffer =
                fdt.set_property_placeholder("chosen", PROP_BOOTARGS, cmd_prop_len)?;
            let mut commandline = CommandlineBuilder::from_prefix(cmd_prop_buffer)?;
            commandline.add_raw("fixup")?;

            // Test custom fixup.
            fdt.set_property(
                "chosen",
                Self::TEST_CUSTOM_FDT_FIXUP_PROP,
                self.test_custom_fdt_fixup
                    .as_ref()
                    .map(|v| v.as_bytes())
                    .unwrap_or(Self::GBL_TEST_FDT_FIXUP),
            )?;

            // Times Self::fixup_bootconfig is called
            fdt.set_property("", c"fixup_bootconfig_calls", &[self.fixup_bootconfig_calls])?;

            // Reports the resulting size with trailing free space for later boot stages.
            let total = fdt.header_ref()?.actual_size() + Self::TEST_FDT_FIXUP_PADDING;
            fdt.shrink_to_fit()?;
            Fdt::new_mut(&mut fdt.as_mut()[..total])?;
            Ok(())
        }

        fn select_device_trees(
            &mut self,
            device_tree: &mut DtComponentsRegistry,
        ) -> Result<(), Error> {
            // Select all overlays.
            device_tree
                .components_mut()
                .filter(|v| v.component_type == DtComponentType::Overlay)
                .for_each(|v| v.selected = true);
            // Select the first base device tree.
            device_tree.autoselect()
        }

        fn select_fit_configuration(
            &mut self,
            _fit: &[u8],
            _metadata: Option<&[u8]>,
        ) -> Result<Option<usize>, Error> {
            Ok(None)
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
            mut cb: impl FnMut(&mut Self, &[&CStr], &CStr),
        ) -> Result<(), Error> {
            cb(
                self,
                &[CString::new(Self::GBL_TEST_VAR).unwrap().as_c_str(), c"1"],
                CString::new(format!("{}:1", Self::GBL_TEST_VAR_VAL)).unwrap().as_c_str(),
            );
            cb(
                self,
                &[CString::new(Self::GBL_TEST_VAR).unwrap().as_c_str(), c"2"],
                CString::new(format!("{}:2", Self::GBL_TEST_VAR_VAL)).unwrap().as_c_str(),
            );
            cb(
                self,
                &[&CString::new(Self::GBL_TEST_VAR_UNSPLIT).unwrap()],
                &CString::new(Self::GBL_TEST_VAR_UNSPLIT_VAL).unwrap(),
            );

            for v in crate::fastboot::vars::GETVAR_ALL_FILTER {
                cb(self, &[&CString::new(*v).unwrap()], c"dont-care");
            }
            // Concatenated reserved variables should also be filtered.
            cb(self, &[c"block-device:1"], c"dont-care");

            Ok(())
        }

        fn fastboot_get_staged(&mut self, out: &mut [u8]) -> Result<(usize, usize), Error> {
            (self.get_staged_handler.as_mut().unwrap())(out)
        }

        fn avb_write_lock_state(
            &mut self,
            lock_type: LockType,
            lock_state: LockState,
        ) -> Result<(), Error> {
            // Add to the trace for cases where it's difficult to analyze the state until the end
            // of the test (e.g. changing multiple times in a single fastboot session).
            self.write_lock_state_traces.push((lock_type, lock_state));

            // If the user has simulated a device state error, locking fails.
            if let Err(err) = &self.avb_device_status.0 {
                return Err(err.clone().into());
            }

            let locked = match lock_state {
                LockState::Locked => true,
                LockState::Unlocked => false,
            };
            match lock_type {
                LockType::Device => self.avb_device_status.is_unlocked = !locked,
                LockType::Critical => self.avb_device_status.is_unlocked_critical = !locked,
            }

            Ok(())
        }

        fn fastboot_get_unlock_ability(&mut self) -> Result<Unlockability, Error> {
            Ok(self
                .avb_read_device_status()
                .map(|s| {
                    if s.is_unlockable {
                        Unlockability::Allowed
                    } else {
                        Unlockability::Prohibited
                    }
                })
                .unwrap())
        }

        fn fastboot_command_exec<'arg, Sender: InfoSender + OkaySender + FailSender>(
            &mut self,
            args: impl Iterator<Item = &'arg CStr> + Clone,
            download: &mut [u8],
            download_used: usize,
            mut sender: Sender,
        ) -> Result<CommandExecType, Error> {
            let args = args.map(|v| v.to_str().unwrap().to_string()).collect::<Vec<_>>();
            if args == ["oem test-oem"] {
                block_on(sender.send_info(Self::GBL_OEM_CMD_INFO_MSG))?;
                block_on(sender.send_okay(""))?;
                Ok(CommandExecType::CustomImpl)
            } else {
                self.command_exec_download = download.to_vec();
                let res = self
                    .fastboot_command_exec_handler
                    .as_mut()
                    .map(|v| v(args, download, download_used))
                    .unwrap_or(Ok(Default::default()));

                let sender = &mut Some(sender);
                if let Some(mut messages) = self.command_exec_send_messages.pop_front() {
                    messages.drain(..).for_each(|val| {
                        match val {
                            SenderMessage::Info(s) => {
                                block_on(sender.as_mut().unwrap().send_info(&s)).unwrap()
                            }
                            SenderMessage::Okay(s) => {
                                block_on(sender.take().unwrap().send_okay(&s)).unwrap()
                            }
                            SenderMessage::Fail(s) => {
                                block_on(sender.take().unwrap().send_fail(&s)).unwrap()
                            }
                        };
                    });
                }

                res
            }
        }

        fn fastboot_get_partition_type(
            &mut self,
            part: &str,
        ) -> Result<FastbootPartitionType, Error> {
            Ok(self.partition_type.get(part).copied().unwrap_or_default())
        }

        fn get_slot_count(&mut self) -> Result<u8, Error> {
            self.slot_count.unwrap()
        }

        fn get_slot_info(&mut self, idx: u8) -> Result<Slot, Error> {
            self.slot_infos[idx as usize]
        }

        fn get_current_slot(&mut self) -> Result<Slot, Error> {
            self.get_slot_info(self.current_slot.unwrap()?)
        }

        fn set_active_slot(&mut self, slot: u8) -> Result<(), Error> {
            // Set slot metadata to default.
            let idx = slot as usize;
            let suffix = self.slot_infos[idx]?.suffix;
            self.slot_infos[idx] = Ok(Slot { suffix, ..Default::default() });
            self.current_slot = Some(Ok(slot));
            Ok(())
        }

        fn get_one_shot_boot_mode(&mut self) -> Result<Option<OneShotBootMode>, Error> {
            Ok(self.one_shot_boot_mode)
        }

        fn handle_loaded_os(
            &mut self,
            _kernel: &[u8],
            _ramdisk: &[u8],
            _device_tree: &[u8],
        ) -> Result<(), Error> {
            Ok(())
        }

        fn get_base_sp(&mut self) -> Option<usize> {
            self.base_sp
        }

        fn get_profiling_backend(&self) -> impl ProfileBackend {
            NullProfiler {}
        }

        fn get_fw_api_level(&self) -> Result<u64, Error> {
            self.fw_api_level.unwrap_or(Err(Error::Unsupported))
        }

        fn get_time(&self) -> Option<&impl GblTime> {
            None::<&FakeGblTime>
        }

        fn get_metrics(&self) -> Option<impl DerefMut<Target = GblMetrics> + '_> {
            None::<Box<GblMetrics>>
        }

        fn get_firmware_version_metrics(&self) -> FirmwareVersionMetrics {
            FirmwareVersionMetrics::default()
        }
    }

    /// Helper for creating a slot object.
    pub(crate) fn slot(suffix: char) -> Slot {
        Slot { suffix: suffix.try_into().unwrap(), ..Default::default() }
    }

    /// Helper for creating a successful slot object.
    pub(crate) fn slot_successful(suffix: char) -> Slot {
        Slot {
            suffix: suffix.try_into().unwrap(),
            bootability: Bootability::Successful(7u8.into()),
            ..Default::default()
        }
    }

    /// Helper for creating an unbootable slot object.
    pub(crate) fn slot_unbootable(suffix: char) -> Slot {
        Slot {
            suffix: suffix.try_into().unwrap(),
            bootability: Bootability::Unbootable(Default::default()),
            ..Default::default()
        }
    }

    // An ops implementation where all interfaces are unsupported.
    #[derive(Default)]
    pub(crate) struct OpsAllUnsupported<'a>(FakeGblOps<'a>);

    impl<'a> GblOps<'a> for OpsAllUnsupported<'_> {
        fn console_out(&mut self) -> Option<&mut dyn Write> {
            Some(&mut self.0)
        }

        fn reboot(&mut self) -> Result<!, Error> {
            Err(Error::Unsupported)
        }

        fn disks(
            &self,
        ) -> &'a [GblDisk<
            Disk<impl BlockIo + 'a, impl BufferPool + 'a>,
            Gpt<impl DerefMut<Target = [u8]> + 'a>,
        >] {
            &[] as &[TestGblDisk]
        }

        fn expected_os(&mut self) -> Result<Option<Os>, Error> {
            Err(Error::Unsupported)
        }

        fn get_random_bytes(&self, _: RngAlgorithm, _: &mut [u8]) -> Result<(), Error> {
            Err(Error::Unsupported)
        }

        #[cfg(feature = "fuchsia")]
        fn zircon_add_device_zbi_items(
            &mut self,
            _: &mut ZbiContainer<&mut [u8]>,
        ) -> Result<(), Error> {
            Err(Error::Unsupported)
        }

        #[cfg(feature = "fuchsia")]
        fn get_zbi_bootloader_files_buffer(&mut self) -> Option<&mut [u8]> {
            None
        }

        fn avb_read_partition_attributes_raw(
            &mut self,
        ) -> AvbIoResult<ArrayMaxSpecializedParts<SpecializedPartition>> {
            Err(AvbIoError::NotImplemented)
        }

        fn avb_read_device_status(&mut self) -> AvbIoResult<AvbDeviceStatus> {
            Err(AvbIoError::NotImplemented)
        }

        fn avb_read_rollback_index(&mut self, _: usize) -> AvbIoResult<u64> {
            Err(AvbIoError::NotImplemented)
        }

        fn avb_write_rollback_index(&mut self, _: usize, _: u64) -> AvbIoResult<()> {
            Err(AvbIoError::NotImplemented)
        }

        fn avb_read_persistent_value(&mut self, _: &CStr, _: &mut [u8]) -> AvbIoResult<usize> {
            Err(AvbIoError::NotImplemented)
        }

        fn avb_write_persistent_value(&mut self, _: &CStr, _: &[u8]) -> AvbIoResult<()> {
            Err(AvbIoError::NotImplemented)
        }

        fn avb_erase_persistent_value(&mut self, _: &CStr) -> AvbIoResult<()> {
            Err(AvbIoError::NotImplemented)
        }

        fn avb_cert_read_permanent_attributes(
            &mut self,
            _: &mut CertPermanentAttributes,
        ) -> AvbIoResult<()> {
            Err(AvbIoError::NotImplemented)
        }

        fn avb_cert_read_permanent_attributes_hash(
            &mut self,
        ) -> AvbIoResult<[u8; SHA256_DIGEST_SIZE]> {
            Err(AvbIoError::NotImplemented)
        }

        fn get_partition_buffer(
            &self,
            _: LoadPartition,
        ) -> Result<PartitionBuffer<impl DerefMut<Target = [u8]> + 'a>, Error> {
            Err::<PartitionBuffer<&mut [u8]>, _>(Error::Unsupported)
        }

        fn sync_partition_buffer(&mut self, _: bool) -> Result<(), Error> {
            Err(Error::Unsupported)
        }

        fn fixup_bootconfig<'c>(
            &mut self,
            _: &[u8],
            _: &'c mut [u8],
        ) -> Result<Option<&'c [u8]>, Error> {
            Err(Error::Unsupported)
        }

        fn fixup_device_tree(&mut self, _: &mut [u8]) -> Result<(), Error> {
            Err(Error::Unsupported)
        }

        fn select_device_trees(&mut self, _: &mut DtComponentsRegistry) -> Result<(), Error> {
            Err(Error::Unsupported)
        }

        fn select_fit_configuration(
            &mut self,
            _: &[u8],
            _: Option<&[u8]>,
        ) -> Result<Option<usize>, Error> {
            Err(Error::Unsupported)
        }

        async fn read_from_partition<'b>(
            &mut self,
            _: &str,
            _: u64,
            _: impl Into<&'b mut UninitSlice>,
        ) -> Result<(), Error> {
            Err(Error::Unsupported)
        }

        /// Writes data to a partition.
        async fn write_to_partition(&mut self, _: &str, _: u64, _: &mut [u8]) -> Result<(), Error> {
            Err(Error::Unsupported)
        }

        fn partition_size(&mut self, _: &str) -> Result<Option<u64>, Error> {
            Err(Error::Unsupported)
        }

        fn avb_handle_verification_result<'b>(
            &mut self,
            _: VerificationStatus,
            _: Option<&CStr>,
            _: Option<impl Iterator<Item = AvbProperty<'b>>>,
            _: Option<impl Iterator<Item = AvbPartition<'b>>>,
        ) -> AvbIoResult<()> {
            Err(AvbIoError::NotImplemented)
        }

        fn factory_data_reset(&mut self) -> Result<(), Error> {
            Err(Error::Unsupported)
        }

        fn avb_validate_vbmeta_public_key(
            &self,
            _: &[u8],
            _: Option<&[u8]>,
        ) -> AvbIoResult<KeyValidationStatus> {
            Err(AvbIoError::NotImplemented)
        }

        fn avf_is_supported(&mut self) -> Result<bool, Error> {
            Err(Error::Unsupported)
        }

        fn avf_read_vendor_dice_handover<'c>(
            &mut self,
            _: &'c mut [u8],
        ) -> Result<&'c [u8], Error> {
            Err(Error::Unsupported)
        }

        fn avf_read_secretkeeper_public_key<'c>(
            &mut self,
            _: &'c mut [u8],
        ) -> Result<Option<&'c [u8]>, Error> {
            Err(Error::Unsupported)
        }

        fn get_slot_count(&mut self) -> Result<u8, Error> {
            Err(Error::Unsupported)
        }

        fn get_slot_info(&mut self, _: u8) -> Result<Slot, Error> {
            Err(Error::Unsupported)
        }

        fn get_current_slot(&mut self) -> Result<Slot, Error> {
            Err(Error::Unsupported)
        }

        fn set_active_slot(&mut self, _: u8) -> Result<(), Error> {
            Err(Error::Unsupported)
        }

        fn get_one_shot_boot_mode(&mut self) -> Result<Option<OneShotBootMode>, Error> {
            Err(Error::Unsupported)
        }

        fn handle_loaded_os(&mut self, _: &[u8], _: &[u8], _: &[u8]) -> Result<(), Error> {
            Err(Error::Unsupported)
        }

        fn get_base_sp(&mut self) -> Option<usize> {
            None
        }

        fn fastboot_variable<'arg>(
            &mut self,
            _: &CStr,
            _: impl Iterator<Item = &'arg CStr> + Clone,
            _: &mut [u8],
        ) -> Result<usize, Error> {
            Err(Error::Unsupported)
        }

        fn fastboot_visit_all_variables(
            &mut self,
            _: impl FnMut(&mut Self, &[&CStr], &CStr),
        ) -> Result<(), Error> {
            Err(Error::Unsupported)
        }

        fn fastboot_get_staged(&mut self, _: &mut [u8]) -> Result<(usize, usize), Error> {
            Err(Error::Unsupported)
        }

        fn avb_write_lock_state(&mut self, _: LockType, _: LockState) -> Result<(), Error> {
            Err(Error::Unsupported)
        }

        fn fastboot_get_unlock_ability(&mut self) -> Result<Unlockability, Error> {
            Err(Error::Unsupported)
        }

        fn fastboot_command_exec<'arg, Sender: InfoSender + OkaySender + FailSender>(
            &mut self,
            _: impl Iterator<Item = &'arg CStr> + Clone,
            _: &mut [u8],
            _: usize,
            _: Sender,
        ) -> Result<CommandExecType, Error> {
            Err(Error::Unsupported)
        }

        fn fastboot_get_partition_type(
            &mut self,
            _part: &str,
        ) -> Result<FastbootPartitionType, Error> {
            Err(Error::Unsupported)
        }

        fn get_profiling_backend(&self) -> impl ProfileBackend {
            NullProfiler {}
        }

        fn get_fw_api_level(&self) -> Result<u64, Error> {
            Err(Error::Unsupported)
        }

        fn get_time(&self) -> Option<&impl GblTime> {
            self.0.get_time()
        }

        fn get_metrics(&self) -> Option<impl DerefMut<Target = GblMetrics> + '_> {
            self.0.get_metrics()
        }

        fn get_firmware_version_metrics(&self) -> FirmwareVersionMetrics {
            self.0.get_firmware_version_metrics()
        }
    }

    #[test]
    fn calculate_stack_usage() {
        let storage = FakeGblOpsStorage::default();
        let mut gbl_ops = FakeGblOps::new(&storage);
        gbl_ops.base_sp = Some(3);
        assert_eq!(gbl_ops.calculate_stack_usage(1), Some(2));
    }

    #[test]
    fn calculate_stack_usage_returns_none_if_base_sp_not_set() {
        let storage = FakeGblOpsStorage::default();
        let mut gbl_ops = FakeGblOps::new(&storage);
        assert_eq!(gbl_ops.calculate_stack_usage(0), None);
    }

    #[test]
    fn calculate_stack_usage_returns_max_if_overflow() {
        let storage = FakeGblOpsStorage::default();
        let mut gbl_ops = FakeGblOps::new(&storage);
        gbl_ops.base_sp = Some(1);
        assert_eq!(gbl_ops.calculate_stack_usage(2), Some(usize::MAX));
    }

    #[test]
    fn fake_gbl_ops_factory_data_reset_default() {
        let storage = FakeGblOpsStorage::default();
        let mut gbl_ops = FakeGblOps::new(&storage);

        // Default behavior should be a no-op success.
        gbl_ops.factory_data_reset().unwrap();
    }

    #[test]
    fn fake_gbl_ops_factory_data_reset_handler() {
        let storage = FakeGblOpsStorage::default();
        let mut gbl_ops = FakeGblOps::new(&storage);

        // Callback side effects should execute.
        let counter = CounterCallback::new();
        let mut fdr_handler = counter.handler();
        gbl_ops.factory_data_reset_handler = Some(&mut fdr_handler);
        gbl_ops.factory_data_reset().unwrap();
        assert_eq!(counter.count(), 1);

        // Handler errors should propagate up.
        let mut err_handler = || Err(Error::Unsupported);
        gbl_ops.factory_data_reset_handler = Some(&mut err_handler);
        assert_eq!(gbl_ops.factory_data_reset(), Err(Error::Unsupported));
    }

    #[test]
    fn avb_read_partition_attributes_raw() {
        let storage = FakeGblOpsStorage::default();
        let mut gbl_ops = FakeGblOps::new(&storage);
        gbl_ops.avb_partition_attributes = Some(AvbIoResult::Ok(vec![]));

        // The raw value should not append any defaults, so should still be empty.
        assert!(gbl_ops.avb_read_partition_attributes_raw().unwrap().is_empty());
    }

    const DEFAULT_USERDATA_ATTRIBUTES: SpecializedPartition = SpecializedPartition {
        name_buffer: cstr_buffer("userdata"),
        verification: None,
        fdr: Fdr::Yes,
        critical: Critical::No,
    };

    const DEFAULT_METADATA_ATTRIBUTES: SpecializedPartition = SpecializedPartition {
        name_buffer: cstr_buffer("metadata"),
        verification: None,
        fdr: Fdr::Yes,
        critical: Critical::No,
    };

    #[test]
    fn avb_read_partition_attributes_not_implemented() {
        let storage = FakeGblOpsStorage::default();
        let mut gbl_ops = FakeGblOps::new(&storage);
        gbl_ops.avb_partition_attributes = None;

        assert_eq!(
            gbl_ops.avb_read_partition_attributes().unwrap().collect::<Vec<_>>(),
            vec![DEFAULT_USERDATA_ATTRIBUTES, DEFAULT_METADATA_ATTRIBUTES]
        );
    }

    #[test]
    fn avb_read_partition_attributes_empty() {
        let storage = FakeGblOpsStorage::default();
        let mut gbl_ops = FakeGblOps::new(&storage);
        gbl_ops.avb_partition_attributes = Some(AvbIoResult::Ok(vec![]));

        assert_eq!(
            gbl_ops.avb_read_partition_attributes().unwrap().collect::<Vec<_>>(),
            vec![DEFAULT_USERDATA_ATTRIBUTES, DEFAULT_METADATA_ATTRIBUTES]
        );
    }

    #[test]
    fn avb_read_partition_attributes_non_empty() {
        let storage = FakeGblOpsStorage::default();
        let mut gbl_ops = FakeGblOps::new(&storage);

        // Unrelated partition attributes should be left in place.
        let other_attributes = SpecializedPartition {
            name_buffer: cstr_buffer("other_partition"),
            verification: Some(Verification::Required),
            fdr: Fdr::Yes,
            critical: Critical::Yes,
        };
        gbl_ops.avb_partition_attributes = Some(AvbIoResult::Ok(vec![other_attributes.clone()]));

        assert_eq!(
            gbl_ops.avb_read_partition_attributes().unwrap().collect::<Vec<_>>(),
            vec![other_attributes, DEFAULT_USERDATA_ATTRIBUTES, DEFAULT_METADATA_ATTRIBUTES]
        );
    }

    #[test]
    fn avb_read_partition_attributes_default_fdr_override() {
        let storage = FakeGblOpsStorage::default();
        let mut gbl_ops = FakeGblOps::new(&storage);

        // The device should be able to override the default FDR behavior.
        let modified_userdata_attributes = SpecializedPartition {
            name_buffer: cstr_buffer("userdata"),
            fdr: Fdr::No,
            ..Default::default()
        };
        gbl_ops.avb_partition_attributes =
            Some(AvbIoResult::Ok(vec![modified_userdata_attributes.clone()]));

        assert_eq!(
            gbl_ops.avb_read_partition_attributes().unwrap().collect::<Vec<_>>(),
            vec![modified_userdata_attributes, DEFAULT_METADATA_ATTRIBUTES]
        );
    }
}
