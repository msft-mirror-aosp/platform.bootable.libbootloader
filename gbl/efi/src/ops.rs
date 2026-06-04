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

//! Implements [Gbl::Ops] for the EFI environment.

use crate::{efi, efi_blocks::EfiGblDisk, utils::EfiTime};
#[cfg(feature = "fuchsia")]
use alloc::vec::Vec;
use arrayvec::ArrayVec;
use core::{ffi::CStr, fmt::Write, ops::DerefMut, ptr::null};
use efi::{
    efi_print, efi_println,
    profiling::EfiProfileBackend,
    protocol::{
        dt_fixup::DtFixupProtocol,
        gbl_efi_avb::GblAvbProtocol,
        gbl_efi_avf::GblAvfProtocol,
        gbl_efi_boot_control::GblBootControlProtocol,
        gbl_efi_boot_memory::{gbl_get_partition_buffer, gbl_sync_partition_buffer},
        gbl_efi_fastboot::GblFastbootProtocol,
        gbl_efi_os_configuration::GblOsConfigurationProtocol,
        random_number_generator::{RandomNumberGeneratorProtocol, RngAlgorithm as EfiRngAlgorithm},
        timestamp::TimestampProtocol,
        Protocol, Versioned,
    },
    utils::{find_fdt_configuration_table, parse_fw_api_level},
    EfiEntry, GBL_EFI_FW_API_LEVEL, GBL_EFI_VENDOR_GUID,
};
use efi_types::{
    GblEfiAvbDeviceStatus, GblEfiAvbKeyValidationStatus, GblEfiAvbLoadedPartition,
    GblEfiAvbProperty, GblEfiAvbVerificationResult, GblEfiDeviceTreeMetadata,
    GblEfiFastbootMessageType, GblEfiVerifiedDeviceTree,
    GBL_EFI_FASTBOOT_COMMAND_EXEC_RESULT_CUSTOM_IMPL,
    GBL_EFI_FASTBOOT_COMMAND_EXEC_RESULT_DEFAULT_IMPL,
    GBL_EFI_FASTBOOT_COMMAND_EXEC_RESULT_PROHIBITED, GBL_EFI_FASTBOOT_MESSAGE_TYPE_FAIL,
    GBL_EFI_FASTBOOT_MESSAGE_TYPE_INFO, GBL_EFI_FASTBOOT_MESSAGE_TYPE_OKAY,
    GBL_EFI_FASTBOOT_PARTITION_TYPE_BUF_LEN, GBL_EFI_ONE_SHOT_BOOT_MODE_BOOTLOADER,
    GBL_EFI_ONE_SHOT_BOOT_MODE_NONE, GBL_EFI_ONE_SHOT_BOOT_MODE_RECOVERY, PARTITION_NAME_LEN_U16,
};
use fastboot::{CommandExecType, Unlockability};
use fdt::Fdt;
use gbl_async::block_on;
use gbl_storage::{BlockIo, Disk, Gpt};
use liberror::{Error, Result};
use libgbl::{
    constants::{FASTBOOT_PARTITION_TYPE_LEN, IMAGE_NAME_MAX_LEN},
    device_tree::{
        DtComponent, DtComponentSource, DtComponentType, DtComponentsRegistry,
        MAXIMUM_DT_COMPONENTS,
    },
    gbl_avb::{
        state::{BootStateColor, KeyValidationStatus, VerificationStatus},
        ArrayMaxParts, ArrayMaxSpecializedParts, AvbDeviceStatus, AvbPartition, AvbProperty,
        LoadPartition, SpecializedPartition,
    },
    gbl_println,
    metrics::{FirmwareVersion, FirmwareVersionMetrics, GblMetrics, GblTime},
    ops::{
        AvbIoError, AvbIoResult, CertPermanentAttributes, FailSender, FastbootPartitionType,
        InfoSender, LockState, LockType, OkaySender, OneShotBootMode, PartitionBuffer,
        RngAlgorithm as GblRngAlgorithm, Slot, SHA256_DIGEST_SIZE,
    },
    partition::{GblDisk, RawName},
    slots::{BootToken, Cursor},
    GblOps, Os, Result as GblResult,
};
use libprofile::ProfileBackend;
use libutils::buffer_pool::BufferPool;
use spin::Mutex;
use static_assertions::{const_assert, const_assert_eq};
#[cfg(feature = "fuchsia")]
use zbi::ZbiContainer;
use zerocopy::IntoBytes;

// Ensure the max partition name length in the image loading protocol matches the max image type
// name length in GBL ops.
const_assert_eq!(PARTITION_NAME_LEN_U16 as usize, IMAGE_NAME_MAX_LEN);

// Asserts that the fastboot partition type buffer is at least as large as the length defined in the
// fastboot protocol.
const_assert!(FASTBOOT_PARTITION_TYPE_LEN >= GBL_EFI_FASTBOOT_PARTITION_TYPE_BUF_LEN);

fn dt_component_to_efi_dt(component: &DtComponent) -> GblEfiVerifiedDeviceTree {
    let (id, rev, custom_size, custom) = match component.selection_metadata.as_ref() {
        Some(m) => {
            let custom = m.custom.as_bytes();
            (m.id, m.rev, custom.len(), custom.as_ptr())
        }
        None => (0, 0, 0, core::ptr::null()),
    };

    GblEfiVerifiedDeviceTree {
        metadata: GblEfiDeviceTreeMetadata {
            // bindgen may make enum i32 or u32. because we only care about bits, cast to u32 is ok.
            source: match component.source_metadata.source {
                DtComponentSource::Boot => efi_types::GBL_EFI_DEVICE_TREE_SOURCE_BOOT,
                DtComponentSource::VendorBoot => efi_types::GBL_EFI_DEVICE_TREE_SOURCE_VENDOR_BOOT,
                DtComponentSource::Dtb => efi_types::GBL_EFI_DEVICE_TREE_SOURCE_DTB,
                DtComponentSource::Dtbo => efi_types::GBL_EFI_DEVICE_TREE_SOURCE_DTBO,
            } as _,
            type_: match component.component_type {
                DtComponentType::BaseDt => efi_types::GBL_EFI_DEVICE_TREE_TYPE_DEVICE_TREE,
                DtComponentType::Overlay => efi_types::GBL_EFI_DEVICE_TREE_TYPE_OVERLAY,
                DtComponentType::PvmDeviceAssignmentOverlay => {
                    efi_types::GBL_EFI_DEVICE_TREE_TYPE_PVM_DA_OVERLAY
                }
            } as _,
            id,
            rev,
            custom_size,
            custom,
        },
        device_tree: component.dt.as_ptr() as _,
        selected: component.selected,
    }
}

pub struct Ops<'a, 'b> {
    pub efi_entry: &'a EfiEntry,
    pub disks: &'b [EfiGblDisk<'a>],
    #[cfg(feature = "fuchsia")]
    pub zbi_bootloader_files_buffer: Vec<u8>,
    pub os: Option<Os>,
    pub base_sp: usize,
    pause_fastboot: bool,
    time: Option<EfiTime<'a>>,
    metrics: Mutex<GblMetrics>,
}

impl<'a, 'b> Ops<'a, 'b> {
    /// Creates a new instance of [Ops]
    pub fn new(
        efi_entry: &'a EfiEntry,
        disks: &'b [EfiGblDisk<'a>],
        os: Option<Os>,
        base_sp: usize,
    ) -> Self {
        let time = if cfg!(not(test)) {
            efi_entry
                .system_table()
                .boot_services()
                .find_first_and_open::<TimestampProtocol>()
                .ok()
                .and_then(|ts| EfiTime::new(ts).ok())
        } else {
            None
        };
        let start_tick = time.as_ref().and_then(|t| t.current_tick().ok());
        Self {
            efi_entry,
            disks,
            #[cfg(feature = "fuchsia")]
            zbi_bootloader_files_buffer: Default::default(),
            os,
            base_sp,
            pause_fastboot: false,
            time,
            metrics: Mutex::new(GblMetrics::new(start_tick)),
        }
    }

    /// Gets the EFI FDT.
    fn get_efi_fdt(&self) -> Option<Fdt<&'a [u8]>> {
        let (_, fdt_bytes) = find_fdt_configuration_table(self.efi_entry)?;
        Fdt::new(fdt_bytes).ok()
    }

    /// Refuses to use a GBL protocol whose firmware-reported revision is below 1.0.
    ///
    /// Every GBL custom protocol has been release with major revision 1. A lower revision
    /// means the firmware ships a pre-released, potentially ABI-incompatible version.
    fn check_gbl_protocol_revision<T: Versioned>(&self, protocol: &T) -> Result<()> {
        let actual = protocol.revision();
        if actual.major < 1 {
            efi_println!(
                self.efi_entry,
                "GBL protocol {} revision {} is below 1.0; refusing to use",
                core::any::type_name::<T>(),
                actual
            );
            return Err(Error::UnsupportedVersion);
        }
        Ok(())
    }

    /// Helper for opening GblAvbProtocol.
    fn open_avb_protocol(&self) -> Result<Protocol<'a, GblAvbProtocol>> {
        let protocol = self
            .efi_entry
            .system_table()
            .boot_services()
            .find_first_and_open::<GblAvbProtocol>()?;
        self.check_gbl_protocol_revision(&protocol)?;
        Ok(protocol)
    }

    /// Helper for opening GblAvfProtocol.
    fn open_avf_protocol(&self) -> Result<Protocol<'a, GblAvfProtocol>> {
        let protocol = self
            .efi_entry
            .system_table()
            .boot_services()
            .find_first_and_open::<GblAvfProtocol>()?;
        self.check_gbl_protocol_revision(&protocol)?;
        Ok(protocol)
    }

    /// Helper for opening GblBootControlProtocol.
    fn open_boot_control_protocol(&self) -> Result<Protocol<'a, GblBootControlProtocol>> {
        let protocol = self
            .efi_entry
            .system_table()
            .boot_services()
            .find_first_and_open::<GblBootControlProtocol>()?;
        self.check_gbl_protocol_revision(&protocol)?;
        Ok(protocol)
    }

    /// Helper for opening GblFastbootProtocol.
    fn open_fastboot_protocol(&self) -> Result<Protocol<'a, GblFastbootProtocol>> {
        let protocol = self
            .efi_entry
            .system_table()
            .boot_services()
            .find_first_and_open::<GblFastbootProtocol>()?;
        self.check_gbl_protocol_revision(&protocol)?;
        Ok(protocol)
    }

    /// Helper for opening GblOsConfigurationProtocol.
    fn open_os_configuration_protocol(&self) -> Result<Protocol<'a, GblOsConfigurationProtocol>> {
        let protocol = self
            .efi_entry
            .system_table()
            .boot_services()
            .find_first_and_open::<GblOsConfigurationProtocol>()?;
        self.check_gbl_protocol_revision(&protocol)?;
        Ok(protocol)
    }

    /// Run protocol integration required tests.
    #[cfg(all(not(test), feature = "gbl_dev"))]
    fn run_integration_test_required<Sender: InfoSender + OkaySender + FailSender>(
        &self,
        sender: Sender,
        send_impl: impl FnOnce(&'static str, Sender, Result<()>) -> Result<()>,
    ) -> Result<()> {
        let res = libprotocol_test::test_all_required_protocols(self.efi_entry);
        send_impl("required protocool integration test", sender, res)
    }

    /// Run protocol integration optional tests.
    #[cfg(all(not(test), feature = "gbl_dev"))]
    fn run_integration_test_optional<Sender: InfoSender + OkaySender + FailSender>(
        &self,
        sender: Sender,
        send_impl: impl FnOnce(&'static str, Sender, Result<()>) -> Result<()>,
    ) -> Result<()> {
        let res = libprotocol_test::test_all_optional_protocols(self.efi_entry);
        send_impl("optional protocol integration test", sender, res)
    }

    /// Check for a local implementation of a custom
    /// fastboot command and, if found, run it.
    fn handle_command_exec_locally<'arg, Sender: InfoSender + OkaySender + FailSender>(
        &self,
        args: impl Iterator<Item = &'arg CStr>,
        sender: Sender,
    ) -> Result<CommandExecType> {
        // Note: can't simplify the type for the command function or lift it out
        //       due to limitations in the type checker as of 2025-10-02.
        let exec_funcs: &[(
            &'static str,
            fn(&Self, Sender, fn(&'static str, Sender, Result<()>) -> Result<()>) -> Result<()>,
        )] = &[
            // These tests depend heavily on libefi and libefi_types, and we don't
            // want to add those dependencies to libgbl, so move the invocation here
            // instead of libgbl/src/ops.rs
            #[cfg(all(not(test), feature = "gbl_dev"))]
            ("oem gbl-integration-test-required", Self::run_integration_test_required),
            #[cfg(all(not(test), feature = "gbl_dev"))]
            ("oem gbl-integration-test-optional", Self::run_integration_test_optional),
        ];

        fn send_func<Sender: InfoSender + OkaySender + FailSender>(
            msg: &str,
            message_sender: Sender,
            res: Result<()>,
        ) -> Result<()> {
            if res.is_ok() {
                block_on(message_sender.send_okay(msg))
            } else {
                block_on(message_sender.send_fail(msg))
            }
        }

        // Maybe use args later.
        let mut args = args.peekable();
        let key = args.peek().and_then(|a| a.to_str().ok());

        if let Some(key) = key
            && let Some(exec_cmd) =
                exec_funcs.iter().find_map(|(k, v)| if *k == key { Some(v) } else { None })
        {
            // Note: we search 'exec_funcs' if the return of
            //       handle_command_exec_via_protocol
            //       is DefaultImpl but return CustomImpl here. This is to prevent
            //       our caller from trying another default impl lookup.
            exec_cmd(self, sender, send_func).map(|_| CommandExecType::CustomImpl)
        } else {
            Ok(CommandExecType::DefaultImpl)
        }
    }

    /// Helper to run GblFastbootProtocol.command_exec.
    fn handle_command_exec_via_protocol<'arg, Sender: InfoSender + OkaySender + FailSender>(
        &self,
        args: impl Iterator<Item = &'arg CStr> + Clone,
        download: &mut [u8],
        download_used: usize,
        sender: &mut Option<Sender>,
    ) -> Result<CommandExecType> {
        match self.open_fastboot_protocol() {
            Ok(v) => {
                match v.command_exec(args, download, download_used, |msg_type, msg| {
                    command_exec_message_sender(msg_type, msg, sender)
                }) {
                    Ok(GBL_EFI_FASTBOOT_COMMAND_EXEC_RESULT_PROHIBITED) => {
                        Ok(CommandExecType::Prohibited)
                    }
                    Ok(GBL_EFI_FASTBOOT_COMMAND_EXEC_RESULT_DEFAULT_IMPL)
                    | Err(Error::NotFound) => Ok(CommandExecType::DefaultImpl),
                    Ok(GBL_EFI_FASTBOOT_COMMAND_EXEC_RESULT_CUSTOM_IMPL) => {
                        Ok(CommandExecType::CustomImpl)
                    }
                    Ok(_) => Err(Error::InvalidState),
                    Err(e) => Err(e),
                }
            }
            Err(Error::NotFound) => Ok(Default::default()),
            Err(e) => Err(e),
        }
    }
}

impl Write for Ops<'_, '_> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        efi_print!(self.efi_entry, "{}", s);
        Ok(())
    }
}

/// Helper function to handle message sending for cammand_exec
fn command_exec_message_sender(
    msg_type: GblEfiFastbootMessageType,
    msg: &str,
    sender: &mut Option<impl InfoSender + OkaySender + FailSender>,
) -> Result<()> {
    match msg_type {
        GBL_EFI_FASTBOOT_MESSAGE_TYPE_INFO => {
            block_on(sender.as_mut().ok_or(Error::ProtocolError)?.send_info(msg))
        }
        GBL_EFI_FASTBOOT_MESSAGE_TYPE_OKAY => {
            block_on(sender.take().ok_or(Error::ProtocolError)?.send_okay(msg))
        }
        GBL_EFI_FASTBOOT_MESSAGE_TYPE_FAIL => {
            block_on(sender.take().ok_or(Error::ProtocolError)?.send_fail(msg))
        }
        _ => Err(Error::InvalidInput),
    }
}

impl<'a, 'b> GblOps<'b> for Ops<'a, 'b> {
    fn console_out(&mut self) -> Option<&mut dyn Write> {
        Some(self)
    }

    /// UEFI console uses \r\n newline.
    fn console_newline(&self) -> &'static str {
        "\r\n"
    }

    /// Reboots the system into the last set boot mode.
    fn reboot(&mut self) -> Result<!> {
        self.efi_entry.system_table().runtime_services().cold_reset()
    }

    fn disks(
        &self,
    ) -> &'b [GblDisk<
        Disk<impl BlockIo + 'b, impl BufferPool + 'b>,
        Gpt<impl DerefMut<Target = [u8]> + 'b>,
    >] {
        self.disks
    }

    fn expected_os(&mut self) -> Result<Option<Os>> {
        Ok(self.os)
    }

    fn get_random_bytes(&self, algorithm: GblRngAlgorithm, buffer: &mut [u8]) -> Result<()> {
        self.efi_entry
            .system_table()
            .boot_services()
            .find_first_and_open::<RandomNumberGeneratorProtocol>()
            .and_then(|p| p.get_rng_bytes(gbl_to_efi_rng_algorithm(algorithm), buffer))
    }

    #[cfg(feature = "fuchsia")]
    fn zircon_add_device_zbi_items(
        &mut self,
        container: &mut ZbiContainer<&mut [u8]>,
    ) -> Result<()> {
        // TODO(b/353272981): Switch to use OS configuration protocol once it is implemented on
        // existing platforms such as VIM3.
        if let Some(fdt) = self.get_efi_fdt()
            && let Ok(blob) = fdt.get_property("zircon", c"zbi-blob")
        {
            container.extend_unaligned(blob).map_err(|_| "Failed to append ZBI")?;
        } else {
            efi_println!(self.efi_entry, "No device ZBI items.\r\n");
        }

        Ok(())
    }

    #[cfg(feature = "fuchsia")]
    fn get_zbi_bootloader_files_buffer(&mut self) -> Option<&mut [u8]> {
        // Switches to use get_image_buffer once available.
        const DEFAULT_SIZE: usize = 4096;
        if self.zbi_bootloader_files_buffer.is_empty() {
            self.zbi_bootloader_files_buffer.resize(DEFAULT_SIZE, 0);
        }
        Some(self.zbi_bootloader_files_buffer.as_mut_slice())
    }

    fn load_slot_interface<'c>(
        &'c mut self,
        _: &'c mut dyn FnMut(&mut [u8]) -> Result<()>,
        _: BootToken,
    ) -> GblResult<Cursor<'c>> {
        unimplemented!();
    }

    fn avb_read_partition_attributes_raw(
        &mut self,
    ) -> AvbIoResult<ArrayMaxSpecializedParts<SpecializedPartition>> {
        match self.open_avb_protocol() {
            Ok(protocol) => protocol.read_partition_attributes().map_err(efi_error_to_avb_error),

            Err(_) => Err(AvbIoError::NotImplemented),
        }
    }

    fn avb_read_device_status(&mut self) -> AvbIoResult<AvbDeviceStatus> {
        match self.open_avb_protocol() {
            Ok(protocol) => protocol
                .read_device_status()
                .map(efi_to_gbl_avb_device_status)
                .map_err(efi_error_to_avb_error),
            Err(_) => Err(AvbIoError::NotImplemented),
        }
    }

    fn avb_read_rollback_index(&mut self, rollback_index_location: usize) -> AvbIoResult<u64> {
        match self.open_avb_protocol() {
            Ok(protocol) => protocol
                .read_rollback_index(rollback_index_location)
                .map_err(efi_error_to_avb_error),
            Err(_) => Err(AvbIoError::NotImplemented),
        }
    }

    fn avb_write_rollback_index(
        &mut self,
        rollback_index_location: usize,
        index: u64,
    ) -> AvbIoResult<()> {
        match self.open_avb_protocol() {
            Ok(protocol) => protocol
                .write_rollback_index(rollback_index_location, index)
                .map_err(efi_error_to_avb_error),
            Err(_) => Err(AvbIoError::NotImplemented),
        }
    }

    fn avb_read_persistent_value(&mut self, name: &CStr, value: &mut [u8]) -> AvbIoResult<usize> {
        match self.open_avb_protocol() {
            Ok(protocol) => {
                protocol.read_persistent_value(name, value).map_err(efi_error_to_avb_error)
            }
            Err(_) => Err(AvbIoError::NotImplemented),
        }
    }

    fn avb_write_persistent_value(&mut self, name: &CStr, value: &[u8]) -> AvbIoResult<()> {
        match self.open_avb_protocol() {
            Ok(protocol) => {
                protocol.write_persistent_value(name, Some(value)).map_err(efi_error_to_avb_error)
            }
            Err(_) => Err(AvbIoError::NotImplemented),
        }
    }

    fn avb_erase_persistent_value(&mut self, name: &CStr) -> AvbIoResult<()> {
        match self.open_avb_protocol() {
            Ok(protocol) => {
                protocol.write_persistent_value(name, None).map_err(efi_error_to_avb_error)
            }
            Err(_) => Err(AvbIoError::NotImplemented),
        }
    }

    fn avb_validate_vbmeta_public_key(
        &self,
        public_key: &[u8],
        public_key_metadata: Option<&[u8]>,
    ) -> AvbIoResult<KeyValidationStatus> {
        match self.open_avb_protocol() {
            Ok(protocol) => protocol
                .validate_vbmeta_public_key(public_key, public_key_metadata)
                .map(to_avb_validation_status_or_panic)
                .map_err(efi_error_to_avb_error),
            Err(_) => Err(AvbIoError::NotImplemented),
        }
    }

    fn avb_cert_read_permanent_attributes(
        &mut self,
        attributes: &mut CertPermanentAttributes,
    ) -> AvbIoResult<()> {
        // TODO(b/337846185): Switch to use GBL Verified Boot EFI protocol when available.
        if let Some(fdt) = self.get_efi_fdt()
            && let Ok(perm_attr) = fdt.get_property("gbl", c"avb-cert-permanent-attributes")
        {
            attributes.as_bytes_mut().clone_from_slice(perm_attr);
            Ok(())
        } else {
            Err(AvbIoError::NotImplemented)
        }
    }

    fn avb_cert_read_permanent_attributes_hash(&mut self) -> AvbIoResult<[u8; SHA256_DIGEST_SIZE]> {
        // TODO(b/337846185): Switch to use GBL Verified Boot EFI protocol when available.
        if let Some(fdt) = self.get_efi_fdt()
            && let Ok(hash) = fdt.get_property("gbl", c"avb-cert-permanent-attributes-hash")
        {
            Ok(hash.try_into().map_err(|_| AvbIoError::Io)?)
        } else {
            Err(AvbIoError::NotImplemented)
        }
    }

    fn avb_handle_verification_result<'c>(
        &mut self,
        status: VerificationStatus,
        digest: Option<&CStr>,
        properties: Option<impl Iterator<Item = AvbProperty<'c>>>,
        partitions: Option<impl Iterator<Item = AvbPartition<'c>>>,
    ) -> AvbIoResult<()> {
        // TODO(b/337846185): Cover `avb_handle_verification_result` with unittests.

        // The maximum number of AVB properties that can be provided to the AVB protocol.
        // If more properties are detected across vbmeta, GBL rejects to boot.
        const AVB_PROPERTIES_MAX_NUM: usize = 128;
        struct AvbPropertiesStorage(ArrayVec<GblEfiAvbProperty, AVB_PROPERTIES_MAX_NUM>);

        /// # Safety
        ///
        /// `GblEfiAvbProperty` raw pointers are re-initialized from the const-borrowed `properties`
        /// data at the start of each lock session and never reused afterward. This ensures the
        /// pointed-to data is accessed only by the current thread, making `Send` safe for this
        /// case.
        unsafe impl Send for AvbPropertiesStorage {}

        // Storage for extracted AVB properties to be provided as a sequential array through the AVB
        // protocol. Mutable static memory is used to avoid large stack allocations.
        static AVB_PROPERTIES_STORAGE: Mutex<AvbPropertiesStorage> =
            Mutex::new(AvbPropertiesStorage(ArrayVec::new_const()));

        match self.open_avb_protocol() {
            Ok(protocol) => {
                #[cfg(not(test))]
                let mut avb_properties_efi = AVB_PROPERTIES_STORAGE.try_lock().unwrap();
                // Blocking lock is used in unittests to ensure this function can be safely called
                // from the separate threads, which must cause an error in UEFI environment.
                #[cfg(test)]
                let mut avb_properties_efi = AVB_PROPERTIES_STORAGE.lock();
                avb_properties_efi.0.clear();

                if let Some(properties) = properties {
                    for prop in properties {
                        avb_properties_efi
                            .0
                            .try_push(gbl_to_efi_avb_property(prop))
                            .inspect_err(|_| {
                                gbl_println!(
                                    self,
                                    "A maximum of {} AVB properties can be provided.",
                                    AVB_PROPERTIES_MAX_NUM
                                )
                            })
                            .map_err(|_| AvbIoError::Io)?;
                    }
                }

                let partitions_efi: ArrayMaxParts<GblEfiAvbLoadedPartition> = partitions
                    .map_or_else(ArrayMaxParts::new, |p| p.map(gbl_to_efi_avb_partition).collect());

                protocol
                    .handle_verification_result(&GblEfiAvbVerificationResult {
                        color_flags: gbl_verification_status_to_efi_color_flags(status),
                        digest: digest.map_or(null(), |p| p.as_ptr() as _),
                        num_partitions: partitions_efi.len(),
                        partitions: match partitions_efi.is_empty() {
                            false => partitions_efi.as_ptr(),
                            true => null(),
                        },
                        num_properties: avb_properties_efi.0.len(),
                        properties: match avb_properties_efi.0.is_empty() {
                            false => avb_properties_efi.0.as_ptr(),
                            true => null(),
                        },
                        reserved: Default::default(),
                    })
                    .map_err(efi_error_to_avb_error)
            }
            _ => Ok(()),
        }
    }

    fn factory_data_reset(&mut self) -> Result<()> {
        match self.open_avb_protocol() {
            Ok(protocol) => protocol.factory_data_reset(),
            Err(e) => Err(e),
        }
    }

    fn avf_is_supported(&mut self) -> Result<bool> {
        match self.open_avf_protocol() {
            Ok(_) => Ok(true),
            // Protocol is optional.
            Err(Error::NotFound | Error::Unsupported) => Ok(false),
            Err(e) => Err(e),
        }
    }

    fn avf_read_vendor_dice_handover<'c>(&mut self, buffer: &'c mut [u8]) -> Result<&'c [u8]> {
        let handover_size = self.open_avf_protocol()?.read_vendor_dice_handover(buffer)?;

        Ok(&buffer[..handover_size])
    }

    fn avf_read_secretkeeper_public_key<'c>(
        &mut self,
        buffer: &'c mut [u8],
    ) -> Result<Option<&'c [u8]>> {
        match self.open_avf_protocol()?.read_secretkeeper_public_key(buffer) {
            Ok(public_key_size) => Ok(Some(&buffer[..public_key_size])),
            // Secret Keeper public key may not be provided for VMs booted with the legacy
            // `VmSecrets::V1` scheme. This shouldn't be supported on modern devices, so
            // print a warning to keep vendors aware.
            //
            // https://cs.android.com/android/platform/superproject/main/+/main:packages/modules/Virtualization/docs/updatable_vm.md
            Err(Error::Unsupported) => {
                efi_println!(
                    self.efi_entry,
                    "Warning: secret keeper public key isn't provided. PVM may not work properly.",
                );
                Ok(None)
            }
            Err(e) => Err(e),
        }
    }

    fn get_partition_buffer(
        &self,
        part: LoadPartition,
    ) -> Result<PartitionBuffer<impl DerefMut<Target = [u8]> + 'b>> {
        Ok(match gbl_get_partition_buffer(self.efi_entry, part.name())? {
            v if v.is_preloaded() => PartitionBuffer::Preloaded(v),
            v => PartitionBuffer::Designated(v),
        })
    }

    fn sync_partition_buffer(&mut self, sync_preloaded: bool) -> Result<()> {
        match gbl_sync_partition_buffer(self.efi_entry, sync_preloaded) {
            Err(Error::NotFound) => Ok(()),
            v => v,
        }
    }

    fn fixup_bootconfig<'c>(
        &mut self,
        bootconfig: &[u8],
        fixup_buffer: &'c mut [u8],
    ) -> Result<Option<&'c [u8]>> {
        match self.open_os_configuration_protocol() {
            Ok(protocol) => match protocol.fixup_bootconfig(bootconfig, fixup_buffer) {
                Ok(fixup_size) => Ok(Some(&fixup_buffer[..fixup_size])),
                Err(Error::Unsupported) => Ok(None),
                Err(e) => Err(e),
            },
            // Protocol is optional.
            Err(Error::NotFound) => Ok(None),
            Err(e) => Err(e),
        }
    }

    fn fixup_device_tree(&mut self, device_tree: &mut [u8]) -> Result<()> {
        match self.efi_entry.system_table().boot_services().find_first_and_open::<DtFixupProtocol>()
        {
            Ok(protocol) => protocol.fixup(device_tree),
            // Protocol is optional.
            Err(Error::NotFound) => Ok(()),
            Err(e) => Err(e),
        }
    }

    fn select_device_trees(
        &mut self,
        components_registry: &mut DtComponentsRegistry,
    ) -> Result<()> {
        match self.open_os_configuration_protocol() {
            Ok(protocol) => {
                // The array allocation below takes up about 24 KiB of stack space. Be careful when
                // increasing the MAXIMUM_DT_COMPONENTS limit.
                const_assert_eq!(MAXIMUM_DT_COMPONENTS, 512);
                let mut uefi_components: ArrayVec<_, MAXIMUM_DT_COMPONENTS> = components_registry
                    .components()
                    .map(|component| dt_component_to_efi_dt(component))
                    .collect();

                protocol.select_device_trees(&mut uefi_components[..])?;

                // Propagate selections to the components_registry.
                components_registry
                    .components_mut()
                    .zip(uefi_components.iter_mut())
                    .enumerate()
                    .for_each(|(index, (component, uefi_component))| {
                        if uefi_component.selected {
                            efi_println!(
                                self.efi_entry,
                                "Device tree component at index {} got selected by UEFI call. \
                                Source: {}. Type: {}",
                                index,
                                component.source_metadata.source,
                                component.component_type,
                            );
                        }
                        component.selected = uefi_component.selected;
                    });

                Ok(())
            }
            // Protocol is optional.
            Err(Error::NotFound) => components_registry.autoselect(),
            Err(e) => Err(e),
        }
    }

    fn select_fit_configuration(
        &mut self,
        fit: &[u8],
        metadata: Option<&[u8]>,
    ) -> Result<Option<usize>> {
        match self.open_os_configuration_protocol() {
            Ok(protocol) => {
                let metadata_slice = metadata.unwrap_or(&[]);
                match protocol.select_fit_configuration(fit, metadata_slice) {
                    Ok(selected_config) => Ok(Some(selected_config)),
                    Err(Error::Unsupported) => Ok(None),
                    Err(e) => Err(e),
                }
            }
            // Protocol is optional.
            Err(Error::NotFound) => Ok(None),
            Err(e) => Err(e),
        }
    }

    fn fastboot_variable<'arg>(
        &mut self,
        name: &CStr,
        args: impl Iterator<Item = &'arg CStr> + Clone,
        out: &mut [u8],
    ) -> Result<usize> {
        self.open_fastboot_protocol()?.get_var(name, args, out)
    }

    fn fastboot_visit_all_variables(
        &mut self,
        mut cb: impl FnMut(&mut Self, &[&CStr], &CStr),
    ) -> Result<()> {
        match self.open_fastboot_protocol() {
            Ok(v) => v.get_var_all(|args, val| cb(self, args, val)),
            Err(Error::NotFound) => Ok(()),
            Err(e) => Err(e),
        }
    }

    fn avb_write_lock_state(&mut self, lock_type: LockType, lock_state: LockState) -> Result<()> {
        let lock_type = match lock_type {
            LockType::Device => efi_types::GBL_EFI_AVB_LOCK_TYPE_DEVICE,
            LockType::Critical => efi_types::GBL_EFI_AVB_LOCK_TYPE_CRITICAL,
        };
        let lock_state = match lock_state {
            LockState::Locked => efi_types::GBL_EFI_AVB_LOCK_STATE_LOCKED,
            LockState::Unlocked => efi_types::GBL_EFI_AVB_LOCK_STATE_UNLOCKED,
        };

        self.open_avb_protocol()?.write_lock_state(lock_type, lock_state)
    }

    fn fastboot_get_unlock_ability(&mut self) -> Result<Unlockability> {
        let unlockable =
            self.avb_read_device_status().map_err(avb_error_to_efi_error)?.is_unlockable;
        let unlock_ability =
            if unlockable { Unlockability::Allowed } else { Unlockability::Prohibited };
        Ok(unlock_ability)
    }

    fn fastboot_get_staged(&mut self, out: &mut [u8]) -> Result<(usize, usize)> {
        match self.open_fastboot_protocol() {
            Ok(v) => v.get_staged(out),
            Err(Error::NotFound) => Ok((0, 0)),
            Err(e) => Err(e),
        }
    }

    fn fastboot_get_partition_type(&mut self, part: &str) -> Result<FastbootPartitionType> {
        let mut part_type = [0u8; _];
        match self
            .open_fastboot_protocol()
            .and_then(|p| p.get_partition_type(RawName::try_from(part)?.to_cstr(), &mut part_type))
        {
            Ok(part_type_len) => Ok((part_type_len, part_type).into()),
            Err(Error::NotFound | Error::Unsupported) => Ok(Default::default()),
            Err(e @ Error::BufferTooSmall(_)) => {
                gbl_println!(
                    self,
                    "fastboot_get_partition_type: buffer_len={}, error={e:?}",
                    part_type.len(),
                );
                Ok(Default::default())
            }
            Err(e) => Err(e),
        }
    }

    fn fastboot_command_exec<'arg, Sender: InfoSender + OkaySender + FailSender>(
        &mut self,
        args: impl Iterator<Item = &'arg CStr> + Clone,
        download: &mut [u8],
        download_used: usize,
        sender: Sender,
    ) -> Result<CommandExecType> {
        let sender = &mut Some(sender);
        let mut res =
            self.handle_command_exec_via_protocol(args.clone(), download, download_used, sender);

        if matches!(res, Ok(CommandExecType::DefaultImpl) | Err(Error::NotFound))
            && let Some(sender) = sender.take()
        {
            res = self.handle_command_exec_locally(args, sender);
        }

        res
    }

    fn get_slot_info(&mut self, slot: u8) -> Result<Slot> {
        self.open_boot_control_protocol()?.get_slot_info(slot)?.try_into()
    }

    fn get_current_slot(&mut self) -> Result<Slot> {
        self.open_boot_control_protocol()?.get_current_slot()?.try_into()
    }

    fn set_active_slot(&mut self, slot: u8) -> Result<()> {
        self.open_boot_control_protocol()?.set_active_slot(slot)
    }

    fn get_one_shot_boot_mode(&mut self) -> Result<Option<OneShotBootMode>> {
        match self.open_boot_control_protocol().and_then(|p| p.get_one_shot_boot_mode()) {
            Ok(GBL_EFI_ONE_SHOT_BOOT_MODE_NONE) => Ok(None),
            Ok(GBL_EFI_ONE_SHOT_BOOT_MODE_BOOTLOADER) => Ok(Some(OneShotBootMode::Bootloader)),
            Ok(GBL_EFI_ONE_SHOT_BOOT_MODE_RECOVERY) => Ok(Some(OneShotBootMode::Recovery)),
            Ok(v) => {
                efi_println!(self.efi_entry, "Unexpected GBL_EFI_ONE_SHOT_BOOT_MODE value: {v:?}");
                Err(Error::InvalidInput)
            }
            // If protocol method is not implemented or unsupported, provides a built-in mechanism
            // of stopping in fastboot by pressing f key from the console.
            #[cfg(feature = "gbl_dev")]
            Err(Error::NotFound | Error::Unsupported) => {
                use crate::utils::wait_key_stroke;
                use core::time::Duration;
                efi_println!(
                    self.efi_entry,
                    "Press 'f' to enter fastboot now, 'p' to enter fastboot after load."
                );
                let pred = |key: efi_types::EfiInputKey| b"pf".contains(&(key.unicode_char as u8));
                // wait_key_stroke generates lots of polling function calls, most of which are just
                // waiting for IO. Disable tracing to prevent it from adding too many meaningless
                // traces.
                let _guard = trace::TraceGuard::new(false);
                match wait_key_stroke(self.efi_entry, pred, Duration::from_secs(2)) {
                    Ok(Some(v)) => {
                        efi_println!(
                            self.efi_entry,
                            "{:?} pressed",
                            char::from_u32(v.unicode_char.into()).unwrap_or('?')
                        );
                        match v.unicode_char as u8 {
                            b'p' => {
                                self.pause_fastboot = true;
                                Ok(None)
                            }
                            b'f' => Ok(Some(OneShotBootMode::Bootloader)),
                            _ => unreachable!(),
                        }
                    }
                    Ok(_) => Ok(None),
                    Err(e) => {
                        efi_println!(self.efi_entry, "wait_key_stroke failed: {e}");
                        Err(e)
                    }
                }
            }
            Err(e) => Err(e),
        }
    }

    fn one_shot_pause_fastboot_after_load(&mut self) -> bool {
        core::mem::take(&mut self.pause_fastboot) || cfg!(feature = "pause-boot-in-fastboot")
    }

    fn get_slot_count(&mut self) -> Result<u8> {
        match self.open_boot_control_protocol().and_then(|p| p.get_slot_count()) {
            #[cfg(feature = "fuchsia")]
            Err(Error::Unsupported) if self.expected_os_is_fuchsia()? => Ok(2),
            v => v,
        }
    }

    fn handle_loaded_os(
        &mut self,
        kernel: &[u8],
        ramdisk: &[u8],
        device_tree: &[u8],
    ) -> Result<()> {
        self.open_boot_control_protocol()?.handle_loaded_os(&efi_types::GblEfiLoadedOs {
            kernel_size: kernel.len(),
            kernel: kernel.as_ptr() as _,
            ramdisk_size: ramdisk.len(),
            ramdisk: ramdisk.as_ptr() as _,
            device_tree_size: device_tree.len(),
            device_tree: device_tree.as_ptr() as _,
            reserved: Default::default(),
        })
    }

    fn get_base_sp(&mut self) -> Option<usize> {
        Some(self.base_sp)
    }

    fn get_profiling_backend(&self) -> impl ProfileBackend {
        EfiProfileBackend::new(self.efi_entry)
    }

    fn get_firmware_version_metrics(&self) -> FirmwareVersionMetrics {
        let mut metrics = FirmwareVersionMetrics::new();
        for (tag, rev) in efi::opened_protocols() {
            let _ = metrics.try_push((tag, FirmwareVersion { major: rev.major, minor: rev.minor }));
        }
        metrics.sort_by(|a, b| a.0.cmp(b.0));
        metrics
    }

    fn get_fw_api_level(&self) -> Result<u64> {
        let mut buf = [0u8; 32];
        let size = self.efi_entry.system_table().runtime_services().get_variable(
            &GBL_EFI_VENDOR_GUID,
            GBL_EFI_FW_API_LEVEL,
            &mut buf,
        )?;
        parse_fw_api_level(&buf[..size])
    }

    fn get_time(&self) -> Option<&impl GblTime> {
        self.time.as_ref()
    }

    fn get_metrics(&self) -> Option<impl DerefMut<Target = GblMetrics> + '_> {
        Some(self.metrics.lock())
    }
}

/// Converts a [AvbPartition] to [GblEfiAvbLoadedPartition]
fn gbl_to_efi_avb_partition(partition: AvbPartition) -> GblEfiAvbLoadedPartition {
    GblEfiAvbLoadedPartition {
        base_name: partition.name.as_ptr() as _,
        data_size: partition.data.len(),
        data: partition.data.as_ptr(),
    }
}

/// Converts a [AvbProperty] to [GblEfiAvbProperty]
fn gbl_to_efi_avb_property(property: AvbProperty) -> GblEfiAvbProperty {
    GblEfiAvbProperty {
        base_partition_name: property.partition.as_ptr() as _,
        key: property.key.as_ptr() as _,
        // Exclude null terminator.
        value_size: property.value_with_nul.len() - 1,
        value: property.value_with_nul.as_ptr(),
    }
}

/// Converts [GblEfiAvbDeviceStatus] bitmask to [AvbDeviceStatus]
fn efi_to_gbl_avb_device_status(mask: GblEfiAvbDeviceStatus) -> AvbDeviceStatus {
    AvbDeviceStatus {
        is_unlocked: mask & efi_types::GBL_EFI_AVB_DEVICE_STATUS_UNLOCKED != 0,
        is_unlocked_critical: mask & efi_types::GBL_EFI_AVB_DEVICE_STATUS_UNLOCKED_CRITICAL != 0,
        is_dm_verity_error: mask & efi_types::GBL_EFI_AVB_DEVICE_STATUS_DM_VERITY_FAILED != 0,
        is_unlockable: mask & efi_types::GBL_EFI_AVB_DEVICE_STATUS_UNLOCKABLE != 0,
    }
}

fn to_avb_validation_status_or_panic(status: GblEfiAvbKeyValidationStatus) -> KeyValidationStatus {
    match status {
        efi_types::GBL_EFI_AVB_KEY_VALIDATION_STATUS_VALID => KeyValidationStatus::Valid,
        efi_types::GBL_EFI_AVB_KEY_VALIDATION_STATUS_VALID_CUSTOM_KEY => {
            KeyValidationStatus::ValidCustomKey
        }
        efi_types::GBL_EFI_AVB_KEY_VALIDATION_STATUS_INVALID => KeyValidationStatus::Invalid,
        _ => panic!("Unrecognized avb key validation status: {:?}", status),
    }
}

fn gbl_verification_status_to_efi_color_flags(status: VerificationStatus) -> u64 {
    let base_color = match status.color {
        BootStateColor::Green => efi_types::GBL_EFI_AVB_BOOT_COLOR_GREEN,
        BootStateColor::Yellow => efi_types::GBL_EFI_AVB_BOOT_COLOR_YELLOW,
        BootStateColor::Orange => efi_types::GBL_EFI_AVB_BOOT_COLOR_ORANGE,
        BootStateColor::Red => efi_types::GBL_EFI_AVB_BOOT_COLOR_RED,
    };
    let eio_flag = match status.is_eio {
        true => efi_types::GBL_EFI_AVB_BOOT_COLOR_RED_EIO,
        false => 0,
    };

    base_color | eio_flag
}

fn gbl_to_efi_rng_algorithm(algorithm: GblRngAlgorithm) -> EfiRngAlgorithm {
    match algorithm {
        GblRngAlgorithm::Default => EfiRngAlgorithm::Default,
        GblRngAlgorithm::Raw => EfiRngAlgorithm::Raw,
    }
}

fn efi_error_to_avb_error(error: Error) -> AvbIoError {
    match error {
        // EFI_STATUS_OUT_OF_RESOURCES
        Error::OutOfResources => AvbIoError::Oom,
        // EFI_STATUS_DEVICE_ERROR
        Error::DeviceError => AvbIoError::Io,
        // EFI_STATUS_NOT_FOUND
        Error::NotFound => AvbIoError::NoSuchValue,
        // EFI_STATUS_END_OF_FILE
        Error::EndOfFile => AvbIoError::RangeOutsidePartition,
        // EFI_STATUS_INVALID_PARAMETER
        Error::InvalidInput => AvbIoError::InvalidValueSize,
        // EFI_STATUS_BUFFER_TOO_SMALL
        Error::BufferTooSmall(required) => {
            AvbIoError::InsufficientSpace(required.unwrap_or_default())
        }
        // EFI_STATUS_UNSUPPORTED
        Error::Unsupported => AvbIoError::NotImplemented,
        _ => AvbIoError::Io,
    }
}

fn avb_error_to_efi_error(error: AvbIoError) -> Error {
    match error {
        AvbIoError::Oom => Error::OutOfResources,
        AvbIoError::Io => Error::DeviceError,
        AvbIoError::NoSuchValue => Error::NotFound,
        AvbIoError::RangeOutsidePartition => Error::EndOfFile,
        AvbIoError::InvalidValueSize => Error::InvalidInput,
        AvbIoError::InsufficientSpace(space) => Error::BufferTooSmall(Some(space)),
        AvbIoError::NotImplemented => Error::Unsupported,
        AvbIoError::NoSuchPartition => Error::InvalidInput,
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use ::efi::protocol::Revision;
    use efi_mocks::{protocol::gbl_efi_avb::GblAvbProtocol, MockEfi};
    use libgbl::{
        device_tree::{DtComponentSourceMetadata, SelectedDtComponent, SelectedDtComponents},
        gbl_avb::{Critical, Fdr, Verification},
    };
    use libutils::cstr_buffer;
    use mockall::predicate::eq;
    use std::slice;

    /// Builds a `MockEfi` whose `find_first_and_open::<P>()` returns a default mock with
    /// `Versioned::revision` overridden to `revision`. The con_out passthrough lets the
    /// rejection path's `efi_println!` succeed without an explicit `write_str` expectation.
    fn mock_efi_with_revision<P: 'static + efi_mocks::protocol::WithRevision>(
        revision: Revision,
    ) -> MockEfi {
        let mut mock_efi = MockEfi::new();
        mock_efi.con_out.expect_write_str().returning(|_| Ok(()));
        mock_efi
            .boot_services
            .expect_find_first_and_open::<P>()
            .return_once(move || Ok(P::with_revision(revision)));
        mock_efi
    }

    #[test]
    fn open_avb_protocol_rejects_pre_1_0() {
        let installed =
            mock_efi_with_revision::<GblAvbProtocol>(Revision { major: 0, minor: 256 }).install();
        let ops = Ops::new(installed.entry(), &[], None, 0);
        assert_eq!(ops.open_avb_protocol().err(), Some(Error::UnsupportedVersion));
    }

    #[test]
    fn open_avb_protocol_accepts_1_0() {
        let installed =
            mock_efi_with_revision::<GblAvbProtocol>(Revision { major: 1, minor: 0 }).install();
        let ops = Ops::new(installed.entry(), &[], None, 0);
        assert!(ops.open_avb_protocol().is_ok());
    }

    #[test]
    fn open_avf_protocol_rejects_pre_1_0() {
        let installed =
            mock_efi_with_revision::<GblAvfProtocol>(Revision { major: 0, minor: 256 }).install();
        let ops = Ops::new(installed.entry(), &[], None, 0);
        assert_eq!(ops.open_avf_protocol().err(), Some(Error::UnsupportedVersion));
    }

    #[test]
    fn open_avf_protocol_accepts_1_0() {
        let installed =
            mock_efi_with_revision::<GblAvfProtocol>(Revision { major: 1, minor: 0 }).install();
        let ops = Ops::new(installed.entry(), &[], None, 0);
        assert!(ops.open_avf_protocol().is_ok());
    }

    #[test]
    fn open_boot_control_protocol_rejects_pre_1_0() {
        let installed =
            mock_efi_with_revision::<GblBootControlProtocol>(Revision { major: 0, minor: 256 })
                .install();
        let ops = Ops::new(installed.entry(), &[], None, 0);
        assert_eq!(ops.open_boot_control_protocol().err(), Some(Error::UnsupportedVersion));
    }

    #[test]
    fn open_boot_control_protocol_accepts_1_0() {
        let installed =
            mock_efi_with_revision::<GblBootControlProtocol>(Revision { major: 1, minor: 0 })
                .install();
        let ops = Ops::new(installed.entry(), &[], None, 0);
        assert!(ops.open_boot_control_protocol().is_ok());
    }

    #[test]
    fn open_fastboot_protocol_rejects_pre_1_0() {
        let installed =
            mock_efi_with_revision::<GblFastbootProtocol>(Revision { major: 0, minor: 256 })
                .install();
        let ops = Ops::new(installed.entry(), &[], None, 0);
        assert_eq!(ops.open_fastboot_protocol().err(), Some(Error::UnsupportedVersion));
    }

    #[test]
    fn open_fastboot_protocol_accepts_1_0() {
        let installed =
            mock_efi_with_revision::<GblFastbootProtocol>(Revision { major: 1, minor: 0 })
                .install();
        let ops = Ops::new(installed.entry(), &[], None, 0);
        assert!(ops.open_fastboot_protocol().is_ok());
    }

    #[test]
    fn open_os_configuration_protocol_rejects_pre_1_0() {
        let installed =
            mock_efi_with_revision::<GblOsConfigurationProtocol>(Revision { major: 0, minor: 256 })
                .install();
        let ops = Ops::new(installed.entry(), &[], None, 0);
        assert_eq!(ops.open_os_configuration_protocol().err(), Some(Error::UnsupportedVersion));
    }

    #[test]
    fn open_os_configuration_protocol_accepts_1_0() {
        let installed =
            mock_efi_with_revision::<GblOsConfigurationProtocol>(Revision { major: 1, minor: 0 })
                .install();
        let ops = Ops::new(installed.entry(), &[], None, 0);
        assert!(ops.open_os_configuration_protocol().is_ok());
    }

    /// Represents possible outcomes for protocol method call.
    #[derive(Copy, Clone)]
    enum ProtocolCallStatus<T> {
        /// Protocol found. Method call succeeded.
        Success(T),
        /// Protocol not found.
        ProtocolLookupError(Error),
        /// Protocol found. Method call failed.
        ProtocolCallError(Error),
    }

    #[test]
    fn ops_write_trait() {
        let mut mock_efi = MockEfi::new();

        mock_efi.con_out.expect_write_str().with(eq("foo bar")).return_const(Ok(()));
        let installed = mock_efi.install();

        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        assert!(write!(&mut ops, "{} {}", "foo", "bar").is_ok());
    }

    /// Helper for testing `avb_read_partition_attributes_raw`.
    fn test_avb_read_partition_attributes_raw(
        call_status: ProtocolCallStatus<&[SpecializedPartition]>,
    ) -> AvbIoResult<ArrayMaxSpecializedParts<SpecializedPartition>> {
        let mut mock_efi = MockEfi::new();

        let mut avb = GblAvbProtocol::default();
        avb.read_partition_attributes_result = match call_status {
            ProtocolCallStatus::Success(data) => Some(Ok(data.iter().cloned().collect())),
            ProtocolCallStatus::ProtocolCallError(err) => Some(Err(err)),
            _ => None,
        };

        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(
            match call_status {
                ProtocolCallStatus::ProtocolLookupError(err) => Err(err),
                _ => Ok(avb),
            },
        );

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);
        ops.avb_read_partition_attributes_raw()
    }

    #[test]
    fn ops_avb_read_partition_attributes_raw_success() {
        let partitions = [
            SpecializedPartition {
                name_buffer: cstr_buffer("boot"),
                verification: Some(Verification::Required),
                fdr: Fdr::No,
                critical: Critical::No,
            },
            SpecializedPartition {
                name_buffer: cstr_buffer("vendor_boot"),
                verification: Some(Verification::IfExists),
                fdr: Fdr::Yes,
                critical: Critical::Yes,
            },
            SpecializedPartition {
                name_buffer: cstr_buffer(&"a".repeat(28)),
                verification: None,
                fdr: Fdr::Yes,
                critical: Critical::No,
            },
        ];

        let result =
            test_avb_read_partition_attributes_raw(ProtocolCallStatus::Success(&partitions[..]))
                .unwrap();

        assert_eq!(&result[..], partitions);
    }

    #[test]
    fn ops_avb_read_partition_attributes_raw_protocol_error() {
        assert_eq!(
            test_avb_read_partition_attributes_raw(ProtocolCallStatus::ProtocolCallError(
                Error::InvalidInput
            )),
            Err(AvbIoError::InvalidValueSize)
        );
    }

    #[test]
    fn ops_avb_read_partition_attributes_raw_protocol_not_found() {
        assert_eq!(
            test_avb_read_partition_attributes_raw(ProtocolCallStatus::ProtocolLookupError(
                Error::NotFound
            )),
            Err(AvbIoError::NotImplemented)
        );
    }

    /// Helper for testing `avb_read_device_status`.
    fn test_avb_read_device_status(
        call_status: ProtocolCallStatus<GblEfiAvbDeviceStatus>,
    ) -> AvbIoResult<AvbDeviceStatus> {
        let mut mock_efi = MockEfi::new();

        let mut avb = GblAvbProtocol::default();
        avb.read_device_status_result = match call_status {
            ProtocolCallStatus::Success(mask) => Some(Ok(mask)),
            ProtocolCallStatus::ProtocolCallError(err) => Some(Err(err)),
            _ => None,
        };
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(
            match call_status {
                ProtocolCallStatus::ProtocolLookupError(err) => Err(err),
                _ => Ok(avb),
            },
        );

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);
        ops.avb_read_device_status()
    }

    #[test]
    fn ops_avb_read_device_status_unlocked() {
        let mask = efi_types::GBL_EFI_AVB_DEVICE_STATUS_UNLOCKED
            | (efi_types::GBL_EFI_AVB_DEVICE_STATUS_UNLOCKABLE);
        assert_eq!(
            test_avb_read_device_status(ProtocolCallStatus::Success(mask)),
            Ok(AvbDeviceStatus {
                is_unlocked: true,
                is_unlocked_critical: false,
                is_dm_verity_error: false,
                is_unlockable: true
            })
        );
    }

    #[test]
    fn ops_avb_read_device_status_dm_verity_error() {
        let mask = efi_types::GBL_EFI_AVB_DEVICE_STATUS_DM_VERITY_FAILED;
        assert_eq!(
            test_avb_read_device_status(ProtocolCallStatus::Success(mask)),
            Ok(AvbDeviceStatus {
                is_unlocked: false,
                is_unlocked_critical: false,
                is_dm_verity_error: true,
                is_unlockable: false
            })
        );
    }

    #[test]
    fn ops_avb_read_device_status_unlocked_and_dm_verity_error() {
        let mask = (efi_types::GBL_EFI_AVB_DEVICE_STATUS_UNLOCKED)
            | (efi_types::GBL_EFI_AVB_DEVICE_STATUS_UNLOCKED_CRITICAL)
            | (efi_types::GBL_EFI_AVB_DEVICE_STATUS_DM_VERITY_FAILED)
            | (efi_types::GBL_EFI_AVB_DEVICE_STATUS_UNLOCKABLE);
        assert_eq!(
            test_avb_read_device_status(ProtocolCallStatus::Success(mask)),
            Ok(AvbDeviceStatus {
                is_unlocked: true,
                is_unlocked_critical: true,
                is_dm_verity_error: true,
                is_unlockable: true
            })
        );
    }

    #[test]
    fn ops_avb_read_device_status_empty() {
        assert_eq!(
            test_avb_read_device_status(ProtocolCallStatus::Success(0)),
            Ok(AvbDeviceStatus {
                is_unlocked: false,
                is_unlocked_critical: false,
                is_dm_verity_error: false,
                is_unlockable: false
            })
        );
    }

    #[test]
    fn ops_avb_read_device_status_protocol_not_found() {
        assert_eq!(
            test_avb_read_device_status(ProtocolCallStatus::ProtocolLookupError(Error::NotFound)),
            Err(AvbIoError::NotImplemented)
        );
    }

    #[test]
    fn ops_avb_read_device_status_method_not_implemented() {
        assert_eq!(
            test_avb_read_device_status(ProtocolCallStatus::ProtocolCallError(Error::Unsupported)),
            Err(AvbIoError::NotImplemented)
        );
    }

    #[test]
    fn ops_avb_read_device_status_method_error() {
        assert_eq!(
            test_avb_read_device_status(ProtocolCallStatus::ProtocolCallError(Error::InvalidInput)),
            Err(AvbIoError::InvalidValueSize)
        );
    }

    #[test]
    fn ops_avb_validate_vbmeta_public_key_returns_valid() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.validate_vbmeta_public_key_result =
            Some(Ok(efi_types::GBL_EFI_AVB_KEY_VALIDATION_STATUS_VALID));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let ops = Ops::new(installed.entry(), &[], None, 0);

        assert_eq!(ops.avb_validate_vbmeta_public_key(&[], None), Ok(KeyValidationStatus::Valid));
    }

    #[test]
    fn ops_avb_validate_vbmeta_public_key_returns_valid_custom_key() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.validate_vbmeta_public_key_result =
            Some(Ok(efi_types::GBL_EFI_AVB_KEY_VALIDATION_STATUS_VALID_CUSTOM_KEY));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let ops = Ops::new(installed.entry(), &[], None, 0);

        assert_eq!(
            ops.avb_validate_vbmeta_public_key(&[], None),
            Ok(KeyValidationStatus::ValidCustomKey)
        );
    }

    #[test]
    fn ops_avb_validate_vbmeta_public_key_returns_invalid() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.validate_vbmeta_public_key_result =
            Some(Ok(efi_types::GBL_EFI_AVB_KEY_VALIDATION_STATUS_INVALID));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let ops = Ops::new(installed.entry(), &[], None, 0);

        assert_eq!(ops.avb_validate_vbmeta_public_key(&[], None), Ok(KeyValidationStatus::Invalid));
    }

    #[test]
    fn ops_avb_validate_vbmeta_public_key_failed_error_mapped() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.validate_vbmeta_public_key_result = Some(Err(Error::OutOfResources));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let ops = Ops::new(installed.entry(), &[], None, 0);

        assert_eq!(ops.avb_validate_vbmeta_public_key(&[], None), Err(AvbIoError::Oom));
    }

    #[test]
    fn ops_avb_validate_vbmeta_public_key_protocol_not_found_mapped_to_not_implemented() {
        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblAvbProtocol>()
            .return_const(Err(Error::NotFound));

        let installed = mock_efi.install();
        let ops = Ops::new(installed.entry(), &[], None, 0);

        assert_eq!(ops.avb_validate_vbmeta_public_key(&[], None), Err(AvbIoError::NotImplemented));
    }

    #[test]
    fn ops_avb_read_rollback_index_success() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.read_rollback_index_result = Some(Ok(12345));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        assert_eq!(ops.avb_read_rollback_index(0), Ok(12345));
    }

    #[test]
    fn ops_avb_read_rollback_index_error() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.read_rollback_index_result = Some(Err(Error::OutOfResources));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        assert_eq!(ops.avb_read_rollback_index(0), Err(AvbIoError::Oom));
    }

    #[test]
    fn ops_avb_read_rollback_index_protocol_not_found() {
        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblAvbProtocol>()
            .return_const(Err(Error::NotFound));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        assert_eq!(ops.avb_read_rollback_index(0), Err(AvbIoError::NotImplemented));
    }

    #[test]
    fn ops_avb_write_rollback_index_success() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.write_rollback_index_result = Some(Ok(()));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        assert!(ops.avb_write_rollback_index(0, 12345).is_ok());
    }

    #[test]
    fn ops_avb_write_rollback_index_error() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.write_rollback_index_result = Some(Err(Error::InvalidInput));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        assert_eq!(ops.avb_write_rollback_index(0, 12345), Err(AvbIoError::InvalidValueSize));
    }

    #[test]
    fn ops_avb_write_rollback_index_protocol_not_found() {
        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblAvbProtocol>()
            .return_const(Err(Error::NotFound));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        assert_eq!(ops.avb_write_rollback_index(0, 12345), Err(AvbIoError::NotImplemented));
    }

    #[test]
    fn ops_avb_read_persistent_value_success() {
        const EXPECTED_LEN: usize = 4;

        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.read_persistent_value_result = Some(Ok(EXPECTED_LEN));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        let mut buffer = [0u8; EXPECTED_LEN];
        assert_eq!(ops.avb_read_persistent_value(c"test", &mut buffer), Ok(EXPECTED_LEN));
    }

    #[test]
    fn ops_avb_read_persistent_value_error() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.read_persistent_value_result = Some(Err(Error::OutOfResources));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        let mut buffer = [0u8; 0];
        assert_eq!(ops.avb_read_persistent_value(c"test", &mut buffer), Err(AvbIoError::Oom));
    }

    #[test]
    fn ops_avb_read_persistent_value_protocol_not_found() {
        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblAvbProtocol>()
            .return_const(Err(Error::NotFound));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        let mut buffer = [0u8; 0];
        assert_eq!(
            ops.avb_read_persistent_value(c"test", &mut buffer),
            Err(AvbIoError::NotImplemented)
        );
    }

    #[test]
    fn ops_avb_write_persistent_value_success() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.write_persistent_value_result = Some(Ok(()));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        assert_eq!(ops.avb_write_persistent_value(c"test", b""), Ok(()));
    }

    #[test]
    fn ops_avb_write_persistent_value_error() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.write_persistent_value_result = Some(Err(Error::InvalidInput));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        assert_eq!(ops.avb_write_persistent_value(c"test", b""), Err(AvbIoError::InvalidValueSize));
    }

    #[test]
    fn ops_avb_write_persistent_value_protocol_not_found() {
        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblAvbProtocol>()
            .return_const(Err(Error::NotFound));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        assert_eq!(ops.avb_write_persistent_value(c"test", b""), Err(AvbIoError::NotImplemented));
    }

    #[test]
    fn ops_avb_erase_persistent_value_success() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.write_persistent_value_result = Some(Ok(()));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        assert_eq!(ops.avb_erase_persistent_value(c"test"), Ok(()));
    }

    #[test]
    fn ops_avb_erase_persistent_value_error() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.write_persistent_value_result = Some(Err(Error::DeviceError));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        assert_eq!(ops.avb_erase_persistent_value(c"test"), Err(AvbIoError::Io));
    }

    fn avb_get_unlock_ability(status_flags: GblEfiAvbDeviceStatus, unlockability: Unlockability) {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.read_device_status_result = Some(Ok(status_flags));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);
        assert_eq!(ops.fastboot_get_unlock_ability(), Ok(unlockability));
    }

    #[test]
    fn test_avb_get_unlock_ability_secured() {
        avb_get_unlock_ability(0, Unlockability::Prohibited);
    }

    #[test]
    fn test_avb_get_unlock_ability_unlockable() {
        avb_get_unlock_ability(
            efi_types::GBL_EFI_AVB_DEVICE_STATUS_UNLOCKABLE,
            Unlockability::Allowed,
        );
    }

    #[test]
    fn ops_avb_erase_persistent_value_protocol_not_found() {
        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblAvbProtocol>()
            .return_const(Err(Error::NotFound));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        assert_eq!(ops.avb_erase_persistent_value(c"test"), Err(AvbIoError::NotImplemented));
    }

    #[test]
    fn test_gbl_to_efi_avb_property() {
        let partition = c"boot";
        let key = c"bootkey";
        let value_with_nul = b"value\0";

        assert_eq!(
            gbl_to_efi_avb_property(AvbProperty { partition, key, value_with_nul }),
            GblEfiAvbProperty {
                base_partition_name: partition.as_ptr() as _,
                key: key.as_ptr() as _,
                value_size: value_with_nul.len() - 1,
                value: value_with_nul.as_ptr(),
            }
        );
    }

    #[test]
    fn test_gbl_to_efi_avb_property_empty() {
        let partition = c"";
        let key = c"";
        let value_with_nul = b"\0";

        assert_eq!(
            gbl_to_efi_avb_property(AvbProperty { partition, key, value_with_nul }),
            GblEfiAvbProperty {
                base_partition_name: partition.as_ptr() as _,
                key: key.as_ptr() as _,
                value_size: value_with_nul.len() - 1,
                value: value_with_nul.as_ptr(),
            }
        );
    }

    #[test]
    fn ops_factory_data_reset_success() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.factory_data_reset_result = Some(Ok(()));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);
        assert_eq!(ops.factory_data_reset(), Ok(()));
    }

    #[test]
    fn ops_factory_data_reset_failure() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.factory_data_reset_result = Some(Err(Error::DeviceError));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);
        assert_eq!(ops.factory_data_reset(), Err(Error::DeviceError));
    }

    #[test]
    fn ops_factory_data_reset_not_found() {
        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblAvbProtocol>()
            .return_once(|| Err(Error::NotFound));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);
        assert_eq!(ops.factory_data_reset(), Err(Error::NotFound));
    }

    #[test]
    fn ops_avf_is_supported() {
        let mut mock_efi = MockEfi::new();
        let avf = GblAvfProtocol::default();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblAvfProtocol>()
            .return_once(move || Ok(avf));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        assert_eq!(ops.avf_is_supported(), Ok(true));
    }

    #[test]
    fn ops_avf_is_supported_not_found() {
        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblAvfProtocol>()
            .return_once(|| Err(Error::NotFound));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        assert_eq!(ops.avf_is_supported(), Ok(false));
    }

    /// Helper for testing `GblAvfProtocol.read_vendor_dice_handover`
    fn test_read_vendor_dice_handover<'a>(
        handover_buffer: &'a mut [u8],
        call_status: ProtocolCallStatus<&'static [u8]>,
    ) -> Result<&'a [u8]> {
        let mut mock_efi = MockEfi::new();
        let call_status_scoped = call_status;

        let mut avf = GblAvfProtocol::default();
        avf.expect_read_vendor_dice_handover().return_once(
            move |buffer| match call_status_scoped {
                ProtocolCallStatus::Success(handover_to_apply) => {
                    buffer[..handover_to_apply.len()].copy_from_slice(handover_to_apply);
                    Ok(handover_to_apply.len())
                }
                ProtocolCallStatus::ProtocolCallError(err) => Err(err),
                _ => panic!("Unexpected ProtocolCallStatus"),
            },
        );
        mock_efi.boot_services.expect_find_first_and_open::<GblAvfProtocol>().return_once(
            move || match call_status {
                ProtocolCallStatus::ProtocolLookupError(err) => Err(err),
                _ => Ok(avf),
            },
        );

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);
        ops.avf_read_vendor_dice_handover(handover_buffer)
    }

    #[test]
    fn ops_avf_read_vendor_dice_handover_returned() {
        const HANDOVER_TO_APPLY: &[u8] = b"handover";

        let mut handover_buffer = [0x0; HANDOVER_TO_APPLY.len()];
        assert_eq!(
            test_read_vendor_dice_handover(
                &mut handover_buffer,
                ProtocolCallStatus::Success(HANDOVER_TO_APPLY)
            ),
            Ok(HANDOVER_TO_APPLY)
        );
    }

    #[test]
    fn ops_avf_read_vendor_dice_handover_protocol_not_found() {
        assert_eq!(
            test_read_vendor_dice_handover(
                &mut [],
                ProtocolCallStatus::ProtocolLookupError(Error::NotFound),
            ),
            Err(Error::NotFound),
        );
    }

    #[test]
    fn ops_avf_read_vendor_dice_handover_error_buffer_too_small() {
        const EXPECTED_SIZE: usize = 10;

        assert_eq!(
            test_read_vendor_dice_handover(
                &mut [],
                ProtocolCallStatus::ProtocolCallError(Error::BufferTooSmall(Some(EXPECTED_SIZE))),
            ),
            Err(Error::BufferTooSmall(Some(EXPECTED_SIZE))),
        );
    }

    /// Helper for testing `GblAvfProtocol.read_secretkeeper_public_key`
    fn test_read_secretkeeper_public_key<'a>(
        key_buffer: &'a mut [u8],
        call_status: ProtocolCallStatus<&'static [u8]>,
    ) -> Result<Option<&'a [u8]>> {
        let mut mock_efi = MockEfi::new();
        mock_efi.con_out.expect_write_str().return_const(Ok(()));
        let call_status_scoped = call_status;

        let mut avf = GblAvfProtocol::default();

        avf.expect_read_secretkeeper_public_key().return_once(
            move |buffer| match call_status_scoped {
                ProtocolCallStatus::Success(key_to_apply) => {
                    buffer[..key_to_apply.len()].copy_from_slice(key_to_apply);
                    Ok(key_to_apply.len())
                }
                ProtocolCallStatus::ProtocolCallError(err) => Err(err),
                _ => panic!("Unexpected ProtocolCallStatus"),
            },
        );
        mock_efi.boot_services.expect_find_first_and_open::<GblAvfProtocol>().return_once(
            move || match call_status {
                ProtocolCallStatus::ProtocolLookupError(err) => Err(err),
                _ => Ok(avf),
            },
        );

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);
        ops.avf_read_secretkeeper_public_key(key_buffer)
    }

    #[test]
    fn ops_avf_read_secretkeeper_public_key_returned() {
        const PUBLIC_KEY: &[u8] = b"secretkeeper_public_key";
        let mut key_buffer = [0u8; PUBLIC_KEY.len()];
        assert_eq!(
            test_read_secretkeeper_public_key(
                &mut key_buffer,
                ProtocolCallStatus::Success(PUBLIC_KEY)
            ),
            Ok(Some(PUBLIC_KEY)),
        );
    }

    #[test]
    fn ops_avf_read_secretkeeper_public_key_not_implemented() {
        assert_eq!(
            test_read_secretkeeper_public_key(
                &mut [],
                ProtocolCallStatus::ProtocolCallError(Error::Unsupported)
            ),
            Ok(None),
        );
    }

    #[test]
    fn ops_avf_read_secretkeeper_public_key_protocol_not_found() {
        assert_eq!(
            test_read_secretkeeper_public_key(
                &mut [],
                ProtocolCallStatus::ProtocolLookupError(Error::NotFound)
            ),
            Err(Error::NotFound),
        );
    }

    #[test]
    fn ops_avf_read_secretkeeper_public_key_buffer_too_small() {
        const EXPECTED_SIZE: usize = 64;
        assert_eq!(
            test_read_secretkeeper_public_key(
                &mut [],
                ProtocolCallStatus::ProtocolCallError(Error::BufferTooSmall(Some(EXPECTED_SIZE)))
            ),
            Err(Error::BufferTooSmall(Some(EXPECTED_SIZE))),
        );
    }

    #[test]
    fn test_get_var_all_not_found() {
        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblFastbootProtocol>()
            .return_once(|| Err(Error::NotFound));
        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);
        ops.fastboot_visit_all_variables(|_, _, _| {}).unwrap();
    }

    #[test]
    fn test_get_var_all_other_errors() {
        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblFastbootProtocol>()
            .return_once(|| Err(Error::InvalidInput));
        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);
        assert!(ops.fastboot_visit_all_variables(|_, _, _| {}).is_err());
    }

    /// Helper for testing `GblOsConfigurationProtocol.fixup_bootconfig`
    fn test_fixup_bootconfig<'a>(
        expected_base: &'static [u8],
        fixup_buffer: &'a mut [u8],
        fixup_to_apply: &'static [u8],
        protocol_lookup_error: Option<Error>,
        protocol_result_error: Option<Error>,
    ) -> Result<Option<&'a [u8]>> {
        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblOsConfigurationProtocol>()
            .return_once(move || {
                if let Some(error) = protocol_lookup_error {
                    return Err(error);
                }

                let mut os_configuration = GblOsConfigurationProtocol::default();

                os_configuration.expect_fixup_bootconfig().return_once(move |base, buffer| {
                    assert_eq!(base, expected_base);
                    buffer[..fixup_to_apply.len()].copy_from_slice(fixup_to_apply);

                    if let Some(protocol_result_error) = protocol_result_error {
                        return Err(protocol_result_error);
                    }

                    Ok(fixup_to_apply.len())
                });

                Ok(os_configuration)
            });

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        ops.fixup_bootconfig(expected_base, fixup_buffer)
    }

    #[test]
    fn test_fixup_bootconfig_success() {
        const BASE: &[u8] = b"key1=value1\nkey2=value2";
        const FIXUP: &[u8] = b"fixup1=value1\nfixup2=value2";

        let mut fixup_buffer = [0x0; FIXUP.len()];
        assert_eq!(
            test_fixup_bootconfig(
                BASE,
                &mut fixup_buffer,
                FIXUP,
                // Protocol is provided.
                None,
                // No protocol call error.
                None,
            ),
            // Expects fixup applied.
            Ok(Some(FIXUP)),
        );
    }

    #[test]
    fn test_fixup_bootconfig_protocol_error() {
        const BASE: &[u8] = b"key1=value1\nkey2=value2";
        const FIXUP: &[u8] = b"fixup1=value1\nfixup2=value2";

        let mut fixup_buffer = [0x0; FIXUP.len()];
        assert_eq!(
            test_fixup_bootconfig(
                BASE,
                &mut fixup_buffer,
                FIXUP,
                // Protocol is provided.
                None,
                // Protocol returns error.
                Some(Error::BufferTooSmall(Some(100))),
            ),
            // Expected to be catched.
            Err(Error::BufferTooSmall(Some(100))),
        );
    }

    #[test]
    fn test_fixup_bootconfig_not_implemented() {
        const BASE: &[u8] = b"key1=value1\nkey2=value2";
        const FIXUP: &[u8] = b"fixup1=value1\nfixup2=value2";

        let mut fixup_buffer = [0x0; FIXUP.len()];
        assert_eq!(
            test_fixup_bootconfig(
                BASE,
                &mut fixup_buffer,
                FIXUP,
                // Protocol is provided.
                None,
                // Implementation isn't provided.
                Some(Error::Unsupported),
            ),
            // Treated as no fixup is provided.
            Ok(None),
        );
    }

    #[test]
    fn test_fixup_bootconfig_protocol_not_found() {
        const BASE: &[u8] = b"key1=value1\nkey2=value2";
        const FIXUP: &[u8] = b"fixup1=value1\nfixup2=value2";

        let mut fixup_buffer = [0x0; FIXUP.len()];
        assert_eq!(
            test_fixup_bootconfig(
                BASE,
                &mut fixup_buffer,
                FIXUP,
                // Protocol not found.
                Some(Error::NotFound),
                // No protocol call error.
                None,
            ),
            // No fixup in case protocol not found.
            Ok(None),
        );
    }

    #[test]
    fn test_fixup_bootconfig_protocol_lookup_failed() {
        const BASE: &[u8] = b"key1=value1\nkey2=value2";
        const FIXUP: &[u8] = b"fixup1=value1\nfixup2=value2";

        let mut fixup_buffer = [0x0; FIXUP.len()];
        assert_eq!(
            test_fixup_bootconfig(
                BASE,
                &mut fixup_buffer,
                FIXUP,
                // Protocol lookup failed.
                Some(Error::AccessDenied),
                // No protocol call error.
                None,
            ),
            // Error catched.
            Err(Error::AccessDenied),
        );
    }

    #[test]
    fn test_select_device_tree_components_select_base_overlay_and_vmdtbo() {
        let base = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let overlay = include_bytes!("../../libfdt/test/data/overlay_by_path.dtbo").to_vec();
        let overlay2 = include_bytes!("../../libfdt/test/data/overlay_by_reference.dtbo").to_vec();
        let vmdtbo1 = include_bytes!("../../libfdt/test/data/overlay_2_by_path.dtbo").to_vec();
        let vmdtbo2 = include_bytes!("../../libfdt/test/data/overlay_2_by_reference.dtbo").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB

        let base_scoped = base.clone();
        let overlay_scoped = overlay.clone();
        let overlay2_scoped = overlay2.clone();
        let vmdtbo1_scoped = vmdtbo1.clone();
        let vmdtbo2_scoped = vmdtbo2.clone();
        let mut mock_efi = MockEfi::new();
        mock_efi.con_out.expect_write_str().return_const(Ok(()));
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblOsConfigurationProtocol>()
            .return_once(|| {
                let mut os_configuration = GblOsConfigurationProtocol::default();

                os_configuration.expect_select_device_trees().return_once(move |components| {
                    assert_eq!(components.len(), 5);

                    // SAFETY:
                    // `components[*].device_trees` are pointing to corresponding base device
                    // tree and overlays buffers.
                    let (
                        base_passed,
                        overlay_passed,
                        overlay2_passed,
                        vmdtbo1_passed,
                        vmdtbo2_passed,
                    ) = unsafe {
                        (
                            slice::from_raw_parts(
                                components[0].device_tree as *const u8,
                                base_scoped.len(),
                            ),
                            slice::from_raw_parts(
                                components[1].device_tree as *const u8,
                                overlay_scoped.len(),
                            ),
                            slice::from_raw_parts(
                                components[2].device_tree as *const u8,
                                overlay2_scoped.len(),
                            ),
                            slice::from_raw_parts(
                                components[3].device_tree as *const u8,
                                vmdtbo1_scoped.len(),
                            ),
                            slice::from_raw_parts(
                                components[4].device_tree as *const u8,
                                vmdtbo2_scoped.len(),
                            ),
                        )
                    };

                    assert_eq!(base_passed, &base_scoped);
                    assert_eq!(overlay_passed, &overlay_scoped[..]);
                    assert_eq!(overlay2_passed, &overlay2_scoped[..]);
                    assert_eq!(vmdtbo1_passed, &vmdtbo1_scoped[..]);
                    assert_eq!(vmdtbo2_passed, &vmdtbo2_scoped[..]);

                    // Select the base device and the second overlay. The first overlay is not
                    // being selected.
                    components[0].selected = true;
                    components[2].selected = true;
                    components[4].selected = true; // selected VMDTBO
                    Ok(())
                });

                Ok(os_configuration)
            });

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        let mut registry = DtComponentsRegistry::new();
        let mut current_buffer = &mut buffer[..];
        current_buffer = registry
            .append(
                &mut ops,
                DtComponentSource::VendorBoot,
                DtComponentType::BaseDt,
                &base,
                current_buffer,
            )
            .unwrap();
        current_buffer = registry
            .append(
                &mut ops,
                DtComponentSource::Dtbo,
                DtComponentType::Overlay,
                &overlay,
                current_buffer,
            )
            .unwrap();
        current_buffer = registry
            .append(
                &mut ops,
                DtComponentSource::Dtbo,
                DtComponentType::Overlay,
                &overlay2,
                current_buffer,
            )
            .unwrap();
        current_buffer = registry
            .append(
                &mut ops,
                DtComponentSource::Dtbo,
                DtComponentType::PvmDeviceAssignmentOverlay,
                &vmdtbo1,
                current_buffer,
            )
            .unwrap();
        registry
            .append(
                &mut ops,
                DtComponentSource::Dtbo,
                DtComponentType::PvmDeviceAssignmentOverlay,
                &vmdtbo2,
                current_buffer,
            )
            .unwrap();

        assert_eq!(ops.select_device_trees(&mut registry), Ok(()));
        assert_eq!(
            registry.into_selected(),
            Ok(SelectedDtComponents {
                base_dt: SelectedDtComponent {
                    source_metadata: DtComponentSourceMetadata {
                        source: DtComponentSource::VendorBoot,
                        source_index: 0,
                    },
                    dt: &base[..]
                },
                vmdtbo: Some(SelectedDtComponent {
                    source_metadata: DtComponentSourceMetadata {
                        source: DtComponentSource::Dtbo,
                        source_index: 0,
                    },
                    dt: &vmdtbo2[..]
                }),
                overlays: [SelectedDtComponent {
                    source_metadata: DtComponentSourceMetadata {
                        source: DtComponentSource::Dtbo,
                        source_index: 0,
                    },
                    dt: &overlay2[..]
                }]
                .into_iter()
                .collect(),
            })
        );
    }

    #[test]
    fn test_select_device_tree_protocol_error() {
        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblOsConfigurationProtocol>()
            .return_once(move || {
                let mut os_configuration = GblOsConfigurationProtocol::default();

                os_configuration
                    .expect_select_device_trees()
                    .return_once(move |_components| Err(Error::InvalidInput));

                Ok(os_configuration)
            });

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        let mut registry = DtComponentsRegistry::new();

        assert_eq!(ops.select_device_trees(&mut registry), Err(Error::InvalidInput));
    }

    #[test]
    fn test_select_device_tree_protocol_not_found() {
        let base = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB

        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblOsConfigurationProtocol>()
            .return_once(move || Err(Error::NotFound));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        // Appends some data to ensure autoselect is passed.
        let mut registry = DtComponentsRegistry::new();
        let current_buffer = &mut buffer[..];
        registry
            .append(
                &mut ops,
                DtComponentSource::VendorBoot,
                DtComponentType::BaseDt,
                &base,
                current_buffer,
            )
            .unwrap();

        assert_eq!(ops.select_device_trees(&mut registry), Ok(()));
    }

    /// Helper for testing `DtFixupProtocol.fixup`
    fn test_fixup_device_tree(
        base: &mut [u8],
        base_after_fixup: &'static [u8],
        protocol_lookup_error: Option<Error>,
        protocol_result: Result<()>,
    ) -> Result<()> {
        let mut mock_efi = MockEfi::new();
        mock_efi.boot_services.expect_find_first_and_open::<DtFixupProtocol>().return_once(
            move || {
                if let Some(error) = protocol_lookup_error {
                    return Err(error);
                }

                let mut dt_fixup = DtFixupProtocol::default();
                dt_fixup.expect_fixup().return_once(move |buffer| {
                    buffer.copy_from_slice(base_after_fixup);
                    protocol_result
                });

                Ok(dt_fixup)
            },
        );

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None, 0);

        let r = ops.fixup_device_tree(base);
        assert_eq!(base, base_after_fixup);
        r
    }

    #[test]
    fn test_fixup_device_tree_success() {
        const WITH_FIXUP: &[u8] = b"device tree after overlay applied";

        let mut device_tree_buffer = [0x0; WITH_FIXUP.len()];
        assert_eq!(
            test_fixup_device_tree(
                &mut device_tree_buffer,
                WITH_FIXUP,
                // No protocol lookup error.
                None,
                // No protocol call error.
                Ok(()),
            ),
            Ok(()),
        );
    }

    #[test]
    fn test_fixup_device_tree_protocol_error() {
        const WITH_FIXUP: &[u8] = b"device tree after overlay applied";

        let mut device_tree_buffer = [0x0; WITH_FIXUP.len()];
        assert_eq!(
            test_fixup_device_tree(
                &mut device_tree_buffer,
                WITH_FIXUP,
                // No protocol lookup error.
                None,
                // Protocol returns error.
                Err(Error::BufferTooSmall(Some(100))),
            ),
            // Expected to be catched.
            Err(Error::BufferTooSmall(Some(100))),
        );
    }

    #[test]
    fn test_fixup_device_tree_protocol_not_found() {
        assert_eq!(
            test_fixup_device_tree(
                &mut [],
                &[],
                // Protocol not found.
                Some(Error::NotFound),
                // No protocol call error.
                Ok(()),
            ),
            // Protocol is optional, so passed.
            Ok(()),
        );
    }

    #[test]
    fn test_fixup_device_tree_protocol_lookup_failed() {
        assert_eq!(
            test_fixup_device_tree(
                &mut [],
                &[],
                // Protocol lookup failed.
                Some(Error::AccessDenied),
                // No protocol call error.
                Ok(()),
            ),
            // Error catched.
            Err(Error::AccessDenied),
        );
    }

    #[test]
    #[cfg(feature = "fuchsia")]
    fn test_slot_count_fuchsia_abr_default() {
        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblBootControlProtocol>()
            .returning(|| Err(Error::Unsupported));
        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], Some(Os::Fuchsia), 0);

        assert_eq!(ops.get_slot_count(), Ok(2));
    }
}
