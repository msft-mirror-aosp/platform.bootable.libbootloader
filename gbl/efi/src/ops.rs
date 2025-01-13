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

use crate::{
    efi,
    efi_blocks::EfiGblDisk,
    utils::{get_efi_fdt, wait_key_stroke},
};
use alloc::{
    alloc::{alloc, handle_alloc_error, Layout},
    vec::Vec,
};
use arrayvec::ArrayVec;
use core::{
    cmp::min, ffi::CStr, fmt::Write, mem::MaybeUninit, num::NonZeroUsize, ops::DerefMut, ptr::null,
    slice::from_raw_parts_mut,
};
use efi::{
    efi_print, efi_println,
    protocol::{
        dt_fixup::DtFixupProtocol, gbl_efi_ab_slot::GblSlotProtocol, gbl_efi_avb::GblAvbProtocol,
        gbl_efi_fastboot::GblFastbootProtocol, gbl_efi_image_loading::GblImageLoadingProtocol,
        gbl_efi_os_configuration::GblOsConfigurationProtocol,
    },
    EfiEntry,
};
use efi_types::{
    GblEfiAvbKeyValidationStatus, GblEfiAvbVerificationResult, GblEfiBootReason,
    GblEfiDeviceTreeMetadata, GblEfiImageInfo, GblEfiVerifiedDeviceTree,
    GBL_EFI_BOOT_REASON_BOOTLOADER, GBL_EFI_BOOT_REASON_COLD, GBL_EFI_BOOT_REASON_FASTBOOTD,
    GBL_EFI_BOOT_REASON_RECOVERY, PARTITION_NAME_LEN_U16,
};
use fdt::Fdt;
use gbl_storage::{BlockIo, Disk, Gpt, SliceMaybeUninit};
use liberror::{Error, Result};
use libgbl::{
    constants::{ImageName, BOOTCMD_SIZE},
    device_tree::{
        DeviceTreeComponent, DeviceTreeComponentSource, DeviceTreeComponentsRegistry,
        MAXIMUM_DEVICE_TREE_COMPONENTS,
    },
    gbl_avb::state::{BootStateColor, KeyValidationStatus},
    ops::{
        AvbIoError, AvbIoResult, CertPermanentAttributes, ImageBuffer, RebootReason, Slot,
        SlotsMetadata, SHA256_DIGEST_SIZE,
    },
    partition::GblDisk,
    slots::{BootToken, Cursor},
    GblOps, Os, Result as GblResult,
};
use safemath::SafeNum;
use zbi::ZbiContainer;
use zerocopy::IntoBytes;

fn to_avb_validation_status_or_panic(status: GblEfiAvbKeyValidationStatus) -> KeyValidationStatus {
    match status {
        efi_types::GBL_EFI_AVB_KEY_VALIDATION_STATUS_VALID => KeyValidationStatus::Valid,
        efi_types::GBL_EFI_AVB_KEY_VALIDATION_STATUS_VALID_CUSTOM_KEY => {
            KeyValidationStatus::ValidCustomKey
        }
        efi_types::GBL_EFI_AVB_KEY_VALIDATION_STATUS_INVALID => KeyValidationStatus::Invalid,
        _ => panic!("Unrecognized avb key validation status: {}", status),
    }
}

fn avb_color_to_efi_color(color: BootStateColor) -> u32 {
    match color {
        BootStateColor::Green => efi_types::GBL_EFI_AVB_BOOT_STATE_COLOR_GREEN,
        BootStateColor::Yellow => efi_types::GBL_EFI_AVB_BOOT_STATE_COLOR_YELLOW,
        BootStateColor::Orange => efi_types::GBL_EFI_AVB_BOOT_STATE_COLOR_ORANGE,
        BootStateColor::RedEio => efi_types::GBL_EFI_AVB_BOOT_STATE_COLOR_RED_EIO,
        BootStateColor::Red => efi_types::GBL_EFI_AVB_BOOT_STATE_COLOR_RED,
    }
}

fn dt_component_to_efi_dt(component: &DeviceTreeComponent) -> GblEfiVerifiedDeviceTree {
    let metadata = match component.source {
        DeviceTreeComponentSource::Dtb(m) | DeviceTreeComponentSource::Dtbo(m) => m,
        _ => Default::default(),
    };

    GblEfiVerifiedDeviceTree {
        metadata: GblEfiDeviceTreeMetadata {
            source: match component.source {
                DeviceTreeComponentSource::Boot => efi_types::GBL_EFI_DEVICE_TREE_SOURCE_BOOT,
                DeviceTreeComponentSource::VendorBoot => {
                    efi_types::GBL_EFI_DEVICE_TREE_SOURCE_VENDOR_BOOT
                }
                DeviceTreeComponentSource::Dtb(_) => efi_types::GBL_EFI_DEVICE_TREE_SOURCE_DTB,
                DeviceTreeComponentSource::Dtbo(_) => efi_types::GBL_EFI_DEVICE_TREE_SOURCE_DTBO,
            },
            id: metadata.id,
            rev: metadata.rev,
            custom: metadata.custom,
            reserved: Default::default(),
        },
        device_tree: component.dt.as_ptr() as _,
        selected: component.selected,
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
        _ => AvbIoError::NotImplemented,
    }
}

pub struct Ops<'a, 'b> {
    pub efi_entry: &'a EfiEntry,
    pub disks: &'b [EfiGblDisk<'a>],
    pub zbi_bootloader_files_buffer: Vec<u8>,
    pub os: Option<Os>,
}

impl<'a, 'b> Ops<'a, 'b> {
    /// Creates a new instance of [Ops]
    pub fn new(efi_entry: &'a EfiEntry, disks: &'b [EfiGblDisk<'a>], os: Option<Os>) -> Self {
        Self { efi_entry, disks, zbi_bootloader_files_buffer: Default::default(), os }
    }

    /// Gets the property of an FDT node from EFI FDT.
    ///
    /// Returns `None` if fail to get the node
    fn get_efi_fdt_prop(&self, path: &str, prop: &CStr) -> Option<&'a [u8]> {
        let (_, fdt_bytes) = get_efi_fdt(&self.efi_entry)?;
        let fdt = Fdt::new(fdt_bytes).ok()?;
        fdt.get_property(path, prop).ok()
    }

    /// Get buffer for partition loading and verification.
    /// Uses GBL EFI ImageLoading protocol.
    ///
    /// # Arguments
    /// * `image_name` - image name to differentiate the buffer properties. Processing is limited
    /// to first [PARTITION_NAME_LEN_U16] symbols, and the remaining will be ignored.
    /// * `size` - requested buffer size
    ///
    /// # Return
    /// * Ok(ImageBuffer) - Return buffer for partition loading and verification.
    /// * Err(_) - on error
    fn get_buffer_image_loading(
        &mut self,
        image_name: &str,
        size: NonZeroUsize,
    ) -> GblResult<ImageBuffer<'static>> {
        let mut image_type = [0u16; PARTITION_NAME_LEN_U16];
        image_type.iter_mut().zip(image_name.encode_utf16()).for_each(|(dst, src)| {
            *dst = src;
        });
        let image_info = GblEfiImageInfo { ImageType: image_type, SizeBytes: size.get() };
        let efi_image_buffer = self
            .efi_entry
            .system_table()
            .boot_services()
            .find_first_and_open::<GblImageLoadingProtocol>()?
            .get_buffer(&image_info)?;

        // EfiImageBuffer -> ImageBuffer
        // Make sure not to drop efi_image_buffer since we transferred ownership to ImageBuffer
        let buffer = efi_image_buffer.take();
        Ok(ImageBuffer::new(buffer))
    }

    /// Get buffer for partition loading and verification.
    /// Uses provided allocator.
    ///
    /// # Arguments
    /// * `image_name` - image name to differentiate the buffer properties
    /// * `size` - requested buffer size
    ///
    /// # Return
    /// * Ok(ImageBuffer) - Return buffer for partition loading and verification.
    /// * Err(_) - on error
    // SAFETY:
    // Allocated buffer is leaked intentionally. ImageBuffer is assumed to reference static memory.
    // ImageBuffer is not expected to be released, and is allocated to hold data necessary for next
    // boot stage (kernel boot). All allocated buffers are expected to be used by kernel.
    fn allocate_image_buffer(image_name: &str, size: NonZeroUsize) -> Result<ImageBuffer<'static>> {
        let size = match image_name {
            "ramdisk" => (SafeNum::from(size.get()) + BOOTCMD_SIZE).try_into()?,
            _ => size.get(),
        };
        // Check for `from_raw_parts_mut()` safety requirements.
        assert!(size < isize::MAX.try_into().unwrap());
        let align = ImageName::try_from(image_name).map(|i| i.alignment()).unwrap_or(1);

        let layout = Layout::from_size_align(size, align).or(Err(Error::InvalidAlignment))?;
        // SAFETY:
        // `layout.size()` is checked to be not zero.
        let ptr = unsafe { alloc(layout) } as *mut MaybeUninit<u8>;
        if ptr.is_null() {
            handle_alloc_error(layout);
        }

        // SAFETY:
        // `ptr` is checked to be not Null.
        // `ptr` is a valid pointer to start of a single memory region of `size`-bytes because it
        // was just returned by alloc. Buffer alignment requirement for u8 is 1-byte which is
        // always the case.
        // `alloc()` makes sure there is no other allocation of the same memory region until
        // current one is released.
        // `size` is a valid size of the memory region since `alloc()` succeeded.
        //
        // Total size of buffer is not greater than `isize::MAX` since it is checked at the
        // beginning of the function.
        //
        // `ptr + size` doesn't wrap since it is returned from alloc and it didn't fail.
        let buf = unsafe { from_raw_parts_mut(ptr, size) };

        Ok(ImageBuffer::new(buf))
    }
}

impl Write for Ops<'_, '_> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        efi_print!(self.efi_entry, "{}", s);
        Ok(())
    }
}

impl<'a, 'b, 'd> GblOps<'b, 'd> for Ops<'a, 'b> {
    fn console_out(&mut self) -> Option<&mut dyn Write> {
        Some(self)
    }

    /// UEFI console uses \r\n newline.
    fn console_newline(&self) -> &'static str {
        "\r\n"
    }

    fn should_stop_in_fastboot(&mut self) -> Result<bool> {
        // TODO(b/349829690): also query GblSlotProtocol.get_boot_reason() for board-specific
        // fastboot triggers.

        // TODO(b/366520234): Switch to use GblSlotProtocol.should_stop_in_fastboot once available.
        match self.get_efi_fdt_prop("gbl", c"stop-in-fastboot") {
            Some(v) => return Ok(*v.get(0).unwrap_or(&0) == 1),
            _ => {}
        }

        efi_println!(self.efi_entry, "Press Backspace to enter fastboot");
        let found = wait_key_stroke(
            self.efi_entry,
            |key| key.unicode_char == 0x08 || (key.unicode_char == 0x0 && key.scan_code == 0x08),
            2000,
        );
        if matches!(found, Ok(true)) {
            efi_println!(self.efi_entry, "Backspace pressed, entering fastboot");
        }
        // TODO(b/358377120): pass the UEFI error when liberror::Error support lands.
        found.or(Err(Error::Other(Some("wait for key stroke error"))))
    }

    /// Reboots the system into the last set boot mode.
    fn reboot(&mut self) {
        self.efi_entry.system_table().runtime_services().cold_reset();
    }

    fn disks(
        &self,
    ) -> &'b [GblDisk<
        Disk<impl BlockIo + 'b, impl DerefMut<Target = [u8]> + 'b>,
        Gpt<impl DerefMut<Target = [u8]> + 'b>,
    >] {
        self.disks
    }

    fn expected_os(&mut self) -> Result<Option<Os>> {
        Ok(self.os)
    }

    fn zircon_add_device_zbi_items(
        &mut self,
        container: &mut ZbiContainer<&mut [u8]>,
    ) -> Result<()> {
        // TODO(b/353272981): Switch to use OS configuration protocol once it is implemented on
        // existing platforms such as VIM3.
        Ok(match self.get_efi_fdt_prop("zircon", c"zbi-blob") {
            Some(blob) => container.extend_unaligned(blob).map_err(|_| "Failed to append ZBI")?,
            _ => efi_println!(self.efi_entry, "No device ZBI items.\r\n"),
        })
    }

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

    fn avb_read_is_device_unlocked(&mut self) -> AvbIoResult<bool> {
        match self.efi_entry.system_table().boot_services().find_first_and_open::<GblAvbProtocol>()
        {
            Ok(protocol) => protocol.read_is_device_unlocked().map_err(efi_error_to_avb_error),
            Err(_) => Err(AvbIoError::NotImplemented),
        }
    }

    fn avb_read_rollback_index(&mut self, rollback_index_location: usize) -> AvbIoResult<u64> {
        match self.efi_entry.system_table().boot_services().find_first_and_open::<GblAvbProtocol>()
        {
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
        match self.efi_entry.system_table().boot_services().find_first_and_open::<GblAvbProtocol>()
        {
            Ok(protocol) => protocol
                .write_rollback_index(rollback_index_location, index)
                .map_err(efi_error_to_avb_error),
            Err(_) => Err(AvbIoError::NotImplemented),
        }
    }

    fn avb_read_persistent_value(&mut self, name: &CStr, value: &mut [u8]) -> AvbIoResult<usize> {
        match self.efi_entry.system_table().boot_services().find_first_and_open::<GblAvbProtocol>()
        {
            Ok(protocol) => {
                protocol.read_persistent_value(name, value).map_err(efi_error_to_avb_error)
            }
            Err(_) => Err(AvbIoError::NotImplemented),
        }
    }

    fn avb_write_persistent_value(&mut self, name: &CStr, value: &[u8]) -> AvbIoResult<()> {
        match self.efi_entry.system_table().boot_services().find_first_and_open::<GblAvbProtocol>()
        {
            Ok(protocol) => {
                protocol.write_persistent_value(name, Some(value)).map_err(efi_error_to_avb_error)
            }
            Err(_) => Err(AvbIoError::NotImplemented),
        }
    }

    fn avb_erase_persistent_value(&mut self, name: &CStr) -> AvbIoResult<()> {
        match self.efi_entry.system_table().boot_services().find_first_and_open::<GblAvbProtocol>()
        {
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
        match self.efi_entry.system_table().boot_services().find_first_and_open::<GblAvbProtocol>()
        {
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
        let perm_attr = self
            .get_efi_fdt_prop("gbl", c"avb-cert-permanent-attributes")
            .ok_or(AvbIoError::NotImplemented)?;
        attributes.as_bytes_mut().clone_from_slice(perm_attr);
        Ok(())
    }

    fn avb_cert_read_permanent_attributes_hash(&mut self) -> AvbIoResult<[u8; SHA256_DIGEST_SIZE]> {
        // TODO(b/337846185): Switch to use GBL Verified Boot EFI protocol when available.
        let hash = self
            .get_efi_fdt_prop("gbl", c"avb-cert-permanent-attributes-hash")
            .ok_or(AvbIoError::NotImplemented)?;
        Ok(hash.try_into().map_err(|_| AvbIoError::Io)?)
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
        match self.efi_entry.system_table().boot_services().find_first_and_open::<GblAvbProtocol>()
        {
            Ok(protocol) => protocol
                .handle_verification_result(&GblEfiAvbVerificationResult {
                    color: avb_color_to_efi_color(color),
                    digest: digest.map_or(null(), |p| p.as_ptr() as _),
                    boot_version: boot_os_version.map_or(null(), |p| p.as_ptr()),
                    boot_security_patch: boot_security_patch.map_or(null(), |p| p.as_ptr()),
                    system_version: system_os_version.map_or(null(), |p| p.as_ptr()),
                    system_security_patch: system_security_patch.map_or(null(), |p| p.as_ptr()),
                    vendor_version: vendor_os_version.map_or(null(), |p| p.as_ptr()),
                    vendor_security_patch: vendor_security_patch.map_or(null(), |p| p.as_ptr()),
                })
                .map_err(efi_error_to_avb_error),
            _ => Ok(()),
        }
    }

    fn get_image_buffer(
        &mut self,
        image_name: &str,
        size: NonZeroUsize,
    ) -> GblResult<ImageBuffer<'d>> {
        self.get_buffer_image_loading(image_name, size)
            .or(Self::allocate_image_buffer(image_name, size)
                .map_err(|e| libgbl::IntegrationError::UnificationError(e)))
    }

    fn get_custom_device_tree(&mut self) -> Option<&'a [u8]> {
        // On Cuttlefish, the device tree comes from the UEFI config tables.
        // TODO(b/353272981): once we've settled on the device tree UEFI protocol, use that
        // instead to provide a Cuttlefish-specific backend.
        Some(get_efi_fdt(&self.efi_entry)?.1)
    }

    fn fixup_os_commandline<'c>(
        &mut self,
        commandline: &CStr,
        fixup_buffer: &'c mut [u8],
    ) -> Result<Option<&'c str>> {
        match self
            .efi_entry
            .system_table()
            .boot_services()
            .find_first_and_open::<GblOsConfigurationProtocol>()
        {
            Ok(protocol) => {
                protocol.fixup_kernel_commandline(commandline, fixup_buffer)?;
                Ok(Some(CStr::from_bytes_until_nul(&fixup_buffer[..])?.to_str()?))
            }
            // Protocol is optional.
            Err(Error::NotFound) => Ok(None),
            Err(e) => Err(e),
        }
    }

    fn fixup_bootconfig<'c>(
        &mut self,
        bootconfig: &[u8],
        fixup_buffer: &'c mut [u8],
    ) -> Result<Option<&'c [u8]>> {
        match self
            .efi_entry
            .system_table()
            .boot_services()
            .find_first_and_open::<GblOsConfigurationProtocol>()
        {
            Ok(protocol) => {
                let fixup_size = protocol.fixup_bootconfig(bootconfig, fixup_buffer)?;
                Ok(Some(&fixup_buffer[..fixup_size]))
            }
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
        components_registry: &mut DeviceTreeComponentsRegistry,
    ) -> Result<()> {
        match self
            .efi_entry
            .system_table()
            .boot_services()
            .find_first_and_open::<GblOsConfigurationProtocol>()
        {
            Ok(protocol) => {
                // Protocol detected, convert to UEFI types.
                let mut uefi_components: ArrayVec<_, MAXIMUM_DEVICE_TREE_COMPONENTS> =
                    components_registry
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
                                Source: {}",
                                index,
                                component.source
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

    fn fastboot_variable<'arg>(
        &mut self,
        name: &CStr,
        args: impl Iterator<Item = &'arg CStr> + Clone,
        out: &mut [u8],
    ) -> Result<usize> {
        self.efi_entry
            .system_table()
            .boot_services()
            .find_first_and_open::<GblFastbootProtocol>()?
            .get_var(name, args, out)
    }

    fn fastboot_visit_all_variables(&mut self, cb: impl FnMut(&[&CStr], &CStr)) -> Result<()> {
        match self
            .efi_entry
            .system_table()
            .boot_services()
            .find_first_and_open::<GblFastbootProtocol>()
        {
            Ok(v) => v.get_var_all(cb),
            Err(Error::NotFound) => Ok(()),
            Err(e) => Err(e),
        }
    }

    fn slots_metadata(&mut self) -> Result<SlotsMetadata> {
        Ok(SlotsMetadata {
            slot_count: self
                .efi_entry
                .system_table()
                .boot_services()
                .find_first_and_open::<GblSlotProtocol>()?
                .load_boot_data()?
                .slot_count
                .try_into()
                .unwrap(),
        })
    }

    fn get_current_slot(&mut self) -> Result<Slot> {
        // TODO(b/363075013): Refactors the opening of slot protocol into a common helper once
        // `MockBootServices::find_first_and_open` is updated to return Protocol<'_, T>.
        self.efi_entry
            .system_table()
            .boot_services()
            .find_first_and_open::<GblSlotProtocol>()?
            .get_current_slot()?
            .try_into()
    }

    fn get_next_slot(&mut self, mark_boot_attempt: bool) -> Result<Slot> {
        self.efi_entry
            .system_table()
            .boot_services()
            .find_first_and_open::<GblSlotProtocol>()?
            .get_next_slot(mark_boot_attempt)?
            .try_into()
    }

    fn set_active_slot(&mut self, slot: u8) -> Result<()> {
        self.efi_entry
            .system_table()
            .boot_services()
            .find_first_and_open::<GblSlotProtocol>()?
            .set_active_slot(slot)
    }

    fn set_reboot_reason(&mut self, reason: RebootReason) -> Result<()> {
        self.efi_entry
            .system_table()
            .boot_services()
            .find_first_and_open::<GblSlotProtocol>()?
            .set_boot_reason(gbl_to_efi_boot_reason(reason), b"")
    }

    fn get_reboot_reason(&mut self) -> Result<RebootReason> {
        let mut subreason = [0u8; 128];
        self.efi_entry
            .system_table()
            .boot_services()
            .find_first_and_open::<GblSlotProtocol>()?
            .get_boot_reason(&mut subreason[..])
            .map(|(v, _)| efi_to_gbl_boot_reason(v))
    }
}

/// Converts a [GblEfiBootReason] to [RebootReason].
fn efi_to_gbl_boot_reason(reason: GblEfiBootReason) -> RebootReason {
    match reason {
        GBL_EFI_BOOT_REASON_RECOVERY => RebootReason::Recovery,
        GBL_EFI_BOOT_REASON_BOOTLOADER => RebootReason::Bootloader,
        GBL_EFI_BOOT_REASON_FASTBOOTD => RebootReason::FastbootD,
        _ => RebootReason::Normal,
    }
}

/// Converts a [RebootReason] to [GblEfiBootReason].
fn gbl_to_efi_boot_reason(reason: RebootReason) -> GblEfiBootReason {
    match reason {
        RebootReason::Recovery => GBL_EFI_BOOT_REASON_RECOVERY,
        RebootReason::Bootloader => GBL_EFI_BOOT_REASON_BOOTLOADER,
        RebootReason::FastbootD => GBL_EFI_BOOT_REASON_FASTBOOTD,
        RebootReason::Normal => GBL_EFI_BOOT_REASON_COLD,
    }
}

/// Inherits everything from `ops` but override a few such as read boot_a from
/// bootimg_buffer, avb_write_rollback_index(), slot operation etc
pub struct RambootOps<'b, T> {
    pub ops: &'b mut T,
    pub bootimg_buffer: &'b mut [u8],
}

impl<'a, 'd, T: GblOps<'a, 'd>> GblOps<'a, 'd> for RambootOps<'_, T> {
    fn console_out(&mut self) -> Option<&mut dyn Write> {
        self.ops.console_out()
    }

    fn should_stop_in_fastboot(&mut self) -> Result<bool> {
        self.ops.should_stop_in_fastboot()
    }

    fn reboot(&mut self) {
        self.ops.reboot()
    }

    fn disks(
        &self,
    ) -> &'a [GblDisk<
        Disk<impl BlockIo + 'a, impl DerefMut<Target = [u8]> + 'a>,
        Gpt<impl DerefMut<Target = [u8]> + 'a>,
    >] {
        self.ops.disks()
    }

    fn expected_os(&mut self) -> Result<Option<Os>> {
        self.ops.expected_os()
    }

    fn zircon_add_device_zbi_items(
        &mut self,
        container: &mut ZbiContainer<&mut [u8]>,
    ) -> Result<()> {
        self.ops.zircon_add_device_zbi_items(container)
    }

    fn get_zbi_bootloader_files_buffer(&mut self) -> Option<&mut [u8]> {
        self.ops.get_zbi_bootloader_files_buffer()
    }

    fn load_slot_interface<'c>(
        &'c mut self,
        _fnmut: &'c mut dyn FnMut(&mut [u8]) -> Result<()>,
        _boot_token: BootToken,
    ) -> GblResult<Cursor<'c>> {
        self.ops.load_slot_interface(_fnmut, _boot_token)
    }

    fn avb_read_is_device_unlocked(&mut self) -> AvbIoResult<bool> {
        self.ops.avb_read_is_device_unlocked()
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

    fn get_image_buffer(
        &mut self,
        image_name: &str,
        size: NonZeroUsize,
    ) -> GblResult<ImageBuffer<'d>> {
        self.ops.get_image_buffer(image_name, size)
    }

    fn get_custom_device_tree(&mut self) -> Option<&'a [u8]> {
        self.ops.get_custom_device_tree()
    }

    fn fixup_os_commandline<'c>(
        &mut self,
        commandline: &CStr,
        fixup_buffer: &'c mut [u8],
    ) -> Result<Option<&'c str>> {
        self.ops.fixup_os_commandline(commandline, fixup_buffer)
    }

    fn fixup_bootconfig<'c>(
        &mut self,
        bootconfig: &[u8],
        fixup_buffer: &'c mut [u8],
    ) -> Result<Option<&'c [u8]>> {
        self.ops.fixup_bootconfig(bootconfig, fixup_buffer)
    }

    fn fixup_device_tree(&mut self, device_tree: &mut [u8]) -> Result<()> {
        self.ops.fixup_device_tree(device_tree)
    }

    fn select_device_trees(
        &mut self,
        components_registry: &mut DeviceTreeComponentsRegistry,
    ) -> Result<()> {
        self.ops.select_device_trees(components_registry)
    }

    fn read_from_partition_sync(
        &mut self,
        part: &str,
        off: u64,
        out: &mut (impl SliceMaybeUninit + ?Sized),
    ) -> Result<()> {
        if part == "boot_a" {
            let len = min(self.bootimg_buffer.len() - off as usize, out.len());
            out.clone_from_slice(&self.bootimg_buffer[off as usize..off as usize + len]);
            Ok(())
        } else {
            self.ops.read_from_partition_sync(part, off, out)
        }
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
        self.ops.avb_handle_verification_result(
            color,
            digest,
            boot_os_version,
            boot_security_patch,
            system_os_version,
            system_security_patch,
            vendor_os_version,
            vendor_security_patch,
        )
    }

    fn avb_validate_vbmeta_public_key(
        &self,
        public_key: &[u8],
        public_key_metadata: Option<&[u8]>,
    ) -> AvbIoResult<KeyValidationStatus> {
        self.ops.avb_validate_vbmeta_public_key(public_key, public_key_metadata)
    }

    fn slots_metadata(&mut self) -> Result<SlotsMetadata> {
        // Ramboot is not suppose to call this interface.
        unreachable!()
    }

    fn get_current_slot(&mut self) -> Result<Slot> {
        // Ramboot is slotless
        Err(Error::Unsupported)
    }

    fn get_next_slot(&mut self, _: bool) -> Result<Slot> {
        // Ramboot is not suppose to call this interface.
        unreachable!()
    }

    fn set_active_slot(&mut self, _: u8) -> Result<()> {
        // Ramboot is not suppose to call this interface.
        unreachable!()
    }

    fn set_reboot_reason(&mut self, _: RebootReason) -> Result<()> {
        // Ramboot is not suppose to call this interface.
        unreachable!()
    }

    fn get_reboot_reason(&mut self) -> Result<RebootReason> {
        // Assumes that ramboot use normal boot mode. But we might consider supporting recovery
        // if there is a usecase.
        Ok(RebootReason::Normal)
    }

    fn fastboot_variable<'arg>(
        &mut self,
        _: &CStr,
        _: impl Iterator<Item = &'arg CStr> + Clone,
        _: &mut [u8],
    ) -> Result<usize> {
        // Ramboot should not need this.
        unreachable!();
    }

    fn fastboot_visit_all_variables(&mut self, _: impl FnMut(&[&CStr], &CStr)) -> Result<()> {
        // Ramboot should not need this.
        unreachable!();
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use efi_mocks::{
        protocol::{gbl_efi_ab_slot::GblSlotProtocol, gbl_efi_avb::GblAvbProtocol},
        MockEfi,
    };
    use efi_types::GBL_EFI_BOOT_REASON;
    use mockall::predicate::eq;
    use std::slice;

    #[test]
    fn ops_write_trait() {
        let mut mock_efi = MockEfi::new();

        mock_efi.con_out.expect_write_str().with(eq("foo bar")).return_const(Ok(()));
        let installed = mock_efi.install();

        let mut ops = Ops::new(installed.entry(), &[], None);

        assert!(write!(&mut ops, "{} {}", "foo", "bar").is_ok());
    }

    #[test]
    fn ops_avb_validate_vbmeta_public_key_returns_valid() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.validate_vbmeta_public_key_result =
            Some(Ok(efi_types::GBL_EFI_AVB_KEY_VALIDATION_STATUS_VALID));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let ops = Ops::new(installed.entry(), &[], None);

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
        let ops = Ops::new(installed.entry(), &[], None);

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
        let ops = Ops::new(installed.entry(), &[], None);

        assert_eq!(ops.avb_validate_vbmeta_public_key(&[], None), Ok(KeyValidationStatus::Invalid));
    }

    #[test]
    fn ops_avb_validate_vbmeta_public_key_failed_error_mapped() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.validate_vbmeta_public_key_result = Some(Err(Error::OutOfResources));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let ops = Ops::new(installed.entry(), &[], None);

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
        let ops = Ops::new(installed.entry(), &[], None);

        assert_eq!(ops.avb_validate_vbmeta_public_key(&[], None), Err(AvbIoError::NotImplemented));
    }

    #[test]
    fn ops_avb_read_is_device_unlocked_returns_true() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.read_is_device_unlocked_result = Some(Ok(true));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None);

        assert_eq!(ops.avb_read_is_device_unlocked(), Ok(true));
    }

    #[test]
    fn ops_avb_read_is_device_unlocked_returns_false() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.read_is_device_unlocked_result = Some(Ok(false));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None);

        assert_eq!(ops.avb_read_is_device_unlocked(), Ok(false));
    }

    #[test]
    fn ops_avb_read_is_device_unlocked_protocol_not_found() {
        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblAvbProtocol>()
            .return_const(Err(Error::NotFound));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None);

        assert_eq!(ops.avb_read_is_device_unlocked(), Err(AvbIoError::NotImplemented));
    }

    #[test]
    fn ops_avb_read_rollback_index_success() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.read_rollback_index_result = Some(Ok(12345));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None);

        assert_eq!(ops.avb_read_rollback_index(0), Ok(12345));
    }

    #[test]
    fn ops_avb_read_rollback_index_error() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.read_rollback_index_result = Some(Err(Error::OutOfResources));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None);

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
        let mut ops = Ops::new(installed.entry(), &[], None);

        assert_eq!(ops.avb_read_rollback_index(0), Err(AvbIoError::NotImplemented));
    }

    #[test]
    fn ops_avb_write_rollback_index_success() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.write_rollback_index_result = Some(Ok(()));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None);

        assert!(ops.avb_write_rollback_index(0, 12345).is_ok());
    }

    #[test]
    fn ops_avb_write_rollback_index_error() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.write_rollback_index_result = Some(Err(Error::InvalidInput));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None);

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
        let mut ops = Ops::new(installed.entry(), &[], None);

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
        let mut ops = Ops::new(installed.entry(), &[], None);

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
        let mut ops = Ops::new(installed.entry(), &[], None);

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
        let mut ops = Ops::new(installed.entry(), &[], None);

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
        let mut ops = Ops::new(installed.entry(), &[], None);

        assert_eq!(ops.avb_write_persistent_value(c"test", b""), Ok(()));
    }

    #[test]
    fn ops_avb_write_persistent_value_error() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.write_persistent_value_result = Some(Err(Error::InvalidInput));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None);

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
        let mut ops = Ops::new(installed.entry(), &[], None);

        assert_eq!(ops.avb_write_persistent_value(c"test", b""), Err(AvbIoError::NotImplemented));
    }

    #[test]
    fn ops_avb_erase_persistent_value_success() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.write_persistent_value_result = Some(Ok(()));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None);

        assert_eq!(ops.avb_erase_persistent_value(c"test"), Ok(()));
    }

    #[test]
    fn ops_avb_erase_persistent_value_error() {
        let mut mock_efi = MockEfi::new();
        let mut avb = GblAvbProtocol::default();
        avb.write_persistent_value_result = Some(Err(Error::DeviceError));
        mock_efi.boot_services.expect_find_first_and_open::<GblAvbProtocol>().return_const(Ok(avb));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None);

        assert_eq!(ops.avb_erase_persistent_value(c"test"), Err(AvbIoError::Io));
    }

    #[test]
    fn ops_avb_erase_persistent_value_protocol_not_found() {
        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblAvbProtocol>()
            .return_const(Err(Error::NotFound));

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None);

        assert_eq!(ops.avb_erase_persistent_value(c"test"), Err(AvbIoError::NotImplemented));
    }

    /// Helper for testing `set_boot_reason`
    fn test_set_reboot_reason(input: RebootReason, expect: GBL_EFI_BOOT_REASON) {
        let mut mock_efi = MockEfi::new();
        mock_efi.boot_services.expect_find_first_and_open::<GblSlotProtocol>().return_once(
            move || {
                let mut slot = GblSlotProtocol::default();
                slot.expect_set_boot_reason().return_once(move |reason, _| {
                    assert_eq!(reason, expect);
                    Ok(())
                });
                Ok(slot)
            },
        );
        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None);
        assert_eq!(ops.set_reboot_reason(input), Ok(()));
    }

    #[test]
    fn test_set_reboot_reason_normal() {
        test_set_reboot_reason(RebootReason::Normal, GBL_EFI_BOOT_REASON_COLD);
    }

    #[test]
    fn test_set_reboot_reason_recovery() {
        test_set_reboot_reason(RebootReason::Recovery, GBL_EFI_BOOT_REASON_RECOVERY);
    }

    #[test]
    fn test_set_reboot_reason_bootloader() {
        test_set_reboot_reason(RebootReason::Bootloader, GBL_EFI_BOOT_REASON_BOOTLOADER);
    }

    #[test]
    fn test_set_reboot_reason_fastbootd() {
        test_set_reboot_reason(RebootReason::FastbootD, GBL_EFI_BOOT_REASON_FASTBOOTD);
    }

    /// Helper for testing `get_boot_reason`
    fn test_get_reboot_reason(input: GBL_EFI_BOOT_REASON, expect: RebootReason) {
        let mut mock_efi = MockEfi::new();
        mock_efi.boot_services.expect_find_first_and_open::<GblSlotProtocol>().return_once(
            move || {
                let mut slot = GblSlotProtocol::default();
                slot.expect_get_boot_reason().return_once(move |_| Ok((input, 0)));
                Ok(slot)
            },
        );
        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None);
        assert_eq!(ops.get_reboot_reason().unwrap(), expect)
    }

    #[test]
    fn test_get_reboot_reason_normal() {
        test_get_reboot_reason(GBL_EFI_BOOT_REASON_COLD, RebootReason::Normal);
    }

    #[test]
    fn test_get_reboot_reason_recovery() {
        test_get_reboot_reason(GBL_EFI_BOOT_REASON_RECOVERY, RebootReason::Recovery);
    }

    #[test]
    fn test_get_reboot_reason_bootloader() {
        test_get_reboot_reason(GBL_EFI_BOOT_REASON_BOOTLOADER, RebootReason::Bootloader);
    }

    #[test]
    fn test_get_reboot_reason_fastbootd() {
        test_get_reboot_reason(GBL_EFI_BOOT_REASON_FASTBOOTD, RebootReason::FastbootD);
    }

    #[test]
    fn test_get_var_all_not_found() {
        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblFastbootProtocol>()
            .return_once(|| Err(Error::NotFound));
        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None);
        ops.fastboot_visit_all_variables(|_, _| {}).unwrap();
    }

    #[test]
    fn test_get_var_all_other_errors() {
        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblFastbootProtocol>()
            .return_once(|| Err(Error::InvalidInput));
        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None);
        assert!(ops.fastboot_visit_all_variables(|_, _| {}).is_err());
    }

    /// Helper for testing `GblOsConfigurationProtocol.fixup_os_commandline`
    fn test_fixup_os_commandline<'a>(
        expected_base: &'static CStr,
        fixup_buffer: &'a mut [u8],
        fixup_to_apply: &'static [u8],
        protocol_lookup_error: Option<Error>,
        protocol_result: Result<()>,
    ) -> Result<Option<&'a str>> {
        let mut mock_efi = MockEfi::new();
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblOsConfigurationProtocol>()
            .return_once(move || {
                if let Some(error) = protocol_lookup_error {
                    return Err(error);
                }

                let mut os_configuration = GblOsConfigurationProtocol::default();

                os_configuration.expect_fixup_kernel_commandline().return_once(
                    move |base, buffer| {
                        assert_eq!(base, expected_base);
                        buffer[..fixup_to_apply.len()].copy_from_slice(fixup_to_apply);
                        protocol_result
                    },
                );

                Ok(os_configuration)
            });

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None);

        ops.fixup_os_commandline(expected_base, fixup_buffer)
    }

    #[test]
    fn test_fixup_os_commandline_success() {
        const BASE: &CStr = c"key1=value1 key2=value2";
        const FIXUP: &CStr = c"fixup1=value1 fixup2=value2";

        let mut fixup_buffer = [0x0; FIXUP.to_bytes_with_nul().len()];
        assert_eq!(
            test_fixup_os_commandline(
                BASE,
                &mut fixup_buffer,
                FIXUP.to_bytes_with_nul(),
                // No protocol lookup error.
                None,
                // No protocol call error.
                Ok(()),
            ),
            // Expects fixup applied.
            Ok(Some(FIXUP.to_str().unwrap()))
        );
    }

    #[test]
    fn test_fixup_os_commandline_success_empty_result() {
        const BASE: &CStr = c"key1=value1 key2=value2";

        let mut fixup_buffer = [0x0; 1];
        assert_eq!(
            test_fixup_os_commandline(
                BASE,
                &mut fixup_buffer,
                // Passes empty fixup to apply.
                &[],
                // No protocol lookup error.
                None,
                // No protocol call error.
                Ok(()),
            ),
            // Expected empty fixup.
            Ok(Some("")),
        );
    }

    #[test]
    fn test_fixup_os_commandline_wrong_fixup() {
        const BASE: &CStr = c"key1=value1 key2=value2";

        // Have no space for null terminator.
        let mut fixup_buffer = [0x0; BASE.to_bytes().len()];
        assert_eq!(
            test_fixup_os_commandline(
                BASE,
                &mut fixup_buffer,
                BASE.to_bytes(),
                // No protocol lookup error.
                None,
                // No protocol call error.
                Ok(()),
            ),
            // Expected error, cannot build c string.
            Err(Error::InvalidInput),
        );
    }

    #[test]
    fn test_fixup_os_commandline_protocol_error() {
        const BASE: &CStr = c"key1=value1 key2=value2";

        let mut fixup_buffer = [0x0; 0];
        assert_eq!(
            test_fixup_os_commandline(
                BASE,
                &mut fixup_buffer,
                &[],
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
    fn test_fixup_os_commandline_protocol_not_found() {
        const BASE: &CStr = c"key1=value1 key2=value2";

        let mut fixup_buffer = [0x0; 0];
        assert_eq!(
            test_fixup_os_commandline(
                BASE,
                &mut fixup_buffer,
                &[],
                // Protocol not found.
                Some(Error::NotFound),
                // No protocol call error.
                Ok(()),
            ),
            // No fixup in case protocol not found.
            Ok(None),
        );
    }

    #[test]
    fn test_fixup_os_commandline_protocol_lookup_failed() {
        const BASE: &CStr = c"key1=value1 key2=value2";

        let mut fixup_buffer = [0x0; 0];
        assert_eq!(
            test_fixup_os_commandline(
                BASE,
                &mut fixup_buffer,
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
        let mut ops = Ops::new(installed.entry(), &[], None);

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
                // No protocol lookup error.
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
                // No protocol lookup error.
                None,
                // Protocol returns error.
                Some(Error::BufferTooSmall(Some(100))),
            ),
            // Expected to be catched.
            Err(Error::BufferTooSmall(Some(100))),
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
    fn test_select_device_tree_components_select_base_and_overlay() {
        let base = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let overlay = include_bytes!("../../libfdt/test/data/overlay_by_path.dtbo").to_vec();
        let overlay2 = include_bytes!("../../libfdt/test/data/overlay_by_reference.dtbo").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB

        let base_scoped = base.clone();
        let overlay_scoped = overlay.clone();
        let overlay2_scoped = overlay2.clone();
        let mut mock_efi = MockEfi::new();
        mock_efi.con_out.expect_write_str().return_const(Ok(()));
        mock_efi
            .boot_services
            .expect_find_first_and_open::<GblOsConfigurationProtocol>()
            .return_once(|| {
                let mut os_configuration = GblOsConfigurationProtocol::default();

                os_configuration.expect_select_device_trees().return_once(move |components| {
                    assert_eq!(components.len(), 3);

                    // SAFETY:
                    // `components[*].device_trees` are pointing to corresponding base device
                    // tree and overlays buffers.
                    let (base_passed, overlay_passed, overlay2_passed) = unsafe {
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
                        )
                    };

                    assert_eq!(base_passed, &base_scoped);
                    assert_eq!(overlay_passed, &overlay_scoped[..]);
                    assert_eq!(overlay2_passed, &overlay2_scoped[..]);

                    // Select the base device and the second overlay. The first overlay is not
                    // being selected.
                    components[0].selected = true;
                    components[2].selected = true;
                    Ok(())
                });

                Ok(os_configuration)
            });

        let installed = mock_efi.install();
        let mut ops = Ops::new(installed.entry(), &[], None);

        let mut registry = DeviceTreeComponentsRegistry::new();
        let mut current_buffer = &mut buffer[..];
        current_buffer = registry
            .append(&mut ops, DeviceTreeComponentSource::VendorBoot, &base, current_buffer)
            .unwrap();
        current_buffer = registry
            .append(
                &mut ops,
                DeviceTreeComponentSource::Dtbo(Default::default()),
                &overlay,
                current_buffer,
            )
            .unwrap();
        registry
            .append(
                &mut ops,
                DeviceTreeComponentSource::Dtbo(Default::default()),
                &overlay2,
                current_buffer,
            )
            .unwrap();

        assert_eq!(ops.select_device_trees(&mut registry), Ok(()));
        assert_eq!(registry.selected(), Ok((&base[..], &[&overlay2[..]][..])));
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
        let mut ops = Ops::new(installed.entry(), &[], None);

        let mut registry = DeviceTreeComponentsRegistry::new();

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
        let mut ops = Ops::new(installed.entry(), &[], None);

        // Appends some data to ensure autoselect is passed.
        let mut registry = DeviceTreeComponentsRegistry::new();
        let current_buffer = &mut buffer[..];
        registry
            .append(&mut ops, DeviceTreeComponentSource::VendorBoot, &base, current_buffer)
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
        let mut ops = Ops::new(installed.entry(), &[], None);

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
}
