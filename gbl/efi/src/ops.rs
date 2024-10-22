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
    efi_blocks::EfiBlockDeviceIo,
    utils::{get_efi_fdt, wait_key_stroke},
};
use alloc::{
    alloc::{alloc, handle_alloc_error, Layout},
    vec::Vec,
};
use core::{ffi::CStr, fmt::Write, mem::MaybeUninit, num::NonZeroUsize, slice::from_raw_parts_mut};
use efi::{
    efi_print, efi_println, protocol::dt_fixup::DtFixupProtocol,
    protocol::gbl_efi_image_loading::GblImageLoadingProtocol,
    protocol::gbl_efi_os_configuration::GblOsConfigurationProtocol, EfiEntry,
};
use efi_types::{GblEfiImageInfo, PARTITION_NAME_LEN_U16};
use fdt::Fdt;
use liberror::{Error, Result};
use libgbl::{
    ops::{AvbIoError, AvbIoResult, CertPermanentAttributes, ImageBuffer, SHA256_DIGEST_SIZE},
    partition::PartitionBlockDevice,
    slots::{BootToken, Cursor},
    BootImages, GblOps, Result as GblResult,
};
use safemath::SafeNum;
use zbi::ZbiContainer;
use zerocopy::AsBytes;

pub struct Ops<'a, 'b> {
    pub efi_entry: &'a EfiEntry,
    pub partitions: &'b [PartitionBlockDevice<'b, &'b mut EfiBlockDeviceIo<'a>>],
    pub zbi_bootloader_files_buffer: Vec<u8>,
}

impl<'a, 'b> Ops<'a, 'b> {
    /// Creates a new instance of [Ops]
    pub fn new(
        efi_entry: &'a EfiEntry,
        partitions: &'b [PartitionBlockDevice<'b, &'b mut EfiBlockDeviceIo<'a>>],
    ) -> Self {
        Self { efi_entry, partitions, zbi_bootloader_files_buffer: Default::default() }
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
    /// * `efi_entry` - EFI entry
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
        const KERNEL_ALIGNMENT: usize = 2 * 1024 * 1024;
        const FDT_ALIGNMENT: usize = 8;
        const BOOTCMD_SIZE: usize = 16 * 1024;
        let size = match image_name {
            "boot" => size.get(),
            "ramdisk" => (SafeNum::from(size.get()) + BOOTCMD_SIZE).try_into()?,
            _ => size.get(),
        };
        // Check for `from_raw_parts_mut()` safety requirements.
        assert!(size < isize::MAX.try_into().unwrap());
        let align = match image_name {
            "boot" => KERNEL_ALIGNMENT,
            "fdt" => FDT_ALIGNMENT,
            _ => 1,
        };

        if size == 0 {
            return Err(Error::Other(Some("allocate_image_buffer() expects non zero size")));
        }

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

impl<'a, 'b> GblOps<'b> for Ops<'a, 'b>
where
    Self: 'b,
{
    type PartitionBlockIo = &'b mut EfiBlockDeviceIo<'a>;

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

    fn preboot(&mut self, _: BootImages) -> Result<()> {
        unimplemented!();
    }

    /// Reboots the system into the last set boot mode.
    fn reboot(&mut self) {
        self.efi_entry.system_table().runtime_services().cold_reset();
    }

    fn partitions(&self) -> Result<&'b [PartitionBlockDevice<'b, Self::PartitionBlockIo>]> {
        Ok(self.partitions)
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

    fn do_fastboot<B: gbl_storage::AsBlockDevice>(&self, _: &mut Cursor<B>) -> GblResult<()> {
        unimplemented!();
    }

    fn load_slot_interface<'c, B: gbl_storage::AsBlockDevice>(
        &'c mut self,
        _: &'c mut B,
        _: BootToken,
    ) -> GblResult<Cursor<'c, B>> {
        unimplemented!();
    }

    fn avb_read_is_device_unlocked(&mut self) -> AvbIoResult<bool> {
        // TODO(b/337846185): Switch to use GBL Verified Boot EFI protocol when available.
        Ok(true)
    }

    fn avb_read_rollback_index(&mut self, _rollback_index_location: usize) -> AvbIoResult<u64> {
        // TODO(b/337846185): Switch to use GBL Verified Boot EFI protocol when available.
        Ok(0)
    }

    fn avb_write_rollback_index(
        &mut self,
        _rollback_index_location: usize,
        _index: u64,
    ) -> AvbIoResult<()> {
        // TODO(b/337846185): Switch to use GBL Verified Boot EFI protocol when available.
        Ok(())
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

    fn get_image_buffer<'c>(
        &mut self,
        image_name: &str,
        size: NonZeroUsize,
    ) -> GblResult<ImageBuffer<'c>> {
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
        Ok(
            match self
                .efi_entry
                .system_table()
                .boot_services()
                .find_first_and_open::<GblOsConfigurationProtocol>()
            {
                Ok(protocol) => {
                    protocol.fixup_kernel_commandline(commandline, fixup_buffer)?;
                    Some(CStr::from_bytes_until_nul(&fixup_buffer[..])?.to_str()?)
                }
                _ => None,
            },
        )
    }

    fn fixup_bootconfig<'c>(
        &mut self,
        bootconfig: &[u8],
        fixup_buffer: &'c mut [u8],
    ) -> Result<Option<&'c [u8]>> {
        Ok(
            match self
                .efi_entry
                .system_table()
                .boot_services()
                .find_first_and_open::<GblOsConfigurationProtocol>()
            {
                Ok(protocol) => {
                    let fixup_size = protocol.fixup_bootconfig(bootconfig, fixup_buffer)?;
                    Some(&fixup_buffer[..fixup_size])
                }
                _ => None,
            },
        )
    }

    fn fixup_device_tree(&mut self, device_tree: &mut [u8]) -> Result<()> {
        if let Ok(protocol) =
            self.efi_entry.system_table().boot_services().find_first_and_open::<DtFixupProtocol>()
        {
            protocol.fixup(device_tree)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use efi_mocks::MockEfi;
    use mockall::predicate::eq;

    #[test]
    fn ops_write_trait() {
        let mut mock_efi = MockEfi::new();

        mock_efi.con_out.expect_write_str().with(eq("foo bar")).return_const(Ok(()));
        let installed = mock_efi.install();

        let mut ops = Ops::new(installed.entry(), &[]);

        assert!(write!(&mut ops, "{} {}", "foo", "bar").is_ok());
    }
}
