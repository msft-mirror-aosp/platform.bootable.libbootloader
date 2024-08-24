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
    efi_blocks::EfiBlockDeviceIo,
    utils::{get_efi_fdt, wait_key_stroke},
};

use core::{ffi::CStr, fmt::Write};
use efi::{efi_print, efi_println, EfiEntry};
use fdt::Fdt;
use liberror::Error;
use libgbl::{
    ops::{AvbIoError, AvbIoResult, CertPermanentAttributes, SHA256_DIGEST_SIZE},
    partition::{
        check_part_unique, read_unique_partition, write_unique_partition, PartitionBlockDevice,
    },
    slots::{BootToken, Cursor},
    BootImages, GblAvbOps, GblOps, Result as GblResult,
};
use zbi::ZbiContainer;
use zerocopy::AsBytes;

pub struct Ops<'a, 'b> {
    pub efi_entry: &'a EfiEntry,
    pub partitions: &'b [PartitionBlockDevice<'b, &'b mut EfiBlockDeviceIo<'a>>],
}

impl<'a> Ops<'a, '_> {
    /// Gets the property of an FDT node from EFI FDT.
    ///
    /// Returns `None` if fail to get the node
    fn get_efi_fdt_prop(&self, path: &str, prop: &CStr) -> Option<&'a [u8]> {
        let (_, fdt_bytes) = get_efi_fdt(&self.efi_entry)?;
        let fdt = Fdt::new(fdt_bytes).ok()?;
        fdt.get_property(path, prop).ok()
    }
}

impl Write for Ops<'_, '_> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        efi_print!(self.efi_entry, "{}", s);
        Ok(())
    }
}

impl GblOps for Ops<'_, '_> {
    fn console_out(&mut self) -> Option<&mut dyn Write> {
        Some(self)
    }

    fn should_stop_in_fastboot(&mut self) -> Result<bool, Error> {
        // TODO(b/349829690): also query GblSlotProtocol.get_boot_reason() for board-specific
        // fastboot triggers.
        efi_println!(self.efi_entry, "Press Backspace to enter fastboot");
        let found = wait_key_stroke(self.efi_entry, '\x08', 2000);
        if matches!(found, Ok(true)) {
            efi_println!(self.efi_entry, "Backspace pressed, entering fastboot");
        }
        // TODO(b/358377120): pass the UEFI error when liberror::Error support lands.
        found.or(Err(Error::Other(Some("wait for key stroke error"))))
    }

    fn preboot(&mut self, _: BootImages) -> Result<(), Error> {
        unimplemented!();
    }

    async fn read_from_partition(
        &mut self,
        part: &str,
        off: u64,
        out: &mut [u8],
    ) -> Result<(), Error> {
        read_unique_partition(self.partitions, part, off, out).await
    }

    async fn write_to_partition(
        &mut self,
        part: &str,
        off: u64,
        data: &mut [u8],
    ) -> Result<(), Error> {
        write_unique_partition(self.partitions, part, off, data).await
    }

    fn partition_size(&mut self, part: &str) -> Result<Option<u64>, Error> {
        match check_part_unique(self.partitions, part) {
            Ok((_, p)) => Ok(Some(p.size()?)),
            Err(Error::NotFound) => Ok(None),
            Err(e) => Err(e),
        }
    }

    fn zircon_add_device_zbi_items(
        &mut self,
        container: &mut ZbiContainer<&mut [u8]>,
    ) -> Result<(), Error> {
        // TODO(b/353272981): Switch to use OS configuration protocol once it is implemented on
        // existing platforms such as VIM3.
        Ok(match self.get_efi_fdt_prop("zircon", c"zbi-blob") {
            Some(blob) => container.extend_unaligned(blob).map_err(|_| "Failed to append ZBI")?,
            _ => efi_println!(self.efi_entry, "No device ZBI items.\r\n"),
        })
    }

    fn do_fastboot<B: gbl_storage::AsBlockDevice>(&self, _: &mut Cursor<B>) -> GblResult<()> {
        unimplemented!();
    }

    fn load_slot_interface<'a, B: gbl_storage::AsBlockDevice>(
        &'a mut self,
        _: &'a mut B,
        _: BootToken,
    ) -> GblResult<Cursor<'a, B>> {
        unimplemented!();
    }

    fn avb_ops(&mut self) -> Option<impl GblAvbOps> {
        Some(self)
    }
}

impl GblAvbOps for &mut Ops<'_, '_> {
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
}
