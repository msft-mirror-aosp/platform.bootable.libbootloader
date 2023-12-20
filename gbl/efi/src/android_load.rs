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

use core::ffi::CStr;
use core::fmt::Write;
use core::str::from_utf8;

use bootconfig::{BootConfigBuilder, BootConfigError};
use bootimg::{BootImage, VendorImageHeader};
use efi::EfiEntry;
use fdt::Fdt;

use crate::utils::{
    aligned_subslice, cstr_bytes_to_str, find_gpt_devices, get_efi_fdt, usize_add, usize_roundup,
    EfiAppError, GblEfiError, Result,
};

// Linux kernel requires 2MB alignment.
const KERNEL_ALIGNMENT: usize = 2 * 1024 * 1024;

/// Loads Android images from disk and fixes up bootconfig, commandline, and FDT.
///
/// A number of simplifications are made:
///
///   * No A/B slot switching is performed. It always boot from *_a slot.
///   * No AVB is performed.
///   * No dynamic partitions.
///   * Only support V3/V4 image and Android 13+ (generic ramdisk from the "init_boot" partition)
///
/// # Returns
///
/// Returns a tuple of 4 slices corresponding to:
///   (kernel load buffer, ramdisk load buffer, FDT load buffer, unused buffer).
pub fn load_android_simple<'a>(
    efi_entry: &EfiEntry,
    load: &'a mut [u8],
) -> Result<(&'a mut [u8], &'a mut [u8], &'a mut [u8], &'a mut [u8])> {
    let mut gpt_devices = find_gpt_devices(efi_entry)?;

    const PAGE_SIZE: usize = 4096; // V3/V4 image has fixed page size 4096;

    // Parse boot header.
    let (boot_header_buffer, load) = load.split_at_mut(PAGE_SIZE);
    gpt_devices.read_gpt_partition("boot_a", 0, boot_header_buffer)?;
    let boot_header = BootImage::parse(boot_header_buffer)?;
    let (kernel_size, cmdline, kernel_hdr_size) = match boot_header {
        BootImage::V3(ref hdr) => (hdr.kernel_size as usize, &hdr.cmdline[..], PAGE_SIZE),
        BootImage::V4(ref hdr) => {
            (hdr._base.kernel_size as usize, &hdr._base.cmdline[..], PAGE_SIZE)
        }
        _ => {
            efi_print!(efi_entry, "V0/V1/V2 images are not supported\n");
            return Err(GblEfiError::EfiAppError(EfiAppError::Unsupported));
        }
    };
    efi_print!(efi_entry, "boot image size: {}\n", kernel_size);
    efi_print!(efi_entry, "boot image cmdline: \"{}\"\n", from_utf8(cmdline).unwrap());

    // Parse vendor boot header.
    let (vendor_boot_header_buffer, load) = load.split_at_mut(PAGE_SIZE);
    gpt_devices.read_gpt_partition("vendor_boot_a", 0, vendor_boot_header_buffer)?;
    let vendor_boot_header = VendorImageHeader::parse(vendor_boot_header_buffer)?;
    let (vendor_ramdisk_size, vendor_hdr_size, vendor_cmdline) = match vendor_boot_header {
        VendorImageHeader::V3(ref hdr) => (
            hdr.vendor_ramdisk_size as usize,
            usize_roundup(hdr.bytes().len(), hdr.page_size)?,
            &hdr.cmdline[..],
        ),
        VendorImageHeader::V4(ref hdr) => (
            hdr._base.vendor_ramdisk_size as usize,
            usize_roundup(hdr.bytes().len(), hdr._base.page_size)?,
            &hdr._base.cmdline[..],
        ),
    };
    efi_print!(efi_entry, "vendor ramdisk size: {}\n", vendor_ramdisk_size);
    efi_print!(efi_entry, "vendor cmdline: \"{}\"\n", from_utf8(vendor_cmdline).unwrap());

    // Parse init_boot header
    let init_boot_header_buffer = &mut load[..PAGE_SIZE];
    gpt_devices.read_gpt_partition("init_boot_a", 0, init_boot_header_buffer)?;
    let init_boot_header = BootImage::parse(init_boot_header_buffer)?;
    let (generic_ramdisk_size, init_boot_hdr_size) = match init_boot_header {
        BootImage::V3(ref hdr) => (hdr.ramdisk_size as usize, PAGE_SIZE),
        BootImage::V4(ref hdr) => (hdr._base.ramdisk_size as usize, PAGE_SIZE),
        _ => {
            efi_print!(efi_entry, "V0/V1/V2 images are not supported\n");
            return Err(GblEfiError::EfiAppError(EfiAppError::Unsupported));
        }
    };
    efi_print!(efi_entry, "init_boot image size: {}\n", generic_ramdisk_size);

    // Load and prepare various images.

    // Load kernel
    let load = aligned_subslice(load, KERNEL_ALIGNMENT)?;
    let (kernel_load_buffer, load) = load.split_at_mut(kernel_size);
    gpt_devices.read_gpt_partition("boot_a", kernel_hdr_size as u64, kernel_load_buffer)?;

    // Load vendor ramdisk
    let load = aligned_subslice(load, KERNEL_ALIGNMENT)?;
    let mut ramdisk_load_curr = 0;
    gpt_devices.read_gpt_partition(
        "vendor_boot_a",
        vendor_hdr_size as u64,
        &mut load[ramdisk_load_curr..][..vendor_ramdisk_size],
    )?;
    ramdisk_load_curr = usize_add(ramdisk_load_curr, vendor_ramdisk_size)?;

    // Load generic ramdisk
    gpt_devices.read_gpt_partition(
        "init_boot_a",
        init_boot_hdr_size as u64,
        &mut load[ramdisk_load_curr..][..generic_ramdisk_size],
    )?;
    ramdisk_load_curr = usize_add(ramdisk_load_curr, generic_ramdisk_size)?;

    // Use the remaining buffer for bootconfig
    let mut bootconfig_builder = BootConfigBuilder::new(&mut load[ramdisk_load_curr..])?;
    // Add slot index
    bootconfig_builder.add("androidboot.slot_suffix=_a\n")?;

    // Boot into Android
    bootconfig_builder.add("androidboot.force_normal_boot=1\n")?;
    // To ignore AVB failure
    bootconfig_builder.add("androidboot.verifiedbootstate=orange\n")?;

    // V4 image has vendor bootconfig.
    if let VendorImageHeader::V4(ref hdr) = vendor_boot_header {
        let mut bootconfig_offset: usize = vendor_hdr_size;
        for image_size in
            [hdr._base.vendor_ramdisk_size, hdr._base.dtb_size, hdr.vendor_ramdisk_table_size]
        {
            bootconfig_offset =
                usize_add(bootconfig_offset, usize_roundup(image_size, hdr._base.page_size)?)?;
        }
        bootconfig_builder.add_with(|out| {
            gpt_devices
                .read_gpt_partition(
                    "vendor_boot_a",
                    bootconfig_offset as u64,
                    &mut out[..hdr.bootconfig_size as usize],
                )
                .map_err(|_| BootConfigError::GenericReaderError(-1))?;
            Ok(hdr.bootconfig_size as usize)
        })?;
    }
    // Check if there is a device specific bootconfig partition.
    match gpt_devices.partition_size("bootconfig") {
        Ok(sz) => {
            bootconfig_builder.add_with(|out| {
                // For proof-of-concept only, we just load as much as possible and figure out the
                // actual bootconfig string length after. This however, can introduce large amount
                // of unnecessary disk access. In real implementation, we might want to either read
                // page by page or find way to know the actual length first.
                let max_size = core::cmp::min(sz, out.len());
                gpt_devices
                    .read_gpt_partition("bootconfig", 0, &mut out[..max_size])
                    .map_err(|_| BootConfigError::GenericReaderError(-1))?;
                // Compute the actual config string size. The config is a null-terminated string.
                Ok(CStr::from_bytes_until_nul(&out[..])
                    .map_err(|_| BootConfigError::GenericReaderError(-1))?
                    .to_bytes()
                    .len())
            })?;
        }
        _ => {}
    }
    efi_print!(efi_entry, "final bootconfig: \"{}\"\n", bootconfig_builder);
    ramdisk_load_curr = usize_add(ramdisk_load_curr, bootconfig_builder.config_bytes().len())?;

    // Prepare FDT.

    // For cuttlefish, FDT comes from EFI vendor configuration table installed by u-boot. In real
    // product, it may come from vendor boot image.
    let (_, fdt_bytes) = get_efi_fdt(&efi_entry).ok_or_else(|| EfiAppError::NoFdt)?;
    let fdt_origin = Fdt::new(fdt_bytes)?;

    // Use the remaining load buffer for updating FDT.
    let (ramdisk_load_buffer, load) = load.split_at_mut(ramdisk_load_curr);
    // libfdt requires FDT buffer to be 8-byte aligned.
    let load = aligned_subslice(load, 8)?;
    let mut fdt = Fdt::new_from_init(&mut load[..], fdt_bytes)?;

    // Add ramdisk range to FDT
    let ramdisk_addr = ramdisk_load_buffer.as_ptr() as u64;
    let ramdisk_end = ramdisk_addr + (ramdisk_load_buffer.len() as u64);
    fdt.set_property(
        "chosen",
        CStr::from_bytes_with_nul(b"linux,initrd-start\0").unwrap(),
        &ramdisk_addr.to_be_bytes(),
    )?;
    fdt.set_property(
        "chosen",
        CStr::from_bytes_with_nul(b"linux,initrd-end\0").unwrap(),
        &ramdisk_end.to_be_bytes(),
    )?;
    efi_print!(&efi_entry, "linux,initrd-start: {:#x}\n", ramdisk_addr);
    efi_print!(&efi_entry, "linux,initrd-end: {:#x}\n", ramdisk_end);

    // Concatenate kernel commandline and add it to FDT.
    let bootargs_prop = CStr::from_bytes_with_nul(b"bootargs\0").unwrap();
    let all_cmdline = [
        cstr_bytes_to_str(fdt_origin.get_property("chosen", bootargs_prop).unwrap_or(&[0]))?,
        " ",
        cstr_bytes_to_str(cmdline)?,
        " ",
        cstr_bytes_to_str(vendor_cmdline)?,
        "\0",
    ];
    let mut all_cmdline_len = 0;
    all_cmdline.iter().for_each(|v| all_cmdline_len += v.len());
    let cmdline_payload = fdt.set_property_placeholder("chosen", bootargs_prop, all_cmdline_len)?;
    let mut cmdline_payload_off: usize = 0;
    for ele in all_cmdline {
        cmdline_payload[cmdline_payload_off..][..ele.len()].clone_from_slice(ele.as_bytes());
        cmdline_payload_off += ele.len();
    }
    efi_print!(&efi_entry, "final cmdline: \"{}\"\n", from_utf8(cmdline_payload).unwrap());

    // Finalize FDT to actual used size.
    fdt.shrink_to_fit()?;

    let fdt_len = fdt.header_ref()?.actual_size();
    let (fdt_load_buffer, remains) = load.split_at_mut(fdt_len);
    Ok((kernel_load_buffer, ramdisk_load_buffer, fdt_load_buffer, remains))
}
