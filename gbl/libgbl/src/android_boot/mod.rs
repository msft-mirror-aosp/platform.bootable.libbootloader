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

//! Android boot support.

use crate::{
    device_tree::{DeviceTreeComponentSource, DeviceTreeComponentsRegistry, FDT_ALIGNMENT},
    gbl_print, gbl_println, GblOps, Result,
};
use bootimg::{BootImage, VendorImageHeader};
use bootparams::{bootconfig::BootConfigBuilder, commandline::CommandlineBuilder};
use core::ffi::CStr;
use dttable::DtTableImage;
use fdt::Fdt;
use liberror::Error;
use libutils::{aligned_offset, aligned_subslice};
use misc::{AndroidBootMode, BootloaderMessage};
use safemath::SafeNum;
use zerocopy::{ByteSlice, IntoBytes, Ref};

mod vboot;
use vboot::{avb_verify_slot, PartitionsToVerify};

mod load;
use load::split_chunks;
pub use load::{android_load_verify, LoadedImages};

#[cfg(target_arch = "aarch64")]
use crate::decompress::decompress_kernel;

/// Device tree bootargs property to store kernel command line.
pub const BOOTARGS_PROP: &CStr = c"bootargs";
/// Linux kernel requires 2MB alignment.
const KERNEL_ALIGNMENT: usize = 2 * 1024 * 1024;

/// A helper to convert a bytes slice containing a null-terminated string to `str`
fn cstr_bytes_to_str(data: &[u8]) -> core::result::Result<&str, Error> {
    Ok(CStr::from_bytes_until_nul(data)?.to_str()?)
}

/// Helper function to parse common fields from boot image headers.
///
/// # Returns
///
/// Returns a tuple of 6 slices corresponding to:
/// (kernel_size, cmdline, page_size, ramdisk_size, second_size, dtb_size)
fn boot_header_elements<B: ByteSlice + PartialEq>(
    hdr: &BootImage<B>,
) -> Result<(usize, &str, usize, usize, usize, usize)> {
    const PAGE_SIZE: usize = 4096; // V3/V4 image has fixed page size 4096;
    Ok(match hdr {
        BootImage::V2(ref hdr) => (
            hdr._base._base.kernel_size as usize,
            cstr_bytes_to_str(&hdr._base._base.cmdline[..])?,
            hdr._base._base.page_size as usize,
            hdr._base._base.ramdisk_size as usize,
            hdr._base._base.second_size as usize,
            hdr.dtb_size as usize,
        ),
        BootImage::V3(ref hdr) => (
            hdr.kernel_size as usize,
            cstr_bytes_to_str(&hdr.cmdline[..])?,
            PAGE_SIZE,
            hdr.ramdisk_size as usize,
            0,
            0,
        ),
        BootImage::V4(ref hdr) => (
            hdr._base.kernel_size as usize,
            cstr_bytes_to_str(&hdr._base.cmdline[..])?,
            PAGE_SIZE,
            hdr._base.ramdisk_size as usize,
            0,
            0,
        ),
        _ => {
            return Err(Error::UnsupportedVersion.into());
        }
    })
}

/// Helper function to parse common fields from vendor image headers.
///
/// # Returns
///
/// Returns a tuple of 5 slices corresponding to:
/// (vendor_ramdisk_size, hdr_size, cmdline, page_size, dtb_size, vendor_bootconfig_size, vendor_ramdisk_table_size)
fn vendor_header_elements<B: ByteSlice + PartialEq>(
    hdr: &VendorImageHeader<B>,
) -> Result<(usize, usize, &str, usize, usize, usize, usize)> {
    Ok(match hdr {
        VendorImageHeader::V3(ref hdr) => (
            hdr.vendor_ramdisk_size as usize,
            SafeNum::from(Ref::bytes(hdr).len())
                .round_up(hdr.page_size)
                .try_into()
                .map_err(Error::from)?,
            cstr_bytes_to_str(&hdr.cmdline.as_bytes())?,
            hdr.page_size as usize,
            hdr.dtb_size as usize,
            0,
            0,
        ),
        VendorImageHeader::V4(ref hdr) => (
            hdr._base.vendor_ramdisk_size as usize,
            SafeNum::from(Ref::bytes(hdr).len())
                .round_up(hdr._base.page_size)
                .try_into()
                .map_err(Error::from)?,
            cstr_bytes_to_str(&hdr._base.cmdline.as_bytes())?,
            hdr._base.page_size as usize,
            hdr._base.dtb_size as usize,
            hdr.bootconfig_size as usize,
            hdr.vendor_ramdisk_table_size as usize,
        ),
    })
}

/// Loads Android images from disk and fixes up bootconfig, commandline, and FDT.
///
/// A number of simplifications are made:
///
///   * No A/B slot switching is performed. It always boot from *_a slot.
///   * No dynamic partitions.
///   * Only support V3/V4 image and Android 13+ (generic ramdisk from the "init_boot" partition)
///   * Only support booting recovery from boot image
///
/// # Arguments
/// * `ops`: the [GblOps] object providing platform-specific backends.
/// * `load`: the combined buffer to load all images into.
///
/// # Returns
/// Returns a tuple of 4 slices corresponding to:
///   (ramdisk load buffer, FDT load buffer, kernel load buffer, unused buffer).
pub fn load_android_simple<'a, 'b, 'c>(
    ops: &mut impl GblOps<'b, 'c>,
    load: &'a mut [u8],
) -> Result<(&'a mut [u8], &'a mut [u8], &'a mut [u8], &'a mut [u8])> {
    const PAGE_SIZE: usize = 4096; // V3/V4 image has fixed page size 4096;

    let (bcb_buffer, load) = load.split_at_mut(BootloaderMessage::SIZE_BYTES);
    ops.read_from_partition_sync("misc", 0, bcb_buffer)?;
    let bcb = BootloaderMessage::from_bytes_ref(bcb_buffer)?;
    let boot_mode = bcb.boot_mode()?;
    gbl_println!(ops, "boot mode from BCB: {}", boot_mode);

    // TODO(b/370317273): use high level abstraction over boot to avoid working
    // with offsets on application level.
    // Parse boot header.
    let (boot_header_buffer, load) = load.split_at_mut(PAGE_SIZE);
    ops.read_from_partition_sync("boot_a", 0, boot_header_buffer)?;
    let boot_header = BootImage::parse(boot_header_buffer).map_err(Error::from)?;
    let (
        kernel_size,
        boot_cmdline,
        kernel_hdr_size,
        boot_ramdisk_size,
        boot_second_size,
        boot_dtb_size,
    ) = boot_header_elements(&boot_header)?;
    gbl_println!(ops, "boot image size: {}", kernel_size);
    gbl_println!(ops, "boot image cmdline: \"{}\"", boot_cmdline);
    gbl_println!(ops, "boot ramdisk size: {}", boot_ramdisk_size);
    gbl_println!(ops, "boot dtb size: {}", boot_dtb_size);

    // TODO(b/370317273): use high level abstraction over vendor_boot to avoid working
    // with offsets on application level.
    // Parse vendor boot header.
    let (vendor_boot_header_buffer, load) = load.split_at_mut(PAGE_SIZE);
    let vendor_boot_header;
    let (
        vendor_ramdisk_size,
        vendor_hdr_size,
        vendor_cmdline,
        vendor_page_size,
        vendor_dtb_size,
        vendor_bootconfig_size,
        vendor_ramdisk_table_size,
    ) = match ops.partition_size("vendor_boot_a") {
        Ok(Some(_sz)) => {
            ops.read_from_partition_sync("vendor_boot_a", 0, vendor_boot_header_buffer)?;
            vendor_boot_header =
                VendorImageHeader::parse(vendor_boot_header_buffer).map_err(Error::from)?;
            vendor_header_elements(&vendor_boot_header)?
        }
        _ => (0 as usize, 0 as usize, "", 0 as usize, 0 as usize, 0 as usize, 0),
    };

    gbl_println!(ops, "vendor ramdisk size: {}", vendor_ramdisk_size);
    gbl_println!(ops, "vendor cmdline: \"{}\"", vendor_cmdline);
    gbl_println!(ops, "vendor dtb size: {}", vendor_dtb_size);

    let (dtbo_buffer, load) = match ops.partition_size("dtbo_a") {
        Ok(Some(sz)) => {
            let (dtbo_buffer, load) = load.split_at_mut(sz.try_into().unwrap());
            ops.read_from_partition_sync("dtbo_a", 0, dtbo_buffer)?;
            (Some(dtbo_buffer), load)
        }
        _ => (None, load),
    };

    let mut components: DeviceTreeComponentsRegistry<'a> = DeviceTreeComponentsRegistry::new();
    let load = match dtbo_buffer {
        Some(ref dtbo_buffer) => {
            let dtbo_table = DtTableImage::from_bytes(dtbo_buffer)?;
            components.append_from_dtbo(&dtbo_table, load)?
        }
        _ => load,
    };

    // First: check for custom FDT (Cuttlefish).
    let load = if ops.get_custom_device_tree().is_none() {
        // Second: "vendor_boot" FDT.
        let (source, part, offset, size) = if vendor_dtb_size > 0 {
            // DTB is located after the header and ramdisk (aligned).
            let offset = (SafeNum::from(vendor_hdr_size) + SafeNum::from(vendor_ramdisk_size))
                .round_up(vendor_page_size)
                .try_into()
                .map_err(Error::from)?;
            (DeviceTreeComponentSource::VendorBoot, "vendor_boot_a", offset, vendor_dtb_size)
        // Third: "boot" FDT.
        } else if boot_dtb_size > 0 {
            // DTB is located after the header, kernel, ramdisk, and second images (aligned).
            let mut offset = SafeNum::from(kernel_hdr_size);
            for image_size in [kernel_size, boot_ramdisk_size, boot_second_size] {
                offset += SafeNum::from(image_size).round_up(kernel_hdr_size);
            }
            (
                DeviceTreeComponentSource::Boot,
                "boot_a",
                offset.try_into().map_err(Error::from)?,
                boot_dtb_size,
            )
        } else {
            return Err(Error::NoFdt.into());
        };

        let (fdt_buffer, load) = aligned_subslice(load, FDT_ALIGNMENT)?.split_at_mut(size);
        ops.read_from_partition_sync(part, offset, fdt_buffer)?;
        components.append(ops, source, fdt_buffer, load)?
    } else {
        load
    };

    // Parse init_boot header
    let init_boot_header_buffer = &mut load[..PAGE_SIZE];
    let (generic_ramdisk_size, init_boot_hdr_size) = match ops.partition_size("init_boot_a") {
        Ok(Some(_sz)) => {
            ops.read_from_partition_sync("init_boot_a", 0, init_boot_header_buffer)?;
            let init_boot_header =
                BootImage::parse(init_boot_header_buffer).map_err(Error::from)?;
            match init_boot_header {
                BootImage::V3(ref hdr) => (hdr.ramdisk_size as usize, PAGE_SIZE),
                BootImage::V4(ref hdr) => (hdr._base.ramdisk_size as usize, PAGE_SIZE),
                _ => {
                    gbl_println!(ops, "V0/V1/V2 images are not supported");
                    return Err(Error::UnsupportedVersion.into());
                }
            }
        }
        _ => (0, 0),
    };
    gbl_println!(ops, "init_boot image size: {}", generic_ramdisk_size);

    // Load and prepare various images.
    let images_buffer = aligned_subslice(load, KERNEL_ALIGNMENT)?;
    let load = &mut images_buffer[..];

    // Load kernel
    // Kernel may need to reserve additional memory after itself. To avoid the risk of this
    // memory overlapping with ramdisk. We place kernel after ramdisk. We first load it to the tail
    // of the buffer and move it forward as much as possible after ramdisk and fdt are loaded,
    // fixed-up and finalized.
    let boot_img_load_offset: usize = {
        let off = SafeNum::from(load.len())
            - SafeNum::from(kernel_size).round_up(kernel_hdr_size)
            - SafeNum::from(boot_ramdisk_size).round_up(kernel_hdr_size);
        let off_idx: usize = off.try_into().map_err(Error::from)?;
        let aligned_off = off - (&load[off_idx] as *const _ as usize % KERNEL_ALIGNMENT);
        aligned_off.try_into().map_err(Error::from)?
    };
    let (load, boot_img_buffer) = load.split_at_mut(boot_img_load_offset);
    let boot_partition_load_size: usize = (SafeNum::from(kernel_size).round_up(kernel_hdr_size)
        + SafeNum::from(boot_ramdisk_size).round_up(kernel_hdr_size))
    .try_into()
    .unwrap();
    ops.read_from_partition_sync(
        "boot_a",
        kernel_hdr_size.try_into().unwrap(),
        &mut boot_img_buffer[..boot_partition_load_size],
    )?;

    // Load vendor ramdisk
    let mut ramdisk_load_curr = SafeNum::ZERO;
    if vendor_ramdisk_size > 0 {
        ops.read_from_partition_sync(
            "vendor_boot_a",
            u64::try_from(vendor_hdr_size).map_err(Error::from)?,
            &mut load[ramdisk_load_curr.try_into().map_err(Error::from)?..][..vendor_ramdisk_size],
        )?;
    }
    ramdisk_load_curr += vendor_ramdisk_size;

    // Load generic ramdisk
    if generic_ramdisk_size > 0 {
        ops.read_from_partition_sync(
            "init_boot_a",
            init_boot_hdr_size.try_into().unwrap(),
            &mut load[ramdisk_load_curr.try_into().map_err(Error::from)?..][..generic_ramdisk_size],
        )?;
        ramdisk_load_curr += generic_ramdisk_size;
    }

    // Load ramdisk from boot image
    if boot_ramdisk_size > 0 {
        let kernel_size_roundup: usize =
            SafeNum::from(kernel_size).round_up(kernel_hdr_size).try_into().unwrap();
        load[ramdisk_load_curr.try_into().map_err(Error::from)?..][..boot_ramdisk_size]
            .copy_from_slice(&boot_img_buffer[kernel_size_roundup..][..boot_ramdisk_size]);
        ramdisk_load_curr += boot_ramdisk_size;
    }

    // Prepare partition data for avb verification
    let (_vendor_boot_load_buffer, remains) = load.split_at_mut(vendor_ramdisk_size);
    let (_init_boot_load_buffer, remains) = remains.split_at_mut(generic_ramdisk_size);
    let (_boot_ramdisk_load_buffer, remains) = remains.split_at_mut(boot_ramdisk_size);
    // Prepare a BootConfigBuilder to add avb generated bootconfig.
    let mut bootconfig_builder = BootConfigBuilder::new(remains)?;

    // Preloaded partitions aren't used. Will be fixed by using load.rs implementation
    avb_verify_slot(ops, 0, &PartitionsToVerify::default(), &mut bootconfig_builder)?;

    // Move kernel to end of the boot image buffer
    let (_boot_img_buffer, kernel_tail_buffer) = {
        let off = SafeNum::from(boot_img_buffer.len()) - kernel_size;
        let off_idx: usize = off.try_into().map_err(Error::from)?;
        let aligned_off = off - (&boot_img_buffer[off_idx] as *const _ as usize % KERNEL_ALIGNMENT);
        let aligned_off_idx = aligned_off.try_into().map_err(Error::from)?;
        boot_img_buffer.copy_within(0..kernel_size, aligned_off_idx);
        boot_img_buffer.split_at_mut(aligned_off_idx)
    };

    // Add slot index
    bootconfig_builder.add("androidboot.slot_suffix=_a\n")?;

    // Placeholder value for now. Userspace can use this value to tell if device is booted with GBL.
    // TODO(yochiang): Generate useful value like version, build_incremental in the bootconfig.
    bootconfig_builder.add("androidboot.gbl.version=0\n")?;
    bootconfig_builder.add("androidboot.gbl.build_number=")?;
    match option_env!("BUILD_NUMBER") {
        None | Some("") => {
            bootconfig_builder.add("eng.build\n")?;
        }
        Some(build_number) => {
            bootconfig_builder.add(build_number)?;
            bootconfig_builder.add("\n")?;
        }
    }

    match boot_mode {
        // TODO(b/329716686): Support bootloader mode
        AndroidBootMode::Normal | AndroidBootMode::BootloaderBootOnce => {
            bootconfig_builder.add("androidboot.force_normal_boot=1\n")?
        }
        _ => {
            // Do nothing
        }
    }

    // V4 image has vendor bootconfig.
    if vendor_bootconfig_size > 0 {
        let mut bootconfig_offset = SafeNum::from(vendor_hdr_size);
        for image_size in [vendor_ramdisk_size, vendor_dtb_size, vendor_ramdisk_table_size] {
            bootconfig_offset += SafeNum::from(image_size).round_up(vendor_page_size);
        }
        bootconfig_builder.add_with(|_, out| {
            ops.read_from_partition_sync(
                "vendor_boot_a",
                bootconfig_offset.try_into()?,
                &mut out[..vendor_bootconfig_size as usize],
            )?;
            Ok(vendor_bootconfig_size as usize)
        })?;
    }

    // TODO(b/353272981): Handle buffer too small
    bootconfig_builder.add_with(|bytes, out| {
        // TODO(b/353272981): Verify provided bootconfig and fail here
        Ok(ops.fixup_bootconfig(&bytes, out)?.map(|slice| slice.len()).unwrap_or(0))
    })?;
    gbl_println!(ops, "final bootconfig: \"{}\"", bootconfig_builder);

    ramdisk_load_curr += bootconfig_builder.config_bytes().len();

    // On ARM, we may need to decompress the kernel and re-split the buffer to the new kernel size.
    #[cfg(target_arch = "aarch64")]
    let (load, kernel_size, kernel_tail_buffer) = {
        let kernel_size = kernel_tail_buffer.len();
        let compressed_kernel_offset = images_buffer.len() - kernel_size;
        let decompressed_kernel_offset =
            decompress_kernel(ops, images_buffer, compressed_kernel_offset)?;
        let (load, kernel_tail_buffer) = images_buffer.split_at_mut(decompressed_kernel_offset);
        (load, kernel_tail_buffer.len(), kernel_tail_buffer)
    };

    // Use the remaining load buffer for the FDT.
    let (ramdisk_load_buffer, load) =
        load.split_at_mut(ramdisk_load_curr.try_into().map_err(Error::from)?);

    let (base, overlays): (&[u8], &[&[u8]]) = if let Some(custom_fdt) = ops.get_custom_device_tree()
    {
        (custom_fdt, &[])
    } else {
        ops.select_device_trees(&mut components)?;
        components.selected()?
    };

    let fdt_buffer = aligned_subslice(load, FDT_ALIGNMENT)?;
    let mut fdt = Fdt::new_from_init(fdt_buffer, base)?;

    gbl_println!(ops, "Applying {} overlays", overlays.len());
    fdt.multioverlay_apply(overlays)?;
    gbl_println!(ops, "Overlays applied");

    // Add ramdisk range to FDT
    let ramdisk_addr: u64 =
        (ramdisk_load_buffer.as_ptr() as usize).try_into().map_err(Error::from)?;
    let ramdisk_end: u64 =
        ramdisk_addr + u64::try_from(ramdisk_load_buffer.len()).map_err(Error::from)?;
    fdt.set_property("chosen", c"linux,initrd-start", &ramdisk_addr.to_be_bytes())?;
    fdt.set_property("chosen", c"linux,initrd-end", &ramdisk_end.to_be_bytes())?;
    gbl_println!(ops, "linux,initrd-start: {:#x}", ramdisk_addr);
    gbl_println!(ops, "linux,initrd-end: {:#x}", ramdisk_end);

    // Update the FDT commandline.
    let device_tree_commandline_length = match fdt.get_property("chosen", BOOTARGS_PROP) {
        Ok(val) => CStr::from_bytes_until_nul(val).map_err(Error::from)?.to_bytes().len(),
        Err(_) => 0,
    };

    // Reserve 1024 bytes for separators and fixup.
    let final_commandline_len =
        device_tree_commandline_length + boot_cmdline.len() + vendor_cmdline.len() + 1024;
    let final_commandline_buffer =
        fdt.set_property_placeholder("chosen", BOOTARGS_PROP, final_commandline_len)?;

    let mut commandline_builder =
        CommandlineBuilder::new_from_prefix(&mut final_commandline_buffer[..])?;
    commandline_builder.add(boot_cmdline)?;
    commandline_builder.add(vendor_cmdline)?;

    // TODO(b/353272981): Handle buffer too small
    commandline_builder.add_with(|current, out| {
        // TODO(b/353272981): Verify provided command line and fail here.
        Ok(ops.fixup_os_commandline(current, out)?.map(|fixup| fixup.len()).unwrap_or(0))
    })?;
    gbl_println!(ops, "final cmdline: \"{}\"", commandline_builder.as_str());

    // Make sure we provide an actual device tree size, so FW can calculate amount of space
    // available for fixup.
    fdt.shrink_to_fit()?;
    // TODO(b/353272981): Make a copy of current device tree and verify provided fixup.
    // TODO(b/353272981): Handle buffer too small
    ops.fixup_device_tree(fdt.as_mut())?;
    fdt.shrink_to_fit()?;

    // Move the kernel backward as much as possible to preserve more space after it. This is
    // necessary in case the input buffer is at the end of address space.
    let kernel_tail_buffer_size = kernel_tail_buffer.len();
    let ramdisk_load_buffer_size = ramdisk_load_buffer.len();
    let fdt_len = fdt.header_ref()?.actual_size();
    // Split out the ramdisk.
    let (ramdisk, remains) = images_buffer.split_at_mut(ramdisk_load_buffer_size);
    // Split out the fdt.
    let (fdt, kernel) = aligned_subslice(remains, FDT_ALIGNMENT)?.split_at_mut(fdt_len);
    // Move the kernel backward as much as possible.
    let kernel = aligned_subslice(kernel, KERNEL_ALIGNMENT)?;
    let kernel_start = kernel.len().checked_sub(kernel_tail_buffer_size).unwrap();
    kernel.copy_within(kernel_start..kernel_start.checked_add(kernel_size).unwrap(), 0);
    // Split out the remaining buffer.
    let (kernel, remains) = kernel.split_at_mut(kernel_size);

    Ok((ramdisk, fdt, kernel, remains))
}

/// Loads Android images from the given slot on disk and fixes up bootconfig, commandline, and FDT.
///
/// On success, returns a tuple of (ramdisk, fdt, kernel, unused buffer).
pub fn android_load_verify_fixup<'a, 'b, 'c>(
    ops: &mut impl GblOps<'b, 'c>,
    slot: u8,
    is_recovery: bool,
    load: &'a mut [u8],
) -> Result<(&'a mut [u8], &'a mut [u8], &'a mut [u8], &'a mut [u8])> {
    let load_addr = load.as_ptr() as usize;
    let images = android_load_verify(ops, slot, is_recovery, load)?;

    let mut components = DeviceTreeComponentsRegistry::new();
    let fdt_load = &mut images.unused[..];
    // TODO(b/353272981): Remove get_custom_device_tree
    let (fdt_load, base, overlays) = match ops.get_custom_device_tree() {
        Some(v) => (fdt_load, v, &[][..]),
        _ => {
            let mut remains = match images.dtbo.len() > 0 {
                // TODO(b/384964561, b/374336105): Investigate if we can avoid additional copy.
                true => components
                    .append_from_dtbo(&DtTableImage::from_bytes(images.dtbo)?, fdt_load)?,
                _ => fdt_load,
            };

            if images.dtb.len() > 0 {
                remains =
                    components.append(ops, DeviceTreeComponentSource::Boot, images.dtb, remains)?;
            }

            if images.dtb_part.len() > 0 {
                let dttable = DtTableImage::from_bytes(images.dtb_part)?;
                remains = components.append_from_dttable(true, &dttable, remains)?;
            }

            ops.select_device_trees(&mut components)?;
            let (base, overlays) = components.selected()?;
            (remains, base, overlays)
        }
    };
    let fdt_load = aligned_subslice(fdt_load, FDT_ALIGNMENT)?;
    let mut fdt = Fdt::new_from_init(&mut fdt_load[..], base)?;

    // Adds ramdisk range to FDT
    let ramdisk_addr: u64 = (images.ramdisk.as_ptr() as usize).try_into().map_err(Error::from)?;
    let ramdisk_end: u64 = ramdisk_addr + u64::try_from(images.ramdisk.len()).unwrap();
    fdt.set_property("chosen", c"linux,initrd-start", &ramdisk_addr.to_be_bytes())?;
    fdt.set_property("chosen", c"linux,initrd-end", &ramdisk_end.to_be_bytes())?;
    gbl_println!(ops, "linux,initrd-start: {:#x}", ramdisk_addr);
    gbl_println!(ops, "linux,initrd-end: {:#x}", ramdisk_end);

    // Updates the FDT commandline.
    let device_tree_commandline_length = match fdt.get_property("chosen", BOOTARGS_PROP) {
        Ok(val) => CStr::from_bytes_until_nul(val).map_err(Error::from)?.to_bytes().len(),
        Err(_) => 0,
    };

    // Reserves 1024 bytes for separators and fixup.
    let final_commandline_len = device_tree_commandline_length
        + images.boot_cmdline.len()
        + images.vendor_cmdline.len()
        + 1024;
    let final_commandline_buffer =
        fdt.set_property_placeholder("chosen", BOOTARGS_PROP, final_commandline_len)?;
    let mut commandline_builder =
        CommandlineBuilder::new_from_prefix(&mut final_commandline_buffer[..])?;
    commandline_builder.add(images.boot_cmdline)?;
    commandline_builder.add(images.vendor_cmdline)?;

    // TODO(b/353272981): Handle buffer too small
    commandline_builder.add_with(|current, out| {
        // TODO(b/353272981): Verify provided command line and fail here.
        Ok(ops.fixup_os_commandline(current, out)?.map(|fixup| fixup.len()).unwrap_or(0))
    })?;
    gbl_println!(ops, "final cmdline: \"{}\"", commandline_builder.as_str());

    gbl_println!(ops, "Applying {} overlays", overlays.len());
    fdt.multioverlay_apply(overlays)?;
    gbl_println!(ops, "Overlays applied");
    // `DeviceTreeComponentsRegistry` internally uses ArrayVec which causes it to have a default
    // life time equal to the scope it lives in. This is unnecessarily strict and prevents us from
    // accessing `load` buffer.
    drop(components);

    // Make sure we provide an actual device tree size, so FW can calculate amount of space
    // available for fixup.
    fdt.shrink_to_fit()?;
    // TODO(b/353272981): Make a copy of current device tree and verify provided fixup.
    // TODO(b/353272981): Handle buffer too small
    ops.fixup_device_tree(fdt.as_mut())?;
    fdt.shrink_to_fit()?;

    // Moves the kernel forward to reserve as much space as possible. This is in case there is not
    // enough memory after `load`, i.e. the memory after it is not mapped or is reserved.
    let ramdisk_off = usize::try_from(ramdisk_addr).unwrap() - load_addr;
    let fdt_len = fdt.header_ref()?.actual_size();
    let fdt_off = fdt_load.as_ptr() as usize - load_addr;
    let kernel_off = images.kernel.as_ptr() as usize - load_addr;
    let kernel_len = images.kernel.len();
    let mut kernel_new = (SafeNum::from(fdt_off) + fdt_len).try_into().map_err(Error::from)?;
    kernel_new += aligned_offset(&mut load[kernel_new..], KERNEL_ALIGNMENT)?;
    load.copy_within(kernel_off..kernel_off + kernel_len, kernel_new);
    let ([_, ramdisk, fdt, kernel], unused) =
        split_chunks(load, &[ramdisk_off, fdt_off - ramdisk_off, kernel_new - fdt_off, kernel_len]);
    let ramdisk = &mut ramdisk[..usize::try_from(ramdisk_end - ramdisk_addr).unwrap()];
    Ok((ramdisk, fdt, kernel, unused))
}

/// Runs full Android bootloader bootflow before kernel handoff.
///
/// The API performs slot selection, handles boot mode, fastboot and loads and verifies Android from
/// disk.
///
/// On success, returns a tuple of slices corresponding to `(ramdisk, FDT, kernel, unused)`
pub fn android_main<'a, 'b, 'c>(
    ops: &mut impl GblOps<'a, 'b>,
    load: &'c mut [u8],
) -> Result<(&'c mut [u8], &'c mut [u8], &'c mut [u8], &'c mut [u8])> {
    let (bcb_buffer, _) = load
        .split_at_mut_checked(BootloaderMessage::SIZE_BYTES)
        .ok_or(Error::BufferTooSmall(Some(BootloaderMessage::SIZE_BYTES)))
        .inspect_err(|e| gbl_println!(ops, "Buffer too small for reading misc. {e}"))?;
    ops.read_from_partition_sync("misc", 0, bcb_buffer)
        .inspect_err(|e| gbl_println!(ops, "Failed to read misc partition {e}"))?;
    let bcb = BootloaderMessage::from_bytes_ref(bcb_buffer)
        .inspect_err(|e| gbl_println!(ops, "Failed to parse bootloader messgae {e}"))?;
    let boot_mode = bcb
        .boot_mode()
        .inspect_err(|e| gbl_println!(ops, "Failed to parse BCB boot mode {e}. Ignored"))
        .unwrap_or(AndroidBootMode::Normal);
    gbl_println!(ops, "Boot mode from BCB: {}", boot_mode);

    // TODO(b/383620444): Add slot and fastboot support.
    let is_recovery = matches!(boot_mode, AndroidBootMode::Recovery);
    android_load_verify_fixup(ops, 0, is_recovery, load)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        gbl_avb::state::{BootStateColor, KeyValidationStatus},
        ops::test::{FakeGblOps, FakeGblOpsStorage},
        tests::AlignedBuffer,
    };
    use load::tests::{
        check_ramdisk, make_expected_bootconfig, read_test_data, read_test_data_as_str,
        AvbResultBootconfigBuilder, TEST_PUBLIC_KEY_DIGEST, TEST_VENDOR_BOOTCONFIG,
    };
    use std::{collections::HashMap, ffi::CString};

    const TEST_ROLLBACK_INDEX_LOCATION: usize = 1;

    // TODO(b/384964561): This is a temporaray test for making sure the generated images work. It
    // will be replaced with more thorough tests as we productionizes `load_android_simple`.
    #[test]
    fn test_load_android_simple() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("boot_no_ramdisk_v4_a.img"));
        storage.add_raw_device(c"init_boot_a", read_test_data("init_boot_a.img"));
        storage.add_raw_device(c"vendor_boot_a", read_test_data("vendor_boot_v4_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("vbmeta_v4_v4_init_boot_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);
        let mut ops = FakeGblOps::new(&storage);
        ops.avb_ops.unlock_state = Ok(false);
        ops.avb_ops.rollbacks = HashMap::from([(TEST_ROLLBACK_INDEX_LOCATION, Ok(0))]);
        let fdt = AlignedBuffer::new_with_data(
            include_bytes!("../../../libfdt/test/data/base.dtb"),
            FDT_ALIGNMENT,
        );
        ops.custom_device_tree = Some(&fdt);
        let mut load_buffer = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let mut out_color = None;
        let mut handler = |color,
                           _: Option<&CStr>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>| {
            out_color = Some(color);
            Ok(())
        };
        ops.avb_handle_verification_result = Some(&mut handler);
        ops.avb_key_validation_status = Some(Ok(KeyValidationStatus::Valid));
        load_android_simple(&mut ops, &mut load_buffer).unwrap();
        assert_eq!(out_color, Some(BootStateColor::Green));
    }

    /// Helper for testing `android_load_verify_fixup` given a partition layout, target slot and
    /// custom device tree.
    fn test_android_load_verify_fixup(
        slot: u8,
        partitions: &[(CString, String)],
        expected_kernel: &[u8],
        expected_ramdisk: &[u8],
        expected_bootconfig: &[u8],
        expected_bootargs: &str,
        expected_fdt_property: &[(&str, &CStr, Option<&[u8]>)],
    ) {
        let mut storage = FakeGblOpsStorage::default();
        for (part, file) in partitions {
            storage.add_raw_device(part, read_test_data(file));
        }
        let mut ops = FakeGblOps::new(&storage);
        ops.avb_ops.unlock_state = Ok(false);
        ops.avb_ops.rollbacks = HashMap::from([(TEST_ROLLBACK_INDEX_LOCATION, Ok(0))]);
        let mut out_color = None;
        let mut handler = |color,
                           _: Option<&CStr>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>| {
            out_color = Some(color);
            Ok(())
        };
        ops.avb_handle_verification_result = Some(&mut handler);
        ops.avb_key_validation_status = Some(Ok(KeyValidationStatus::Valid));

        let mut load_buffer = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let (ramdisk, fdt, kernel, _) =
            android_load_verify_fixup(&mut ops, slot, false, &mut load_buffer).unwrap();
        assert_eq!(kernel, expected_kernel);
        check_ramdisk(ramdisk, expected_ramdisk, expected_bootconfig);

        let fdt = Fdt::new(fdt).unwrap();
        // "linux,initrd-start/end" are updated.
        assert_eq!(
            fdt.get_property("/chosen", c"linux,initrd-start").unwrap(),
            (ramdisk.as_ptr() as usize).to_be_bytes(),
        );
        assert_eq!(
            fdt.get_property("/chosen", c"linux,initrd-end").unwrap(),
            (ramdisk.as_ptr() as usize + ramdisk.len()).to_be_bytes(),
        );

        // Commandlines are updated.
        assert_eq!(
            CStr::from_bytes_until_nul(fdt.get_property("/chosen", c"bootargs").unwrap()).unwrap(),
            CString::new(expected_bootargs).unwrap().as_c_str(),
        );

        // Fixup is applied.
        assert_eq!(fdt.get_property("/chosen", c"fixup").unwrap(), &[1]);

        // Other FDT properties are as expected.
        for (path, property, res) in expected_fdt_property {
            assert_eq!(
                fdt.get_property(&path, &property).ok(),
                res.clone(),
                "{path}:{property:?} value doesn't match"
            );
        }
    }

    /// Helper for testing `android_load_verify_fixup` for v2 boot image or lower.
    fn test_android_load_verify_fixup_v2_or_lower(
        ver: u8,
        slot: char,
        additional_parts: &[(&CStr, &str)],
        additional_expected_fdt_properties: &[(&str, &CStr, Option<&[u8]>)],
    ) {
        let vbmeta = format!("vbmeta_v{ver}_{slot}.img");
        let mut parts: Vec<(CString, String)> = vec![
            (CString::new(format!("boot_{slot}")).unwrap(), format!("boot_v{ver}_{slot}.img")),
            (CString::new(format!("vbmeta_{slot}")).unwrap(), vbmeta.clone()),
        ];
        for (part, file) in additional_parts.iter().cloned() {
            parts.push((part.into(), file.into()));
        }

        test_android_load_verify_fixup(
            (u64::from(slot) - ('a' as u64)).try_into().unwrap(),
            &parts,
            &read_test_data(format!("kernel_{slot}.img")),
            &read_test_data(format!("generic_ramdisk_{slot}.img")),
            &make_expected_bootconfig(&vbmeta, slot, ""),
            "existing_arg_1=existing_val_1 existing_arg_2=existing_val_2 cmd_key_1=cmd_val_1,cmd_key_2=cmd_val_2",
            additional_expected_fdt_properties,
        )
    }

    #[test]
    fn test_android_load_verify_fixup_v0_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"dtb_slot", Some(b"a\0"))];
        // V0 image doesn't have built-in dtb. We need to provide from dtb partition.
        let parts = &[(c"dtb_a", "dtb_a.img")];
        test_android_load_verify_fixup_v2_or_lower(0, 'a', parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v0_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"dtb_slot", Some(b"a\0")),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a", "dtbo_a.img"), (c"dtb_a", "dtb_a.img")];
        test_android_load_verify_fixup_v2_or_lower(0, 'a', parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v0_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"dtb_slot", Some(b"b\0"))];
        let parts = &[(c"dtb_b", "dtb_b.img")];
        test_android_load_verify_fixup_v2_or_lower(0, 'b', parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v0_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"dtb_slot", Some(b"b\0")),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b", "dtbo_b.img"), (c"dtb_b", "dtb_b.img")];
        test_android_load_verify_fixup_v2_or_lower(0, 'b', parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v1_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"dtb_slot", Some(b"a\0"))];
        // V1 image doesn't have built-in dtb. We need to provide from dtb partition.
        let parts = &[(c"dtb_a", "dtb_a.img")];
        test_android_load_verify_fixup_v2_or_lower(1, 'a', parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v1_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"dtb_slot", Some(b"a\0")),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a", "dtbo_a.img"), (c"dtb_a", "dtb_a.img")];
        test_android_load_verify_fixup_v2_or_lower(1, 'a', parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v1_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"dtb_slot", Some(b"b\0"))];
        let parts = &[(c"dtb_b", "dtb_b.img")];
        test_android_load_verify_fixup_v2_or_lower(1, 'b', parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v1_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"dtb_slot", Some(b"b\0")),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b", "dtbo_b.img"), (c"dtb_b", "dtb_b.img")];
        test_android_load_verify_fixup_v2_or_lower(1, 'b', parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v2_slot_a() {
        // V2 image has built-in dtb. We don't need to provide custom device tree.
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v2_or_lower(2, 'a', &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v2_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a".into(), "dtbo_a.img".into())];
        test_android_load_verify_fixup_v2_or_lower(2, 'a', parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v2_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v2_or_lower(2, 'b', &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v2_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b".into(), "dtbo_b.img".into())];
        test_android_load_verify_fixup_v2_or_lower(2, 'b', parts, fdt_prop);
    }

    /// Common helper for testing `android_load_verify_fixup` for v3/v4 boot image.
    fn test_android_load_verify_fixup_v3_or_v4(
        slot: char,
        partitions: &[(CString, String)],
        vbmeta_file: &str,
        expected_vendor_bootconfig: &str,
        additional_expected_fdt_properties: &[(&str, &CStr, Option<&[u8]>)],
    ) {
        let expected_ramdisk = [
            read_test_data(format!("vendor_ramdisk_{slot}.img")),
            read_test_data(format!("generic_ramdisk_{slot}.img")),
        ]
        .concat();
        test_android_load_verify_fixup(
            (u64::from(slot) - ('a' as u64)).try_into().unwrap(),
            &partitions,
            &read_test_data(format!("kernel_{slot}.img")),
            &expected_ramdisk,
            &make_expected_bootconfig(&vbmeta_file, slot, expected_vendor_bootconfig),
            "existing_arg_1=existing_val_1 existing_arg_2=existing_val_2 cmd_key_1=cmd_val_1,cmd_key_2=cmd_val_2 cmd_vendor_key_1=cmd_vendor_val_1,cmd_vendor_key_2=cmd_vendor_val_2",
            additional_expected_fdt_properties,
        )
    }

    /// Helper for testing `android_load_verify_fixup` for v3/v4 boot image without init_boot.
    fn test_android_load_verify_fixup_v3_or_v4_no_init_boot(
        boot_ver: u32,
        vendor_ver: u32,
        slot: char,
        expected_vendor_bootconfig: &str,
        additional_parts: &[(CString, String)],
        additional_expected_fdt_properties: &[(&str, &CStr, Option<&[u8]>)],
    ) {
        let vbmeta = format!("vbmeta_v{boot_ver}_v{vendor_ver}_{slot}.img");
        let mut parts: Vec<(CString, String)> = vec![
            (CString::new(format!("boot_{slot}")).unwrap(), format!("boot_v{boot_ver}_{slot}.img")),
            (
                CString::new(format!("vendor_boot_{slot}")).unwrap(),
                format!("vendor_boot_v{vendor_ver}_{slot}.img"),
            ),
            (CString::new(format!("vbmeta_{slot}")).unwrap(), vbmeta.clone()),
        ];
        parts.extend_from_slice(additional_parts);
        test_android_load_verify_fixup_v3_or_v4(
            slot,
            &parts,
            &vbmeta,
            expected_vendor_bootconfig,
            additional_expected_fdt_properties,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_no_init_boot_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 3, 'a', "", &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_no_init_boot_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a".into(), "dtbo_a.img".into())];
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 3, 'a', "", parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_no_init_boot_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 3, 'a', "", &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_no_init_boot_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b".into(), "dtbo_b.img".into())];
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 3, 'b', "", parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_no_init_boot_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 3, 'a', "", &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_no_init_boot_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a".into(), "dtbo_a.img".into())];
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 3, 'a', "", parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_no_init_boot_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 3, 'a', "", &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_no_init_boot_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b".into(), "dtbo_b.img".into())];
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 3, 'b', "", parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_no_init_boot_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 4, 'a', config, &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_no_init_boot_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a".into(), "dtbo_a.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 4, 'a', config, parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_no_init_boot_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 4, 'a', config, &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_no_init_boot_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b".into(), "dtbo_b.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 4, 'b', config, parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_no_init_boot_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 4, 'a', config, &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_no_init_boot_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a".into(), "dtbo_a.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 4, 'a', config, parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_no_init_boot_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 4, 'a', config, &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_no_init_boot_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b".into(), "dtbo_b.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 4, 'b', config, parts, fdt_prop);
    }

    /// Helper for testing `android_load_verify_fixup` for v3/v4 boot image with init_boot.
    fn test_android_load_verify_fixup_v3_or_v4_init_boot(
        boot_ver: u32,
        vendor_ver: u32,
        slot: char,
        expected_vendor_bootconfig: &str,
        additional_parts: &[(CString, String)],
        additional_expected_fdt_properties: &[(&str, &CStr, Option<&[u8]>)],
    ) {
        let vbmeta = format!("vbmeta_v{boot_ver}_v{vendor_ver}_init_boot_{slot}.img");
        let mut parts: Vec<(CString, String)> = vec![
            (
                CString::new(format!("boot_{slot}")).unwrap(),
                format!("boot_no_ramdisk_v{boot_ver}_{slot}.img"),
            ),
            (
                CString::new(format!("vendor_boot_{slot}")).unwrap(),
                format!("vendor_boot_v{vendor_ver}_{slot}.img"),
            ),
            (CString::new(format!("init_boot_{slot}")).unwrap(), format!("init_boot_{slot}.img")),
            (CString::new(format!("vbmeta_{slot}")).unwrap(), vbmeta.clone()),
        ];
        parts.extend_from_slice(additional_parts);
        test_android_load_verify_fixup_v3_or_v4(
            slot,
            &parts,
            &vbmeta,
            expected_vendor_bootconfig,
            additional_expected_fdt_properties,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_init_boot_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 3, 'a', "", &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_init_boot_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a".into(), "dtbo_a.img".into())];
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 3, 'a', "", parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_init_boot_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 3, 'a', "", &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_init_boot_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b".into(), "dtbo_b.img".into())];
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 3, 'b', "", parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_init_boot_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 3, 'a', "", &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_init_boot_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a".into(), "dtbo_a.img".into())];
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 3, 'a', "", parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_init_boot_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 3, 'a', "", &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_init_boot_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b".into(), "dtbo_b.img".into())];
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 3, 'b', "", parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_init_boot_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 4, 'a', config, &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_init_boot_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a".into(), "dtbo_a.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 4, 'a', config, parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_init_boot_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 4, 'a', config, &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_init_boot_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b".into(), "dtbo_b.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 4, 'b', config, parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_init_boot_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 4, 'a', config, &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_init_boot_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a".into(), "dtbo_a.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 4, 'a', config, parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_init_boot_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 4, 'a', config, &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_init_boot_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b".into(), "dtbo_b.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 4, 'b', config, parts, fdt_prop);
    }

    /// Helper for checking V2 image loaded from slot A and in normal mode.
    fn checks_loaded_v2_slot_a_normal_mode(ramdisk: &[u8], kernel: &[u8]) {
        let expected_bootconfig = AvbResultBootconfigBuilder::new()
            .vbmeta_size(read_test_data("vbmeta_v2_a.img").len())
            .digest(read_test_data_as_str("vbmeta_v2_a.digest.txt").strip_suffix("\n").unwrap())
            .public_key_digest(TEST_PUBLIC_KEY_DIGEST)
            .extra(FakeGblOps::GBL_TEST_BOOTCONFIG)
            .extra("androidboot.force_normal_boot=1\n")
            .extra(format!("androidboot.slot_suffix=_a\n"))
            .build();
        check_ramdisk(ramdisk, &read_test_data("generic_ramdisk_a.img"), &expected_bootconfig);
        assert_eq!(kernel, read_test_data("kernel_a.img"));
    }

    /// Helper for checking V2 image loaded from slot A and in recovery mode.
    fn checks_loaded_v2_slot_a_recovery_mode(ramdisk: &[u8], kernel: &[u8]) {
        let expected_bootconfig = AvbResultBootconfigBuilder::new()
            .vbmeta_size(read_test_data("vbmeta_v2_a.img").len())
            .digest(read_test_data_as_str("vbmeta_v2_a.digest.txt").strip_suffix("\n").unwrap())
            .public_key_digest(TEST_PUBLIC_KEY_DIGEST)
            .extra(FakeGblOps::GBL_TEST_BOOTCONFIG)
            .extra(format!("androidboot.slot_suffix=_a\n"))
            .build();
        check_ramdisk(ramdisk, &read_test_data("generic_ramdisk_a.img"), &expected_bootconfig);
        assert_eq!(kernel, read_test_data("kernel_a.img"));
    }

    /// Helper for getting default FakeGblOps for tests.
    fn default_test_gbl_ops(storage: &FakeGblOpsStorage) -> FakeGblOps {
        let mut ops = FakeGblOps::new(&storage);
        ops.avb_ops.unlock_state = Ok(false);
        ops.avb_ops.rollbacks = HashMap::from([(TEST_ROLLBACK_INDEX_LOCATION, Ok(0))]);
        ops.avb_key_validation_status = Some(Ok(KeyValidationStatus::Valid));
        ops
    }

    #[test]
    fn test_android_load_verify_fixup_recovery_mode() {
        // Recovery mode is specified by the absence of bootconfig arg
        // "androidboot.force_normal_boot=1\n" and therefore independent of image versions. We can
        // pick any image version for test. Use v2 for simplicity.
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("vbmeta_v2_a.img"));

        let mut ops = default_test_gbl_ops(&storage);
        let mut load_buffer = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let (ramdisk, _, kernel, _) =
            android_load_verify_fixup(&mut ops, 0, true, &mut load_buffer).unwrap();
        checks_loaded_v2_slot_a_recovery_mode(ramdisk, kernel)
    }

    #[test]
    fn test_android_main_bcb_normal_mode() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        let mut load_buffer = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let (ramdisk, _, kernel, _) = android_main(&mut ops, &mut load_buffer).unwrap();
        checks_loaded_v2_slot_a_normal_mode(ramdisk, kernel)
    }

    #[test]
    fn test_android_main_bcb_recovery_mode() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        ops.write_to_partition_sync("misc", 0, &mut b"boot-recovery".to_vec()).unwrap();
        let mut load_buffer = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let (ramdisk, _, kernel, _) = android_main(&mut ops, &mut load_buffer).unwrap();
        checks_loaded_v2_slot_a_recovery_mode(ramdisk, kernel)
    }
}
