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
    gbl_avb::ops::GblAvbOps,
    gbl_print, gbl_println, GblOps, IntegrationError, Result,
};
use arrayvec::ArrayVec;
use avb::{slot_verify, HashtreeErrorMode, Ops as _, SlotVerifyFlags};
use bootimg::{BootImage, VendorImageHeader};
use bootparams::{bootconfig::BootConfigBuilder, commandline::CommandlineBuilder};
use core::{ffi::CStr, fmt::Write};
use dttable::DtTableImage;
use fdt::Fdt;
use liberror::Error;
use libutils::aligned_subslice;
use misc::{AndroidBootMode, BootloaderMessage};
use safemath::SafeNum;
use zerocopy::{AsBytes, ByteSlice};

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

/// Helper function for performing libavb verification.
///
/// Currently this requires the caller to preload all relevant images from disk; in its final
/// state `ops` will provide the necessary callbacks for where the images should go in RAM and
/// which ones are preloaded.
///
/// # Arguments
/// * `ops`: [GblOps] providing device-specific backend.
/// * `kernel`: buffer containing the `boot` image loaded from disk.
/// * `vendor_boot`: buffer containing the `vendor_boot` image loaded from disk.
/// * `init_boot`: buffer containing the `init_boot` image loaded from disk.
/// * `dtbo`: buffer containing the `dtbo` image loaded from disk, if it exists.
/// * `bootconfig_builder`: object to write the bootconfig data into.
///
/// # Returns
/// `()` on success, error if the images fail to verify or we fail to update the bootconfig.
fn avb_verify_slot<'a>(
    ops: &mut impl GblOps<'a>,
    kernel: &[u8],
    vendor_boot: &[u8],
    init_boot: &[u8],
    dtbo: Option<&[u8]>,
    bootconfig_builder: &mut BootConfigBuilder,
) -> Result<()> {
    // We need the list of partition names to verify with libavb, and a corresponding list of
    // (name, image) tuples to register as [GblAvbOps] preloaded data.
    let mut partitions = ArrayVec::<_, 4>::new();
    let mut preloaded = ArrayVec::<_, 4>::new();
    for (c_name, image) in [
        (c"boot", Some(kernel)),
        (c"vendor_boot", Some(vendor_boot)),
        (c"init_boot", Some(init_boot)),
        (c"dtbo", dtbo),
    ] {
        if let Some(image) = image {
            partitions.push(c_name);
            preloaded.push((c_name.to_str().unwrap(), image));
        }
    }

    let mut avb_ops = GblAvbOps::new(ops, &preloaded[..], false);
    let avb_state = match avb_ops.read_is_device_unlocked()? {
        true => "orange",
        _ => "green",
    };

    let res = slot_verify(
        &mut avb_ops,
        &partitions,
        Some(c"_a"),
        SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_NONE,
        // For demo, we use the same setting as Cuttlefish u-boot.
        HashtreeErrorMode::AVB_HASHTREE_ERROR_MODE_RESTART_AND_INVALIDATE,
    )
    .map_err(|e| IntegrationError::from(e.without_verify_data()))?;

    // Append avb generated bootconfig.
    for cmdline_arg in res.cmdline().to_str().unwrap().split(' ') {
        write!(bootconfig_builder, "{}\n", cmdline_arg).or(Err(Error::BufferTooSmall(None)))?;
    }

    // Append "androidboot.verifiedbootstate="
    write!(bootconfig_builder, "androidboot.verifiedbootstate={}\n", avb_state)
        .or(Err(Error::BufferTooSmall(None)))?;
    Ok(())
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
            SafeNum::from(hdr.bytes().len())
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
            SafeNum::from(hdr.bytes().len())
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
pub fn load_android_simple<'a, 'b>(
    ops: &mut impl GblOps<'b>,
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
        let off = SafeNum::from(load.len()) - kernel_size - boot_ramdisk_size;
        let off_idx: usize = off.try_into().map_err(Error::from)?;
        let aligned_off = off - (&load[off_idx] as *const _ as usize % KERNEL_ALIGNMENT);
        aligned_off.try_into().map_err(Error::from)?
    };
    let (load, boot_img_buffer) = load.split_at_mut(boot_img_load_offset);
    ops.read_from_partition_sync(
        "boot_a",
        kernel_hdr_size.try_into().unwrap(),
        &mut boot_img_buffer[..kernel_size + boot_ramdisk_size],
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
        load[ramdisk_load_curr.try_into().map_err(Error::from)?..][..boot_ramdisk_size]
            .copy_from_slice(&boot_img_buffer[kernel_size..][..boot_ramdisk_size]);
        ramdisk_load_curr += boot_ramdisk_size;
    }

    // Prepare partition data for avb verification
    let (vendor_boot_load_buffer, remains) = load.split_at_mut(vendor_ramdisk_size);
    let (init_boot_load_buffer, remains) = remains.split_at_mut(generic_ramdisk_size);
    let (_boot_ramdisk_load_buffer, remains) = remains.split_at_mut(boot_ramdisk_size);
    // Prepare a BootConfigBuilder to add avb generated bootconfig.
    let mut bootconfig_builder = BootConfigBuilder::new(remains)?;
    // Perform avb verification.
    avb_verify_slot(
        ops,
        boot_img_buffer,
        vendor_boot_load_buffer,
        init_boot_load_buffer,
        dtbo_buffer.as_deref(),
        &mut bootconfig_builder,
    )?;

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
