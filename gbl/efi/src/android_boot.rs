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

use crate::{
    avb::GblEfiAvbOps, efi_blocks::find_block_devices, ops::Ops, utils::cstr_bytes_to_str,
};
use avb::{slot_verify, HashtreeErrorMode, Ops as _, SlotVerifyFlags};
use bootconfig::BootConfigBuilder;
use bootimg::{BootImage, VendorImageHeader};
use core::cmp::max;
use core::{ffi::CStr, fmt::Write, str::from_utf8};
use efi::{exit_boot_services, EfiEntry};
use fdt::Fdt;
use liberror::Error;
use libgbl::{gbl_print, gbl_println, GblOps, IntegrationError, Result};
use libutils::aligned_subslice;
use misc::{AndroidBootMode, BootloaderMessage};
use safemath::SafeNum;
use zerocopy::{AsBytes, ByteSlice};

#[cfg(target_arch = "aarch64")]
use gbl_efi_aarch64::decompress_kernel;

// Linux kernel requires 2MB alignment.
const KERNEL_ALIGNMENT: usize = 2 * 1024 * 1024;
// libfdt requires FDT buffer to be 8-byte aligned.
const FDT_ALIGNMENT: usize = 8;

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
    let mut partitions = vec![c"boot", c"vendor_boot", c"init_boot"];
    let mut preloaded =
        vec![("boot", kernel), ("vendor_boot", vendor_boot), ("init_boot", init_boot)];

    if let Some(dtbo) = dtbo {
        partitions.push(c"dtbo");
        preloaded.push(("dtbo", dtbo));
    }

    let mut avb_ops = GblEfiAvbOps::new(ops, Some(&preloaded));
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
) -> Result<(usize, &[u8], usize, usize, usize, usize)> {
    const PAGE_SIZE: usize = 4096; // V3/V4 image has fixed page size 4096;
    Ok(match hdr {
        BootImage::V2(ref hdr) => {
            let kernel_size = hdr._base._base.kernel_size as usize;
            let page_size = hdr._base._base.page_size as usize;
            let ramdisk_size = hdr._base._base.ramdisk_size as usize;
            let second_size = hdr._base._base.second_size as usize;
            let dtb_size = hdr.dtb_size as usize;
            (
                kernel_size,
                &hdr._base._base.cmdline[..],
                page_size,
                ramdisk_size,
                second_size,
                dtb_size,
            )
        }
        BootImage::V3(ref hdr) => {
            (hdr.kernel_size as usize, &hdr.cmdline[..], PAGE_SIZE, hdr.ramdisk_size as usize, 0, 0)
        }
        BootImage::V4(ref hdr) => (
            hdr._base.kernel_size as usize,
            &hdr._base.cmdline[..],
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
/// (vendor_ramdisk_size, hdr_size, cmdline, page_size, dtb_size)
fn vendor_header_elements<B: ByteSlice + PartialEq>(
    hdr: &VendorImageHeader<B>,
) -> Result<(usize, usize, &[u8], usize, usize)> {
    Ok(match hdr {
        VendorImageHeader::V3(ref hdr) => (
            hdr.vendor_ramdisk_size as usize,
            SafeNum::from(hdr.bytes().len())
                .round_up(hdr.page_size)
                .try_into()
                .map_err(Error::from)?,
            &hdr.cmdline.as_bytes(),
            hdr.page_size as usize,
            hdr.dtb_size as usize,
        ),
        VendorImageHeader::V4(ref hdr) => (
            hdr._base.vendor_ramdisk_size as usize,
            SafeNum::from(hdr.bytes().len())
                .round_up(hdr._base.page_size)
                .try_into()
                .map_err(Error::from)?,
            &hdr._base.cmdline.as_bytes(),
            hdr._base.page_size as usize,
            hdr._base.dtb_size as usize,
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

    // Parse boot header.
    let (boot_header_buffer, load) = load.split_at_mut(PAGE_SIZE);
    ops.read_from_partition_sync("boot_a", 0, boot_header_buffer)?;
    let boot_header = BootImage::parse(boot_header_buffer).map_err(Error::from)?;
    let (kernel_size, cmdline, kernel_hdr_size, boot_ramdisk_size, boot_second_size, boot_dtb_size) =
        boot_header_elements(&boot_header)?;
    gbl_println!(ops, "boot image size: {}", kernel_size);
    gbl_println!(ops, "boot image cmdline: \"{}\"", from_utf8(cmdline).unwrap());
    gbl_println!(ops, "boot ramdisk size: {}", boot_ramdisk_size);
    gbl_println!(ops, "boot dtb size: {}", boot_dtb_size);

    // Parse vendor boot header.
    let (vendor_boot_header_buffer, load) = load.split_at_mut(PAGE_SIZE);
    ops.read_from_partition_sync("vendor_boot_a", 0, vendor_boot_header_buffer)?;
    let vendor_boot_header =
        VendorImageHeader::parse(vendor_boot_header_buffer).map_err(Error::from)?;
    let (vendor_ramdisk_size, vendor_hdr_size, vendor_cmdline, vendor_page_size, vendor_dtb_size) =
        vendor_header_elements(&vendor_boot_header)?;
    gbl_println!(ops, "vendor ramdisk size: {}", vendor_ramdisk_size);
    gbl_println!(ops, "vendor cmdline: \"{}\"", from_utf8(vendor_cmdline).unwrap());
    gbl_println!(ops, "vendor dtb size: {}", vendor_dtb_size);

    let (dtbo_buffer, load) = match ops.partition_size("dtbo_a") {
        Ok(Some(sz)) => {
            let (dtbo_buffer, load) =
                aligned_subslice(load, FDT_ALIGNMENT)?.split_at_mut(sz.try_into().unwrap());
            ops.read_from_partition_sync("dtbo_a", 0, dtbo_buffer)?;
            (Some(dtbo_buffer), load)
        }
        _ => (None, load),
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
    ops.read_from_partition_sync(
        "vendor_boot_a",
        u64::try_from(vendor_hdr_size).map_err(Error::from)?,
        &mut load[ramdisk_load_curr.try_into().map_err(Error::from)?..][..vendor_ramdisk_size],
    )?;
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
    if let VendorImageHeader::V4(ref hdr) = vendor_boot_header {
        let mut bootconfig_offset = SafeNum::from(vendor_hdr_size);
        for image_size in
            [hdr._base.vendor_ramdisk_size, hdr._base.dtb_size, hdr.vendor_ramdisk_table_size]
        {
            bootconfig_offset += SafeNum::from(image_size).round_up(hdr._base.page_size);
        }
        bootconfig_builder.add_with(|out| {
            ops.read_from_partition_sync(
                "vendor_boot_a",
                bootconfig_offset.try_into()?,
                &mut out[..hdr.bootconfig_size as usize],
            )?;
            Ok(hdr.bootconfig_size as usize)
        })?;
    }
    // Check if there is a device specific bootconfig partition.
    match ops.partition_size("bootconfig") {
        Ok(Some(sz)) => {
            bootconfig_builder.add_with(|out| {
                // For proof-of-concept only, we just load as much as possible and figure out the
                // actual bootconfig string length after. This however, can introduce large amount
                // of unnecessary disk access. In real implementation, we might want to either read
                // page by page or find way to know the actual length first.
                let max_size = core::cmp::min(sz.try_into().unwrap(), out.len());
                ops.read_from_partition_sync("bootconfig", 0, &mut out[..max_size])?;
                // Compute the actual config string size. The config is a null-terminated string.
                Ok(CStr::from_bytes_until_nul(&out[..])
                    .or(Err(Error::InvalidInput))?
                    .to_bytes()
                    .len())
            })?;
        }
        _ => {}
    }
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

    // Prepare FDT.

    // For cuttlefish, FDT comes from EFI vendor configuration table installed by u-boot. In real
    // product, it may come from vendor boot image.
    let mut fdt_bytes_buffer = vec![0u8; max(vendor_dtb_size, boot_dtb_size)];
    let fdt_bytes_buffer = &mut fdt_bytes_buffer[..];
    let fdt_bytes = match ops.get_custom_device_tree() {
        Some(fdt_bytes) => fdt_bytes,
        None if vendor_dtb_size > 0 => {
            let vendor_dtb_offset: usize = (SafeNum::from(vendor_hdr_size)
                + SafeNum::from(vendor_ramdisk_size))
            .round_up(vendor_page_size)
            .try_into()
            .map_err(Error::from)?;
            gbl_println!(
                ops,
                "Loading vendor_boot dtb size {} at {}",
                vendor_dtb_size,
                vendor_dtb_offset
            );
            let fdt_bytes = &mut fdt_bytes_buffer[..vendor_dtb_size.try_into().unwrap()];
            ops.read_from_partition_sync(
                "vendor_boot_a",
                vendor_dtb_offset.try_into().unwrap(),
                fdt_bytes,
            )?;
            fdt_bytes
        }
        None if boot_dtb_size > 0 => {
            let mut boot_dtb_offset = SafeNum::from(kernel_hdr_size);
            for image_size in [kernel_size, boot_ramdisk_size, boot_second_size] {
                boot_dtb_offset += SafeNum::from(image_size).round_up(kernel_hdr_size);
            }
            let fdt_bytes = &mut fdt_bytes_buffer[..boot_dtb_size.try_into().unwrap()];
            ops.read_from_partition_sync("boot_a", boot_dtb_offset.try_into().unwrap(), fdt_bytes)?;
            fdt_bytes
        }
        None => &mut [],
    };
    let fdt_origin = Fdt::new(fdt_bytes)?;

    // Use the remaining load buffer for updating FDT.
    let (ramdisk_load_buffer, load) =
        load.split_at_mut(ramdisk_load_curr.try_into().map_err(Error::from)?);
    let load = aligned_subslice(load, FDT_ALIGNMENT)?;
    let mut fdt = Fdt::new_from_init(&mut load[..], fdt_bytes)?;

    // Add ramdisk range to FDT
    let ramdisk_addr: u64 =
        (ramdisk_load_buffer.as_ptr() as usize).try_into().map_err(Error::from)?;
    let ramdisk_end: u64 =
        ramdisk_addr + u64::try_from(ramdisk_load_buffer.len()).map_err(Error::from)?;
    fdt.set_property("chosen", c"linux,initrd-start", &ramdisk_addr.to_be_bytes())?;
    fdt.set_property("chosen", c"linux,initrd-end", &ramdisk_end.to_be_bytes())?;
    gbl_println!(ops, "linux,initrd-start: {:#x}", ramdisk_addr);
    gbl_println!(ops, "linux,initrd-end: {:#x}", ramdisk_end);

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
    gbl_println!(ops, "final cmdline: \"{}\"", from_utf8(cmdline_payload).unwrap());

    // Finalize FDT to actual used size.
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

// The following implements a demo for booting Android from disk. It can be run from
// Cuttlefish by adding `--android_efi_loader=<path of this EFI binary>` to the command line.
//
// A number of simplifications are made (see `android_load::load_android_simple()`):
//
//   * No A/B slot switching is performed. It always boot from *_a slot.
//   * No AVB is performed.
//   * No dynamic partitions.
//   * Only support V3/V4 image and Android 13+ (generic ramdisk from the "init_boot" partition)
//
// The missing pieces above are currently under development as part of the full end-to-end boot
// flow in libgbl, which will eventually replace this demo. The demo is currently used as an
// end-to-end test for libraries developed so far.
pub fn android_boot_demo(entry: EfiEntry) -> Result<()> {
    let mut blks = find_block_devices(&entry)?;
    let partitions = &blks.as_gbl_parts()?;
    let mut ops = Ops { efi_entry: &entry, partitions };

    gbl_println!(ops, "Try booting as Android");

    // Allocate buffer for load.
    let mut load_buffer = vec![0u8; 128 * 1024 * 1024]; // 128MB

    let (ramdisk, fdt, kernel, remains) = load_android_simple(&mut ops, &mut load_buffer[..])?;

    gbl_println!(ops, "");
    gbl_println!(
        ops,
        "Booting kernel @ {:#x}, ramdisk @ {:#x}, fdt @ {:#x}",
        kernel.as_ptr() as usize,
        ramdisk.as_ptr() as usize,
        fdt.as_ptr() as usize
    );
    gbl_println!(ops, "");

    #[cfg(target_arch = "aarch64")]
    {
        drop(blks); // Drop `blks` to release the borrow on `entry`.
        let _ = exit_boot_services(entry, remains)?;
        // SAFETY: We currently targets at Cuttlefish emulator where images are provided valid.
        unsafe { boot::aarch64::jump_linux_el2_or_lower(kernel, ramdisk, fdt) };
    }

    #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
    {
        let fdt = fdt::Fdt::new(&fdt[..])?;
        drop(blks); // Drop `blks` to release the borrow on `entry`.
        let efi_mmap = exit_boot_services(entry, remains)?;
        // SAFETY: We currently target at Cuttlefish emulator where images are provided valid.
        unsafe {
            boot::x86::boot_linux_bzimage(
                kernel,
                ramdisk,
                fdt.get_property(
                    "chosen",
                    core::ffi::CStr::from_bytes_with_nul(b"bootargs\0").unwrap(),
                )
                .unwrap(),
                |e820_entries| {
                    // Convert EFI memory type to e820 memory type.
                    if efi_mmap.len() > e820_entries.len() {
                        return Err(Error::MemoryMapCallbackError(-1));
                    }
                    for (idx, mem) in efi_mmap.into_iter().enumerate() {
                        e820_entries[idx] = boot::x86::e820entry {
                            addr: mem.physical_start,
                            size: mem.number_of_pages * 4096,
                            type_: crate::utils::efi_to_e820_mem_type(mem.memory_type),
                        };
                    }
                    Ok(efi_mmap.len().try_into().unwrap())
                },
                0x9_0000,
            )?;
        }
        unreachable!();
    }

    #[cfg(target_arch = "riscv64")]
    {
        let boot_hart_id = entry
            .system_table()
            .boot_services()
            .find_first_and_open::<efi::protocol::riscv::RiscvBootProtocol>()?
            .get_boot_hartid()?;
        gbl_println!(ops, "riscv boot_hart_id: {}", boot_hart_id);
        drop(blks); // Drop `blks` to release the borrow on `entry`.
        let _ = exit_boot_services(entry, remains)?;
        // SAFETY: We currently target at Cuttlefish emulator where images are provided valid.
        unsafe { boot::riscv64::jump_linux(kernel, boot_hart_id, fdt) };
    }
}
