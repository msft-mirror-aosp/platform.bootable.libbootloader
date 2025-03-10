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

use super::{avb_verify_slot, cstr_bytes_to_str};
use crate::{
    android_boot::PartitionsToVerify,
    constants::{FDT_ALIGNMENT, KERNEL_ALIGNMENT, PAGE_SIZE},
    decompress::{decompress_kernel, is_compressed},
    gbl_print, gbl_println,
    ops::GblOps,
    partition::RAW_PARTITION_NAME_LEN,
    IntegrationError,
};
use arrayvec::ArrayString;
use bootimg::{defs::*, BootImage, VendorImageHeader};
use bootparams::bootconfig::BootConfigBuilder;
use core::{
    array,
    ffi::CStr,
    fmt::Write,
    ops::{Deref, Range},
};
use liberror::Error;
use libutils::aligned_subslice;
use safemath::SafeNum;
use zerocopy::{IntoBytes, Ref};

// Represents a slot suffix.
struct SlotSuffix([u8; 3]);

impl SlotSuffix {
    // Creates a new instance.
    fn new(slot: u8) -> Result<Self, Error> {
        let suffix = u32::from(slot) + u32::from(b'a');
        match char::from_u32(suffix).map(|v| v.is_ascii_lowercase()) {
            Some(true) => Ok(Self([b'_', suffix.try_into().unwrap(), 0])),
            _ => Err(Error::Other(Some("Invalid slot index"))),
        }
    }

    // Casts as CStr.
    fn as_cstr(&self) -> &CStr {
        CStr::from_bytes_with_nul(&self.0[..]).unwrap()
    }
}

impl Deref for SlotSuffix {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_cstr().to_str().unwrap()
    }
}

/// Returns a slotted partition name.
fn slotted_part(part: &str, slot: u8) -> Result<ArrayString<RAW_PARTITION_NAME_LEN>, Error> {
    let mut res = ArrayString::new_const();
    write!(res, "{}{}", part, &SlotSuffix::new(slot)? as &str).unwrap();
    Ok(res)
}

// Helper for constructing a range that ends at a page aligned boundary. Specifically, it returns
// `start..round_up(start + sz, page_size)`
fn page_aligned_range(
    start: impl Into<SafeNum>,
    sz: impl Into<SafeNum>,
    page_size: impl Into<SafeNum>,
) -> Result<Range<usize>, Error> {
    let start = start.into();
    Ok(start.try_into()?..(start + sz.into()).round_up(page_size.into()).try_into()?)
}

/// Represents a loaded boot image of version 2 and lower.
///
/// TODO(b/384964561): Investigate if the APIs are better suited for bootimg.rs. The issue
/// is that it uses `Error` and `SafeNum` from GBL.
struct BootImageV2Info<'a> {
    cmdline: &'a str,
    page_size: usize,
    kernel_range: Range<usize>,
    ramdisk_range: Range<usize>,
    dtb_range: Range<usize>,
    // Actual dtb size without padding.
    //
    // We need to know the exact size because the fdt buffer will be passed to
    // `DeviceTreeComponentsRegistry::append` which assumes that the buffer contains concatenated
    // device trees and will try to parse for additional device trees if the preivous one doesn't
    // consume all buffer.
    dtb_sz: usize,
    image_size: usize,
}

impl<'a> BootImageV2Info<'a> {
    /// Creates a new instance.
    fn new(buffer: &'a [u8]) -> Result<Self, Error> {
        let header = BootImage::parse(buffer)?;
        if matches!(header, BootImage::V3(_) | BootImage::V4(_)) {
            return Err(Error::InvalidInput);
        }
        // This is valid since v1/v2 are superset of v0.
        let v0 = Ref::into_ref(Ref::<_, boot_img_hdr_v0>::from_prefix(&buffer[..]).unwrap().0);
        let page_size: usize = v0.page_size.try_into()?;
        let cmdline = cstr_bytes_to_str(&v0.cmdline[..])?;
        let kernel_range = page_aligned_range(page_size, v0.kernel_size, page_size)?;
        let ramdisk_range = page_aligned_range(kernel_range.end, v0.ramdisk_size, page_size)?;
        let second_range = page_aligned_range(ramdisk_range.end, v0.second_size, page_size)?;

        let start = u64::try_from(second_range.end)?;
        let (off, sz) = match header {
            BootImage::V1(v) => (v.recovery_dtbo_offset, v.recovery_dtbo_size),
            BootImage::V2(v) => (v._base.recovery_dtbo_offset, v._base.recovery_dtbo_size),
            _ => (start, 0),
        };
        let recovery_dtb_range = match off >= start {
            true => page_aligned_range(off, sz, page_size)?,
            _ if off == 0 => page_aligned_range(start, 0, page_size)?,
            _ => return Err(Error::Other(Some("Unexpected recovery_dtbo_offset"))),
        };
        let dtb_sz: usize = match header {
            BootImage::V2(v) => v.dtb_size.try_into().unwrap(),
            _ => 0,
        };
        let dtb_range = page_aligned_range(recovery_dtb_range.end, dtb_sz, page_size)?;
        let image_size = dtb_range.end;
        Ok(Self { cmdline, page_size, kernel_range, ramdisk_range, dtb_range, dtb_sz, image_size })
    }
}

// Contains information of a V3/V4 boot image.
struct BootImageV3Info {
    kernel_range: Range<usize>,
    ramdisk_range: Range<usize>,
    image_size: usize,
}

impl BootImageV3Info {
    /// Creates a new instance.
    fn new(buffer: &[u8]) -> Result<Self, Error> {
        let header = BootImage::parse(buffer)?;
        if !matches!(header, BootImage::V3(_) | BootImage::V4(_)) {
            return Err(Error::InvalidInput);
        }
        let v3 = Self::v3(buffer);
        let kernel_range = page_aligned_range(PAGE_SIZE, v3.kernel_size, PAGE_SIZE)?;
        let ramdisk_range = page_aligned_range(kernel_range.end, v3.ramdisk_size, PAGE_SIZE)?;
        let sz = match header {
            BootImage::V4(v) => v.signature_size,
            _ => 0,
        };
        let signature_range = page_aligned_range(ramdisk_range.end, sz, PAGE_SIZE)?;
        let image_size = signature_range.end;

        Ok(Self { kernel_range, ramdisk_range, image_size })
    }

    /// Gets the v3 base header.
    fn v3(buffer: &[u8]) -> &boot_img_hdr_v3 {
        // This is valid since v4 is superset of v3.
        Ref::into_ref(Ref::from_prefix(&buffer[..]).unwrap().0)
    }

    // Decodes the kernel cmdline
    fn cmdline(buffer: &[u8]) -> Result<&str, Error> {
        cstr_bytes_to_str(&Self::v3(buffer).cmdline[..])
    }
}

/// Contains vendor boot image information.
struct VendorBootImageInfo {
    header_size: usize,
    ramdisk_range: Range<usize>,
    dtb_range: Range<usize>,
    // Actual dtb size without padding.
    //
    // We need to know the exact size because the fdt buffer will be passed to
    // `DeviceTreeComponentsRegistry::append` which assumes that the buffer contains concatenated
    // device trees and will try to parse for additional device trees if the preivous one doesn't
    // consume all buffer.
    dtb_sz: usize,
    bootconfig_range: Range<usize>,
    image_size: usize,
}

impl VendorBootImageInfo {
    /// Creates a new instance.
    fn new(buffer: &[u8]) -> Result<Self, Error> {
        let header = VendorImageHeader::parse(buffer)?;
        let v3 = Self::v3(buffer);
        let page_size = v3.page_size;
        let header_size = match header {
            VendorImageHeader::V3(hdr) => SafeNum::from(hdr.as_bytes().len()),
            VendorImageHeader::V4(hdr) => SafeNum::from(hdr.as_bytes().len()),
        }
        .round_up(page_size)
        .try_into()?;
        let ramdisk_range = page_aligned_range(header_size, v3.vendor_ramdisk_size, page_size)?;
        let dtb_sz: usize = v3.dtb_size.try_into().unwrap();
        let dtb_range = page_aligned_range(ramdisk_range.end, dtb_sz, page_size)?;

        let (table_sz, bootconfig_sz) = match header {
            VendorImageHeader::V4(hdr) => (hdr.vendor_ramdisk_table_size, hdr.bootconfig_size),
            _ => (0, 0),
        };
        let table = page_aligned_range(dtb_range.end, table_sz, page_size)?;
        let bootconfig_range = table.end..(table.end + usize::try_from(bootconfig_sz)?);
        let image_size = SafeNum::from(bootconfig_range.end).round_up(page_size).try_into()?;
        Ok(Self { header_size, ramdisk_range, dtb_range, dtb_sz, bootconfig_range, image_size })
    }

    /// Gets the v3 base header.
    fn v3(buffer: &[u8]) -> &vendor_boot_img_hdr_v3 {
        Ref::into_ref(Ref::<_, _>::from_prefix(&buffer[..]).unwrap().0)
    }

    // Decodes the vendor cmdline
    fn cmdline(buffer: &[u8]) -> Result<&str, Error> {
        cstr_bytes_to_str(&Self::v3(buffer).cmdline[..])
    }
}

/// Contains various loaded image components by `android_load_verify`
pub struct LoadedImages<'a> {
    /// dtbo image.
    pub dtbo: &'a mut [u8],
    /// Kernel commandline.
    pub boot_cmdline: &'a str,
    /// Vendor commandline,
    pub vendor_cmdline: &'a str,
    /// DTB.
    pub dtb: &'a mut [u8],
    /// DTB from partition.
    pub dtb_part: &'a mut [u8],
    /// Kernel image.
    pub kernel: &'a mut [u8],
    /// Ramdisk image.
    pub ramdisk: &'a mut [u8],
    /// Unused portion. Can be used by the caller to construct FDT.
    pub unused: &'a mut [u8],
}

impl<'a> Default for LoadedImages<'a> {
    fn default() -> LoadedImages<'a> {
        LoadedImages {
            dtbo: &mut [][..],
            boot_cmdline: "",
            vendor_cmdline: "",
            dtb: &mut [][..],
            dtb_part: &mut [][..],
            kernel: &mut [][..],
            ramdisk: &mut [][..],
            unused: &mut [][..],
        }
    }
}

/// Loads and verifies Android images of the given slot.
pub fn android_load_verify<'a, 'b, 'c>(
    ops: &mut impl GblOps<'a, 'b>,
    slot: u8,
    is_recovery: bool,
    load: &'c mut [u8],
) -> Result<LoadedImages<'c>, IntegrationError> {
    let mut res = LoadedImages::default();

    let slot_suffix = SlotSuffix::new(slot)?;
    // Additional partitions loaded before loading standard boot images.
    let mut partitions = PartitionsToVerify::default();

    // Loads dtbo.
    let dtbo_part = slotted_part("dtbo", slot)?;
    let (dtbo, remains) = load_entire_part(ops, &dtbo_part, &mut load[..])?;
    if dtbo.len() > 0 {
        partitions.try_push_preloaded(c"dtbo", &dtbo[..])?;
    }

    // Loads dtb.
    let remains = aligned_subslice(remains, FDT_ALIGNMENT)?;
    let dtb_part = slotted_part("dtb", slot)?;
    let (dtb, remains) = load_entire_part(ops, &dtb_part, &mut remains[..])?;
    if dtb.len() > 0 {
        partitions.try_push_preloaded(c"dtb", &dtb[..])?;
    }

    let add = |v: &mut BootConfigBuilder| {
        if !is_recovery {
            v.add("androidboot.force_normal_boot=1\n")?;
        }
        Ok(write!(v, "androidboot.slot_suffix={}\n", &slot_suffix as &str)?)
    };

    // Loads boot image header and inspect version
    ops.read_from_partition_sync(&slotted_part("boot", slot)?, 0, &mut remains[..PAGE_SIZE])?;
    match BootImage::parse(&remains[..]).map_err(Error::from)? {
        BootImage::V3(_) | BootImage::V4(_) => {
            load_verify_v3_and_v4(ops, slot, &partitions, add, &mut res, remains)?
        }
        _ => load_verify_v2_and_lower(ops, slot, &partitions, add, &mut res, remains)?,
    };

    drop(partitions);
    res.dtbo = dtbo;
    res.dtb_part = dtb;
    Ok(res)
}

/// Loads and verifies android boot images of version 0, 1 and 2.
///
/// * Both kernel and ramdisk come from the boot image.
/// * vendor_boot, init_boot are irrelevant.
///
/// # Args
///
/// * `ops`: An implementation of [GblOps].
/// * `slot`: slot index.
/// * `additional_partitions`: Additional partitions for verification.
/// * `out`: A `&mut LoadedImages` for output.
/// * `load`: The load buffer. The boot header must be preloaded into this buffer.
fn load_verify_v2_and_lower<'a, 'b, 'c>(
    ops: &mut impl GblOps<'a, 'b>,
    slot: u8,
    additional_partitions: &PartitionsToVerify,
    add_additional_bootconfig: impl FnOnce(&mut BootConfigBuilder) -> Result<(), Error>,
    out: &mut LoadedImages<'c>,
    load: &'c mut [u8],
) -> Result<(), IntegrationError> {
    // Loads boot image.
    let boot_size = BootImageV2Info::new(load).unwrap().image_size;
    let boot_part = slotted_part("boot", slot)?;
    let (boot, remains) = split(load, boot_size)?;
    ops.read_from_partition_sync(&boot_part, 0, boot)?;

    // Performs libavb verification.

    // Prepares a BootConfigBuilder to add avb generated bootconfig.
    let mut bootconfig_builder = BootConfigBuilder::new(remains)?;
    // Puts in a subscope for auto dropping `to_verify`, so that the slices it
    // borrows can be released.
    {
        let mut to_verify = PartitionsToVerify::default();
        to_verify.try_push_preloaded(c"boot", &boot[..])?;
        to_verify.try_extend_preloaded(additional_partitions)?;
        avb_verify_slot(ops, slot, &to_verify, &mut bootconfig_builder)?;
    }

    // Adds platform-specific bootconfig.
    bootconfig_builder.add_with(|bytes, out| {
        Ok(ops.fixup_bootconfig(&bytes, out)?.map(|slice| slice.len()).unwrap_or(0))
    })?;
    add_additional_bootconfig(&mut bootconfig_builder)?;
    let bootconfig_size = bootconfig_builder.config_bytes().len();

    // We now have the following layout:
    //
    // | boot_hdr | kernel | ramdisk | second | recovery_dtb | dtb | bootconfig | remains |
    // |------------------------------`boot_ex`---------------------------------|
    //
    // We need to:
    // 1. move bootconfig to after ramdisk.
    // 2. relocate the kernel to the tail so that all memory after it can be used as scratch memory.
    //    It is observed that riscv kernel reaches into those memory and overwrites data.
    //
    // TODO(b/384964561): Investigate if `second`, `recovery_dtb` needs to be kept.
    let (boot_ex, remains) = load.split_at_mut(boot_size + bootconfig_size);
    let boot_img = BootImageV2Info::new(boot_ex).unwrap();
    let page_size = boot_img.page_size;
    let dtb_sz = boot_img.dtb_sz;
    // Relocates kernel to tail.
    let kernel_range = boot_img.kernel_range;
    let kernel = boot_ex.get(kernel_range.clone()).unwrap();
    let (remains, _, kernel_sz) = relocate_kernel(ops, kernel, remains)?;
    // Relocates dtb to tail.
    let dtb_range = boot_img.dtb_range;
    let (_, dtb) = split_aligned_tail(remains, dtb_range.len(), FDT_ALIGNMENT)?;
    dtb[..dtb_range.len()].clone_from_slice(boot_ex.get(dtb_range).unwrap());
    // Move ramdisk forward and bootconfig following it.
    let ramdisk_range = boot_img.ramdisk_range;
    boot_ex.copy_within(ramdisk_range.start..ramdisk_range.end, kernel_range.start);
    boot_ex.copy_within(boot_size.., kernel_range.start + ramdisk_range.len());

    // We now have the following layout:
    // | boot_hdr | ramdisk + bootconfig | unused | dtb | kernel |
    let ramdisk_sz = ramdisk_range.len() + bootconfig_size;
    let unused_sz = slice_offset(dtb, boot_ex) - page_size - ramdisk_sz;
    let dtb_padding = dtb.len() - dtb_sz;
    let hdr;
    ([hdr, out.ramdisk, out.unused, out.dtb, _, out.kernel], _) =
        split_chunks(load, &[page_size, ramdisk_sz, unused_sz, dtb_sz, dtb_padding, kernel_sz]);
    out.boot_cmdline = BootImageV2Info::new(hdr).unwrap().cmdline;
    Ok(())
}

/// Loads and verifies android boot images of version 3 and 4.
///
/// V3, V4 images have the following characteristics:
///
/// * Kernel comes from "boot_a/b" partition.
/// * Generic ramdisk may come from either "boot_a/b" or "init_boot_a/b" partitions.
/// * Vendor ramdisk comes from "vendor_boot_a/b" partition.
/// * V4 vendor_boot contains additional bootconfig.
///
/// From the perspective of Android versions:
///
/// Android 11:
///
/// * Can use v3 header.
/// * Generic ramdisk is in the "boot_a/b" partitions.
///
/// Android 12:
///
/// * Can use v3 or v4 header.
/// * Generic ramdisk is in the "boot_a/b" partitions.
///
/// Android 13:
///
/// * Can use v3 or v4 header.
/// * Generic ramdisk is in the "init_boot_a/b" partitions.
///
/// # References
///
/// https://source.android.com/docs/core/architecture/bootloader/boot-image-header
/// https://source.android.com/docs/core/architecture/partitions/vendor-boot-partitions
/// https://source.android.com/docs/core/architecture/partitions/generic-boot
///
/// # Args
///
/// * `ops`: An implementation of [GblOps].
/// * `slot`: slot index.
/// * `additional_partitions`: Additional partitions for verification.
/// * `out`: A `&mut LoadedImages` for output.
/// * `load`: The load buffer. The boot header must be preloaded into this buffer.
fn load_verify_v3_and_v4<'a, 'b, 'c>(
    ops: &mut impl GblOps<'a, 'b>,
    slot: u8,
    additional_partitions: &PartitionsToVerify,
    add_additional_bootconfig: impl FnOnce(&mut BootConfigBuilder) -> Result<(), Error>,
    out: &mut LoadedImages<'c>,
    load: &'c mut [u8],
) -> Result<(), IntegrationError> {
    // Creates a `start` marker for `slice_offset()` to compute absolute slice offset later.
    let (start, load) = load.split_at_mut(0);

    let boot_part = slotted_part("boot", slot)?;
    let vendor_boot_part = slotted_part("vendor_boot", slot)?;
    let init_boot_part = slotted_part("init_boot", slot)?;

    let boot_img_info = BootImageV3Info::new(load).unwrap();

    // Loads vendor boot image.
    ops.read_from_partition_sync(&vendor_boot_part, 0, &mut load[..PAGE_SIZE])?;
    let vendor_boot_info = VendorBootImageInfo::new(&load[..PAGE_SIZE])?;
    let (vendor_boot, remains) = split(&mut load[..], vendor_boot_info.image_size)?;
    ops.read_from_partition_sync(&vendor_boot_part, 0, vendor_boot)?;

    // Loads boot image.
    let (boot, remains) = split(remains, boot_img_info.image_size)?;
    ops.read_from_partition_sync(&boot_part, 0, boot)?;

    // Loads init_boot image if boot doesn't contain a ramdisk.
    let (init_boot, remains, init_boot_info) = match boot_img_info.ramdisk_range.len() > 0 {
        false => {
            ops.read_from_partition_sync(&init_boot_part, 0, &mut remains[..PAGE_SIZE])?;
            let init_boot_info = BootImageV3Info::new(&remains[..])?;
            let (out, remains) = split(remains, init_boot_info.image_size)?;
            ops.read_from_partition_sync(&init_boot_part, 0, out)?;
            (out, remains, Some(init_boot_info))
        }
        _ => (&mut [][..], remains, None),
    };

    // Performs libavb verification.

    // Prepares a BootConfigBuilder to add avb generated bootconfig.
    let mut bootconfig_builder = BootConfigBuilder::new(remains)?;
    // Puts in a subscope for auto dropping `to_verify`, so that the slices it
    // borrows can be released.
    {
        let mut to_verify = PartitionsToVerify::default();
        to_verify.try_push_preloaded(c"boot", &boot)?;
        to_verify.try_push_preloaded(c"vendor_boot", &vendor_boot)?;
        if init_boot.len() > 0 {
            to_verify.try_push_preloaded(c"init_boot", &init_boot)?;
        }
        to_verify.try_extend_preloaded(additional_partitions)?;
        avb_verify_slot(ops, slot, &to_verify, &mut bootconfig_builder)?;
    }

    // Adds platform-specific bootconfig.
    bootconfig_builder.add_with(|bytes, out| {
        Ok(ops.fixup_bootconfig(&bytes, out)?.map(|slice| slice.len()).unwrap_or(0))
    })?;
    add_additional_bootconfig(&mut bootconfig_builder)?;

    // We now have the following layout:
    //
    // +------------------------+
    // | vendor boot header     |
    // +------------------------+
    // | vendor ramdisk         |
    // +------------------------+
    // | dtb                    |
    // +------------------------+
    // | vendor ramdisk table   |
    // +------------------------+
    // | vendor bootconfig      |
    // +------------------------+    +------------------------+
    // | boot hdr               |    | boot hdr               |
    // +------------------------+    +------------------------+
    // | kernel                 |    | kernel                 |
    // +------------------------+    +------------------------+
    // |                        |    | boot signature         |
    // |                        | or +------------------------+
    // | generic ramdisk        |    | init_boot hdr          |
    // |                        |    +------------------------+
    // |                        |    | generic ramdisk        |
    // +------------------------+    +------------------------+
    // | boot signature         |    | boot signature         |
    // +------------------------+    +------------------------+
    // | avb + board bootconfig |
    // +------------------------+
    // | unused                 |
    // +------------------------+
    //
    // We need to:
    // * Relocate kernel to the tail of the load buffer to reserve all memory after it for scratch.
    // * Relocates dtb, boot hdr to elsewhere.
    // * Move generic ramdisk to follow vendor ramdisk.
    // * Move vendor bootconfig, avb + board bootconfig to follow generic ramdisk.

    // Appends vendor bootconfig so that the section can be discarded.
    let vendor_bootconfig = vendor_boot.get(vendor_boot_info.bootconfig_range).unwrap();
    bootconfig_builder.add_with(|_, out| {
        out.get_mut(..vendor_bootconfig.len())
            .ok_or(Error::BufferTooSmall(Some(vendor_bootconfig.len())))?
            .clone_from_slice(vendor_bootconfig);
        Ok(vendor_bootconfig.len())
    })?;
    let bootconfig_size = bootconfig_builder.config_bytes().len();
    let (bootconfig, remains) = remains.split_at_mut(bootconfig_size);

    // Relocates kernel to tail.
    let kernel = boot.get(boot_img_info.kernel_range.clone()).unwrap();
    let (remains, kernel, kernel_sz) = relocate_kernel(ops, kernel, remains)?;
    let kernel_buf_len = kernel.len();

    // Relocates boot header to tail.
    let (remains, boot_hdr) = split_aligned_tail(remains, PAGE_SIZE, 1)?;
    boot_hdr.clone_from_slice(&boot[..PAGE_SIZE]);
    let boot_hdr_sz = boot_hdr.len();

    // Relocates dtb to tail.
    let dtb = vendor_boot.get(vendor_boot_info.dtb_range).unwrap();
    let (_, dtb_reloc) = split_aligned_tail(remains, dtb.len(), FDT_ALIGNMENT)?;
    dtb_reloc[..dtb.len()].clone_from_slice(dtb);
    let dtb_sz = vendor_boot_info.dtb_sz;
    let dtb_pad = dtb_reloc.len() - dtb_sz;

    // Moves generic ramdisk and bootconfig forward
    let generic_ramdisk_range = match init_boot_info {
        Some(v) => offset_range(v.ramdisk_range, slice_offset(init_boot, start)),
        _ => offset_range(boot_img_info.ramdisk_range, slice_offset(boot, start)),
    };
    let vendor_ramdisk_range = vendor_boot_info.ramdisk_range;
    let bootconfig_range = offset_range(0..bootconfig_size, slice_offset(bootconfig, start));
    load.copy_within(generic_ramdisk_range.clone(), vendor_ramdisk_range.end);
    load.copy_within(bootconfig_range, vendor_ramdisk_range.end + generic_ramdisk_range.len());
    let ramdisk_sz = vendor_ramdisk_range.len() + generic_ramdisk_range.len() + bootconfig_size;

    // We now have the following layout:
    //
    // +------------------------+
    // | vendor boot header     |
    // +------------------------+
    // | vendor ramdisk         |
    // +------------------------+
    // | generic ramdisk        |
    // +------------------------+
    // | vendor bootconfig      |
    // +------------------------+
    // | avb + board bootconfig |
    // +------------------------+
    // | unused                 |
    // +------------------------+
    // | dtb                    |
    // +------------------------+
    // | boot hdr               |
    // +------------------------+
    // | kernel                 |
    // +------------------------+
    //
    // Splits out the images and returns.
    let vendor_hdr_sz = vendor_boot_info.header_size;
    let unused_sz =
        load.len() - vendor_hdr_sz - ramdisk_sz - boot_hdr_sz - dtb_sz - dtb_pad - kernel_buf_len;
    let (vendor_hdr, boot_hdr);
    ([vendor_hdr, out.ramdisk, out.unused, out.dtb, _, boot_hdr, out.kernel], _) = split_chunks(
        load,
        &[vendor_hdr_sz, ramdisk_sz, unused_sz, dtb_sz, dtb_pad, boot_hdr_sz, kernel_sz],
    );
    out.boot_cmdline = BootImageV3Info::cmdline(boot_hdr)?;
    out.vendor_cmdline = VendorBootImageInfo::cmdline(vendor_hdr)?;
    Ok(())
}

// A helper for calculating the relative offset of `buf` to `src`.
fn slice_offset(buf: &[u8], src: &[u8]) -> usize {
    (buf.as_ptr() as usize).checked_sub(src.as_ptr() as usize).unwrap()
}

/// Wrapper of `split_at_mut_checked` with error conversion.
fn split(buffer: &mut [u8], size: usize) -> Result<(&mut [u8], &mut [u8]), Error> {
    buffer.split_at_mut_checked(size).ok_or(Error::BufferTooSmall(Some(size)))
}

/// Split buffer from the tail with the given alignment such that the buffer is at least `size`
/// bytes.
fn split_aligned_tail(
    buffer: &mut [u8],
    size: usize,
    align: usize,
) -> Result<(&mut [u8], &mut [u8]), Error> {
    let off = SafeNum::from(buffer.len()) - size;
    let rem = buffer[off.try_into()?..].as_ptr() as usize % align;
    split(buffer, usize::try_from(off - rem)?)
}

/// Splits a buffer into multiple chunks of the given sizes.
///
/// Returns an array of slices corresponding to the given sizes and the remaining slice.
pub(super) fn split_chunks<'a, const N: usize>(
    buf: &'a mut [u8],
    sizes: &[usize; N],
) -> ([&'a mut [u8]; N], &'a mut [u8]) {
    let mut chunks: [_; N] = array::from_fn(|_| &mut [][..]);
    let mut remains = buf;
    for (i, ele) in sizes.iter().enumerate() {
        (chunks[i], remains) = remains.split_at_mut(*ele);
    }
    (chunks, remains)
}

/// Helper for loading entire partition.
///
/// * Returns the loaded slice and the remaining slice.
/// * If the partition doesn't exist, an empty loaded slice is returned.
fn load_entire_part<'a, 'b, 'c>(
    ops: &mut impl GblOps<'a, 'b>,
    part: &str,
    load: &'c mut [u8],
) -> Result<(&'c mut [u8], &'c mut [u8]), Error> {
    match ops.partition_size(&part)? {
        Some(sz) => {
            let sz = sz.try_into()?;
            gbl_println!(ops, "Found {} partition.", &part);
            let (out, remains) = split(load, sz)?;
            ops.read_from_partition_sync(&part, 0, out)?;
            Ok((out, remains))
        }
        _ => {
            gbl_println!(ops, "Partition {} doesn't exist. Skip loading.", &part);
            Ok((&mut [][..], &mut load[..]))
        }
    }
}

/// A helper function for relocating and decompressing kernel to a different buffer.
///
/// The relocated kernel will be place at the tail.
///
/// Returns the leading unused slice, the relocated slice and the actual kernel size without
/// alignment padding.
fn relocate_kernel<'a, 'b, 'c>(
    ops: &mut impl GblOps<'a, 'b>,
    kernel: &[u8],
    dst: &'c mut [u8],
) -> Result<(&'c mut [u8], &'c mut [u8], usize), Error> {
    if is_compressed(kernel) {
        split(dst, kernel.len())?.0.clone_from_slice(kernel);
        let off = decompress_kernel(ops, dst, 0)?;
        let (leading, relocated) = dst.split_at_mut(off);
        let kernel_size = relocated.len();
        Ok((leading, relocated, kernel_size))
    } else {
        let (prefix, tail) = split_aligned_tail(dst, kernel.len(), KERNEL_ALIGNMENT)?;
        tail[..kernel.len()].clone_from_slice(kernel);
        Ok((prefix, tail, kernel.len()))
    }
}

// Adds offset to a given range i.e. [start+off, end+off)
fn offset_range(lhs: Range<usize>, off: usize) -> Range<usize> {
    lhs.start.checked_add(off).unwrap()..lhs.end.checked_add(off).unwrap()
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::{
        gbl_avb::state::{BootStateColor, KeyValidationStatus},
        ops::test::{FakeGblOps, FakeGblOpsStorage},
        tests::AlignedBuffer,
    };
    use bootparams::bootconfig::BOOTCONFIG_TRAILER_SIZE;
    use std::{
        ascii::escape_default, collections::HashMap, ffi::CString, fs, path::Path, string::String,
    };

    // See libgbl/testdata/gen_test_data.py for test data generation.
    const TEST_ROLLBACK_INDEX_LOCATION: usize = 1;

    // The commandline in the generated vendor boot image.
    // See libgbl/testdata/gen_test_data.py for test data generation.
    const TEST_VENDOR_CMDLINE: &str =
        "cmd_vendor_key_1=cmd_vendor_val_1,cmd_vendor_key_2=cmd_vendor_val_2";
    // The vendor bootconfig in the generated vendor boot image.
    // See libgbl/testdata/gen_test_data.py for test data generation.
    pub(crate) const TEST_VENDOR_BOOTCONFIG: &str =
        "androidboot.config_1=val_1\x0aandroidboot.config_2=val_2\x0a";

    /// Digest of public key used to execute AVB.
    pub(crate) const TEST_PUBLIC_KEY_DIGEST: &str =
        "7ec02ee1be696366f3fa91240a8ec68125c4145d698f597aa2b3464b59ca7fc3";

    // Test data path
    const TEST_DATA_PATH: &str = "external/gbl/libgbl/testdata/android";

    /// Reads a data file under libgbl/testdata/
    pub(crate) fn read_test_data(file: impl AsRef<str>) -> Vec<u8> {
        println!("reading file: {}", file.as_ref());
        fs::read(Path::new(format!("{TEST_DATA_PATH}/{}", file.as_ref()).as_str())).unwrap()
    }

    /// Reads a data file as string under libgbl/testdata/
    pub(crate) fn read_test_data_as_str(file: impl AsRef<str>) -> String {
        fs::read_to_string(Path::new(format!("{TEST_DATA_PATH}/{}", file.as_ref()).as_str()))
            .unwrap()
    }

    // Returns the test dtb
    fn test_dtb() -> Vec<u8> {
        read_test_data("device_tree.dtb")
    }

    /// Generates a readable string for a bootconfig bytes.
    pub(crate) fn dump_bootconfig(data: &[u8]) -> String {
        let s = data.iter().map(|v| escape_default(*v).to_string()).collect::<Vec<_>>().concat();
        let s = s.split("\\\\").collect::<Vec<_>>().join("\\");
        s.split("\\n").collect::<Vec<_>>().join("\n")
    }

    /// A helper for assert checking ramdisk binary and bootconfig separately.
    pub(crate) fn check_ramdisk(ramdisk: &[u8], expected_bin: &[u8], expected_bootconfig: &[u8]) {
        let (ramdisk, bootconfig) = ramdisk.split_at(expected_bin.len());
        assert_eq!(ramdisk, expected_bin);
        assert_eq!(
            bootconfig,
            expected_bootconfig,
            "\nexpect: \n{}\nactual: \n{}\n",
            dump_bootconfig(expected_bootconfig),
            dump_bootconfig(bootconfig),
        );
    }

    /// Helper for testing load/verify and assert verfiication success.
    fn test_android_load_verify_success(
        slot: u8,
        partitions: &[(CString, String)],
        expected_kernel: &[u8],
        expected_ramdisk: &[u8],
        expected_bootconfig: &[u8],
        expected_dtb: &[u8],
        expected_dtbo: &[u8],
        expected_vendor_cmdline: &str,
    ) {
        let mut storage = FakeGblOpsStorage::default();
        for (part, file) in partitions {
            storage.add_raw_device(part, read_test_data(file));
        }
        let mut ops = FakeGblOps::new(&storage);
        ops.avb_ops.unlock_state = Ok(false);
        ops.avb_ops.rollbacks = HashMap::from([(TEST_ROLLBACK_INDEX_LOCATION, Ok(0))]);
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
        let loaded = android_load_verify(&mut ops, slot, false, &mut load_buffer).unwrap();

        assert_eq!(loaded.dtb, expected_dtb);
        assert_eq!(out_color, Some(BootStateColor::Green));
        assert_eq!(loaded.boot_cmdline, "cmd_key_1=cmd_val_1,cmd_key_2=cmd_val_2");
        assert_eq!(loaded.vendor_cmdline, expected_vendor_cmdline);
        assert_eq!(loaded.kernel, expected_kernel);
        assert_eq!(loaded.dtbo, expected_dtbo);
        check_ramdisk(loaded.ramdisk, expected_ramdisk, expected_bootconfig);
    }

    /// A helper for generating avb bootconfig with the given parameters.
    pub(crate) struct AvbResultBootconfigBuilder {
        vbmeta_size: usize,
        digest: String,
        boot_digest: Option<String>,
        init_boot_digest: Option<String>,
        dtb_digest: Option<String>,
        dtbo_digest: Option<String>,
        vendor_boot_digest: Option<String>,
        public_key_digest: String,
        color: BootStateColor,
        unlocked: bool,
        extra: String,
    }

    impl AvbResultBootconfigBuilder {
        pub(crate) fn new() -> Self {
            Self {
                vbmeta_size: 0,
                digest: String::new(),
                boot_digest: None,
                init_boot_digest: None,
                dtb_digest: None,
                dtbo_digest: None,
                vendor_boot_digest: None,
                public_key_digest: String::new(),
                color: BootStateColor::Green,
                unlocked: false,
                extra: String::new(),
            }
        }

        pub(crate) fn vbmeta_size(mut self, size: usize) -> Self {
            self.vbmeta_size = size;
            self
        }

        pub(crate) fn digest(mut self, digest: impl Into<String>) -> Self {
            self.digest = digest.into();
            self
        }

        pub(crate) fn partition_digest(mut self, name: &str, digest: impl Into<String>) -> Self {
            let digest = Some(digest.into());
            match name {
                "boot" => self.boot_digest = digest,
                "init_boot" => self.init_boot_digest = digest,
                "vendor_boot" => self.vendor_boot_digest = digest,
                "dtb" => self.dtb_digest = digest,
                "dtbo" => self.dtbo_digest = digest,
                _ => panic!("unknown digest name requested"),
            };
            self
        }

        pub(crate) fn public_key_digest(mut self, pk_digest: impl Into<String>) -> Self {
            self.public_key_digest = pk_digest.into();
            self
        }

        pub(crate) fn color(mut self, color: BootStateColor) -> Self {
            self.color = color;
            self
        }

        pub(crate) fn unlocked(mut self, unlocked: bool) -> Self {
            self.unlocked = unlocked;
            self
        }

        pub(crate) fn extra(mut self, extra: impl Into<String>) -> Self {
            self.extra += &extra.into();
            self
        }

        pub(crate) fn build_string(self) -> String {
            let device_state = match self.unlocked {
                true => "unlocked",
                false => "locked",
            };

            let mut boot_digests = String::new();
            for (name, maybe_digest) in [
                ("boot", &self.boot_digest),
                ("dtb", &self.dtb_digest),
                ("dtbo", &self.dtbo_digest),
                ("init_boot", &self.init_boot_digest),
                ("vendor_boot", &self.vendor_boot_digest),
            ] {
                if let Some(digest) = maybe_digest {
                    boot_digests += format!(
                        "androidboot.vbmeta.{name}.hash_alg=sha256
androidboot.vbmeta.{name}.digest={digest}\n"
                    )
                    .as_str()
                }
            }

            format!(
                "androidboot.vbmeta.device=PARTUUID=00000000-0000-0000-0000-000000000000
androidboot.vbmeta.public_key_digest={}
androidboot.vbmeta.avb_version=1.3
androidboot.vbmeta.device_state={}
androidboot.vbmeta.hash_alg=sha512
androidboot.vbmeta.size={}
androidboot.vbmeta.digest={}
androidboot.vbmeta.invalidate_on_error=yes
androidboot.veritymode=enforcing
{}androidboot.verifiedbootstate={}
{}",
                self.public_key_digest,
                device_state,
                self.vbmeta_size,
                self.digest,
                boot_digests.as_str(),
                self.color,
                self.extra
            )
        }

        pub(crate) fn build(self) -> Vec<u8> {
            make_bootconfig(self.build_string())
        }
    }

    // A helper for generating expected bootconfig.
    pub(crate) fn make_bootconfig(bootconfig: impl AsRef<str>) -> Vec<u8> {
        let bootconfig = bootconfig.as_ref();
        let mut buffer = vec![0u8; bootconfig.len() + BOOTCONFIG_TRAILER_SIZE];
        let mut res = BootConfigBuilder::new(&mut buffer).unwrap();
        res.add_with(|_, out| {
            out[..bootconfig.len()].clone_from_slice(bootconfig.as_bytes());
            Ok(bootconfig.as_bytes().len())
        })
        .unwrap();
        res.config_bytes().to_vec()
    }

    pub(crate) struct MakeExpectedBootconfigInclude {
        pub boot: bool,
        pub init_boot: bool,
        pub vendor_boot: bool,
        pub dtb: bool,
        pub dtbo: bool,
    }

    impl MakeExpectedBootconfigInclude {
        fn is_include_str(&self, name: &str) -> bool {
            match name {
                "boot" => self.boot,
                "init_boot" => self.init_boot,
                "vendor_boot" => self.vendor_boot,
                "dtb" => self.dtb,
                "dtbo" => self.dtbo,
                _ => false,
            }
        }
    }

    impl Default for MakeExpectedBootconfigInclude {
        fn default() -> MakeExpectedBootconfigInclude {
            MakeExpectedBootconfigInclude {
                boot: true,
                init_boot: true,
                vendor_boot: true,
                dtb: true,
                dtbo: true,
            }
        }
    }

    /// Helper for generating expected bootconfig after load and verification.
    pub(crate) fn make_expected_bootconfig(
        vbmeta_file: &str,
        slot: char,
        vendor_config: &str,
        include: MakeExpectedBootconfigInclude,
    ) -> Vec<u8> {
        let vbmeta_file = Path::new(vbmeta_file);
        let vbmeta_digest = vbmeta_file.with_extension("digest.txt");
        let vbmeta_digest = vbmeta_digest.to_str().unwrap();
        let mut builder = AvbResultBootconfigBuilder::new()
            .vbmeta_size(read_test_data(vbmeta_file.to_str().unwrap()).len())
            .digest(read_test_data_as_str(vbmeta_digest).strip_suffix("\n").unwrap())
            .public_key_digest(TEST_PUBLIC_KEY_DIGEST)
            .extra(FakeGblOps::GBL_TEST_BOOTCONFIG)
            .extra("androidboot.force_normal_boot=1\n")
            .extra(format!("androidboot.slot_suffix=_{slot}\n"))
            .extra(vendor_config);

        for name in ["boot", "vendor_boot", "init_boot", "dtbo", "dtb"].iter() {
            let file = vbmeta_file.with_extension(format!("{name}.digest.txt"));
            println!("{file:?}");
            if include.is_include_str(name)
                && Path::new(format!("{TEST_DATA_PATH}/{}", file.to_str().unwrap()).as_str())
                    .exists()
            {
                builder = builder.partition_digest(
                    name,
                    read_test_data_as_str(file.to_str().unwrap()).strip_suffix("\n").unwrap(),
                );
            }
        }

        builder.build()
    }

    /// Helper for testing load/verify for a/b slot v0,1,2 image with dtbo partition.
    ///
    /// # Args
    ///
    /// * `ver`: Boot image version.
    /// * `slot`: Target slot to boot.
    /// * `additional_part`: A list of pair `(partition name, file name)` representing additional
    ///   partitions for creating boot storage.
    /// * `expected_dtb`: The expected DTB.
    /// * `expected_dtbo`: The expected DTBO.
    fn test_android_load_verify_v2_and_lower_slot(
        ver: u8,
        slot: char,
        additional_part: &[(CString, String)],
        expected_dtb: &[u8],
        expected_dtbo: &[u8],
    ) {
        let dtbo =
            additional_part.iter().any(|(name, _)| name.to_str().unwrap().starts_with("dtbo_"));
        let vbmeta = format!("vbmeta_v{ver}_{slot}.img");
        let boot = format!("boot_v{ver}_{slot}.img");
        let mut parts: Vec<(CString, String)> = vec![
            (CString::new(format!("boot_{slot}")).unwrap(), boot.clone()),
            (CString::new(format!("vbmeta_{slot}")).unwrap(), vbmeta.clone()),
        ];
        parts.extend_from_slice(additional_part);

        test_android_load_verify_success(
            (u64::from(slot) - ('a' as u64)).try_into().unwrap(),
            &parts,
            &read_test_data(format!("kernel_{slot}.img")),
            &read_test_data(format!("generic_ramdisk_{slot}.img")),
            &make_expected_bootconfig(
                &vbmeta,
                slot,
                "",
                MakeExpectedBootconfigInclude { dtbo, dtb: false, ..Default::default() },
            ),
            expected_dtb,
            expected_dtbo,
            "",
        );
    }

    #[test]
    fn test_android_load_verify_v0_slot_a() {
        test_android_load_verify_v2_and_lower_slot(0, 'a', &[], &[], &[])
    }

    #[test]
    fn test_android_load_verify_v0_slot_b() {
        test_android_load_verify_v2_and_lower_slot(0, 'b', &[], &[], &[]);
    }

    #[test]
    fn test_android_load_verify_v1_slot_a() {
        test_android_load_verify_v2_and_lower_slot(1, 'a', &[], &[], &[])
    }

    #[test]
    fn test_android_load_verify_v1_slot_b() {
        test_android_load_verify_v2_and_lower_slot(1, 'b', &[], &[], &[]);
    }

    #[test]
    fn test_android_load_verify_v2_slot_a() {
        test_android_load_verify_v2_and_lower_slot(2, 'a', &[], &test_dtb(), &[])
    }

    #[test]
    fn test_android_load_verify_v2_slot_b() {
        test_android_load_verify_v2_and_lower_slot(2, 'b', &[], &test_dtb(), &[]);
    }

    fn test_android_load_verify_v2_and_lower_slot_with_dtbo(
        ver: u8,
        slot: char,
        expected_dtb: &[u8],
    ) {
        let dtbo = read_test_data(format!("dtbo_{slot}.img"));
        let parts: Vec<(CString, String)> =
            vec![(CString::new(format!("dtbo_{slot}")).unwrap(), format!("dtbo_{slot}.img"))];
        test_android_load_verify_v2_and_lower_slot(ver, slot, &parts, expected_dtb, &dtbo);
    }

    #[test]
    fn test_android_load_verify_v0_slot_a_with_dtbo() {
        test_android_load_verify_v2_and_lower_slot_with_dtbo(0, 'a', &[])
    }

    #[test]
    fn test_android_load_verify_v0_slot_b_with_dtbo() {
        test_android_load_verify_v2_and_lower_slot_with_dtbo(0, 'b', &[]);
    }

    #[test]
    fn test_android_load_verify_v1_slot_a_with_dtbo() {
        test_android_load_verify_v2_and_lower_slot_with_dtbo(1, 'a', &[])
    }

    #[test]
    fn test_android_load_verify_v1_slot_b_with_dtbo() {
        test_android_load_verify_v2_and_lower_slot_with_dtbo(1, 'b', &[]);
    }

    #[test]
    fn test_android_load_verify_v2_slot_a_with_dtbo() {
        test_android_load_verify_v2_and_lower_slot_with_dtbo(2, 'a', &test_dtb())
    }

    #[test]
    fn test_android_load_verify_v2_slot_b_with_dtbo() {
        test_android_load_verify_v2_and_lower_slot_with_dtbo(2, 'b', &test_dtb());
    }

    /// Helper for testing load/verify for v3/v4 boot/vendor_boot images.
    ///
    /// # Args
    ///
    /// * `partitions`: A list of pair `(partition name, file name)` for creating boot storage.
    /// * `vbmeta_file`: The vbmeta file for the storage. Used for constructing expected bootconfig.
    /// * `expected_digest`: The expected digest outputed by vbmeta.
    /// * `expected_vendor_bootconfig`: The expected vendor_boot_config.
    fn test_android_load_verify_v3_and_v4(
        slot: char,
        partitions: &[(CString, String)],
        vbmeta: &str,
        expected_vendor_bootconfig: &str,
        expected_dtbo: &[u8],
    ) {
        let dtbo = partitions.iter().any(|(name, _)| name.to_str().unwrap().starts_with("dtbo_"));
        test_android_load_verify_success(
            (u64::from(slot) - ('a' as u64)).try_into().unwrap(),
            partitions,
            &read_test_data(format!("kernel_{slot}.img")),
            &[
                read_test_data(format!("vendor_ramdisk_{slot}.img")),
                read_test_data(format!("generic_ramdisk_{slot}.img")),
            ]
            .concat(),
            &make_expected_bootconfig(
                &vbmeta,
                slot,
                expected_vendor_bootconfig,
                MakeExpectedBootconfigInclude { dtbo, dtb: false, ..Default::default() },
            ),
            &test_dtb(),
            expected_dtbo,
            TEST_VENDOR_CMDLINE,
        );
    }

    /// Helper for testing v3/v4 boot image without init_boot partition.
    fn test_android_load_verify_boot_v3_v4_slot_no_init_boot(
        slot: char,
        boot_ver: u32,
        vendor_ver: u32,
        additional_part: &[(CString, String)],
        expected_vendor_bootconfig: &str,
        expected_dtbo: &[u8],
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
        parts.extend_from_slice(additional_part);
        test_android_load_verify_v3_and_v4(
            slot,
            &parts[..],
            &vbmeta,
            expected_vendor_bootconfig,
            expected_dtbo,
        );
    }

    /// Helper for testing v3/v4 boot image with init_boot partition.
    fn test_android_load_verify_boot_v3_v4_slot_init_boot(
        slot: char,
        boot_ver: u32,
        vendor_ver: u32,
        additional_part: &[(CString, String)],
        expected_vendor_bootconfig: &str,
        expected_dtbo: &[u8],
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
        parts.extend_from_slice(additional_part);
        test_android_load_verify_v3_and_v4(
            slot,
            &parts[..],
            &vbmeta,
            expected_vendor_bootconfig,
            expected_dtbo,
        );
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v3_no_init_boot_slot_a() {
        test_android_load_verify_boot_v3_v4_slot_no_init_boot('a', 3, 3, &[], "", &[])
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v3_no_init_boot_slot_b() {
        test_android_load_verify_boot_v3_v4_slot_no_init_boot('b', 3, 3, &[], "", &[])
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v3_init_boot_slot_a() {
        test_android_load_verify_boot_v3_v4_slot_init_boot('a', 3, 3, &[], "", &[])
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v3_init_boot_slot_b() {
        test_android_load_verify_boot_v3_v4_slot_init_boot('b', 3, 3, &[], "", &[])
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v4_no_init_boot_slot_a() {
        test_android_load_verify_boot_v3_v4_slot_no_init_boot(
            'a',
            3,
            4,
            &[],
            TEST_VENDOR_BOOTCONFIG,
            &[],
        )
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v4_no_init_boot_slot_b() {
        test_android_load_verify_boot_v3_v4_slot_no_init_boot(
            'b',
            3,
            4,
            &[],
            TEST_VENDOR_BOOTCONFIG,
            &[],
        )
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v4_init_boot_slot_a() {
        test_android_load_verify_boot_v3_v4_slot_init_boot(
            'a',
            3,
            4,
            &[],
            TEST_VENDOR_BOOTCONFIG,
            &[],
        )
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v4_init_boot_slot_b() {
        test_android_load_verify_boot_v3_v4_slot_init_boot(
            'b',
            3,
            4,
            &[],
            TEST_VENDOR_BOOTCONFIG,
            &[],
        )
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v3_no_init_boot_slot_a() {
        test_android_load_verify_boot_v3_v4_slot_no_init_boot('a', 4, 3, &[], "", &[])
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v3_no_init_boot_slot_b() {
        test_android_load_verify_boot_v3_v4_slot_no_init_boot('b', 4, 3, &[], "", &[])
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v3_init_boot_slot_a() {
        test_android_load_verify_boot_v3_v4_slot_init_boot('a', 4, 3, &[], "", &[])
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v3_init_boot_slot_b() {
        test_android_load_verify_boot_v3_v4_slot_init_boot('b', 4, 3, &[], "", &[])
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v4_no_init_boot_slot_a() {
        test_android_load_verify_boot_v3_v4_slot_no_init_boot(
            'a',
            4,
            4,
            &[],
            TEST_VENDOR_BOOTCONFIG,
            &[],
        )
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v4_no_init_boot_slot_b() {
        test_android_load_verify_boot_v3_v4_slot_no_init_boot(
            'b',
            4,
            4,
            &[],
            TEST_VENDOR_BOOTCONFIG,
            &[],
        )
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v4_init_boot_slot_a() {
        test_android_load_verify_boot_v3_v4_slot_init_boot(
            'a',
            4,
            4,
            &[],
            TEST_VENDOR_BOOTCONFIG,
            &[],
        )
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v4_init_boot_slot_b() {
        test_android_load_verify_boot_v3_v4_slot_init_boot(
            'b',
            4,
            4,
            &[],
            TEST_VENDOR_BOOTCONFIG,
            &[],
        )
    }

    /// Same as `test_android_load_verify_boot_v3_v4_slot_no_init_boot` but with dtbo partition.
    fn test_android_load_verify_boot_v3_v4_slot_no_init_boot_with_dtbo(
        slot: char,
        boot_ver: u32,
        vendor_ver: u32,
        expected_vendor_bootconfig: &str,
    ) {
        let dtbo = read_test_data(format!("dtbo_{slot}.img"));
        let parts: Vec<(CString, String)> =
            vec![(CString::new(format!("dtbo_{slot}")).unwrap(), format!("dtbo_{slot}.img"))];
        test_android_load_verify_boot_v3_v4_slot_no_init_boot(
            slot,
            boot_ver,
            vendor_ver,
            &parts,
            expected_vendor_bootconfig,
            &dtbo,
        );
    }

    /// Same as `test_android_load_verify_boot_v3_v4_slot_init_boot` but with dtbo partition.
    fn test_android_load_verify_boot_v3_v4_slot_init_boot_with_dtbo(
        slot: char,
        boot_ver: u32,
        vendor_ver: u32,
        expected_vendor_bootconfig: &str,
    ) {
        let dtbo = read_test_data(format!("dtbo_{slot}.img"));
        let parts: Vec<(CString, String)> =
            vec![(CString::new(format!("dtbo_{slot}")).unwrap(), format!("dtbo_{slot}.img"))];
        test_android_load_verify_boot_v3_v4_slot_init_boot(
            slot,
            boot_ver,
            vendor_ver,
            &parts,
            expected_vendor_bootconfig,
            &dtbo,
        );
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v3_no_init_boot_slot_a_with_dtbo() {
        test_android_load_verify_boot_v3_v4_slot_no_init_boot_with_dtbo('a', 3, 3, "")
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v3_no_init_boot_slot_b_with_dtbo() {
        test_android_load_verify_boot_v3_v4_slot_no_init_boot_with_dtbo('b', 3, 3, "")
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v3_init_boot_slot_a_with_dtbo() {
        test_android_load_verify_boot_v3_v4_slot_init_boot_with_dtbo('a', 3, 3, "")
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v3_init_boot_slot_b_with_dtbo() {
        test_android_load_verify_boot_v3_v4_slot_init_boot_with_dtbo('b', 3, 3, "")
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v4_no_init_boot_slot_a_with_dtbo() {
        test_android_load_verify_boot_v3_v4_slot_no_init_boot_with_dtbo(
            'a',
            3,
            4,
            TEST_VENDOR_BOOTCONFIG,
        )
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v4_no_init_boot_slot_b_with_dtbo() {
        test_android_load_verify_boot_v3_v4_slot_no_init_boot_with_dtbo(
            'b',
            3,
            4,
            TEST_VENDOR_BOOTCONFIG,
        )
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v4_init_boot_slot_a_with_dtbo() {
        test_android_load_verify_boot_v3_v4_slot_init_boot_with_dtbo(
            'a',
            3,
            4,
            TEST_VENDOR_BOOTCONFIG,
        )
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v4_init_boot_slot_b_with_dtbo() {
        test_android_load_verify_boot_v3_v4_slot_init_boot_with_dtbo(
            'b',
            3,
            4,
            TEST_VENDOR_BOOTCONFIG,
        )
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v3_no_init_boot_slot_a_with_dtbo() {
        test_android_load_verify_boot_v3_v4_slot_no_init_boot_with_dtbo('a', 4, 3, "")
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v3_no_init_boot_slot_b_with_dtbo() {
        test_android_load_verify_boot_v3_v4_slot_no_init_boot_with_dtbo('b', 4, 3, "")
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v3_init_boot_slot_a_with_dtbo() {
        test_android_load_verify_boot_v3_v4_slot_init_boot_with_dtbo('a', 4, 3, "")
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v3_init_boot_slot_b_with_dtbo() {
        test_android_load_verify_boot_v3_v4_slot_init_boot_with_dtbo('b', 4, 3, "")
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v4_no_init_boot_slot_a_with_dtbo() {
        test_android_load_verify_boot_v3_v4_slot_no_init_boot_with_dtbo(
            'a',
            4,
            4,
            TEST_VENDOR_BOOTCONFIG,
        )
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v4_no_init_boot_slot_b_with_dtbo() {
        test_android_load_verify_boot_v3_v4_slot_no_init_boot_with_dtbo(
            'b',
            4,
            4,
            TEST_VENDOR_BOOTCONFIG,
        )
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v4_init_boot_slot_a_with_dtbo() {
        test_android_load_verify_boot_v3_v4_slot_init_boot_with_dtbo(
            'a',
            4,
            4,
            TEST_VENDOR_BOOTCONFIG,
        )
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v4_init_boot_slot_b_with_dtbo() {
        test_android_load_verify_boot_v3_v4_slot_init_boot_with_dtbo(
            'b',
            4,
            4,
            TEST_VENDOR_BOOTCONFIG,
        )
    }
}
