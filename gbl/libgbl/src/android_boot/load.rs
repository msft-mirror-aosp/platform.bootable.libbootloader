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

use super::cstr_bytes_to_str;
use crate::{
    constants::{FDT_ALIGNMENT, KERNEL_ALIGNMENT},
    decompress::{decompress_kernel, is_compressed},
    gbl_avb::{ops::GblAvbOps, state::BootStateColor},
    gbl_print, gbl_println,
    ops::GblOps,
    partition::RAW_PARTITION_NAME_LEN,
    IntegrationError,
};
use arrayvec::{ArrayString, ArrayVec};
use avb::{slot_verify, HashtreeErrorMode, SlotVerifyFlags};
use bootimg::{defs::*, BootImage, VendorImageHeader};
use bootparams::{bootconfig::BootConfigBuilder, entry::CommandlineParser};
use core::{
    array,
    ffi::CStr,
    fmt::Write,
    ops::{Deref, Range},
};
use liberror::Error;
use safemath::SafeNum;
use zerocopy::{IntoBytes, Ref};

// Value of page size for v3/v4 header.
const PAGE_SIZE: usize = 4096;

// Maximum number of partition allowed for verification.
//
// The value is randomly chosen for now. We can update it as we see more usecases.
const MAX_NUM_PARTITION: usize = 16;

// Type alias for ArrayVec of size `MAX_NUM_PARTITION`:
type ArrayMaxParts<T> = ArrayVec<T, MAX_NUM_PARTITION>;

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
        let dtb_sz = match header {
            BootImage::V2(v) => v.dtb_size,
            _ => 0,
        };
        let dtb_range = page_aligned_range(recovery_dtb_range.end, dtb_sz, page_size)?;
        let image_size = dtb_range.end;
        Ok(Self { cmdline, page_size, kernel_range, ramdisk_range, dtb_range, image_size })
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
        let dtb_range = page_aligned_range(ramdisk_range.end, v3.dtb_size, page_size)?;

        let (table_sz, bootconfig_sz) = match header {
            VendorImageHeader::V4(hdr) => (hdr.vendor_ramdisk_table_size, hdr.bootconfig_size),
            _ => (0, 0),
        };
        let table = page_aligned_range(dtb_range.end, table_sz, page_size)?;
        let bootconfig_range = table.end..(table.end + usize::try_from(bootconfig_sz)?);
        let image_size = SafeNum::from(bootconfig_range.end).round_up(page_size).try_into()?;
        Ok(Self { header_size, ramdisk_range, dtb_range, bootconfig_range, image_size })
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
    load: &'c mut [u8],
) -> Result<LoadedImages<'c>, IntegrationError> {
    let mut res = LoadedImages::default();

    // Loads dtbo.
    let dtbo_part = slotted_part("dtbo", slot)?;
    let (dtbo, remains) = load_entire_part(ops, &dtbo_part, &mut load[..])?;

    // Additional partitions loaded before loading standard boot images.
    let mut parts = ArrayVec::<_, 1>::new();
    let mut preloaded = ArrayVec::<_, 1>::new();
    if dtbo.len() > 0 {
        parts.push(c"dtbo");
        preloaded.push((&dtbo_part as &str, &dtbo[..]));
    }

    // Loads boot image header and inspect version
    ops.read_from_partition_sync(&slotted_part("boot", slot)?, 0, &mut remains[..PAGE_SIZE])?;
    match BootImage::parse(&remains[..]).map_err(Error::from)? {
        BootImage::V3(_) | BootImage::V4(_) => {
            load_verify_v3_and_v4(ops, slot, &parts, &preloaded, &mut res, remains)?
        }
        _ => load_verify_v2_and_lower(ops, slot, &parts, &preloaded, &mut res, remains)?,
    };

    drop(parts);
    drop(preloaded);
    res.dtbo = dtbo;
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
/// * `additional_parts`: Additional partitions for verification.
/// * `additional_preloaded`: Additional preloaded images.
/// * `out`: A `&mut LoadedImages` for output.
/// * `load`: The load buffer. The boot header must be preloaded into this buffer.
fn load_verify_v2_and_lower<'a, 'b, 'c>(
    ops: &mut impl GblOps<'a, 'b>,
    slot: u8,
    additional_parts: &[&CStr],
    additional_preloaded: &[(&str, &[u8])],
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
    // Puts in a subscope for auto dropping `to_verify` and `preload`, so that the slices they
    // borrow can be released.
    {
        // Prepares partitions and preloaded images
        let err = || IntegrationError::from(Error::TooManyPartitions(MAX_NUM_PARTITION));
        let mut to_verify = ArrayMaxParts::try_from(additional_parts).map_err(|_| err())?;
        let mut preloaded = ArrayMaxParts::try_from(additional_preloaded).map_err(|_| err())?;
        to_verify.try_push(c"boot").map_err(|_| err())?;
        preloaded.try_push((&boot_part, &boot[..])).map_err(|_| err())?;
        avb_verify_slot(ops, slot, &to_verify[..], &preloaded[..], &mut bootconfig_builder)?;
    }

    // Adds platform-specific bootconfig.
    bootconfig_builder.add_with(|bytes, out| {
        Ok(ops.fixup_bootconfig(&bytes, out)?.map(|slice| slice.len()).unwrap_or(0))
    })?;
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
    // Relocates kernel to tail.
    let kernel_range = boot_img.kernel_range;
    let kernel = boot_ex.get(kernel_range.clone()).unwrap();
    let (remains, _) = relocate_kernel(ops, kernel, remains)?;
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
    let dtb_sz = dtb.len();
    let hdr;
    ([hdr, out.ramdisk, out.unused, out.dtb], out.kernel) =
        split_chunks(load, &[page_size, ramdisk_sz, unused_sz, dtb_sz]);
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
/// * `additional_parts`: Additional partitions for verification.
/// * `additional_preloaded`: Additional preloaded images.
/// * `out`: A `&mut LoadedImages` for output.
/// * `load`: The load buffer. The boot header must be preloaded into this buffer.
fn load_verify_v3_and_v4<'a, 'b, 'c>(
    ops: &mut impl GblOps<'a, 'b>,
    slot: u8,
    additional_parts: &[&CStr],
    additional_preloaded: &[(&str, &[u8])],
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
    // Puts in a subscope for auto dropping `to_verify` and `preload`, so that the slices they
    // borrow can be released.
    {
        // Prepares partitions and preloaded images
        let err = || IntegrationError::from(Error::TooManyPartitions(MAX_NUM_PARTITION));
        let mut to_verify = ArrayMaxParts::try_from(additional_parts).map_err(|_| err())?;
        let mut preloaded = ArrayMaxParts::try_from(additional_preloaded).map_err(|_| err())?;
        to_verify.try_extend_from_slice(&[c"boot", c"vendor_boot"]).map_err(|_| err())?;
        preloaded.try_push((&boot_part as _, &boot[..])).map_err(|_| err())?;
        preloaded.try_push((&vendor_boot_part as _, &vendor_boot[..])).map_err(|_| err())?;
        if init_boot.len() > 0 {
            to_verify.try_push(c"init_boot").map_err(|_| err())?;
            preloaded.try_push((&init_boot_part, &init_boot[..])).map_err(|_| err())?;
        }
        avb_verify_slot(ops, slot, &to_verify[..], &preloaded[..], &mut bootconfig_builder)?;
    }

    // Adds platform-specific bootconfig.
    bootconfig_builder.add_with(|bytes, out| {
        Ok(ops.fixup_bootconfig(&bytes, out)?.map(|slice| slice.len()).unwrap_or(0))
    })?;

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
    let (remains, kernel) = relocate_kernel(ops, kernel, remains)?;
    let kernel_sz = kernel.len();

    // Relocates boot header to tail.
    let (remains, boot_hdr) = split_aligned_tail(remains, PAGE_SIZE, 1)?;
    boot_hdr.clone_from_slice(&boot[..PAGE_SIZE]);
    let boot_hdr_sz = boot_hdr.len();

    // Relocates dtb to tail.
    let dtb = vendor_boot.get(vendor_boot_info.dtb_range).unwrap();
    let (_, dtb_reloc) = split_aligned_tail(remains, dtb.len(), FDT_ALIGNMENT)?;
    dtb_reloc[..dtb.len()].clone_from_slice(dtb);
    let dtb_sz = dtb_reloc.len();

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
    let unused_sz = load.len() - vendor_hdr_sz - ramdisk_sz - boot_hdr_sz - dtb_sz - kernel_sz;
    let (vendor_hdr, boot_hdr);
    ([vendor_hdr, out.ramdisk, out.unused, out.dtb, boot_hdr], out.kernel) =
        split_chunks(load, &[vendor_hdr_sz, ramdisk_sz, unused_sz, dtb_sz, boot_hdr_sz]);
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
fn split_chunks<'a, const N: usize>(
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
            gbl_println!(ops, "Partition {} doesn't exist.", &part);
            Ok((&mut [][..], &mut load[..]))
        }
    }
}

/// A helper function for relocating and decompressing kernel to a different buffer.
///
/// The relocated kernel will be place at the tail.
///
/// Returns the leading unused slice and the relocated slice.
fn relocate_kernel<'a, 'b, 'c>(
    ops: &mut impl GblOps<'a, 'b>,
    kernel: &[u8],
    dst: &'c mut [u8],
) -> Result<(&'c mut [u8], &'c mut [u8]), Error> {
    if is_compressed(kernel) {
        split(dst, kernel.len())?.0.clone_from_slice(kernel);
        let off = decompress_kernel(ops, dst, 0)?;
        Ok(dst.split_at_mut(off))
    } else {
        let (prefix, tail) = split_aligned_tail(dst, kernel.len(), KERNEL_ALIGNMENT)?;
        tail[..kernel.len()].clone_from_slice(kernel);
        Ok((prefix, tail))
    }
}

// Adds offset to a given range i.e. [start+off, end+off)
fn offset_range(lhs: Range<usize>, off: usize) -> Range<usize> {
    lhs.start.checked_add(off).unwrap()..lhs.end.checked_add(off).unwrap()
}

/// Helper for performing AVB verification.
///
/// TODO(b/384964561): This is a temporary placeholder for testing. A production version of this
/// API is under development in libgbl/src/android_boot/vboot.rs, which will replace this one.
///
/// # Args
///
/// * `ops`: An implementation of GblOps.
/// * `slot`: The slot index.
/// * `parts_to_verify`: List of partitions to verify.
/// * `preloaded`: Preloaded partitions.
/// * `bootconfig_builder`: A [BootConfigBuilder] for libavb to add avb bootconfig.
fn avb_verify_slot<'a, 'b, 'c>(
    ops: &'c mut impl GblOps<'a, 'b>,
    slot: u8,
    partitions: &[&CStr],
    preloaded: &'c [(&'c str, &'c [u8])],
    bootconfig_builder: &mut BootConfigBuilder,
) -> Result<(), IntegrationError> {
    let mut avb_ops = GblAvbOps::new(ops, preloaded, false);
    let res = slot_verify(
        &mut avb_ops,
        partitions,
        Some(SlotSuffix::new(slot)?.as_cstr()),
        SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_NONE,
        HashtreeErrorMode::AVB_HASHTREE_ERROR_MODE_RESTART_AND_INVALIDATE,
    )
    .map_err(|e| IntegrationError::from(e.without_verify_data()))?;

    for entry in CommandlineParser::new(res.cmdline().to_str().unwrap()) {
        write!(bootconfig_builder, "{}\n", entry?).or(Err(Error::BufferTooSmall(None)))?;
    }

    avb_ops.handle_verification_result(Some(&res), BootStateColor::Green, None)?;

    // Append "androidboot.verifiedbootstate="
    write!(bootconfig_builder, "androidboot.verifiedbootstate={}\n", BootStateColor::Green)
        .or(Err(Error::BufferTooSmall(None)))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        gbl_avb::state::KeyValidationStatus,
        ops::test::{FakeGblOps, FakeGblOpsStorage},
        tests::AlignedBuffer,
    };
    use bootparams::bootconfig::BOOTCONFIG_TRAILER_SIZE;
    use std::{ascii::escape_default, collections::HashMap, fs, path::Path, string::String};

    // See libgbl/testdata/gen_test_data.py for test data generation.
    const TEST_ROLLBACK_INDEX_LOCATION: usize = 1;

    // The DTB in the test mkbootimg images.
    // See libgbl/testdata/gen_test_data.py for test data generation.
    const BASE_DTB: &[u8] = include_bytes!("../../../libfdt/test/data/base.dtb");

    // The commandline in the generated vendor boot image.
    // See libgbl/testdata/gen_test_data.py for test data generation.
    const TEST_VENDOR_CMDLINE: &str =
        "cmd_vendor_key_1=cmd_vendor_val_1,cmd_vendor_key_1=cmd_vendor_val_1";
    // The vendor bootconfig in the generated vendor boot image.
    // See libgbl/testdata/gen_test_data.py for test data generation.
    const TEST_VENDOR_BOOTCONFIG: &str =
        "androidboot.config_1=val_1\x0aandroidboot.config_2=val_2\x0a";

    // Digest of public key used to execute AVB.
    const TEST_PUBLIC_KEY_DIGEST: &str =
        "7ec02ee1be696366f3fa91240a8ec68125c4145d698f597aa2b3464b59ca7fc3";

    /// Reads a data file under libgbl/testdata/
    fn read_test_data(file: impl AsRef<str>) -> Vec<u8> {
        println!("reading file: {}", file.as_ref());
        fs::read(Path::new(
            format!("external/gbl/libgbl/testdata/android/{}", file.as_ref()).as_str(),
        ))
        .unwrap()
    }

    /// Generates a readable string for a bootconfig bytes.
    fn dump_bootconfig(data: &[u8]) -> String {
        let s = data.iter().map(|v| escape_default(*v).to_string()).collect::<Vec<_>>().concat();
        let s = s.split("\\\\").collect::<Vec<_>>().join("\\");
        s.split("\\n").collect::<Vec<_>>().join("\n")
    }

    /// Helper for testing load/verify and assert verfiication success.
    fn test_android_load_verify_success(
        partitions: &[(&CStr, &str)],
        expected_kernel: &[u8],
        expected_ramdisk: &[u8],
        expected_bootconfig: &[u8],
        expected_dtb: &[u8],
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
        let loaded = android_load_verify(&mut ops, 0, &mut load_buffer).unwrap();

        assert!(loaded.dtb.starts_with(expected_dtb));
        assert_eq!(out_color, Some(BootStateColor::Green));
        assert_eq!(loaded.boot_cmdline, "cmd_key_1=cmd_val_1,cmd_key_2=cmd_val_2");
        assert_eq!(loaded.vendor_cmdline, expected_vendor_cmdline);
        assert!(loaded.kernel.starts_with(expected_kernel));
        let (ramdisk, bootconfig) = loaded.ramdisk.split_at_mut(expected_ramdisk.len());
        assert_eq!(ramdisk, expected_ramdisk);
        assert_eq!(
            bootconfig,
            expected_bootconfig,
            "\nexpect: \n{}\nactual: \n{}\n",
            dump_bootconfig(expected_bootconfig),
            dump_bootconfig(bootconfig),
        );
    }

    // A helper for generating avb bootconfig with the given parameters.
    fn avb_bootconfig(
        vbmeta_size: usize,
        digest: &str,
        public_key_digest: &str,
    ) -> std::string::String {
        format!(
            "androidboot.vbmeta.device=PARTUUID=00000000-0000-0000-0000-000000000000
androidboot.vbmeta.public_key_digest={public_key_digest}
androidboot.vbmeta.avb_version=1.3
androidboot.vbmeta.device_state=locked
androidboot.vbmeta.hash_alg=sha512
androidboot.vbmeta.size={vbmeta_size}
androidboot.vbmeta.digest={digest}
androidboot.vbmeta.invalidate_on_error=yes
androidboot.veritymode=enforcing
androidboot.verifiedbootstate=green
"
        )
    }

    // A helper for generating expected bootconfig.
    fn make_bootconfig(bootconfig: impl AsRef<str>) -> Vec<u8> {
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

    /// Helper for testing load/verify for v0//v1/v2 boot images.
    ///
    /// # Args
    ///
    /// * `partitions`: A list of pair `(partition name, file name)` for creating boot storage.
    /// * `vbmeta_file`: The vbmeta file for the storage. Used for constructing expected bootconfig.
    /// * `expected_dtb`: The expected DTB.
    /// * `expected_digest`: The expected digest outputed by vbmeta.
    fn test_android_load_verify_v2_and_lower(
        partitions: &[(&CStr, &str)],
        vbmeta_file: &str,
        expected_dtb: &[u8],
        expected_digest: &str,
    ) {
        let expected_bootconfig = make_bootconfig(
            &(avb_bootconfig(
                read_test_data(vbmeta_file).len(),
                expected_digest,
                TEST_PUBLIC_KEY_DIGEST,
            ) + FakeGblOps::GBL_TEST_BOOTCONFIG),
        );
        test_android_load_verify_success(
            partitions,
            &read_test_data("kernel_a.img"),
            &read_test_data("generic_ramdisk_a.img"),
            &expected_bootconfig,
            expected_dtb,
            "",
        );
    }

    #[test]
    fn test_android_load_verify_v0() {
        let vbmeta = "vbmeta_v0_a.img";
        let parts = [(c"boot_a", "boot_v0_a.img"), (c"vbmeta_a", vbmeta)];
        test_android_load_verify_v2_and_lower(&parts[..], vbmeta, &[], "0976e60490f1213035010310ec3ba277e9cf7ad6ca68433a9eb43871bdf1ae317df70f412714b5d2f54ee9ce4723f3e855be25e0c87b31da6aedddb61fbeb0c6");
    }

    #[test]
    fn test_android_load_verify_v1() {
        let vbmeta = "vbmeta_v1_a.img";
        let parts = [(c"boot_a", "boot_v1_a.img"), (c"vbmeta_a", vbmeta)];
        test_android_load_verify_v2_and_lower(&parts[..], vbmeta, &[], "f483f94d975bc741562e64ac6814d6970b6c589dee84b7160c63e726d8848fe65c3e165393df22dd69338a65082f4f6d289549de05018e03b1184116fda111ce");
    }

    #[test]
    fn test_android_load_verify_v2() {
        let vbmeta = "vbmeta_v2_a.img";
        let parts = [(c"boot_a", "boot_v2_a.img"), (c"vbmeta_a", vbmeta)];
        test_android_load_verify_v2_and_lower(&parts[..], vbmeta, BASE_DTB, "554568eef20d8550c37c06f7988cc76d9ed113b3403a04f345ed4fb0d5acccff531a9f4f862a19f0a3977af8f574c11018f0c8eac142897f0d17527da1911ffe");
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
        partitions: &[(&CStr, &str)],
        vbmeta_file: &str,
        expected_digest: &str,
        expected_vendor_bootconfig: &str,
    ) {
        let expected_bootconfig = make_bootconfig(
            avb_bootconfig(
                read_test_data(vbmeta_file).len(),
                expected_digest,
                TEST_PUBLIC_KEY_DIGEST,
            ) + FakeGblOps::GBL_TEST_BOOTCONFIG
                + expected_vendor_bootconfig,
        );
        test_android_load_verify_success(
            partitions,
            &read_test_data("kernel_a.img"),
            &[read_test_data("vendor_ramdisk_a.img"), read_test_data("generic_ramdisk_a.img")]
                .concat(),
            &expected_bootconfig,
            BASE_DTB,
            TEST_VENDOR_CMDLINE,
        );
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v3_no_init_boot() {
        let vbmeta_file = "vbmeta_v3_v3_a.img";
        let parts = [
            (c"boot_a", "boot_v3_a.img"),
            (c"vendor_boot_a", "vendor_boot_v3_a.img"),
            (c"vbmeta_a", vbmeta_file),
        ];
        test_android_load_verify_v3_and_v4(&parts[..],  vbmeta_file, "c9ff8edd4be86f3a7b0850529bbe6a8095a00af8162151387f98393a5f551c28bcec5ef6c15c91ee994d075afcde9becfe236c62968750e32bd5f74ac2625c32", "");
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v3_init_boot() {
        let vbmeta_file = "vbmeta_v3_v3_init_boot_a.img";
        let parts = [
            (c"boot_a", "boot_no_ramdisk_v3_a.img"),
            (c"init_boot_a", "init_boot_a.img"),
            (c"vendor_boot_a", "vendor_boot_v3_a.img"),
            (c"vbmeta_a", vbmeta_file),
        ];
        test_android_load_verify_v3_and_v4(&parts[..],  vbmeta_file, "c46faba2db23fb6758021747f2276165cff909d17b8d05938c267ec5bd370d09c94014dfd3adc5d36dd3a05eae94dce638197f06ee67fb726c55ef752383b5f7", "");
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v4_no_init_boot() {
        let vbmeta_file = "vbmeta_v3_v4_a.img";
        let parts = [
            (c"boot_a", "boot_v3_a.img"),
            (c"vendor_boot_a", "vendor_boot_v4_a.img"),
            (c"vbmeta_a", vbmeta_file),
        ];
        test_android_load_verify_v3_and_v4(&parts[..],  vbmeta_file, "1034811a69575d8f276cdbf4ddfb2eaf028d79cc78215fdfbadd50452b4155b64e484ed632ab85159cb91f40d084bf5aa48bfb3080a2229b4ecad2900114e765", TEST_VENDOR_BOOTCONFIG);
    }

    #[test]
    fn test_android_load_verify_boot_v3_vendor_v4_init_boot() {
        let vbmeta_file = "vbmeta_v3_v4_init_boot_a.img";
        let parts = [
            (c"boot_a", "boot_no_ramdisk_v3_a.img"),
            (c"init_boot_a", "init_boot_a.img"),
            (c"vendor_boot_a", "vendor_boot_v4_a.img"),
            (c"vbmeta_a", vbmeta_file),
        ];
        test_android_load_verify_v3_and_v4(&parts[..],  vbmeta_file, "66bc22d274eddcb405001e7548404f143adef5d3e628e5b083ed7b88b11442e3dc09429b2ddd693a8b0dcd7d133b9b5f60f597845ab98d32e158b3996a450d65", TEST_VENDOR_BOOTCONFIG);
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v3_no_init_boot() {
        let vbmeta_file = "vbmeta_v4_v3_a.img";
        let parts = [
            (c"boot_a", "boot_v4_a.img"),
            (c"vendor_boot_a", "vendor_boot_v3_a.img"),
            (c"vbmeta_a", vbmeta_file),
        ];
        test_android_load_verify_v3_and_v4(&parts[..],  vbmeta_file, "6a87e40686eb4a56d4cff406475f153d846ed8dba8ce68666e1433b33f75adcf524fb510fcb34753e5c1778a2bec5de7b2fbeab31995518a339cec99a2d20e8b", "");
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v3_init_boot() {
        let vbmeta_file = "vbmeta_v4_v3_init_boot_a.img";
        let parts = [
            (c"boot_a", "boot_no_ramdisk_v4_a.img"),
            (c"init_boot_a", "init_boot_a.img"),
            (c"vendor_boot_a", "vendor_boot_v3_a.img"),
            (c"vbmeta_a", vbmeta_file),
        ];
        test_android_load_verify_v3_and_v4(&parts[..],  vbmeta_file, "59b109531b311e0d66ee58ca2d347db9e379a2877d048625fb5bde6bcb80df03120b9be482c282bd8c753524c7114a9cf6cfbfa336e137bcb1af55c6bc4d169a", "");
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v4_no_init_boot() {
        let vbmeta_file = "vbmeta_v4_v4_a.img";
        let parts = [
            (c"boot_a", "boot_v4_a.img"),
            (c"vendor_boot_a", "vendor_boot_v4_a.img"),
            (c"vbmeta_a", vbmeta_file),
        ];
        test_android_load_verify_v3_and_v4(&parts[..],  vbmeta_file, "f074f0c7330873e71dadc4b00f010fa9aa0fcf81db1b1c3bc3cc9e98dd5ee572699d34b067f6b9cb44e8948f4e3c7182bec6761cf796f9f00c142a348b78264d", TEST_VENDOR_BOOTCONFIG);
    }

    #[test]
    fn test_android_load_verify_boot_v4_vendor_v4_init_boot() {
        let vbmeta_file = "vbmeta_v4_v4_init_boot_a.img";
        let parts = [
            (c"boot_a", "boot_no_ramdisk_v4_a.img"),
            (c"init_boot_a", "init_boot_a.img"),
            (c"vendor_boot_a", "vendor_boot_v4_a.img"),
            (c"vbmeta_a", vbmeta_file),
        ];
        test_android_load_verify_v3_and_v4(&parts[..],  vbmeta_file, "cf41369887ecd31c543cac5fc48a868e2359e935735f528cc7bd149a7e0a4544fd36abbd5871eb03514d00fa05548bed5c804ace07e111eb17a3026adcfd1c14", TEST_VENDOR_BOOTCONFIG);
    }
}
