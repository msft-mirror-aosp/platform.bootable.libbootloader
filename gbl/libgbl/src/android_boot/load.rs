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

use super::{cstr_bytes_to_str, BootBuffer};
use crate::{
    android_boot::{
        avf::{build_pvmfw_data_region, BootInfo},
        kernel::{parse_kernel_attributes, KernelAttributes},
    },
    constants::{FDT_ALIGNMENT, KERNEL_ALIGNMENT, PAGE_SIZE},
    decompress::decompress_kernel,
    device_tree::DtComponentSource,
    fastboot::boot_items::BootItemContainer,
    gbl_avb::{state::BootStateColor, LoadPartition},
    gbl_println,
    ops::GblOps,
    slots::{slotted_part, Slot},
};
use avb::SlotVerifyData;
use bootimg::{defs::*, BootImage, VendorImageHeader};
use core::{mem::take, ops::Range};
use liberror::Error;
use libutils::{aligned_offset, aligned_subslice};
use safemath::SafeNum;
use zerocopy::{IntoBytes, Ref};

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
#[derive(Clone)]
struct BootImageV2Info<'a> {
    cmdline: &'a str,
    kernel_range: Range<usize>,
    ramdisk_range: Range<usize>,
    dtb_range: Range<usize>,
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
        Ok(Self { cmdline, kernel_range, ramdisk_range, dtb_range })
    }
}

// Contains information of a V3/V4 boot image.
#[derive(Clone)]
pub(crate) struct BootImageV3Info {
    pub kernel_range: Range<usize>,
    pub ramdisk_range: Range<usize>,
}

impl BootImageV3Info {
    /// Creates a new instance.
    pub(crate) fn new(buffer: &[u8]) -> Result<Self, Error> {
        let header = BootImage::parse(buffer)?;
        if !matches!(header, BootImage::V3(_) | BootImage::V4(_)) {
            return Err(Error::InvalidInput);
        }
        let v3 = Self::v3(buffer);
        let kernel_range = page_aligned_range(PAGE_SIZE, v3.kernel_size, PAGE_SIZE)?;
        let ramdisk_range = page_aligned_range(kernel_range.end, v3.ramdisk_size, PAGE_SIZE)?;
        Ok(Self { kernel_range, ramdisk_range })
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

#[repr(u32)]
#[derive(Debug)]
enum VendorBootRamdiskType {
    NONE = VENDOR_RAMDISK_TYPE_NONE,
    PLTFORM = VENDOR_RAMDISK_TYPE_PLATFORM,
    RECOVERY = VENDOR_RAMDISK_TYPE_RECOVERY,
    DLKM = VENDOR_RAMDISK_TYPE_DLKM,
}

impl TryFrom<u32> for VendorBootRamdiskType {
    type Error = Error;
    fn try_from(value: u32) -> Result<Self, Self::Error> {
        match value {
            VENDOR_RAMDISK_TYPE_NONE => Ok(VendorBootRamdiskType::NONE),
            VENDOR_RAMDISK_TYPE_PLATFORM => Ok(VendorBootRamdiskType::PLTFORM),
            VENDOR_RAMDISK_TYPE_RECOVERY => Ok(VendorBootRamdiskType::RECOVERY),
            VENDOR_RAMDISK_TYPE_DLKM => Ok(VendorBootRamdiskType::DLKM),
            _ => Err(Error::InvalidInput),
        }
    }
}

#[derive(Debug)]
struct VendorBootRamdiskEntry {
    ramdisk_range: Range<usize>,
    ramdisk_type: VendorBootRamdiskType,
}

/// Contains vendor boot image information.
struct VendorBootImageInfo {
    ramdisk_range: Range<usize>,
    dtb_range: Range<usize>,
    bootconfig_range: Range<usize>,
    ramdisk_table: arrayvec::ArrayVec<VendorBootRamdiskEntry, RAMDISK_TABLE_MAX_ENTRIES>,
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
        .round_up(page_size);
        let ramdisk_range = page_aligned_range(header_size, v3.vendor_ramdisk_size, page_size)?;
        let dtb_sz: usize = v3.dtb_size.try_into().unwrap();
        let dtb_range = page_aligned_range(ramdisk_range.end, dtb_sz, page_size)?;

        let (table_sz, bootconfig_sz) = match header {
            VendorImageHeader::V4(hdr) => (hdr.vendor_ramdisk_table_size, hdr.bootconfig_size),
            _ => (0, 0),
        };
        let table = page_aligned_range(dtb_range.end, table_sz, page_size)?;
        let bootconfig_range = table.end..(table.end + usize::try_from(bootconfig_sz)?);
        let mut ramdisk_table = arrayvec::ArrayVec::new();
        if let VendorImageHeader::V4(hdr) = header {
            if hdr.vendor_ramdisk_table_entry_num > 0 {
                let table_entries: Ref<_, [vendor_ramdisk_table_entry_v4]> =
                    Ref::from_prefix_with_elems(
                        &buffer[table],
                        hdr.vendor_ramdisk_table_entry_num as usize,
                    )
                    .map_err(|_| Error::InvalidInput)?
                    .0;
                if hdr.vendor_ramdisk_table_entry_num as usize > RAMDISK_TABLE_MAX_ENTRIES {
                    return Err(Error::Other(Some(
                        "Ramdisk table entry exceeded max supported entry count",
                    )));
                }

                ramdisk_table.extend(table_entries.iter().map(|e| {
                    let start = ramdisk_range.start + e.ramdisk_offset as usize;
                    let end = start + e.ramdisk_size as usize;
                    VendorBootRamdiskEntry {
                        ramdisk_range: start..end,
                        ramdisk_type: e.ramdisk_type.try_into().unwrap(),
                    }
                }));
            }
        }
        Ok(Self { ramdisk_range, dtb_range, bootconfig_range, ramdisk_table })
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

// Max number of ramdisks supported in vendor_boot partition.
// There's currently no limit on how many ramdisks entries can be
// in the vendor_boot ramdisk table, so we set a reasonable limit here.
// Feel free to adjust
pub const RAMDISK_TABLE_MAX_ENTRIES: usize = 8;
// init_boot/boot + however many ramdisks in vendor_boot
//                + however many ramdisks in vendor_kernel_boot
pub const RAMDISK_MAX_ENTRIES: usize = RAMDISK_TABLE_MAX_ENTRIES * 2 + 2;

/// Contains various loaded image components by `android_load_verified`
#[derive(Default)]
pub struct LoadedImages<'a> {
    /// dtbo image.
    pub dtbo: &'a [u8],
    /// Kernel commandline.
    pub boot_cmdline: &'a str,
    /// Vendor commandline,
    pub vendor_cmdline: &'a str,
    /// Vendor commandline,
    pub vendor_bootconfig: &'a [u8],
    /// DTB.
    pub dtb: &'a [u8],
    /// DTB source.
    pub dtb_source: Option<DtComponentSource>,
    /// DTB from partition.
    pub dtb_part: &'a [u8],
    /// pVM firmware image.
    pub pvmfw: &'a [u8],
    /// kernel from boot image,
    pub kernel: &'a [u8],
    /// ramdisks to be concatenated (vendor_boot+vendor_kernel_boot+init_boot/boot)
    pub ramdisks: arrayvec::ArrayVec<&'a [u8], RAMDISK_MAX_ENTRIES>,
}

/// Helper for getting a successfully verified partition from `SlotVerifyData`
fn get_verified_partition<'a, 'b>(
    ops: &mut impl GblOps<'a>,
    part: LoadPartition,
    slot: Option<Slot>,
    unlocked: bool,
    optional: bool,
    verify_data: &'b SlotVerifyData,
) -> Result<&'b [u8], Error> {
    let slotted = slotted_part(part.name(), slot.map(|s| s.suffix));
    let part_res =
        verify_data.partition_data().iter().find(|v| v.partition_name() == part.name_cstr());
    match part_res {
        None if optional => {
            gbl_println!(ops, "{slotted:?} is not loaded by avb. Image is optional. Skipping.");
            Ok(&[][..])
        }
        None => {
            gbl_println!(
                ops,
                "Error: {slotted:?} is required but is not loaded by avb. \
                The partition may be missing or not included in the vbmeta."
            );
            Err(Error::NotFound)
        }
        Some(v) => match v.verify_result() {
            Ok(_) => Ok(v.data()),
            Err(_) if unlocked => {
                gbl_println!(
                    ops,
                    "{slotted:?} verification failed. Device is unlocked. Continuing."
                );
                Ok(v.data())
            }
            _ => unreachable!(), // Should not reach here if locked and verification failed.
        },
    }
}

/// Helper for parsing and logging boot image version.
fn log_and_parse_bootimg<'a, 'b>(
    ops: &mut impl GblOps<'a>,
    data: &'b [u8],
) -> Result<BootImage<&'b [u8]>, Error> {
    let bootimg = BootImage::parse(&data[..]).map_err(Error::from)?;
    let ver_str = match bootimg {
        BootImage::V0(_) => "V0",
        BootImage::V1(_) => "V1",
        BootImage::V2(_) => "V2",
        BootImage::V3(_) => "V3",
        BootImage::V4(_) => "V4",
    };
    gbl_println!(ops, "Boot image {ver_str}.");
    Ok(bootimg)
}

/// Loads android images from avb verified partitions.
///
/// # Args
///
/// * `ops`: An implementation of `GblOps`.
/// * `slot`: The target slot to loader.
/// * `unlocked`: The unlock state.
/// * `is_recovery`: Whether we are booting to recovery.
/// * `verify_data`: `SlotVerifyData` returns from `avb_slot_verify`.
pub(super) fn android_load_verified<'a, 'b>(
    ops: &mut impl GblOps<'a>,
    slot: Option<Slot>,
    unlocked: bool,
    is_recovery: bool,
    verify_data: &'b SlotVerifyData,
) -> Result<LoadedImages<'b>, Error> {
    let mut images = LoadedImages::default();
    images.dtb_part =
        get_verified_partition(ops, LoadPartition::Dtb, slot, unlocked, true, verify_data)?;
    images.dtbo =
        get_verified_partition(ops, LoadPartition::Dtbo, slot, unlocked, true, verify_data)?;
    if ops.avf_is_supported()? {
        images.pvmfw =
            get_verified_partition(ops, LoadPartition::Pvmfw, slot, unlocked, true, verify_data)?;
    }
    let boot =
        get_verified_partition(ops, LoadPartition::Boot, slot, unlocked, false, verify_data)?;
    match log_and_parse_bootimg(ops, boot)? {
        BootImage::V3(_) | BootImage::V4(_) => load_v3_and_v4_verified(
            ops,
            boot,
            slot,
            unlocked,
            is_recovery,
            verify_data,
            &mut images,
        ),
        BootImage::V0(_) | BootImage::V1(_) | BootImage::V2(_) => {
            load_v2_or_lower_verified(boot, &mut images)
        }
    }?;
    Ok(images)
}

/// Loads android boot images of version 0, 1 and 2 from avb verified partitions.
///
/// # Args
///
/// * `boot`: A buffer containing the boot image loaded by avb.
/// * `images`: The output `LoadedImages` that stores image slices from `boot`.
///
/// For v0, v1, v2 images:
///
/// * Both kernel and ramdisk come from the boot image.
/// * vendor_boot, init_boot are irrelevant.
fn load_v2_or_lower_verified<'a, 'b, 'c>(
    boot: &'c [u8],
    images: &mut LoadedImages<'c>,
) -> Result<(), Error> {
    let info = BootImageV2Info::new(boot).unwrap();
    images.boot_cmdline = info.cmdline;
    images.dtb = get_range(boot, &info.dtb_range)?;
    images.dtb_source = Some(DtComponentSource::Boot);
    images.kernel = get_range(boot, &info.kernel_range)?;
    images.ramdisks.push(get_range(boot, &info.ramdisk_range)?);
    Ok(())
}

fn parse_vendor_ramdisks<'a, const CAP: usize>(
    image_data: &'a [u8],
    info: &VendorBootImageInfo,
    is_recovery: bool,
    ramdisks: &mut arrayvec::ArrayVec<&'a [u8], CAP>,
) -> Result<(), Error> {
    // Recovery ramdisk is only needed in recovery mode. So if we are not
    // booting recovery, skip recovery ramdisk
    if info.ramdisk_table.is_empty() {
        // No ramdisk table (v3 image), just load all ramdisks.
        ramdisks.push(get_range(image_data, &info.ramdisk_range)?);
    } else {
        for e in info.ramdisk_table.iter() {
            // Skips recovery ramdisk when booting to normal android
            if !is_recovery && matches!(e.ramdisk_type, VendorBootRamdiskType::RECOVERY) {
                continue;
            }
            ramdisks.push(get_range(image_data, &e.ramdisk_range)?);
        }
    }
    Ok(())
}

/// Loads android boot images of version 3 and 4 from avb verified partitions.
///
/// # Args
///
/// * `ops`: An implementation of `GblOps`.
/// * `boot`: A buffer containing the boot image.
/// * `slot`: The target slot to loader.
/// * `unlocked`: The unlock state.
/// * `is_recovery`: Whether we are booting to recovery.
/// * `verify_data`: `SlotVerifyData` returns from `avb_slot_verify`.
/// * `images`: The output `LoadedImages` that stores image slices from partitions in `verify_data`.
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
fn load_v3_and_v4_verified<'a, 'b>(
    ops: &mut impl GblOps<'a>,
    boot: &'b [u8],
    slot: Option<Slot>,
    unlocked: bool,
    is_recovery: bool,
    verify_data: &'b SlotVerifyData,
    images: &mut LoadedImages<'b>,
) -> Result<(), Error> {
    let boot_info = BootImageV3Info::new(boot).unwrap();
    images.boot_cmdline = BootImageV3Info::cmdline(boot)?;

    // Loads vendor_boot partition, including ramdisk, dtb, commandline etc.
    let vendor_boot =
        get_verified_partition(ops, LoadPartition::VendorBoot, slot, unlocked, false, verify_data)?;
    let vendor_boot_info = VendorBootImageInfo::new(vendor_boot)?;
    images.vendor_cmdline = VendorBootImageInfo::cmdline(vendor_boot)?;
    images.dtb = get_range(vendor_boot, &vendor_boot_info.dtb_range)?;
    images.dtb_source = Some(DtComponentSource::VendorBoot);
    images.vendor_bootconfig = get_range(vendor_boot, &vendor_boot_info.bootconfig_range)?;
    images.kernel = get_range(boot, &boot_info.kernel_range)?;
    parse_vendor_ramdisks(&vendor_boot, &vendor_boot_info, is_recovery, &mut images.ramdisks)?;

    // Finds and loads vendor_kernel_boot partition if provided.
    let vendor_kernel_boot = get_verified_partition(
        ops,
        LoadPartition::VendorKernelBoot,
        slot,
        unlocked,
        true,
        verify_data,
    )?;
    if vendor_kernel_boot.len() > 0 {
        let info = VendorBootImageInfo::new(vendor_kernel_boot)?;
        // DTB should be provided by vendor_kerenl_boot if it exists.
        images.dtb = get_range(vendor_kernel_boot, &info.dtb_range)?;
        parse_vendor_ramdisks(&vendor_kernel_boot, &info, is_recovery, &mut images.ramdisks)?;
    }

    // Loads generic ramdisk, which may come from either boot or init_boot.
    let generic_ramdisk = match boot_info.ramdisk_range.is_empty() {
        true => get_verified_partition(
            ops,
            LoadPartition::InitBoot,
            slot,
            unlocked,
            false,
            verify_data,
        )?,
        false => boot,
    };
    let generic_ramdisk_range = BootImageV3Info::new(generic_ramdisk)?.ramdisk_range;
    images.ramdisks.push(get_range(generic_ramdisk, &generic_ramdisk_range)?);
    Ok(())
}

/// Wrapper of `split_at_mut_checked` with error conversion.
pub(crate) fn split(buffer: &mut [u8], size: usize) -> Result<(&mut [u8], &mut [u8]), Error> {
    buffer.split_at_mut_checked(size).ok_or(Error::BufferTooSmall(Some(size)))
}

/// Wrapper of slice::get with error conversion.
fn get_range<'a>(buffer: &'a [u8], range: &Range<usize>) -> Result<&'a [u8], Error> {
    buffer.get(range.clone()).ok_or(Error::InvalidInput)
}

/// Calculates the offset from the start of the buffer to obtain an aligned tail
/// that can fit at least `size` bytes with the given alignment.
///
/// Returns the starting offset of the aligned tail slice.
pub(crate) fn aligned_tail_offset(
    buffer: &[u8],
    size: usize,
    align: usize,
) -> Result<usize, Error> {
    let off = SafeNum::from(buffer.len()) - size;
    let rem = buffer[off.try_into()?..].as_ptr() as usize % align;
    Ok(usize::try_from(off - rem)?)
}

/// Parses and returns the kernel image from a boot image.
#[cfg(feature = "fuchsia")]
pub fn get_kernel(boot: &[u8]) -> Result<&[u8], Error> {
    match BootImage::parse(&boot[..]).map_err(Error::from)? {
        BootImage::V3(_) | BootImage::V4(_) => boot.get(BootImageV3Info::new(boot)?.kernel_range),
        _ => boot.get(BootImageV2Info::new(boot)?.kernel_range),
    }
    .ok_or(Error::InvalidInput)
}

/// Helper data strucuture for loading boot images into a `BootBuffer`.
///
///
/// Each image is loaded to its designated buffers if provided. If not, it'll be loaded to
/// `loader.general` according to the following layout:
///
/// +---------------------------+
/// | kernel                    |
/// +---------------------------+
/// | pvmfw                     |
/// +---------------------------+
/// | ramdisk                   |
/// +---------------------------+
/// | bootconfig                |
/// +---------------------------+
/// | FDT                       |
/// +---------------------------+
///
/// Unused image segments will be empty.
#[derive(Default)]
pub(super) struct BootBufferLoader<'a> {
    bufs: BootBuffer<'a>,
    general: &'a mut [u8],

    pub(super) ramdisk_sz: usize,
    pub(super) bootconfig_sz: usize,
    /// Reserved kernel region size, including headroom for BSS and other post-image segments.
    pub(super) kernel_sz: usize,

    general_fdt: Range<usize>,
    general_kernel: Option<&'a mut [u8]>,
}

impl<'a> BootBufferLoader<'a> {
    pub(super) fn new(bufs: BootBuffer<'a>) -> Self {
        Self { bufs, ..Default::default() }
    }

    /// Splits out the unused buffer and take the boot item container.
    pub(super) fn take_boot_items(&mut self) -> BootItemContainer<'a> {
        let mut boot_items = self.bufs.take_boot_items();
        self.general = boot_items.split_unused();
        boot_items
    }

    /// Loads pvmfw image.
    pub(super) fn pvmfw_load<'b>(
        &mut self,
        ops: &mut impl GblOps<'b>,
        img: &[u8],
        kernel_attrs: &KernelAttributes,
        verify_data: &SlotVerifyData,
        unlocked: bool,
        is_recovery: bool,
        color: BootStateColor,
        dtbo_part: &[u8],
    ) -> Result<(&'a mut [u8], usize), Error> {
        // Parse the partition header and extract the pvmfw binary
        let info = BootImageV3Info::new(img)?;
        let pvmfw_bin = img.get(info.kernel_range.clone()).ok_or(Error::BadBufferSize)?;
        let pvmfw_bin_len = pvmfw_bin.len();
        let boot_info = BootInfo::new(unlocked, is_recovery, color, verify_data);
        Ok(match self.bufs.pvmfw_data.as_mut() {
            Some(v) => {
                build_pvmfw_data_region(ops, v, pvmfw_bin, kernel_attrs, &boot_info, dtbo_part)
                    .map(|sz| (&mut take(v)[..sz], pvmfw_bin_len))?
            }
            _ => {
                // Kernel must already be loaded, nothing else should be.
                assert_ne!(self.kernel_sz, 0);
                assert_eq!(self.ramdisk_sz, 0);
                assert_eq!(self.bootconfig_sz, 0);
                assert_eq!(self.general_fdt, 0..0);
                // Use the kernel's page size so the hypervisor's identity mapping covers the
                // pvmfw region exactly.
                let off = aligned_offset(&self.general, kernel_attrs.page_size)?;
                let sz = build_pvmfw_data_region(
                    ops,
                    &mut self.general[off..],
                    pvmfw_bin,
                    kernel_attrs,
                    &boot_info,
                    dtbo_part,
                )?;
                let (pvmfw, general) = take(&mut self.general)[off..].split_at_mut(sz);
                self.general = general;
                (pvmfw, pvmfw_bin_len)
            }
        })
    }

    /// Decompresses and loads kernel into the kernel buffer.
    pub(super) fn kernel_load<'b>(
        &mut self,
        ops: &mut impl GblOps<'b>,
        kernel: &[u8],
    ) -> Result<KernelAttributes, Error> {
        let attrs = match self.bufs.kernel.as_mut() {
            // Designated buffer, decompresses directly into it.
            Some(v) => {
                let sz = decompress_kernel(ops, kernel, v)?;
                let attrs = parse_kernel_attributes(&v[..sz])?;
                if attrs.reserved_size > v.len() {
                    return Err(Error::BufferTooSmall(Some(attrs.reserved_size)));
                }
                attrs
            }
            // Use general buffer. Decompresses at the head and carves the kernel out of
            // `self.general` so subsequent loads see only the remaining space.
            _ => {
                // Nothing else may be loaded yet.
                assert_eq!(self.ramdisk_sz, 0);
                assert_eq!(self.bootconfig_sz, 0);
                assert_eq!(self.general_fdt, 0..0);
                assert!(self.general_kernel.is_none());
                let off = aligned_offset(&self.general, KERNEL_ALIGNMENT)?;
                let sz = decompress_kernel(ops, kernel, &mut self.general[off..])?;
                let attrs = parse_kernel_attributes(&self.general[off..off + sz])?;
                if off + attrs.reserved_size > self.general.len() {
                    return Err(Error::BufferTooSmall(Some(off + attrs.reserved_size)));
                }
                let (kernel, general) =
                    take(&mut self.general)[off..].split_at_mut(attrs.reserved_size);
                self.general = general;
                self.general_kernel = Some(kernel);
                attrs
            }
        };
        self.kernel_sz = attrs.reserved_size;
        Ok(attrs)
    }

    /// Loads ramdisks to the buffer.
    pub(super) fn ramdisk_load(&mut self, ramdisks: &[&[u8]]) -> Result<(), Error> {
        self.ramdisk_sz = ramdisks.iter().map(|v| v.len()).sum();
        let mut rem = match self.bufs.ramdisk.as_mut() {
            Some(v) => v,
            _ => {
                // Kernel and pvmfw must already be carved out; bootconfig/fdt not yet loaded.
                assert_eq!(self.bootconfig_sz, 0);
                assert_eq!(self.general_fdt.len(), 0);
                self.general_fdt = self.ramdisk_sz..self.ramdisk_sz;
                self.general = aligned_subslice(take(&mut self.general), PAGE_SIZE)?;
                split(self.general, self.ramdisk_sz)?.0
            }
        };
        let mut curr;
        for v in ramdisks {
            (curr, rem) = split(rem, v.len()).unwrap();
            curr.clone_from_slice(v);
        }
        Ok(())
    }

    /// Expands bootconfig buffer to cover the rest of unused space and returns it.
    pub(super) fn expand_bootconfig_buffer(&mut self) -> Result<&mut [u8], Error> {
        self.check_general_fdt_range();
        match self.bufs.ramdisk.as_mut() {
            Some(v) => Ok(&mut v[self.ramdisk_sz..]),
            _ => {
                // Moves FDT to the right most position to make more space for bootconfig fixup.
                let off =
                    aligned_tail_offset(&self.general, self.general_fdt.len(), FDT_ALIGNMENT)?;
                self.general.copy_within(self.general_fdt.clone(), off);
                self.general_fdt = off..off + self.general_fdt.len();
                Ok(&mut self.general[self.ramdisk_sz..off])
            }
        }
    }

    /// Sets bootconfig size.
    pub(super) fn set_bootconfig_size(&mut self, sz: usize) {
        self.bootconfig_sz = sz;
    }

    /// Computes the end of bootconfig segment in the general load buffer.
    fn general_bootconfig_end(&self) -> Result<usize, Error> {
        match self.bufs.ramdisk.is_some() {
            // Designated ramdisk. The segment is unused in general load buffer.
            true => Ok(0),
            _ => Ok((SafeNum::from(self.ramdisk_sz) + self.bootconfig_sz).try_into()?),
        }
    }

    /// Returns the designated fdt buffer and the unused buffer after bootconfig in the
    /// general load buffer for constructing FDT.
    ///
    /// Note: the unused buffer is still necessary even if we have designated buffer because we
    /// need it for relocating DT sources.
    pub(super) fn get_fdt_and_general_unused_buffer(
        &mut self,
    ) -> Result<(Option<&mut [u8]>, &mut [u8]), Error> {
        let unused_off = self.general_bootconfig_end()?;
        let fdt = self.bufs.fdt.as_mut().map(|v| v as _);
        Ok((fdt, &mut self.general[unused_off..]))
    }

    /// Sets FDT range.
    ///
    /// The intended usage is to get the buffer using `Self::get_fdt_and_general_unused_buffer()`,
    /// construct FDT, compute the ptr range, release the borrow then call this API.
    pub(super) fn set_fdt_range(&mut self, fdt: Range<*const u8>) {
        // Updates `self.general_fdt` if fdt is loaded to general load buffer.
        if self.bufs.fdt.is_none() {
            self.general_fdt = sub_slice_range(&self.general.as_ptr_range(), &fdt).unwrap();
            self.check_general_fdt_range();
        }
    }

    /// Expands FDT buffer to cover the rest of unused space.
    pub(super) fn expand_fdt(&mut self) -> Result<&mut [u8], Error> {
        // Computes the values that require borrowing self first.
        let bootconfig_end = self.general_bootconfig_end()?;
        self.check_general_fdt_range();
        match self.bufs.fdt.as_mut() {
            // Noop for designated FDT buffer.
            Some(v) => Ok(&mut v[..]),
            _ => {
                // Moves FDT to the left most position.
                // Starts at PAGE_SIZE aligned address to make sure that the preceding ramdisk
                // image (if no designated ramdisk buffer is provided), has a page aligned end.
                let align = self.bufs.ramdisk.as_ref().map_or(PAGE_SIZE, |_| FDT_ALIGNMENT);
                self.general_fdt =
                    move_left(self.general, &self.general_fdt, bootconfig_end, align)?;
                self.general_fdt.end = self.general.len();
                Ok(&mut self.general[self.general_fdt.start..])
            }
        }
    }

    /// Checks Self::general_fdt_range is a valid.
    fn check_general_fdt_range(&self) {
        // Either empty or a valid range between bootconfig and the end of `self.general`.
        assert!(
            self.general_fdt.len() == 0
                || self.general_fdt.start >= self.general_bootconfig_end().unwrap()
                    && self.general_fdt.end <= self.general.len()
        );
    }

    /// Splits out the [ramdisk, fdt, kernel, unused] buffers without consuming the loader.
    pub(super) fn splits(&mut self) -> [&mut [u8]; 4] {
        BootBufferLoader {
            bufs: self.bufs.as_borrowed(),
            general: self.general,
            ramdisk_sz: self.ramdisk_sz,
            bootconfig_sz: self.bootconfig_sz,
            kernel_sz: self.kernel_sz,
            general_fdt: self.general_fdt.clone(),
            general_kernel: self.general_kernel.as_deref_mut(),
        }
        .into_splits()
    }

    /// Consumes the loader and splits out the [ramdisk, fdt, kernel, unused] buffers.
    pub(super) fn into_splits(self) -> [&'a mut [u8]; 4] {
        let (rem, unused) = self.general.split_at_mut(self.general_fdt.end);
        let (ramdisk, fdt) = rem.split_at_mut(self.general_fdt.start);
        // Use designated buffers if provided, otherwise falls back to `general`
        let ramdisk = self.bufs.ramdisk.unwrap_or(ramdisk);
        let fdt = self.bufs.fdt.unwrap_or(fdt);
        let kernel = self.bufs.kernel.or(self.general_kernel).unwrap();
        [ramdisk, fdt, kernel, unused]
    }
}

/// Computes the index range of `sub` in the parent slice `buf`.
///
/// Returns None if the `sub` is not a sublice of `buf`
pub(crate) fn sub_slice_range(
    buf: &Range<*const u8>,
    sub: &Range<*const u8>,
) -> Option<Range<usize>> {
    let start = (sub.start as usize).checked_sub(buf.start as _)?;
    let end = (sub.end as usize).checked_sub(buf.start as _)?;
    (sub.end <= buf.end).then_some(start..end)
}

/// Moves data in subslice range `sub` to the left most aligned position after `bound`.
///
/// Returns the new range.
fn move_left(
    buffer: &mut [u8],
    sub: &Range<usize>,
    bound: usize,
    align: usize,
) -> Result<Range<usize>, Error> {
    let range = buffer.as_ptr_range();
    let buffer = aligned_subslice(&mut buffer[..sub.end][bound..], align)?;
    buffer.get(..sub.len()).ok_or(Error::BufferTooSmall(Some(sub.len())))?;
    buffer.copy_within(buffer.len() - sub.len().., 0);
    Ok(sub_slice_range(&range, &buffer[..sub.len()].as_ptr_range()).unwrap())
}
