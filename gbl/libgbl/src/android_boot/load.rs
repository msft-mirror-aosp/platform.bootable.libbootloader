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
use bootimg::{defs::*, BootImage};
use bootparams::{bootconfig::BootConfigBuilder, entry::CommandlineParser};
use core::{
    array,
    ffi::CStr,
    fmt::Write,
    ops::{Deref, Range},
};
use liberror::Error;
use safemath::SafeNum;
use zerocopy::Ref;

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
struct LoadedBootImageV2<'a> {
    cmdline: &'a str,
    page_size: usize,
    kernel_range: Range<usize>,
    ramdisk_range: Range<usize>,
    dtb_range: Range<usize>,
    image_size: usize,
}

impl<'a> LoadedBootImageV2<'a> {
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

/// Contains various loaded image components by `android_load_verify`
pub struct LoadedImages<'a> {
    /// dtbo image.
    pub dtbo: &'a mut [u8],
    /// Kernel commandline.
    pub boot_cmdline: &'a str,
    /// Boot DTB.
    pub boot_dtb: &'a mut [u8],
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
            boot_dtb: &mut [][..],
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
        BootImage::V3(_) | BootImage::V4(_) => unimplemented!(),
        _ => load_verify_v2_and_lower(ops, slot, &parts, &preloaded, &mut res, remains)?,
    };

    drop(parts);
    drop(preloaded);
    res.dtbo = dtbo;
    Ok(res)
}

/// Loads android images for boot images of version 0, 1 and 2.
///
/// * Both kernel and ramdisk comes from the boot image.
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
    let boot_size = LoadedBootImageV2::new(load).unwrap().image_size;
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
    let boot_img = LoadedBootImageV2::new(boot_ex).unwrap();
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
    ([hdr, out.ramdisk, out.unused, out.boot_dtb], out.kernel) =
        split_chunks(load, &[page_size, ramdisk_sz, unused_sz, dtb_sz]);
    out.boot_cmdline = LoadedBootImageV2::new(hdr).unwrap().cmdline;
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
        &partitions,
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
    use std::{ascii::escape_default, collections::HashMap, fs, path::Path, string::String};

    // See libgbl/testdata/gen_test_data.py for test data generation.
    const TEST_ROLLBACK_INDEX_LOCATION: usize = 1;

    // The DTB in the test mkbootimg images.
    // See libgbl/testdata/gen_test_data.py for test data generation.
    const BASE_DTB: &[u8] = include_bytes!("../../../libfdt/test/data/base.dtb");

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

    /// Helper for testing `android_load_verify_v2_and_lower`
    fn test_android_load_verify_v2_and_lower(
        partitions: &[(&CStr, &str)],
        epxected_boot_dtb: &[u8],
        epxected_bootconfig: &[u8],
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

        assert!(loaded.boot_dtb.starts_with(epxected_boot_dtb));
        assert_eq!(out_color, Some(BootStateColor::Green));
        assert_eq!(loaded.boot_cmdline, "cmd_key_1=cmd_val_1,cmd_key_2=cmd_val_2");
        assert!(loaded.kernel.starts_with(&read_test_data("kernel_a.img")));
        let expected_ramdisk = read_test_data("generic_ramdisk_a.img");
        let (ramdisk, bootconfig) = loaded.ramdisk.split_at_mut(expected_ramdisk.len());
        assert_eq!(ramdisk, expected_ramdisk);
        assert_eq!(
            bootconfig,
            epxected_bootconfig,
            "\nexpect: \n{}\nactual: \n{}\n",
            dump_bootconfig(epxected_bootconfig),
            dump_bootconfig(bootconfig),
        );
    }

    #[test]
    fn test_android_load_verify_v0() {
        let epxected_bootconfig =
b"androidboot.vbmeta.device=PARTUUID=00000000-0000-0000-0000-000000000000
androidboot.vbmeta.avb_version=1.3
androidboot.vbmeta.device_state=locked
androidboot.vbmeta.hash_alg=sha512
androidboot.vbmeta.size=2112
androidboot.vbmeta.digest=62f7c218ba6fe0f7941cf8eb9249279b70009fcc7d9792ea149919526ece05b4d357525941d22008a7d55e0ec6f9128976a2590130e30cc03005eeeb82e9ba90
androidboot.vbmeta.invalidate_on_error=yes
androidboot.veritymode=enforcing
androidboot.verifiedbootstate=green
arg1=val1
arg2=val2
\xf1\x01\x00\x00\x08\xa5\x00\x00#BOOTCONFIG
";
        let parts = [(c"boot_a", "boot_v0_a.img"), (c"vbmeta_a", "vbmeta_v0_a.img")];
        test_android_load_verify_v2_and_lower(&parts[..], &[], epxected_bootconfig);
    }

    #[test]
    fn test_android_load_verify_v1() {
        let epxected_bootconfig =
b"androidboot.vbmeta.device=PARTUUID=00000000-0000-0000-0000-000000000000
androidboot.vbmeta.avb_version=1.3
androidboot.vbmeta.device_state=locked
androidboot.vbmeta.hash_alg=sha512
androidboot.vbmeta.size=2112
androidboot.vbmeta.digest=667257b6b96086f67d7a4f82210b677a9d9e4104022b1476853b8f619f3323f97de47c7c4a3e61e4cad1c5af787f502d34c6262a99919a3345c3e18d0b503e41
androidboot.vbmeta.invalidate_on_error=yes
androidboot.veritymode=enforcing
androidboot.verifiedbootstate=green
arg1=val1
arg2=val2
\xf1\x01\x00\x00\x7f\xa4\x00\x00#BOOTCONFIG
";
        let parts = [(c"boot_a", "boot_v1_a.img"), (c"vbmeta_a", "vbmeta_v1_a.img")];
        test_android_load_verify_v2_and_lower(&parts[..], &[], epxected_bootconfig);
    }

    #[test]
    fn test_android_load_verify_v2() {
        let epxected_bootconfig =
b"androidboot.vbmeta.device=PARTUUID=00000000-0000-0000-0000-000000000000
androidboot.vbmeta.avb_version=1.3
androidboot.vbmeta.device_state=locked
androidboot.vbmeta.hash_alg=sha512
androidboot.vbmeta.size=2112
androidboot.vbmeta.digest=6c519ca9d0b6e3163de0e3473d74602775679bcb9015c80735f669414bbe68a5cede298a354602711aa009e29055e839101773b34251dd42f8fdda64d08c8897
androidboot.vbmeta.invalidate_on_error=yes
androidboot.veritymode=enforcing
androidboot.verifiedbootstate=green
arg1=val1
arg2=val2
\xf1\x01\x00\x00y\xa4\x00\x00#BOOTCONFIG
";
        let parts = [(c"boot_a", "boot_v2_a.img"), (c"vbmeta_a", "vbmeta_v2_a.img")];
        test_android_load_verify_v2_and_lower(&parts[..], BASE_DTB, epxected_bootconfig);
    }
}
