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

//! # Generic Boot Loader (gbl) Library
//!
//! TODO: b/312610098 - add documentation.
//!
//! The intended users of this library are firmware, bootloader, and bring-up teams at OEMs and SOC
//! Vendors

// This code is intended for use in bootloaders that typically will not support
// the Rust standard library
#![cfg_attr(not(any(test, android_dylib)), no_std)]
// TODO: b/312610985 - return warning for unused partitions
#![allow(unused_variables, dead_code)]
// TODO: b/312608163 - Adding ZBI library usage to check dependencies
extern crate zbi;

use core::fmt::{Debug, Display, Formatter};
use lazy_static::lazy_static;
use spin::Mutex;

pub mod boot_mode;
pub mod boot_reason;
pub mod digest;
pub mod error;
pub mod ops;

pub use boot_mode::BootMode;
pub use boot_reason::KnownBootReason;
pub use digest::{Context, Digest, SwContext, SwDigest};
pub use error::{Error, Result};
pub use ops::{DefaultGblOps, GblOps};

// TODO: b/312607649 - Replace placeholders with actual structures: https://r.android.com/2721974, etc
/// TODO: b/312607649 - placeholder type
pub struct Partition {}
/// TODO: b/312607649 - placeholder type
pub struct InfoStruct {}
/// TODO: b/312607649 - placeholder type
pub struct AvbDescriptor {}
/// TODO: b/312607649 - placeholder type
pub struct AvbVerificationFlags(u32); // AvbVBMetaImageFlags from
                                      // external/avb/libavb/avb_vbmeta_image.h

/// Structure representing partition and optional address it is required to be loaded.
/// If no address is provided GBL will use default one.
pub struct PartitionRamMap<'b, 'c> {
    /// Partition details
    pub partition: &'b Partition,

    /// Optional memory region to load partitions.
    /// If it's not provided default values will be used.
    pub address: Option<&'c mut [u8]>,

    loaded: bool,
    verified: bool,
}

/// Boot Image in memory
pub struct BootImage<'a>(&'a mut [u8]);

/// Vendor Boot Image in memory
pub struct VendorBootImage<'a>(&'a mut [u8]);

/// Init Boot Image in memory
pub struct InitBootImage<'a>(&'a mut [u8]);

/// Kernel Image in memory
pub struct KernelImage<'a>(&'a mut [u8]);

/// Ramdisk in memory
pub struct Ramdisk<'a>(&'a mut [u8]);
/// Bootconfig in memory
pub struct Bootconfig<'a>(&'a mut [u8]);
/// DTB in memory
pub struct Dtb<'a>(&'a mut [u8]);

/// Create Boot Image from corresponding partition for `partitions_ram_map` and `avb_descriptors`
/// lists
pub fn get_boot_image<'a: 'b, 'b: 'c, 'c>(
    avb_descriptors: &[AvbDescriptor],
    partitions_ram_map: &'a mut [PartitionRamMap<'b, 'c>],
) -> (Option<BootImage<'c>>, &'a mut [PartitionRamMap<'b, 'c>]) {
    match partitions_ram_map.len() {
        0 => (None, partitions_ram_map),
        _ => {
            let (partition_map, tail) = partitions_ram_map.split_first_mut().unwrap();
            (partition_map.address.take().map(BootImage), tail)
        }
    }
}

/// Create Vendor Boot Image from corresponding partition for `partitions_ram_map` and
/// `avb_descriptors` lists
pub fn get_vendor_boot_image<'a: 'b, 'b: 'c, 'c>(
    avb_descriptors: &[AvbDescriptor],
    partitions_ram_map: &'a mut [PartitionRamMap<'b, 'c>],
) -> (Option<VendorBootImage<'c>>, &'a mut [PartitionRamMap<'b, 'c>]) {
    match partitions_ram_map.len() {
        0 => (None, partitions_ram_map),
        _ => {
            let (partition_map, tail) = partitions_ram_map.split_first_mut().unwrap();
            (partition_map.address.take().map(VendorBootImage), tail)
        }
    }
}

/// Create Init Boot Image from corresponding partition for `partitions` and `avb_descriptors` lists
pub fn get_init_boot_image<'a: 'b, 'b: 'c, 'c>(
    avb_descriptors: &[AvbDescriptor],
    partitions_ram_map: &'a mut [PartitionRamMap<'b, 'c>],
) -> (Option<InitBootImage<'c>>, &'a mut [PartitionRamMap<'b, 'c>]) {
    match partitions_ram_map.len() {
        0 => (None, partitions_ram_map),
        _ => {
            let (partition_map, tail) = partitions_ram_map.split_first_mut().unwrap();
            (partition_map.address.take().map(InitBootImage), tail)
        }
    }
}

/// Create separate image types from [AvbDescriptor]
pub fn get_images<'a: 'b, 'b: 'c, 'c>(
    avb_descriptors: &mut [AvbDescriptor],
    partitions_ram_map: &'a mut [PartitionRamMap<'b, 'c>],
) -> (
    Option<BootImage<'c>>,
    Option<InitBootImage<'c>>,
    Option<VendorBootImage<'c>>,
    &'a mut [PartitionRamMap<'b, 'c>],
) {
    let (boot_image, partitions_ram_map) = get_boot_image(avb_descriptors, partitions_ram_map);
    let (init_boot_image, partitions_ram_map) =
        get_init_boot_image(avb_descriptors, partitions_ram_map);
    let (vendor_boot_image, partitions_ram_map) =
        get_vendor_boot_image(avb_descriptors, partitions_ram_map);
    (boot_image, init_boot_image, vendor_boot_image, partitions_ram_map)
}

// TODO: b/312607649 - Boot slot placeholder
#[derive(Debug, PartialEq)]
#[repr(u32)]
/// Boot slots used by ABR model
pub enum BootSlot {
    /// '_a'
    A = 0,
    /// '_b'
    B = 1,
}

impl Display for BootSlot {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let str = match self {
            BootSlot::A => "a",
            BootSlot::B => "b",
        };
        write!(f, "{str}")
    }
}

// TODO: b/312608785 - helper function that would track slices don't overlap
// [core::slice::from_raw_parts_mut] is not stable for `const` so we have to use `lazy_static` for
// initialization of constants.
unsafe fn mutex_buffer(address: usize, size: usize) -> Mutex<&'static mut [u8]> {
    // SAFETY: user should make sure that multiple function user doesn't use overlaping ranges.
    // And (addr, size) pair is safe to convert to slice.
    Mutex::new(unsafe { core::slice::from_raw_parts_mut(address as *mut u8, size) })
}

lazy_static! {
    // SAFETY: `test_default_memory_regions()' tests that slices don't overlap
    static ref BOOT_IMAGE: Mutex<&'static mut[u8]> = unsafe {
        mutex_buffer(0x1000_0000, 0x1000_0000)
    };
    // SAFETY: `test_default_memory_regions()' tests that slices don't overlap
    static ref KERNEL_IMAGE: Mutex<&'static mut[u8]> = unsafe {
        mutex_buffer(0x8020_0000, 0x0100_0000)
    };
    // SAFETY: `test_default_memory_regions()' tests that slices don't overlap
    static ref VENDOR_BOOT_IMAGE: Mutex<&'static mut[u8]> = unsafe {
        mutex_buffer(0x3000_0000, 0x1000_0000)
    };
    // SAFETY: `test_default_memory_regions()' tests that slices don't overlap
    static ref INIT_BOOT_IMAGE: Mutex<&'static mut[u8]> = unsafe {
        mutex_buffer(0x4000_0000, 0x1000_0000)
    };
    // SAFETY: `test_default_memory_regions()' tests that slices don't overlap
    static ref RAMDISK: Mutex<&'static mut[u8]> = unsafe {
        mutex_buffer(0x8420_0000, 0x0100_0000)
    };
    // SAFETY: `test_default_memory_regions()' tests that slices don't overlap
    static ref BOOTCONFIG: Mutex<&'static mut[u8]> = unsafe {
        mutex_buffer(0x6000_0000, 0x1000_0000)
    };
    // SAFETY: `test_default_memory_regions()' tests that slices don't overlap
    static ref DTB: Mutex<&'static mut[u8]> = unsafe {
        mutex_buffer(0x8000_0000, 0x0010_0000)
    };
}

#[derive(Debug)]
/// GBL object that provides implementation of helpers for boot process.
pub struct Gbl<'a, D, C> {
    ops: &'a mut dyn GblOps<D, C>,
    image_verification: bool,
}

impl<'a, D, C> Gbl<'a, D, C>
where
    D: Digest,
    C: Context<D>,
{
    fn new<'b>(ops: &'b mut impl GblOps<D, C>) -> Gbl<'a, D, C>
    where
        'b: 'a,
    {
        Gbl { ops, image_verification: true }
    }

    fn new_no_verification<'b>(ops: &'b mut impl GblOps<D, C>) -> Gbl<'a, D, C>
    where
        'b: 'a,
    {
        Gbl { ops, image_verification: false }
    }
}

impl<'a, D, C> Gbl<'a, D, C>
where
    D: Digest,
    C: Context<D>,
{
    /// Get Boot Mode
    ///
    /// # Returns
    ///
    /// * `Ok(())` - on success
    /// * `Err(Error)` - on failure
    pub fn get_boot_mode(&self) -> Result<BootMode> {
        unimplemented!();
    }

    /// Reset Boot Mode (strictly reset generic android struct - not vendor specific)
    ///
    /// # Returns
    ///
    /// * `Ok(())` - on success
    /// * `Err(Error)` - on failure
    pub fn reset_boot_mode(&mut self) -> Result<()> {
        unimplemented!();
    }

    /// Get Boot Slot
    ///
    /// # Returns
    ///
    /// * `Ok(&str)` - Slot Suffix as [BootSolt] enum
    /// * `Err(Error)` - on failure
    pub fn get_boot_slot(&self) -> Result<BootSlot> {
        unimplemented!();
    }

    /// Verify + Load Image Into memory
    ///
    /// Load from disk, validate with AVB
    ///
    /// # Arguments
    ///   * `partitions_ram_map` - Partitions to verify with optional address to load image to.
    ///   * `avb_verification_flags` - AVB verification flags/options
    ///   * `boot_slot` - Optional Boot Slot
    ///
    /// # Returns
    ///
    /// * `Ok(&[avb_descriptor])` - Array of AVB Descriptors - AVB return codes, partition name,
    /// image load address, image size, AVB Footer contents (version details, etc.)
    /// * `Err(Error)` - on failure
    pub fn load_and_verify_image<'b>(
        &self,
        partitions_ram_map: &mut [PartitionRamMap],
        avb_verification_flags: AvbVerificationFlags,
        boot_slot: Option<&BootSlot>,
    ) -> Result<&'b mut [AvbDescriptor]>
    where
        'a: 'b,
    {
        // TODO: b/312608785 - check that provided buffers don't overlap.
        // Default addresses to use
        let default_boot_image_buffer = BOOT_IMAGE.lock();
        let default_vendor_boot_image_buffer = VENDOR_BOOT_IMAGE.lock();
        let default_init_boot_image_buffer = INIT_BOOT_IMAGE.lock();
        unimplemented!("partition loading and verification");
    }

    /// Info Load
    ///
    /// Unpack boot image in RAM
    ///
    /// # Arguments
    ///   * `boot_image_buffer` - Buffer that contains (Optionally Verified) Boot Image
    ///   * `boot_mode` - Boot Mode
    ///   * `boot_slot` - [Optional] Boot Slot
    ///
    /// # Returns
    ///
    /// * `Ok(InfoStruct)` - Info Struct (Concatenated kernel commandline - includes slot,
    /// bootconfig selection, normal_mode, Concatenated bootconfig) on success
    /// * `Err(Error)` - on failure
    pub fn unpack_boot_image(
        &self,
        boot_image_buffer: &BootImage,
        boot_mode: &BootMode,
        boot_slot: Option<&BootSlot>,
    ) -> Result<InfoStruct> {
        unimplemented!();
    }

    /// Kernel Load
    ///
    /// Prepare kernel in RAM for booting
    ///
    /// # Arguments
    ///   * `info` - Info Struct from Info Load
    ///   * `image_buffer` - Buffer that contains (Verified) Boot Image
    ///   * `load_buffer` - Kernel Load buffer
    ///
    /// # Returns
    ///
    /// * `Ok(())` - on success
    /// * `Err(Error)` - on failure
    pub fn kernel_load(
        &self,
        info: &InfoStruct,
        image_buffer: BootImage,
        load_buffer: &mut [u8],
    ) -> Result<KernelImage> {
        unimplemented!();
    }

    /// Ramdisk + Bootconfig Load
    ///
    /// Kernel Load
    /// (Could break this into a RD and Bootconfig specific function each, TBD)
    /// Prepare ramdisk/bootconfig in RAM for booting
    ///
    /// # Arguments
    ///   * `info` - Info Struct from Info Load
    ///   * `vendor_boot_image` - Buffer that contains (Verified) Vendor Boot Image
    ///   * `init_boot_image` - Buffer that contains (Verified) Init Boot Image
    ///   * `ramdisk_load_buffer` - Ramdisk Load buffer (not compressed)
    ///   * `bootconfig_load_buffer` - Bootconfig Load buffer (not compressed). This bootconfig
    ///   will have data added at the end to include bootloader specific options such as
    ///   force_normal_boot and other other android specific details
    ///
    /// # Returns
    ///
    /// * `Ok(&str)` - on success returns Kernel command line
    /// * `Err(Error)` - on failure
    pub fn ramdisk_bootconfig_load(
        &self,
        info: &InfoStruct,
        vendor_boot_image: &VendorBootImage,
        init_boot_image: &InitBootImage,
        ramdisk_load_buffer: &mut [u8],
        bootconfig_load_buffer: &mut [u8],
    ) -> Result<&'static str> {
        unimplemented!();
    }

    /// DTB Update And Load
    ///
    /// Prepare DTB in RAM for booting
    ///
    /// # Arguments
    ///   * `info` - Info Struct from Info Load
    ///   * `vendor_boot_image_buffer` - Buffer that contains (Verified) Vendor Boot Image
    ///
    /// # Returns
    ///
    /// * `Ok()` - on success
    /// * `Err(Error)` - on failure
    pub fn dtb_update_and_load(
        &self,
        info: &InfoStruct,
        vendor_boot_image_buffer: VendorBootImage,
    ) -> Result<Dtb> {
        unimplemented!();
    }

    /// Kernel Jump
    ///
    ///
    /// # Arguments
    ///   * `kernel_load_buffer` - Kernel Load buffer
    ///   * `ramdisk_bootconfi_load_buffer` - Concatenated Ramdisk, (Bootconfig if present) Load
    ///   buffer
    ///   * `dtb_load_buffer` - DTB Load buffer
    ///
    /// # Returns
    ///
    /// * doesn't return on success
    /// * `Err(Error)` - on failure
    // Nevertype could be used here when it is stable https://github.com/serde-rs/serde/issues/812
    pub fn kernel_jump(
        &self,
        kernel_load_buffer: KernelImage,
        ramdisk_load_buffer: Ramdisk,
        dtb_load_buffer: Dtb,
    ) -> Result<()> {
        unimplemented!();
    }

    /// Load, verify, and boot
    ///
    /// Wrapper around the above functions for devices that don't need custom behavior between each
    /// step
    ///
    /// # Arguments
    ///   * `partitions_ram_map` - Partitions to verify and optional address for them to be loaded.
    ///   * `avb_verification_flags` - AVB verification flags/options
    ///
    /// # Returns
    ///
    /// * doesn't return on success
    /// * `Err(Error)` - on failure
    // Nevertype could be used here when it is stable https://github.com/serde-rs/serde/issues/812
    pub fn load_verify_boot<'b: 'c, 'c, 'd: 'b>(
        &mut self,
        partitions_ram_map: &'d mut [PartitionRamMap<'b, 'c>],
        avb_verification_flags: AvbVerificationFlags,
    ) -> Result<()> {
        let mut boot_mode = self.get_boot_mode()?;
        self.reset_boot_mode()?;

        // Handle fastboot mode
        if boot_mode == BootMode::Bootloader {
            let res = self.ops.do_fastboot();
            match res {
                // After `fastboot continue` we need to requery mode and continue usual process.
                Ok(_) => {
                    boot_mode = self.get_boot_mode()?;
                }
                // Fastboot is not available so we try continue
                Err(Error::NotImplemented) => (),
                // Fail on any other error
                Err(e) => return Err(e),
            }
        }

        let boot_slot = self.get_boot_slot()?;
        let avb_descriptors = self.load_and_verify_image(
            partitions_ram_map,
            AvbVerificationFlags(0),
            Some(&boot_slot),
        )?;

        let (boot_image, init_boot_image, vendor_boot_image, _) =
            get_images(avb_descriptors, partitions_ram_map);
        let boot_image = boot_image.ok_or(Error::MissingImage)?;
        let vendor_boot_image = vendor_boot_image.ok_or(Error::MissingImage)?;
        let init_boot_image = init_boot_image.ok_or(Error::MissingImage)?;

        let info_struct = self.unpack_boot_image(&boot_image, &boot_mode, Some(&boot_slot))?;

        let mut kernel_load_buffer = KERNEL_IMAGE.lock();
        let kernel_image = self.kernel_load(&info_struct, boot_image, &mut kernel_load_buffer)?;

        let mut ramdisk_load_buffer = RAMDISK.lock();
        let mut bootconfig_load_buffer = BOOTCONFIG.lock();
        let cmd_line = self.ramdisk_bootconfig_load(
            &info_struct,
            &vendor_boot_image,
            &init_boot_image,
            &mut ramdisk_load_buffer,
            &mut bootconfig_load_buffer,
        )?;

        self.dtb_update_and_load(&info_struct, vendor_boot_image)?;

        let mut dtb_load_buffer = DTB.lock();
        let dtb = Dtb(&mut dtb_load_buffer);
        let ramdisk = Ramdisk(&mut ramdisk_load_buffer);
        self.kernel_jump(kernel_image, ramdisk, dtb)
    }
}

impl<'a> Default for Gbl<'a, SwDigest, SwContext> {
    fn default() -> Self {
        Self { ops: DefaultGblOps::new(), image_verification: true }
    }
}

#[cfg(test)]
mod tests {
    extern crate itertools;

    use super::*;
    use itertools::Itertools;

    pub fn get_end(buf: &[u8]) -> Option<*const u8> {
        Some((buf.as_ptr() as usize).checked_add(buf.len())? as *const u8)
    }

    // Check if ranges overlap
    // Range is in form of [lower, upper)
    fn is_overlap(a: &[u8], b: &[u8]) -> bool {
        !((get_end(b).unwrap() <= a.as_ptr()) || (get_end(a).unwrap() <= b.as_ptr()))
    }

    #[test]
    fn test_default_memory_regions() {
        let memory_ranges = [
            &BOOT_IMAGE.lock(),
            &KERNEL_IMAGE.lock(),
            &VENDOR_BOOT_IMAGE.lock(),
            &INIT_BOOT_IMAGE.lock(),
            &RAMDISK.lock(),
            &BOOTCONFIG.lock(),
            &DTB.lock(),
        ];

        for (r1, r2) in memory_ranges.into_iter().tuple_combinations() {
            let overlap = is_overlap(r1, r2);
            assert!(
                !overlap,
                "Following pair overlap: ({}..{}), ({}..{})",
                r1.as_ptr() as usize,
                get_end(r1).unwrap() as usize,
                r2.as_ptr() as usize,
                get_end(r2).unwrap() as usize
            );
        }
    }
}
