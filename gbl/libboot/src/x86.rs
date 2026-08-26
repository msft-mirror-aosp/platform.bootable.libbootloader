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

//! Boot protocol implementation for x86 platforms.
//!
//! For linux, the library currently only supports bzimage and protocol version 2.06+.
//! Specifically, modern memory layout is used, protected kernel is loaded to high address at
//! 0x100000 and command line size can be greater than 255 characters.
//!
//!                     ~                        ~
//!                     |  Protected-mode kernel |
//!             100000  +------------------------+
//!                     |  I/O memory hole       |
//!             0A0000  +------------------------+
//!                     |  Reserved for BIOS     |      Leave as much as possible unused
//!                     ~                        ~
//!                     |  Command line          |      (Can also be below the X+10000 mark)
//!                     +------------------------+
//!                     |  Stack/heap            |      For use by the kernel real-mode code.
//!  low_mem_addr+08000 +------------------------+
//!                     |  Kernel setup          |      The kernel real-mode code.
//!                     |  Kernel boot sector    |      The kernel legacy boot sector.
//!        low_mem_addr +------------------------+
//!                     |  Boot loader           |      <- Boot sector entry point 0000:7C00
//!             001000  +------------------------+
//!                     |  Reserved for MBR/BIOS |
//!             000800  +------------------------+
//!                     |  Typically used by MBR |
//!             000600  +------------------------+
//!                     |  BIOS use only         |
//!             000000  +------------------------+
//!
//! See https://www.kernel.org/doc/html/v5.11/x86/boot.html#the-linux-x86-boot-protocol for more
//! detail.

use core::arch::asm;
use core::mem::size_of;
use core::slice::from_raw_parts_mut;
use liberror::{Error, Result};
#[cfg(feature = "fuchsia")]
use zbi::ZbiContainer;

pub use x86_bootparam_defs::{boot_e820_entry as e820entry, boot_params, efi_info, setup_header};
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout, Ref};

// Sector size is fixed to 512
const SECTOR_SIZE: usize = 512;
/// Boot sector and setup code section is 32K at most.
const BOOT_SETUP_LOAD_SIZE: usize = 0x8000;
/// Address for loading the protected mode kernel
const LOAD_ADDR_HIGH: usize = 0x10_0000;
// Flag value to use high address for protected mode kernel.
const LOAD_FLAG_LOADED_HIGH: u8 = 0x1;

/// In 64-bit boot protocol, the kernel is started by jumping to the
/// 64-bit kernel entry point, which is the start address of loaded
/// 64-bit kernel plus 0x200.
#[cfg(target_arch = "x86_64")]
const ENTRY_POINT_OFFSET: usize = 0x200;

/// Selectors the 64-bit Linux boot protocol requires to be live on entry; see
/// Documentation/arch/x86/boot.rst, "64-bit BOOT PROTOCOL".
#[cfg(target_arch = "x86_64")]
const BOOT_CS: u16 = 0x10;
#[cfg(target_arch = "x86_64")]
const BOOT_DS: u16 = 0x18;

/// Operand of `lgdt`.
#[cfg(target_arch = "x86_64")]
#[repr(C, packed)]
struct GdtDescriptor {
    limit: u16,
    base: u64,
}

#[cfg(target_arch = "x86_64")]
#[repr(align(8))]
struct AlignedGdt([u64; 4]);

/// Flat descriptors for [BOOT_CS] and [BOOT_DS].
///
/// A selector is a byte offset into the table, so [BOOT_CS] is entry 2 and [BOOT_DS] is entry 3.
/// Entry 1 exists to place them there; it holds the 32-bit flat code descriptor that the kernel's
/// own early GDT keeps in the same slot.
#[cfg(target_arch = "x86_64")]
static BOOT_GDT: AlignedGdt = AlignedGdt([
    0,
    0x00cf9a000000ffff, // 32-bit flat code.
    0x00af9a000000ffff, // 64-bit flat code, BOOT_CS.
    0x00cf92000000ffff, // Flat data, BOOT_DS.
]);

/// E820 RAM address range type.
pub const E820_ADDRESS_TYPE_RAM: u32 = 1;
/// E820 reserved address range type.
pub const E820_ADDRESS_TYPE_RESERVED: u32 = 2;
/// E820 ACPI address range type.
pub const E820_ADDRESS_TYPE_ACPI: u32 = 3;
/// E820 NVS address range type.
pub const E820_ADDRESS_TYPE_NVS: u32 = 4;
/// E820 unusable address range type.
pub const E820_ADDRESS_TYPE_UNUSABLE: u32 = 5;
/// E820 PMEM address range type.
pub const E820_ADDRESS_TYPE_PMEM: u32 = 7;

/// Wrapper for `struct boot_params {}` C structure
#[repr(transparent)]
#[derive(Copy, Clone, Immutable, FromBytes, IntoBytes, KnownLayout)]
pub struct BootParams(boot_params);

impl BootParams {
    /// Cast a bytes into a reference of BootParams header
    pub fn from_bytes_ref(buffer: &[u8]) -> Result<&BootParams> {
        Ok(Ref::into_ref(
            Ref::<_, BootParams>::new_from_prefix(buffer)
                .ok_or(Error::BufferTooSmall(Some(size_of::<BootParams>())))?
                .0,
        ))
    }

    /// Cast a bytes into a mutable reference of BootParams header.
    pub fn from_bytes_mut(buffer: &mut [u8]) -> Result<&mut BootParams> {
        Ok(Ref::into_mut(
            Ref::<_, BootParams>::new_from_prefix(buffer)
                .ok_or(Error::BufferTooSmall(Some(size_of::<BootParams>())))?
                .0,
        ))
    }

    /// Return a mutable reference of the `setup_header` struct field in `boot_params`
    pub fn setup_header_mut(&mut self) -> &mut setup_header {
        &mut self.0.hdr
    }

    /// Return a const reference of the `setup_header` struct field in `boot_params`
    pub fn setup_header_ref(&self) -> &setup_header {
        &self.0.hdr
    }

    /// Checks whether image is valid and version is supported.
    pub fn check(&self) -> Result<()> {
        // Check magic.
        if !(self.setup_header_ref().boot_flag == 0xAA55
            && self.setup_header_ref().header.to_le_bytes() == *b"HdrS")
        {
            return Err(Error::BadMagic);
        }

        // Check if it is bzimage and version is supported.
        if !(self.0.hdr.version >= 0x0206
            && ((self.setup_header_ref().loadflags & LOAD_FLAG_LOADED_HIGH) != 0))
        {
            return Err(Error::UnsupportedVersion);
        }

        Ok(())
    }

    /// Gets the number of sectors in the setup code section.
    pub fn setup_sects(&self) -> usize {
        match self.setup_header_ref().setup_sects {
            0 => 4,
            v => v as usize,
        }
    }

    /// Gets the offset to the protected mode kernel in the image.
    ///
    /// The value is also the same as the sum of legacy boot sector plus setup code size.
    pub fn kernel_off(&self) -> usize {
        // one boot sector + setup sectors
        (1 + self.setup_sects()) * SECTOR_SIZE
    }

    /// Gets e820 map entries.
    pub fn e820_map(&mut self) -> &mut [e820entry] {
        &mut self.0.e820_table[..]
    }

    /// Gets efi_info by copying.
    pub fn get_efi_info(&self) -> efi_info {
        self.0.efi_info
    }

    /// Sets efi_info by copying.
    pub fn set_efi_info(&mut self, info: efi_info) {
        self.0.efi_info = info;
    }
}

/// Helper to setup boot params and relocate bzimage kernel.
///
/// # Safety
///
/// * `low_mem_addr` must point to valid low memory buffer.
/// * `LOAD_ADDR_HIGH` (0x10_0000) must be available for kernel relocation.
unsafe fn setup_bzimage_boot_params<'a>(
    kernel: &[u8],
    ramdisk: &[u8],
    cmdline: &[u8],
    low_mem_addr: usize,
) -> Result<&'a mut BootParams> {
    let bootparam = BootParams::from_bytes_ref(&kernel[..])?;
    bootparam.check()?;

    // low memory address greater than 0x9_0000 is bogus.
    assert!(low_mem_addr <= 0x9_0000);
    // SAFETY: By safety requirement of this function, `low_mem_addr` points to sufficiently large
    // memory.
    let boot_param_buffer =
        unsafe { from_raw_parts_mut(low_mem_addr as *mut _, BOOT_SETUP_LOAD_SIZE) };
    // Note: We currently boot directly from protected mode kernel and bypass real-mode kernel.
    // Thus we omit the heap section. Revisit this if we encounter platforms that have to boot from
    // real-mode kernel.
    let cmdline_start = low_mem_addr + BOOT_SETUP_LOAD_SIZE;
    // Should not reach into I/O memory hole section.
    assert!(cmdline_start + cmdline.len() <= 0x0A0000);
    // SAFETY: By safety requirement of this function, `low_mem_addr` points to sufficiently large
    // memory.
    let cmdline_buffer = unsafe { from_raw_parts_mut(cmdline_start as *mut _, cmdline.len()) };

    let boot_sector_size = bootparam.kernel_off();
    // Copy protected mode kernel to load address
    // SAFETY: By safety requirement of this function, `LOAD_ADDR_HIGH` points to sufficiently
    // large memory.
    unsafe {
        from_raw_parts_mut(LOAD_ADDR_HIGH as *mut u8, kernel[boot_sector_size..].len())
            .clone_from_slice(&kernel[boot_sector_size..]);
    }

    // Zeroizes the entire boot sector.
    boot_param_buffer.fill(0);
    let bootparam_fixup = BootParams::from_bytes_mut(boot_param_buffer)?;
    // Only copies over the header. Leaves the rest zeroes.
    *bootparam_fixup.setup_header_mut() =
        *BootParams::from_bytes_ref(&kernel[..])?.setup_header_ref();

    let bootparam_fixup = BootParams::from_bytes_mut(boot_param_buffer)?;

    // Sets commandline.
    cmdline_buffer.clone_from_slice(cmdline);
    bootparam_fixup.setup_header_mut().cmd_line_ptr = cmdline_start.try_into().unwrap();
    bootparam_fixup.setup_header_mut().cmdline_size = cmdline.len().try_into().unwrap();

    // Sets ramdisk address.
    bootparam_fixup.setup_header_mut().ramdisk_image = (ramdisk.as_ptr() as usize).try_into()?;
    bootparam_fixup.setup_header_mut().ramdisk_size = ramdisk.len().try_into()?;

    // Sets to loader type "special loader". (Anything other than 0, otherwise linux kernel ignores
    // ramdisk.)
    bootparam_fixup.setup_header_mut().type_of_loader = 0xff;

    Ok(bootparam_fixup)
}

/// Boots a Linux bzimage.
///
/// # Args
///
/// * `kernel`: Buffer holding the loaded bzimage.
///
/// * `ramdisk`: Buffer holding the loaded ramdisk.
///
/// * `cmdline`: Command line argument blob.
///
/// * `mmap_cb`: A caller provided callback for setting the e820 memory map. The callback takes in
///     a mutable reference of e820 map entries (&mut [e820entry]). On success, it should return
///     the number of used entries. On error, it can return a
///     `Error::MemoryMapCallbackError(<code>)` to propagate a custom error code.
///
/// * `low_mem_addr`: The lowest memory touched by the bootloader section. This is where boot param
///      starts.
///
/// * The API is not expected to return on success.
///
/// # Safety
///
/// * Caller must ensure that `kernel` contains a valid Linux kernel and `low_mem_addr` is valid.
/// * Caller must ensure that there is enough memory at address 0x10_0000 for relocating `kernel`.
pub unsafe fn boot_linux_bzimage<F>(
    kernel: &[u8],
    ramdisk: &[u8],
    cmdline: &[u8],
    mmap_cb: F,
    low_mem_addr: usize,
) -> Result<!>
where
    F: FnOnce(&mut [e820entry], &mut efi_info) -> Result<u8>,
{
    // SAFETY: Forwarding safety requirements to helper.
    let bootparam_fixup =
        unsafe { setup_bzimage_boot_params(kernel, ramdisk, cmdline, low_mem_addr)? };

    // Fix up e820 memory map.
    let mut efi_info = bootparam_fixup.get_efi_info();
    let num_entries = mmap_cb(bootparam_fixup.e820_map(), &mut efi_info)?;
    bootparam_fixup.set_efi_info(efi_info);
    bootparam_fixup.0.e820_entries = num_entries;

    // Establish the segment state the 64-bit boot protocol requires, then enter the kernel.
    //
    // A plain `jmp` would leave CS as whatever the firmware was using. The protocol requires
    // entry through BOOT_CS, so push the selector and the target and reload CS with a far
    // return; `.byte 0x48, 0xcb` is `rex.W retf`, which has no mnemonic in Rust's assembler.
    //
    // SAFETY: By safety requirement of this function, input contains a valid linux kernel.
    unsafe {
        let gdt_descriptor = GdtDescriptor {
            limit: (size_of::<AlignedGdt>() - 1) as u16,
            base: BOOT_GDT.0.as_ptr() as u64,
        };
        asm!(
            // Mask interrupts before touching the GDT. UEFI runs boot services with interrupts
            // enabled and ExitBootServices() does not clear IF, so an interrupt taken between
            // the lgdt and the cli would be dispatched through the firmware IDT against a
            // descriptor table that no longer holds the selectors it refers to.
            "cli",
            "lgdt [rdx]",
            "mov ax, {boot_ds}",
            "mov ds, ax",
            "mov es, ax",
            "mov ss, ax",
            "cld",
            "push {boot_cs}",
            "push rcx",
            ".byte 0x48, 0xcb",
            in("rdx") &gdt_descriptor,
            in("rcx") LOAD_ADDR_HIGH + ENTRY_POINT_OFFSET,
            in("rsi") low_mem_addr,
            boot_cs = const BOOT_CS,
            boot_ds = const BOOT_DS,
            options(noreturn),
        );
    }
}

/// Jump to prepared ZBI Fuchsia entry
///
/// SAFETY:
/// Caller must ensure `entry` is valid entry point for kernel.
/// Caller must ensure `data` is valid ZBI data and is 4K aligned.
#[cfg(feature = "fuchsia")]
pub unsafe fn zbi_boot_raw(entry: usize, data: &[u8]) -> ! {
    // Clears stack pointers, interrupt and jumps to protected mode kernel.
    // SAFETY: By safety requirement of this function, input contains a valid ZBI kernel.
    unsafe {
        asm!(
            "xor ebp, ebp",
            "xor esp, esp",
            "cld",
            "cli",
            "jmp {ep}",
            ep = in(reg) entry,
            in("rsi") data.as_ptr(),
        );
    }

    unreachable!();
}

/// Boot ZBI kernel from provided ZBI containers
///
/// SAFETY:
/// Caller must ensure `kernel` is valid ZBI kernel and is 4K aligned.
/// Caller must ensure `data` is valid ZBI data and is 4K aligned.
#[cfg(feature = "fuchsia")]
pub unsafe fn zbi_boot(kernel: &[u8], data: &[u8]) -> ! {
    let (entry, _) =
        ZbiContainer::parse(kernel).unwrap().get_kernel_entry_and_reserved_memory_size().unwrap();
    let addr = (kernel.as_ptr() as usize).checked_add(usize::try_from(entry).unwrap()).unwrap();
    // SAFETY:
    // `addr` is calculated from kernel ZBI, which is valid according to safety requirements for
    // `zbi_boot()` function.
    // `data` is required to be valid ZBI data as per safety requirements for `zbi_boot()`
    unsafe { zbi_boot_raw(addr, data) };
}
