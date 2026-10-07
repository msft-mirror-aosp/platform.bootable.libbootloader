// Copyright 2026, The Android Open Source Project
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

//! Standalone test kernel main loop in Rust.

#![no_std]
#![no_main]

use bootparams::bootconfig::extract_bootconfig;
use core::{
    alloc::{GlobalAlloc, Layout},
    slice::from_raw_parts,
};
use fdt::Fdt;
use libutils::FromHexStr;
use opendice::{dice::bcc_handover_parse, extract_subject_algorithm_from_dice_chain};
use pvmfwconfig::{PvmfwConfig, PvmfwConfigEntryType};
use semihosting::{File, OpenMode};
use trace::trace_total_size;
// Noop allocator to meet dependency requirement.
struct StubAllocator;

// SAFETY: This is a noop allocator.
unsafe impl GlobalAlloc for StubAllocator {
    unsafe fn alloc(&self, _layout: Layout) -> *mut u8 {
        core::ptr::null_mut()
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
}

#[global_allocator]
static ALLOCATOR: StubAllocator = StubAllocator;

/// Stack canary guard value for ELF stack protector.
#[no_mangle]
pub static __stack_chk_guard: usize = 0xffffffff;

/// Stack protector failure handler for ELF objects.
#[no_mangle]
pub extern "C" fn __stack_chk_fail() -> ! {
    semihosting::println!("ERROR: Stack protection check failed inside custom test_kernel!");
    semihosting::shutdown(1);
}

/// Rust exception handling personality stub.
#[no_mangle]
pub extern "C" fn rust_eh_personality() {}

/// Trap handler for trap-mode UBSan.
#[no_mangle]
pub extern "C" fn gbl_ubsan_trap() -> ! {
    semihosting::println!("ERROR: UBSan trap triggered inside custom test_kernel!");
    semihosting::shutdown(1);
}

/// Linux like kernel main entry
///
/// # Safety
///
/// * Caller must guarantee that `fdt_addr` points to a valid device tree blob.
/// * Caller must guarantee that `linux,initrd-start` and `linux,initrd-end` mark a valid ramdisk
///   address range if specified
/// * Caller must guarantee that `androidboot.gbl.trace_addr` and `androidboot.gbl.trace_size`
///   mark a valid GBL trace address range if specified.
/// * Caller must guarantee that the `reg` property of `/reserved-memory/pkvm_guest_firmware`
///   marks a valid pvmfw address range if the node is present.
#[no_mangle]
pub unsafe extern "C" fn kernel_main(fdt_addr: *const u8) -> ! {
    semihosting::println!("GBL Custom Kernel loaded and self-relocated successfully from Rust!");

    // For now we don't expect fdt to be null.
    assert!(!fdt_addr.is_null());

    // Parses FDT
    // SAFETY: By safety contract, if fdt_addr is not null, it points to a valid dtb.
    let (_, slice) = unsafe { fdt::FdtHeader::from_raw(fdt_addr) }
        .inspect_err(|e| semihosting::println!("Failed to parse fdt {e}"))
        .unwrap();
    let fdt = Fdt::new(slice).unwrap();
    // Extract ramdisk range
    let initrd_start_prop = fdt.get_property("chosen", c"linux,initrd-start").unwrap();
    let initrd_end_prop = fdt.get_property("chosen", c"linux,initrd-end").unwrap();
    let initrd_start = u64::from_be_bytes(initrd_start_prop.try_into().unwrap());
    let initrd_end = u64::from_be_bytes(initrd_end_prop.try_into().unwrap());
    let ramdisk_len = usize::try_from(initrd_end - initrd_start).unwrap();

    // SAFETY: By safety contract, `linux,initrd-start` and `linux,initrd-end` marks a valid
    // ramdisk address range.
    let ramdisk_slice = unsafe { from_raw_parts(initrd_start as *const u8, ramdisk_len) };
    let bootconfig = extract_bootconfig(ramdisk_slice)
        .inspect_err(|e| semihosting::println!("Failed to extract bootconfig: {:?}", e))
        .unwrap();

    let trace_addr: Option<usize> = find_bootconfig(bootconfig, "androidboot.gbl.trace_addr")
        .and_then(|v| FromHexStr::try_from_hex_str(v).ok());
    let trace_size: Option<usize> = find_bootconfig(bootconfig, "androidboot.gbl.trace_size")
        .and_then(|v| FromHexStr::try_from_hex_str(v).ok());
    if let Some((addr, sz)) = trace_addr.zip(trace_size) {
        semihosting::println!("Found trace buffer at {addr:#x}, sz: {sz:#x}");
        // SAFETY: By safety contract, `trace_addr` and `trace_size` marks a valid
        // trace address range.
        let trace = unsafe { from_raw_parts(addr as *const u8, sz) };
        // Make sure D-cache is flushed for the trace data.
        boot::aarch64::flush_dcache_buffer(trace);
        if let Some(v) = trace_total_size(trace).ok().filter(|v| *v != 0) {
            semihosting::println!("trace data size: {v}");
            let mut f = File::open(c"trace.bin", OpenMode::WriteBinary).unwrap();
            f.write(&trace[..v]).unwrap();
        }
    }

    let is_normal = find_bootconfig(bootconfig, "androidboot.force_normal_boot") == Some("1");
    semihosting::println!("Normal Mode: {is_normal:?}",);

    // SAFETY: By safety contract, the `reg` property of `/reserved-memory/pkvm_guest_firmware`
    // marks a valid pvmfw address range.
    if let Some(config_data) = unsafe { pvmfw_config_data(&fdt) } {
        let config = PvmfwConfig::from_bytes(config_data).expect("Failed to parse pvmfw config");
        let dice_handover = config
            .entry(PvmfwConfigEntryType::DiceHandover)
            .expect("Failed to read DICE handover entry");
        assert!(!dice_handover.is_empty());
        let parsed = bcc_handover_parse(dice_handover).expect("Failed to parse DICE handover");
        let bcc = parsed.bcc.expect("Missing BCC in DICE handover");
        let extracted_alg =
            extract_subject_algorithm_from_dice_chain(bcc).expect("Failed to extract subject alg");
        semihosting::println!("[DICE-TEST] Extracted algorithm: {:?}", extracted_alg);
    }

    semihosting::println!("Exiting QEMU test via semihosting.");
    // Terminate QEMU cleanly via libsemihosting
    semihosting::shutdown(0);
}

/// Returns the pvmfw configuration data from the region described by
/// `/reserved-memory/pkvm_guest_firmware`, or `None` if the region is not described.
///
/// # Safety
///
/// Caller must guarantee that the `reg` property of `/reserved-memory/pkvm_guest_firmware`, if
/// present, marks a valid pvmfw address range.
unsafe fn pvmfw_config_data(fdt: &Fdt<&[u8]>) -> Option<&'static [u8]> {
    const PVMFW_NODE_PATH: &str = "/reserved-memory/pkvm_guest_firmware";
    let reg_prop = fdt.get_property(PVMFW_NODE_PATH, c"reg").ok()?;

    // `reg` is encoded with the cell counts declared on `/reserved-memory`.
    let address_cells = fdt.get_property_u32("/reserved-memory", c"#address-cells").unwrap();
    let size_cells = fdt.get_property_u32("/reserved-memory", c"#size-cells").unwrap();
    let (base_bytes, size_bytes) = reg_prop.split_at(4 * address_cells as usize);
    assert_eq!(size_bytes.len(), 4 * size_cells as usize, "unexpected pvmfw `reg` length");

    let config_offset = fdt.get_property_u32(PVMFW_NODE_PATH, c"config-data-offset").unwrap();

    // SAFETY: By safety contract, `reg` marks a valid pvmfw address range.
    let pvmfw =
        unsafe { from_raw_parts(read_cells(base_bytes) as *const u8, read_cells(size_bytes)) };
    Some(&pvmfw[config_offset as usize..])
}

/// Decodes a big-endian device tree cell sequence of up to 64 bits.
fn read_cells(bytes: &[u8]) -> usize {
    let mut buf = [0u8; 8];
    buf[8 - bytes.len()..].copy_from_slice(bytes);
    u64::from_be_bytes(buf).try_into().unwrap()
}

/// Helper function to find a bootconfig value by key. If multiple entries with the same
/// key exist, the last one is returned. Assignment ":=" operator is not supported.
fn find_bootconfig<'a>(config: &'a str, key: &str) -> Option<&'a str> {
    Some(config.lines().filter_map(|v| v.split_once('=').filter(|(k, _)| *k == key)).last()?.1)
}

#[panic_handler]
fn panic(p_info: &core::panic::PanicInfo) -> ! {
    semihosting::println!("Panic! {}", p_info);
    semihosting::shutdown(1);
}

/// Unwind resume stub required for ELF linking.
#[no_mangle]
pub extern "C" fn _Unwind_Resume(_: *mut core::ffi::c_void) {
    panic!();
}
