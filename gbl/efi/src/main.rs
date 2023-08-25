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

#![no_std]
#![no_main]

#[cfg(target_arch = "riscv64")]
mod riscv64;

use core::fmt::Write;
use core::panic::PanicInfo;
use zerocopy::{AsBytes, FromBytes, LayoutVerified};

// The following is a minimal hello world like application and is mainly for
// testing the UEFI toolchain. It'll be updated to a full generic bootloader
// application as development goes.

// UEFI simple text output protocol. For this hello world application, we only
// need the `output_string` function.
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct SimpleTextOutputProtocol {
    pub reset: *mut core::ffi::c_void,
    pub output_string: ::core::option::Option<
        unsafe extern "C" fn(self_: *mut SimpleTextOutputProtocol, string: *mut u16) -> usize,
    >,
    pub test_string: *mut core::ffi::c_void,
    pub query_mode: *mut core::ffi::c_void,
    pub set_mode: *mut core::ffi::c_void,
    pub set_attribute: *mut core::ffi::c_void,
    pub clear_screen: *mut core::ffi::c_void,
    pub set_cursor_position: *mut core::ffi::c_void,
    pub enable_cursor: *mut core::ffi::c_void,
    pub mode: *mut core::ffi::c_void,
}

// UEFI system table. For this hello world application, we only need the
// console out simple text output protocol.
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct EfiSystemTable {
    pub efi_table_header: [u8; 24usize],
    pub firmware_vendor: *mut u16,
    pub firmware_version: u32,
    pub console_in_handle: *mut core::ffi::c_void,
    pub console_in_protocol: *mut core::ffi::c_void,
    pub console_out_handle: *mut core::ffi::c_void,
    pub console_out_protocol: *mut SimpleTextOutputProtocol,
    pub standard_error_handle: *mut core::ffi::c_void,
    pub standard_error_protocol: *mut SimpleTextOutputProtocol,
    pub run_time_service: *mut core::ffi::c_void,
    pub boot_service: *mut core::ffi::c_void,
    pub number_of_table_entries: usize,
    pub configuration_table: *const core::ffi::c_void,
}

#[derive(FromBytes, AsBytes)]
#[repr(C)]
pub struct EfiTableHeader {
    pub signature: u64,
    pub revision: u32,
    pub header_size: u32,
    pub crc32: u32,
    pub reserved: u32,
}

fn puts(system_table_ptr: *mut EfiSystemTable, msg: &str) {
    let systab = unsafe { *system_table_ptr };
    let console_out_protocol = unsafe { *systab.console_out_protocol };
    match console_out_protocol.output_string {
        Some(output_string) => {
            for ch in msg.as_bytes() {
                let mut char16_msg: [u16; 2usize] = [*ch as u16, 0];
                unsafe {
                    output_string(systab.console_out_protocol, char16_msg.as_mut_ptr());
                }
            }
        }
        None => {}
    }
}

struct EfiConsole {
    system_table_ptr: *mut EfiSystemTable,
}

impl Write for EfiConsole {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        puts(self.system_table_ptr, s);
        Ok(())
    }
}

#[no_mangle]
pub extern "C" fn efi_main(
    _image_handle: *mut core::ffi::c_void,
    system_table_ptr: *mut EfiSystemTable,
) {
    let systab = unsafe { *system_table_ptr };
    let efi_table_header =
        LayoutVerified::<_, EfiTableHeader>::new(&systab.efi_table_header[..]).unwrap();
    let mut efi_console = EfiConsole { system_table_ptr };
    puts(system_table_ptr, "Rust EFI application.\n");
    puts(system_table_ptr, "EFI header table:\n");
    write!(&mut efi_console, "  signature: {}\n", efi_table_header.signature).unwrap();
    write!(&mut efi_console, "  revision: {}\n", efi_table_header.revision).unwrap();
    write!(&mut efi_console, "  header_size: {}\n", efi_table_header.header_size).unwrap();
    write!(&mut efi_console, "  crc32: {}\n", efi_table_header.crc32).unwrap();
    loop {}
}

#[panic_handler]
fn panic(_panic: &PanicInfo) -> ! {
    loop {}
}
