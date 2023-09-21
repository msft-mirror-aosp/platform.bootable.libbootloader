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
use efi::defs::*;

// The following is a minimal hello world like application and is mainly for
// testing the UEFI toolchain. It'll be updated to a full generic bootloader
// application as development goes.

fn puts(system_table_ptr: *mut EfiSystemTable, msg: &str) {
    let systab = unsafe { *system_table_ptr };
    let console_out_protocol = unsafe { *systab.con_out };
    match console_out_protocol.output_string {
        Some(output_string) => {
            for ch in msg.as_bytes() {
                let mut char16_msg: [u16; 2usize] = [*ch as u16, 0];
                unsafe {
                    output_string(systab.con_out, char16_msg.as_mut_ptr());
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
    let efi_table_header = systab.header;
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
