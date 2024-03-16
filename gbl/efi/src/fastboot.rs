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

// This EFI application implements a demo for booting Android/Fuchsia from disk. See
// bootable/libbootloader/gbl/README.md for how to run the demo. See comments of
// `android_boot:android_boot_demo()` and `fuchsia_boot:fuchsia_boot_demo()` for
// supported/unsupported features at the moment.

use crate::error::Result;
use crate::net::{with_efi_network, EfiTcpSocket};
use core::fmt::Write;
use core::str::Split;
use efi::{efi_print, efi_println, EfiEntry};
use fastboot::{CommandError, Fastboot, FastbootImplementation, TcpStream, TransportError};

const DEFAULT_TIMEOUT_MS: u64 = 5_000;
const FASTBOOT_TCP_PORT: u16 = 5554;

struct EfiFastbootTcpTransport<'a, 'b, 'c> {
    transport_error: &'c mut Result<()>,
    socket: &'c mut EfiTcpSocket<'a, 'b>,
}

impl TcpStream for EfiFastbootTcpTransport<'_, '_, '_> {
    /// Reads to `out` for exactly `out.len()` number bytes from the TCP connection.
    fn read_exact(&mut self, out: &mut [u8]) -> core::result::Result<(), TransportError> {
        *self.transport_error = self.socket.receive_exact(out, DEFAULT_TIMEOUT_MS);
        self.transport_error.as_ref().map_err(|_| TransportError::Others(""))?;
        Ok(())
    }

    /// Sends exactly `data.len()` number bytes from `data` to the TCP connection.
    fn write_exact(&mut self, data: &[u8]) -> core::result::Result<(), TransportError> {
        *self.transport_error = self.socket.send_exact(data, DEFAULT_TIMEOUT_MS);
        self.transport_error.as_ref().map_err(|_| TransportError::Others(""))?;
        Ok(())
    }
}

/// TODO(b/328786603): Placeholder only. It'll be replaced by a generic GBL Fastboot implementation
/// in a separate library.
pub struct GblFastboot {}

impl FastbootImplementation for GblFastboot {
    fn get_var(
        &mut self,
        _: &str,
        _: Split<char>,
        _: &mut [u8],
    ) -> core::result::Result<usize, CommandError> {
        Err("Not found".into())
    }

    fn get_var_all<F>(&mut self, _: F) -> core::result::Result<(), CommandError>
    where
        F: FnMut(&str, &[&str], &str),
    {
        Ok(())
    }
}

/// Internal helper for performing Fastboot over TCP.
fn fastboot_tcp_usb(
    socket: &mut EfiTcpSocket,
    efi_entry: &EfiEntry,
    download_buffer: &mut [u8],
) -> Result<()> {
    let mut gbl_fastboot = GblFastboot {};
    efi_println!(efi_entry, "Listening for Fastboot over TCP...");
    efi_println!(efi_entry, "IP addresses:");
    socket.interface().ip_addrs().iter().for_each(|v| {
        efi_println!(efi_entry, "\t{}", v.address());
    });
    loop {
        socket.listen(FASTBOOT_TCP_PORT)?;
        let listen_start = EfiTcpSocket::timestamp(0);
        loop {
            socket.poll();
            if socket.check_active() {
                // Has connection.
                efi_println!(
                    efi_entry,
                    "Connection from {}",
                    socket.get_socket().remote_endpoint().unwrap()
                );

                let mut transport_error = Ok(());
                let mut transport = EfiFastbootTcpTransport {
                    transport_error: &mut transport_error,
                    socket: socket,
                };
                let mut fastboot = Fastboot::new(&mut download_buffer[..]);
                let _ = fastboot.run_tcp_session(&mut transport, &mut gbl_fastboot);
                efi_println!(efi_entry, "Fastboot TCP session ends. {:?}", transport_error);
                break;
            } else if EfiTcpSocket::timestamp(listen_start) > DEFAULT_TIMEOUT_MS {
                // Reset once in a while in case a remote client disconnects in the middle of
                // TCP handshake and leaves the socket in a half open state.
                break;
            }

            // Perform Fastboot over USB here.
        }
    }
}

/// Runs Fastboot.
pub fn run_fastboot(efi_entry: &EfiEntry) -> Result<()> {
    // TODO(b/328786603): Figure out where to get download buffer size.
    let mut download_buffer = vec![0u8; 512 * 1024 * 1024];
    match with_efi_network(efi_entry, |socket| -> Result<()> {
        fastboot_tcp_usb(socket, efi_entry, &mut download_buffer[..])
    })? {
        Err(e) => {
            efi_println!(efi_entry, "Failed to initilaize network {:?}", e);
            // Perform Fastboot over USB here.
        }
        _ => {}
    };
    Ok(())
}
