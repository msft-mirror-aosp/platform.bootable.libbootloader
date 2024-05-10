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

use crate::error::{EfiAppError, GblEfiError, Result as GblResult};
use crate::net::{with_efi_network, EfiTcpSocket};
use crate::utils::{find_gpt_devices, loop_with_timeout};
use core::{fmt::Write, result::Result};
use efi::{
    defs::{EFI_STATUS_NOT_READY, EFI_STATUS_NOT_STARTED},
    efi_print, efi_println,
    protocol::{android_boot::AndroidBootProtocol, Protocol},
    EfiEntry,
};
use fastboot::{Fastboot, TcpStream, Transport, TransportError};
use libgbl::fastboot::GblFastboot;

const DEFAULT_TIMEOUT_MS: u64 = 5_000;
const FASTBOOT_TCP_PORT: u16 = 5554;

struct EfiFastbootTcpTransport<'a, 'b, 'c> {
    last_err: GblResult<()>,
    socket: &'c mut EfiTcpSocket<'a, 'b>,
}

impl<'a, 'b, 'c> EfiFastbootTcpTransport<'a, 'b, 'c> {
    fn new(socket: &'c mut EfiTcpSocket<'a, 'b>) -> Self {
        Self { last_err: Ok(()), socket: socket }
    }
}

impl TcpStream for EfiFastbootTcpTransport<'_, '_, '_> {
    /// Reads to `out` for exactly `out.len()` number bytes from the TCP connection.
    fn read_exact(&mut self, out: &mut [u8]) -> Result<(), TransportError> {
        self.last_err = self.socket.receive_exact(out, DEFAULT_TIMEOUT_MS);
        self.last_err.as_ref().map_err(|_| TransportError::Others("TCP read error"))?;
        Ok(())
    }

    /// Sends exactly `data.len()` number bytes from `data` to the TCP connection.
    fn write_exact(&mut self, data: &[u8]) -> Result<(), TransportError> {
        self.last_err = self.socket.send_exact(data, DEFAULT_TIMEOUT_MS);
        self.last_err.as_ref().map_err(|_| TransportError::Others("TCP write error"))?;
        Ok(())
    }
}

/// `UsbTransport` implements the `fastboot::Transport` trait using USB interfaces from
/// EFI_ANDROID_BOOT_PROTOCOL.
pub struct UsbTransport<'a, 'b> {
    last_err: GblResult<()>,
    max_packet_size: usize,
    protocol: &'b Protocol<'a, AndroidBootProtocol>,
}

impl<'a, 'b> UsbTransport<'a, 'b> {
    fn new(max_packet_size: usize, protocol: &'b Protocol<'a, AndroidBootProtocol>) -> Self {
        Self { last_err: Ok(()), max_packet_size: max_packet_size, protocol: protocol }
    }

    /// Waits for the previous send to complete up to `DEFAULT_TIMEOUT_MS` timeout.
    fn wait_for_send(&self) -> GblResult<()> {
        loop_with_timeout(self.protocol.efi_entry(), DEFAULT_TIMEOUT_MS, || {
            match (|| -> GblResult<bool> {
                Ok(self
                    .protocol
                    .efi_entry()
                    .system_table()
                    .boot_services()
                    .check_event(&self.protocol.wait_for_send_completion()?)?)
            })() {
                Ok(true) => Ok(Ok(())),
                Ok(false) => Err(false),
                Err(e) => Ok(Err(e)),
            }
        })?
        .ok_or(EfiAppError::Timeout)??;
        Ok(())
    }
}

impl Transport for UsbTransport<'_, '_> {
    fn receive_packet(&mut self, out: &mut [u8]) -> Result<usize, TransportError> {
        let mut out_size = 0;
        self.last_err = Ok(());
        match self.protocol.fastboot_usb_receive(out, &mut out_size) {
            Ok(()) => Ok(out_size),
            Err(e) if e.is_efi_err(EFI_STATUS_NOT_READY) => Ok(0),
            Err(e) => {
                self.last_err = Err(e.into());
                Err(TransportError::Others("USB receive error"))
            }
        }
    }

    fn send_packet(&mut self, packet: &[u8]) -> Result<(), TransportError> {
        let mut sent = 0;
        self.last_err = (|| -> GblResult<()> {
            while sent < packet.len() {
                let to_send = core::cmp::min(packet.len() - sent, self.max_packet_size);
                let mut out_size = 0;
                self.protocol.fastboot_usb_send(&packet[sent..][..to_send], &mut out_size)?;
                self.wait_for_send()?;
                sent += to_send;
            }
            Ok(())
        })();
        Ok(*self.last_err.as_ref().map_err(|_| TransportError::Others("USB send error"))?)
    }
}

/// Loops and polls both USB and TCP transport. Runs Fastboot if any is available.
fn fastboot_loop(
    efi_entry: &EfiEntry,
    gbl_fb: &mut GblFastboot,
    fastboot: &mut Fastboot,
    mut socket: Option<&mut EfiTcpSocket>,
    mut usb: Option<&mut UsbTransport>,
) -> GblResult<()> {
    if socket.is_none() && usb.is_none() {
        return Err(EfiAppError::Unsupported.into());
    }

    efi_println!(efi_entry, "Fastboot USB: {}", usb.as_ref().map_or("No", |_| "Yes"));
    if let Some(socket) = socket.as_ref() {
        efi_println!(efi_entry, "Fastboot TCP: Yes");
        efi_println!(efi_entry, "Device IP addresses:");
        socket.interface().ip_addrs().iter().for_each(|v| {
            efi_println!(efi_entry, "\t{}", v.address());
        });
    } else {
        efi_println!(efi_entry, "Fastboot TCP: No");
    }

    let mut listen_start_timestamp = EfiTcpSocket::timestamp(0);
    loop {
        // Checks and processes commands over USB.
        if let Some(usb) = usb.as_mut() {
            if fastboot.process_next_command(*usb, gbl_fb).is_err() {
                efi_println!(efi_entry, "Fastboot USB error: {:?}", usb.last_err);
            }
        }

        // Checks and processes commands over TCP.
        if let Some(socket) = socket.as_mut() {
            socket.poll();
            let mut reset_socket = false;
            if socket.check_active() {
                let remote = socket.get_socket().remote_endpoint().unwrap();
                efi_println!(efi_entry, "TCP connection from {}", remote);
                let mut transport = EfiFastbootTcpTransport::new(socket);
                let _ = fastboot.run_tcp_session(&mut transport, gbl_fb);
                match transport.last_err {
                    Ok(()) | Err(GblEfiError::EfiAppError(EfiAppError::PeerClosed)) => {}
                    Err(e) => {
                        efi_println!(efi_entry, "Fastboot TCP error {:?}", e);
                    }
                }
                reset_socket = true;
            } else if EfiTcpSocket::timestamp(listen_start_timestamp) > DEFAULT_TIMEOUT_MS {
                // Reset once in a while in case a remote client disconnects in the middle of
                // TCP handshake and leaves the socket in a half open state.
                reset_socket = true;
            }

            if reset_socket {
                listen_start_timestamp = EfiTcpSocket::timestamp(0);
                if let Err(e) = socket.listen(FASTBOOT_TCP_PORT) {
                    efi_println!(efi_entry, "TCP listen error: {:?}", e);
                }
            }
        }
    }
}

/// Initializes the Fastboot USB interface and returns a `UsbTransport`.
fn init_usb<'a, 'b>(
    android_boot_protocol: &Option<&'b Protocol<'a, AndroidBootProtocol>>,
) -> GblResult<UsbTransport<'a, 'b>> {
    let protocol = android_boot_protocol.ok_or(EfiAppError::Unsupported)?;
    match protocol.fastboot_usb_interface_stop() {
        Err(e) if !e.is_efi_err(EFI_STATUS_NOT_STARTED) => return Err(e.into()),
        _ => {}
    };
    Ok(UsbTransport::new(protocol.fastboot_usb_interface_start()?, protocol))
}

/// Runs Fastboot.
pub fn run_fastboot(
    efi_entry: &EfiEntry,
    android_boot_protocol: Option<&Protocol<'_, AndroidBootProtocol>>,
) -> GblResult<()> {
    let mut gpt_devices = find_gpt_devices(efi_entry)?;
    let mut gbl_fb = GblFastboot::new(&mut gpt_devices);
    // TODO(b/328786603): Figure out where to get download buffer size.
    let mut download_buffer = vec![0u8; 512 * 1024 * 1024];
    let mut fastboot = Fastboot::new(&mut download_buffer[..]);

    let mut usb = match init_usb(&android_boot_protocol) {
        Ok(v) => Some(v),
        Err(e) => {
            efi_println!(efi_entry, "Failed to start Fastboot over USB. {:?}.", e);
            None
        }
    };

    match with_efi_network(efi_entry, |socket| -> GblResult<()> {
        fastboot_loop(efi_entry, &mut gbl_fb, &mut fastboot, Some(socket), usb.as_mut())
    }) {
        Err(e) => {
            efi_println!(efi_entry, "Failed to start EFI network. {:?}.", e);
            fastboot_loop(efi_entry, &mut gbl_fb, &mut fastboot, None, usb.as_mut())
        }
        v => v?,
    }
}
