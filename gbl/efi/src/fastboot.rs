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

use crate::{
    net::{EfiGblNetwork, EfiTcpSocket},
    ops::Ops,
};
use alloc::{boxed::Box, vec::Vec};
use core::{cmp::min, fmt::Write, future::Future, mem::take, pin::Pin, sync::atomic::AtomicU64};
use efi::{
    efi_print, efi_println,
    protocol::{gbl_efi_fastboot_usb::GblFastbootUsbProtocol, Protocol},
    EfiEntry,
};
use fastboot::{TcpStream, Transport};
use gbl_async::{block_on, YieldCounter};
use liberror::{Error, Result};
use libgbl::fastboot::{run_gbl_fastboot, GblTcpStream, GblUsbTransport, PinFutContainer};

const DEFAULT_TIMEOUT_MS: u64 = 5_000;
const FASTBOOT_TCP_PORT: u16 = 5554;

struct EfiFastbootTcpTransport<'a, 'b, 'c> {
    socket: &'c mut EfiTcpSocket<'a, 'b>,
}

impl<'a, 'b, 'c> EfiFastbootTcpTransport<'a, 'b, 'c> {
    fn new(socket: &'c mut EfiTcpSocket<'a, 'b>) -> Self {
        Self { socket: socket }
    }
}

impl TcpStream for EfiFastbootTcpTransport<'_, '_, '_> {
    /// Reads to `out` for exactly `out.len()` number bytes from the TCP connection.
    async fn read_exact(&mut self, out: &mut [u8]) -> Result<()> {
        self.socket.receive_exact(out, DEFAULT_TIMEOUT_MS).await
    }

    /// Sends exactly `data.len()` number bytes from `data` to the TCP connection.
    async fn write_exact(&mut self, data: &[u8]) -> Result<()> {
        self.socket.send_exact(data, DEFAULT_TIMEOUT_MS).await
    }
}

impl GblTcpStream for EfiFastbootTcpTransport<'_, '_, '_> {
    fn accept_new(&mut self) -> bool {
        let efi_entry = self.socket.efi_entry;
        self.socket.poll();
        // If not listenining, start listening.
        // If not connected but it's been `DEFAULT_TIMEOUT_MS`, restart listening in case the remote
        // client disconnects in the middle of TCP handshake and leaves the socket in a half open
        // state.
        if !self.socket.is_listening_or_handshaking()
            || (!self.socket.check_active()
                && self.socket.time_since_last_listen() > DEFAULT_TIMEOUT_MS)
        {
            let _ = self
                .socket
                .listen(FASTBOOT_TCP_PORT)
                .inspect_err(|e| efi_println!(efi_entry, "TCP listen error: {:?}", e));

            // TODO(b/368647237): Enable only in Fuchsia context.
            self.socket.broadcast_fuchsia_fastboot_mdns();
        } else if self.socket.check_active() {
            self.socket.set_io_yield_threshold(1024 * 1024); // 1MB
            let remote = self.socket.get_socket().remote_endpoint().unwrap();
            efi_println!(efi_entry, "TCP connection from {}", remote);
            return true;
        }
        false
    }
}

/// `UsbTransport` implements the `fastboot::Transport` trait using USB interfaces from
/// GBL_EFI_FASTBOOT_USB_PROTOCOL.
pub struct UsbTransport<'a> {
    max_packet_size: usize,
    protocol: Protocol<'a, GblFastbootUsbProtocol>,
    io_yield_counter: YieldCounter,
    // Buffer for prefetching an incoming packet in `wait_for_packet()`.
    // Alternatively we can also consider adding an EFI event for packet arrive. But UEFI firmware
    // may be more complicated.
    prefetched: (Vec<u8>, usize),
}

impl<'a> UsbTransport<'a> {
    fn new(max_packet_size: usize, protocol: Protocol<'a, GblFastbootUsbProtocol>) -> Self {
        Self {
            max_packet_size,
            protocol,
            io_yield_counter: YieldCounter::new(1024 * 1024),
            prefetched: (vec![0u8; max_packet_size], 0),
        }
    }

    /// Polls and cache the next USB packet.
    ///
    /// Returns Ok(true) if there is a new packet. Ok(false) if there is no incoming packet. Err()
    /// otherwise.
    fn poll_next_packet(&mut self) -> Result<bool> {
        match &mut self.prefetched {
            (pkt, len) if *len == 0 => match self.protocol.fastboot_usb_receive(pkt) {
                Ok(out_size) => {
                    *len = out_size;
                    return Ok(true);
                }
                Err(Error::NotReady) => return Ok(false),
                Err(e) => return Err(e),
            },
            _ => Ok(true),
        }
    }
}

impl Transport for UsbTransport<'_> {
    async fn receive_packet(&mut self, out: &mut [u8]) -> Result<usize> {
        let len = match &mut self.prefetched {
            (pkt, len) if *len > 0 => {
                let out = out.get_mut(..*len).ok_or(Error::BufferTooSmall(Some(*len)))?;
                let src = pkt.get(..*len).ok_or(Error::Other(Some("Invalid USB read size")))?;
                out.clone_from_slice(src);
                take(len)
            }
            _ => self.protocol.receive_packet(out).await?,
        };
        // Forces a yield to the executor if the data received/sent reaches a certain
        // threshold. This is to prevent the async code from holding up the CPU for too long
        // in case IO speed is high and the executor uses cooperative scheduling.
        self.io_yield_counter.increment(len.try_into().unwrap()).await;
        Ok(len)
    }

    async fn send_packet(&mut self, packet: &[u8]) -> Result<()> {
        let mut curr = &packet[..];
        while !curr.is_empty() {
            let to_send = min(curr.len(), self.max_packet_size);
            self.protocol.send_packet(&curr[..to_send], DEFAULT_TIMEOUT_MS).await?;
            // Forces a yield to the executor if the data received/sent reaches a certain
            // threshold. This is to prevent the async code from holding up the CPU for too long
            // in case IO speed is high and the executor uses cooperative scheduling.
            self.io_yield_counter.increment(to_send.try_into().unwrap()).await;
            curr = &curr[to_send..];
        }
        Ok(())
    }
}

impl GblUsbTransport for UsbTransport<'_> {
    fn has_packet(&mut self) -> bool {
        let efi_entry = self.protocol.efi_entry();
        self.poll_next_packet()
            .inspect_err(|e| efi_println!(efi_entry, "Error while polling next packet: {:?}", e))
            .unwrap_or(false)
    }
}

/// Initializes the Fastboot USB interface and returns a `UsbTransport`.
fn init_usb(efi_entry: &EfiEntry) -> Result<UsbTransport> {
    let protocol =
        efi_entry.system_table().boot_services().find_first_and_open::<GblFastbootUsbProtocol>()?;
    match protocol.fastboot_usb_interface_stop() {
        Err(e) if e != Error::NotStarted => Err(e),
        _ => Ok(UsbTransport::new(protocol.fastboot_usb_interface_start()?, protocol)),
    }
}

// Wrapper of vector of pinned futures.
#[derive(Default)]
struct VecPinFut<'a>(Vec<Pin<Box<dyn Future<Output = ()> + 'a>>>);

impl<'a> PinFutContainer<'a> for VecPinFut<'a> {
    fn add_with<F: Future<Output = ()> + 'a>(&mut self, f: impl FnOnce() -> F) {
        self.0.push(Box::pin(f()));
    }

    fn for_each_remove_if(
        &mut self,
        mut cb: impl FnMut(&mut Pin<&mut (dyn Future<Output = ()> + 'a)>) -> bool,
    ) {
        for idx in (0..self.0.len()).rev() {
            cb(&mut self.0[idx].as_mut()).then(|| self.0.swap_remove(idx));
        }
    }
}

pub fn fastboot(efi_gbl_ops: &mut Ops) -> Result<()> {
    let efi_entry = efi_gbl_ops.efi_entry;
    efi_println!(efi_entry, "Entering fastboot mode...");

    let usb = init_usb(efi_entry)
        .inspect(|_| efi_println!(efi_entry, "Started Fastboot over USB."))
        .inspect_err(|e| efi_println!(efi_entry, "Failed to start Fastboot over USB. {:?}.", e))
        .ok();

    let ts = AtomicU64::new(0);
    let mut net: EfiGblNetwork = Default::default();
    let mut tcp = net
        .init(efi_entry, &ts)
        .inspect(|v| {
            efi_println!(efi_entry, "Started Fastboot over TCP");
            efi_println!(efi_entry, "IP address:");
            v.interface().ip_addrs().iter().for_each(|v| {
                efi_println!(efi_entry, "\t{}", v.address());
            });
        })
        .inspect_err(|e| efi_println!(efi_entry, "Failed to start EFI network. {:?}.", e))
        .ok();
    let tcp = tcp.as_mut().map(|v| EfiFastbootTcpTransport::new(v));

    let download_buffers = vec![vec![0u8; 512 * 1024 * 1024]; 2].into();
    block_on(run_gbl_fastboot(efi_gbl_ops, &download_buffers, VecPinFut::default(), usb, tcp));
    Ok(())
}
