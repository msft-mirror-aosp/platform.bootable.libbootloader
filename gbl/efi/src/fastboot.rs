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
    efi_blocks::{find_block_devices, EfiBlockDeviceIo},
    error::{EfiAppError, GblEfiError, Result as GblResult},
    net::{with_efi_network, EfiTcpSocket},
};
use alloc::vec::Vec;
use core::{cmp::min, fmt::Write, future::Future, result::Result};
use efi::{
    defs::{EFI_STATUS_NOT_READY, EFI_STATUS_NOT_STARTED},
    efi_print, efi_println,
    protocol::{android_boot::AndroidBootProtocol, Protocol},
    utils::Timeout,
    EfiEntry,
};
use fastboot::{
    process_next_command, run_tcp_session, CommandError, TcpStream, Transport, TransportError,
};
use gbl_async::{yield_now, YieldCounter};
use gbl_cyclic_executor::CyclicExecutor;
use libgbl::fastboot::{GblFastboot, GblFbResource, TasksExecutor};
use spin::Mutex;

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
    async fn read_exact(&mut self, out: &mut [u8]) -> Result<(), TransportError> {
        self.last_err = self.socket.receive_exact(out, DEFAULT_TIMEOUT_MS).await;
        self.last_err.as_ref().map_err(|_| TransportError::Others("TCP read error"))?;
        Ok(())
    }

    /// Sends exactly `data.len()` number bytes from `data` to the TCP connection.
    async fn write_exact(&mut self, data: &[u8]) -> Result<(), TransportError> {
        self.last_err = self.socket.send_exact(data, DEFAULT_TIMEOUT_MS).await;
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
    io_yield_counter: YieldCounter,
}

impl<'a, 'b> UsbTransport<'a, 'b> {
    fn new(max_packet_size: usize, protocol: &'b Protocol<'a, AndroidBootProtocol>) -> Self {
        Self {
            last_err: Ok(()),
            max_packet_size,
            protocol,
            io_yield_counter: YieldCounter::new(u64::MAX),
        }
    }

    /// Sets the maximum number of bytes to read or write before a force await.
    pub fn set_io_yield_threshold(&mut self, threshold: u64) {
        self.io_yield_counter = YieldCounter::new(threshold)
    }

    /// Waits for the previous send to complete up to `DEFAULT_TIMEOUT_MS` timeout.
    async fn wait_for_send(&self) -> GblResult<()> {
        let timer = Timeout::new(self.protocol.efi_entry(), DEFAULT_TIMEOUT_MS)?;
        let bs = self.protocol.efi_entry().system_table().boot_services();
        while !timer.check()? {
            match bs.check_event(&self.protocol.wait_for_send_completion()?)? {
                true => return Ok(()),
                _ => yield_now().await,
            }
        }
        Err(EfiAppError::Timeout.into())
    }
}

impl Transport for UsbTransport<'_, '_> {
    async fn receive_packet(&mut self, out: &mut [u8]) -> Result<usize, TransportError> {
        let mut out_size = 0;
        self.last_err = Ok(());
        match self.protocol.fastboot_usb_receive(out, &mut out_size) {
            Ok(()) => {
                // Forces a yield to the executor if the data received/sent reaches a certain
                // threshold. This is to prevent the async code from holding up the CPU for too long
                // in case IO speed is high and the executor uses cooperative scheduling.
                self.io_yield_counter.increment(out_size.try_into().unwrap()).await;
                Ok(out_size)
            }
            Err(e) if e.is_efi_err(EFI_STATUS_NOT_READY) => Ok(0),
            Err(e) => {
                self.last_err = Err(e.into());
                Err(TransportError::Others("USB receive error"))
            }
        }
    }

    async fn send_packet(&mut self, packet: &[u8]) -> Result<(), TransportError> {
        self.last_err = async {
            let mut curr = &packet[..];
            while !curr.is_empty() {
                let to_send = min(curr.len(), self.max_packet_size);
                let mut out_size = 0;
                self.protocol.fastboot_usb_send(&curr[..to_send], &mut out_size)?;
                // Forces a yield to the executor if the data received/sent reaches a certain
                // threshold. This is to prevent the async code from holding up the CPU for too long
                // in case IO speed is high and the executor uses cooperative scheduling.
                self.io_yield_counter.increment(to_send.try_into().unwrap()).await;
                curr = &curr[to_send..];
                self.wait_for_send().await?;
            }
            Ok(())
        }
        .await;
        Ok(*self.last_err.as_ref().map_err(|_| TransportError::Others("USB send error"))?)
    }
}

/// Loops and polls both USB and TCP transport. Runs Fastboot if any is available.
async fn fastboot_loop<'a>(
    efi_entry: &EfiEntry,
    gbl_fb: &mut GblFastboot<'_, 'a, EfiFbTaskExecutor<'a>, &'_ mut EfiBlockDeviceIo<'_>>,
    mut socket: Option<&mut EfiTcpSocket<'_, '_>>,
    mut usb: Option<&mut UsbTransport<'_, '_>>,
) {
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
            usb.set_io_yield_threshold(1024 * 1024); // 1MB
            if process_next_command(*usb, gbl_fb).await.is_err() {
                efi_println!(efi_entry, "Fastboot USB error: {:?}", usb.last_err);
            }
        }

        // Checks and processes commands over TCP.
        if let Some(socket) = socket.as_mut() {
            socket.set_io_yield_threshold(1024 * 1024); // 1MB
            socket.poll();
            let mut reset_socket = false;
            if socket.check_active() {
                let remote = socket.get_socket().remote_endpoint().unwrap();
                efi_println!(efi_entry, "TCP connection from {}", remote);
                let mut transport = EfiFastbootTcpTransport::new(socket);
                let _ = run_tcp_session(&mut transport, gbl_fb).await;
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

        yield_now().await;
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

/// `EfiFbTaskExecutor` implements the `TasksExecutor` trait used by GBL fastboot for scheduling
/// disk IO tasks.
#[derive(Default)]
struct EfiFbTaskExecutor<'a>(Mutex<CyclicExecutor<'a>>);

impl<'a> TasksExecutor<'a> for EfiFbTaskExecutor<'a> {
    fn spawn_task(&self, task: impl Future<Output = ()> + 'a) -> Result<(), CommandError> {
        Ok(self.0.lock().spawn_task(task))
    }
}

/// Spawns and runs Fastboot tasks.
fn run_fastboot<'a>(
    efi_entry: &EfiEntry,
    gbl_fb: &mut GblFastboot<'_, 'a, EfiFbTaskExecutor<'a>, &'_ mut EfiBlockDeviceIo<'_>>,
    blk_io_executor: &EfiFbTaskExecutor<'a>,
    socket: Option<&mut EfiTcpSocket<'_, '_>>,
    usb: Option<&mut UsbTransport<'_, '_>>,
) -> GblResult<()> {
    if socket.is_none() && usb.is_none() {
        return Err(EfiAppError::Unsupported.into());
    }
    let mut task_executor: CyclicExecutor = Default::default();
    // Fastboot command loop task.
    task_executor.spawn_task(fastboot_loop(efi_entry, gbl_fb, socket, usb));
    // Disk IO task.
    task_executor.spawn_task(async {
        loop {
            blk_io_executor.0.lock().poll();
            yield_now().await;
        }
    });
    task_executor.run();
    Ok(())
}

/// Runs Fastboot.
pub fn fastboot(
    efi_entry: &EfiEntry,
    android_boot_protocol: Option<&Protocol<'_, AndroidBootProtocol>>,
) -> GblResult<()> {
    // TODO(b/328786603): Figure out where to get download buffer size.
    let mut download_buffers = vec![vec![0u8; 512 * 1024 * 1024]; 2];
    let mut gbl_fb_download_buffers =
        download_buffers.iter_mut().map(|v| v.as_mut_slice()).collect::<Vec<_>>();
    let mut blks = find_block_devices(efi_entry)?;
    let mut gbl_fb_devs = blks.0.iter_mut().map(|v| v.as_gpt_dev().into()).collect::<Vec<_>>();
    let shared_state = GblFbResource::new(&mut gbl_fb_devs[..], &mut gbl_fb_download_buffers[..]);
    let blk_io_executor: EfiFbTaskExecutor = Default::default();
    let gbl_fb = &mut GblFastboot::new(&blk_io_executor, &shared_state);

    let mut usb = match init_usb(&android_boot_protocol) {
        Ok(v) => Some(v),
        Err(e) => {
            efi_println!(efi_entry, "Failed to start Fastboot over USB. {:?}.", e);
            None
        }
    };

    match with_efi_network(efi_entry, |socket| {
        run_fastboot(efi_entry, gbl_fb, &blk_io_executor, Some(socket), usb.as_mut())
    }) {
        Err(e) => {
            efi_println!(efi_entry, "Failed to start EFI network. {:?}.", e);
            run_fastboot(efi_entry, gbl_fb, &blk_io_executor, None, usb.as_mut())
        }
        v => v?,
    }
}
