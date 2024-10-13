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
use alloc::vec::Vec;
use core::{
    cell::RefCell, cmp::min, fmt::Write, future::Future, mem::take, sync::atomic::AtomicU64,
};
use efi::{
    efi_print, efi_println,
    protocol::{gbl_efi_fastboot_usb::GblFastbootUsbProtocol, Protocol},
    EfiEntry,
};
use fastboot::{
    process_next_command, run_tcp_session, CommandResult, FastbootImplementation, TcpStream,
    Transport,
};
use gbl_async::{yield_now, YieldCounter};
use gbl_cyclic_executor::CyclicExecutor;
use liberror::{Error, Result};
use libgbl::fastboot::{GblFastboot, TasksExecutor};
use spin::{Mutex, MutexGuard};

const DEFAULT_TIMEOUT_MS: u64 = 5_000;
const FASTBOOT_TCP_PORT: u16 = 5554;

struct EfiFastbootTcpTransport<'a, 'b, 'c> {
    last_err: Result<()>,
    socket: &'c mut EfiTcpSocket<'a, 'b>,
}

impl<'a, 'b, 'c> EfiFastbootTcpTransport<'a, 'b, 'c> {
    fn new(socket: &'c mut EfiTcpSocket<'a, 'b>) -> Self {
        Self { last_err: Ok(()), socket: socket }
    }
}

impl TcpStream for EfiFastbootTcpTransport<'_, '_, '_> {
    /// Reads to `out` for exactly `out.len()` number bytes from the TCP connection.
    async fn read_exact(&mut self, out: &mut [u8]) -> Result<()> {
        self.last_err = self.socket.receive_exact(out, DEFAULT_TIMEOUT_MS).await;
        self.last_err.as_ref().or(Err(Error::Other(Some("Tcp read error"))))?;
        Ok(())
    }

    /// Sends exactly `data.len()` number bytes from `data` to the TCP connection.
    async fn write_exact(&mut self, data: &[u8]) -> Result<()> {
        self.last_err = self.socket.send_exact(data, DEFAULT_TIMEOUT_MS).await;
        self.last_err.as_ref().or(Err(Error::Other(Some("Tcp write error"))))?;
        Ok(())
    }
}

/// `UsbTransport` implements the `fastboot::Transport` trait using USB interfaces from
/// GBL_EFI_FASTBOOT_USB_PROTOCOL.
pub struct UsbTransport<'a> {
    last_err: Result<()>,
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
            last_err: Ok(()),
            max_packet_size,
            protocol,
            io_yield_counter: YieldCounter::new(u64::MAX),
            prefetched: (vec![0u8; max_packet_size], 0),
        }
    }

    /// Sets the maximum number of bytes to read or write before a force await.
    pub fn set_io_yield_threshold(&mut self, threshold: u64) {
        self.io_yield_counter = YieldCounter::new(threshold)
    }

    /// Reads the next packet from the EFI USB protocol into the given buffer.
    async fn receive_next_from_efi(&mut self, out: &mut [u8]) -> Result<usize> {
        match self.protocol.receive_packet(out).await {
            Ok(sz) => {
                // Forces a yield to the executor if the data received/sent reaches a certain
                // threshold. This is to prevent the async code from holding up the CPU for too long
                // in case IO speed is high and the executor uses cooperative scheduling.
                self.io_yield_counter.increment(sz.try_into().unwrap()).await;
                return Ok(sz);
            }
            Err(e) => {
                self.last_err = Err(e.into());
                return Err(Error::Other(Some("USB receive error")));
            }
        }
    }

    /// Waits until a packet is cached into an internal buffer.
    async fn cache_next_packet(&mut self) -> Result<()> {
        match &mut self.prefetched {
            (pkt, len) if *len == 0 => {
                let mut packet = take(pkt);
                let len = self.receive_next_from_efi(&mut packet[..]).await?;
                self.prefetched = (packet, len);
            }
            _ => {}
        }
        Ok(())
    }
}

impl Transport for UsbTransport<'_> {
    async fn receive_packet(&mut self, out: &mut [u8]) -> Result<usize> {
        match &mut self.prefetched {
            (pkt, len) if *len > 0 => {
                let out = out.get_mut(..*len).ok_or(Error::BufferTooSmall(Some(*len)))?;
                let src = pkt.get(..*len).ok_or(Error::Other(Some("Invalid USB read size")))?;
                out.clone_from_slice(src);
                return Ok(take(len));
            }
            _ => self.receive_next_from_efi(out).await,
        }
    }

    async fn send_packet(&mut self, packet: &[u8]) -> Result<()> {
        self.last_err = async {
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
        .await;
        Ok(*self.last_err.as_ref().map_err(|_| Error::Other(Some("USB send error")))?)
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

/// `EfiFbTaskExecutor` implements the `TasksExecutor` trait used by GBL fastboot for scheduling
/// disk IO tasks.
#[derive(Default)]
struct EfiFbTaskExecutor<'a>(RefCell<CyclicExecutor<'a>>);

impl<'a> TasksExecutor<'a> for EfiFbTaskExecutor<'a> {
    fn spawn_task(&self, task: impl Future<Output = ()> + 'a) -> CommandResult<()> {
        // The method is synchronous and we expect it to run in the same thread (enforced by
        // `RefCell` not being Sync). Thus the borrow should always succeed.
        Ok(self.0.borrow_mut().spawn_task(task))
    }

    fn poll_all(&self) {
        self.0.borrow_mut().poll();
    }
}

/// Waits until a shared resource protected by a mutex is acquired successfully.
async fn lock<T>(resource: &Mutex<T>) -> MutexGuard<T> {
    loop {
        // Yield first so that repetitive calls guarantees at least one yield.
        yield_now().await;
        match resource.try_lock() {
            Some(v) => return v,
            _ => {}
        }
    }
}

/// Task routine for Fastboot over USB.
async fn fastboot_usb(
    efi_entry: &EfiEntry,
    gbl_fb: &Mutex<&mut impl FastbootImplementation>,
    usb: &mut UsbTransport<'_>,
) {
    usb.set_io_yield_threshold(1024 * 1024); // 1MB
    loop {
        match usb.cache_next_packet().await {
            Err(_) => efi_println!(efi_entry, "Fastboot USB error: {:?}", usb.last_err),
            _ => match process_next_command(usb, *lock(gbl_fb).await).await {
                Err(_) => efi_println!(efi_entry, "Fastboot USB error: {:?}", usb.last_err),
                _ => {}
            },
        }
    }
}

/// Task routine for Fastboot over TCP.
async fn fastboot_tcp(
    efi_entry: &EfiEntry,
    gbl_fb: &Mutex<&mut impl FastbootImplementation>,
    socket: &mut EfiTcpSocket<'_, '_>,
) {
    socket.set_io_yield_threshold(1024 * 1024); // 1MB
    loop {
        // Acquires the lock before proceeding to handle network. This reduces interference to the
        // Fastboot USB task which maybe in the middle of a download. `lock()` internally yields
        // control to the executor and check later if the mutex can't be acquired.
        let mut gbl_fb = lock(gbl_fb).await;
        socket.poll();
        let mut reset_socket = false;
        if socket.check_active() {
            let remote = socket.get_socket().remote_endpoint().unwrap();
            efi_println!(efi_entry, "TCP connection from {}", remote);
            let mut transport = EfiFastbootTcpTransport::new(socket);
            let _ = run_tcp_session(&mut transport, *gbl_fb).await;
            match transport.last_err {
                Ok(()) | Err(Error::Disconnected) => {}
                Err(e) => efi_println!(efi_entry, "Fastboot TCP error {:?}", e),
            }
            reset_socket = true;
        }
        // Reset once in a while in case a remote client disconnects in the middle of
        // TCP handshake and leaves the socket in a half open state.
        if reset_socket || socket.time_since_last_listen() > DEFAULT_TIMEOUT_MS {
            if let Err(e) = socket.listen(FASTBOOT_TCP_PORT) {
                efi_println!(efi_entry, "TCP listen error: {:?}", e);
            }
        }
        // Necessary because our executor uses cooperative scheduling.
        yield_now().await;
    }
}

/// Runs Fastboot.
pub fn fastboot(efi_gbl_ops: &mut Ops) -> Result<()> {
    let efi_entry = efi_gbl_ops.efi_entry;
    efi_println!(efi_entry, "Entering fastboot mode...");
    // TODO(b/328786603): Figure out where to get download buffer size.
    let mut download_buffers = vec![vec![0u8; 512 * 1024 * 1024]; 2];
    let download_buffers =
        download_buffers.iter_mut().map(|v| v.as_mut_slice().into()).collect::<Vec<_>>();
    let blk_io_executor: EfiFbTaskExecutor = Default::default();
    let gbl_fb = &mut GblFastboot::new(&blk_io_executor, efi_gbl_ops, &download_buffers);

    // Scans USB.
    let mut usb = init_usb(efi_entry)
        .inspect_err(|e| efi_println!(efi_entry, "Failed to start Fastboot over USB. {:?}.", e))
        .ok();

    // Scans TCP.
    let ts = AtomicU64::new(0);
    let mut net: EfiGblNetwork = Default::default();
    let mut socket = net
        .init(efi_entry, &ts)
        .inspect_err(|e| efi_println!(efi_entry, "Failed to start EFI network. {:?}.", e))
        .ok();

    if usb.is_none() && socket.is_none() {
        return Err(Error::Unsupported);
    }

    // Prepares various fastboot tasks.
    let gbl_fb = gbl_fb.into();
    let mut task_executor: CyclicExecutor = Default::default();
    // Fastboot over USB task.
    match usb {
        Some(ref mut v) => {
            efi_println!(efi_entry, "Started Fastboot over USB.");
            task_executor.spawn_task(fastboot_usb(efi_entry, &gbl_fb, v));
        }
        _ => {}
    }
    // Fastboot over TCP task.
    match socket {
        Some(ref mut v) => {
            efi_println!(efi_entry, "Started Fastboot over TCP");
            efi_println!(efi_entry, "IP address:");
            v.interface().ip_addrs().iter().for_each(|v| {
                efi_println!(efi_entry, "\t{}", v.address());
            });
            task_executor.spawn_task(fastboot_tcp(efi_entry, &gbl_fb, v));
        }
        _ => {}
    }
    // Task for scheduling disk IO tasks spawned by Fastboot.
    task_executor.spawn_task(async {
        loop {
            blk_io_executor.poll_all();
            yield_now().await;
        }
    });
    // Run all tasks.
    task_executor.run();
    Ok(())
}
