// Copyright (C) 2026 The Android Open Source Project
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
// limitations under the License.

//! This crate provides utilities for Virtio VSOCK in GBL.

#![no_std]

extern crate alloc;

use acpi::{sdt::mcfg::Mcfg, AcpiTables, Handler as AcpiHandler, PciAddress, PhysicalMapping};
use alloc::alloc::{alloc, dealloc, Layout};
use core::{ptr::NonNull, time::Duration};
use efi::{
    utils::{find_acpi_configuration_table, find_fdt_configuration_table},
    EfiEntry,
};
use liberror::Error;
use libutils::arch_timestamp;
use spin::Mutex;
pub use virtio_drivers::device::socket::VsockAddr;
use virtio_drivers::{
    device::socket::{VirtIOSocket, VsockConnectionManager, VsockEvent, VsockEventType},
    transport::{
        pci::{
            bus::{Cam, MmioCam, PciRoot},
            virtio_device_type, PciTransport,
        },
        DeviceType,
    },
    BufferDirection, Hal, PhysAddr,
};

mod fastboot_transport;
pub use fastboot_transport::FastbootTransport;

const EFI_PAGE_SIZE: usize = efi_types::EFI_PAGE_SIZE as usize;

#[derive(Clone)]
struct GblAcpiHandler;

#[rustfmt::skip]
impl AcpiHandler for GblAcpiHandler {
    /// # Safety: Caller should follow the safety requirements in
    /// acpi::Handler::map_physical_region.
    unsafe fn map_physical_region<T>(
        &self,
        physical_address: usize,
        size: usize,
    ) -> PhysicalMapping<Self, T> {
        PhysicalMapping {
            physical_start: physical_address,
            virtual_start: NonNull::new(physical_address as _).unwrap(),
            region_length: size,
            mapped_length: size,
            handler: GblAcpiHandler,
        }
    }

    fn unmap_physical_region<T>(_: &PhysicalMapping<Self, T>) {}
    fn read_u8(&self, _address: usize) -> u8 { unimplemented!() }
    fn read_u16(&self, _address: usize) -> u16 { unimplemented!() }
    fn read_u32(&self, _address: usize) -> u32 { unimplemented!() }
    fn read_u64(&self, _address: usize) -> u64 { unimplemented!() }
    fn write_u8(&self, _address: usize, _value: u8) { unimplemented!() }
    fn write_u16(&self, _address: usize, _value: u16) { unimplemented!() }
    fn write_u32(&self, _address: usize, _value: u32) { unimplemented!() }
    fn write_u64(&self, _address: usize, _value: u64) { unimplemented!() }
    fn read_io_u8(&self, _port: u16) -> u8 { unimplemented!() }
    fn read_io_u16(&self, _port: u16) -> u16 { unimplemented!() }
    fn read_io_u32(&self, _port: u16) -> u32 { unimplemented!() }
    fn write_io_u8(&self, _port: u16, _value: u8) { unimplemented!() }
    fn write_io_u16(&self, _port: u16, _value: u16) { unimplemented!() }
    fn write_io_u32(&self, _port: u16, _value: u32) { unimplemented!() }
    fn read_pci_u8(&self, _address: PciAddress, _offset: u16) -> u8 { unimplemented!() }
    fn read_pci_u16(&self, _address: PciAddress, _offset: u16) -> u16 { unimplemented!() }
    fn read_pci_u32(&self, _address: PciAddress, _offset: u16) -> u32 { unimplemented!() }
    fn write_pci_u8(&self, _address: PciAddress, _offset: u16, _value: u8) { unimplemented!() }
    fn write_pci_u16(&self, _address: PciAddress, _offset: u16, _value: u16) { unimplemented!() }
    fn write_pci_u32(&self, _address: PciAddress, _offset: u16, _value: u32) { unimplemented!() }
    fn nanos_since_boot(&self) -> u64 { unimplemented!() }
    fn stall(&self, _microseconds: u64) { unimplemented!() }
    fn sleep(&self, _milliseconds: u64) { unimplemented!() }
}

/// Detects the ECAM base address using ACPI or Device Tree.
pub fn detect_ecam(entry: &EfiEntry) -> Option<(u64, u64)> {
    get_ecam_from_acpi(entry).or_else(|| get_ecam_from_dt(entry))
}

/// Gets ECAM address and size from ACPI (i.e. EDK platforms).
fn get_ecam_from_acpi(entry: &EfiEntry) -> Option<(u64, u64)> {
    let acpi_ptr = find_acpi_configuration_table(entry)?;
    // SAFETY: By UEFI spec, the ACPI configuration table gives the ACPI address.
    let tables = unsafe { AcpiTables::from_rsdp(GblAcpiHandler, acpi_ptr as _).ok()? };

    let mcfg_mapping = tables.find_table::<Mcfg>()?;
    mcfg_mapping.entries().iter().next().map(|entry| {
        (
            entry.base_address,
            (entry.bus_number_end as u64 - entry.bus_number_start as u64 + 1) * 0x100000,
        )
    })
}

/// Gets ECAM address and size from device tree (i.e. u-boot platforms).
fn get_ecam_from_dt(entry: &EfiEntry) -> Option<(u64, u64)> {
    let (_header, dt) = find_fdt_configuration_table(entry)?;
    let fdt = fdt::Fdt::new(dt).ok()?;
    // Virtio is almost exclusively used for qemu, which hardcodes pcie@10000000 as the base
    // address for pcie devices. Revisit if we ever use this for non-qemu platforms.
    let pcie_prop = fdt.get_property("pcie@10000000", c"reg").ok()?;
    let pcie_base = u64::from_be_bytes(pcie_prop[..8].try_into().unwrap());
    let pci_size = u64::from_be_bytes(pcie_prop[8..][..8].try_into().unwrap());
    Some((pcie_base, pci_size))
}

/// HAL implementation for VirtIO in GBL.
pub struct GblVirtIoHal {}

/// SAFETY:
/// The implementation meets the safety requirements by `virtio_drivers::Hal`:
/// * `dma_alloc` guarantees to return valid, page-aligned, zeroed memory. The memory is not
///   aliased by any other allocation or references.
/// * `mmio_phys_to_virt` returns the same pointer as the input physical address. Because GBL
///   requires identity mapping, the return pointer is guaranteed to be valid.
unsafe impl Hal for GblVirtIoHal {
    fn dma_alloc(pages: usize, _direction: BufferDirection) -> (PhysAddr, NonNull<u8>) {
        // SAFETY: The layout is valid and the allocation will be deallocated by dma_dealloc.
        let ptr = NonNull::new(unsafe {
            alloc(Layout::from_size_align(pages * EFI_PAGE_SIZE, EFI_PAGE_SIZE).unwrap())
        })
        .unwrap();
        // SAFETY: The pointer is non-null and points to a valid allocated region.
        unsafe { ptr.write_bytes(0, pages * EFI_PAGE_SIZE) };
        (ptr.as_ptr() as _, ptr)
    }

    /// # Safety: Caller should follow the safety requirements in
    /// virtio_drivers::Hal::dma_dealloc.
    unsafe fn dma_dealloc(paddr: PhysAddr, _vaddr: NonNull<u8>, pages: usize) -> i32 {
        // SAFETY: The memory points to a valid allocated region allocated by dma_alloc.
        unsafe {
            dealloc(
                paddr as _,
                Layout::from_size_align(pages * EFI_PAGE_SIZE, EFI_PAGE_SIZE).unwrap(),
            )
        };
        0
    }

    /// # Safety: Caller should follow the safety requirements in
    /// virtio_drivers::Hal::mmio_phys_to_virt.
    unsafe fn mmio_phys_to_virt(paddr: PhysAddr, _size: usize) -> NonNull<u8> {
        // NA. GBL operates on physical or identity map address space.
        NonNull::new(paddr as _).unwrap()
    }

    /// # Safety: Caller should follow the safety requirements in
    /// virtio_drivers::Hal::share.
    unsafe fn share(buffer: NonNull<[u8]>, _direction: BufferDirection) -> PhysAddr {
        // NA. GBL operates on physical or identity map address space.
        buffer.as_ptr().cast::<usize>() as _
    }

    /// # Safety: Caller should follow the safety requirements in
    /// virtio_drivers::Hal::unshare.
    unsafe fn unshare(_paddr: PhysAddr, _buffer: NonNull<[u8]>, _direction: BufferDirection) {
        // NA. GBL operates on physical or identity map address space.
    }
}

/// Session status
#[derive(Debug, Copy, Clone)]
pub enum SessionStatus {
    /// Session is listening for a new connection.
    Listening,
    /// Session is connected to a remote address.
    Connected(VsockAddr),
    /// Session is closed.
    Closed,
}

const MAX_SLOT: usize = 8;
const MAX_BUFFER_SIZE: usize = 64 * 1024;

/// Tracks state of a connection.
struct Slot {
    /// Session ID.
    sid: u64,
    /// Remote address. None -- listening, Some -- connected
    remote: Option<VsockAddr>,
    /// Port number.
    port: u32,
    /// Timeout duration.
    timeout: Duration,
    /// Last event timestamp.
    last_event_ts: Duration,
}

/// GBL VirtIO VSOCK Connection Manager.
pub struct GblVsockConnectionManager {
    slots: [Option<Slot>; MAX_SLOT],
    connection_manager: VsockConnectionManager<GblVirtIoHal, PciTransport, MAX_BUFFER_SIZE>,
    next_sid: u64,
}

fn timestamp() -> Duration {
    arch_timestamp().unwrap_or(Duration::from_millis(0))
}

impl GblVsockConnectionManager {
    /// Creates a new instance.
    pub fn new(
        connection_manager: VsockConnectionManager<GblVirtIoHal, PciTransport, MAX_BUFFER_SIZE>,
    ) -> Self {
        Self { slots: [const { None }; MAX_SLOT], connection_manager, next_sid: 0 }
    }

    /// Listens for a new connection.
    ///
    /// On success returns the session id.
    pub fn listen(&mut self, port: u32, timeout: Duration) -> Result<u64, Error> {
        self.poll();
        // Allocates an unuesd slot for tracking this connection.
        let Some(slot) = self.slots.iter_mut().find(|s| s.is_none()) else {
            return Err(Error::NotReady);
        };
        let sid = self.next_sid;
        *slot = Some(Slot { sid, remote: None, port, timeout, last_event_ts: timestamp() });
        self.next_sid += 1;
        self.connection_manager.listen(port);
        Ok(sid)
    }

    /// Returns the session status.
    pub fn session_status(&mut self, sid: u64) -> SessionStatus {
        self.poll();
        match self.slots.iter().find_map(|v| v.as_ref().filter(|v| v.sid == sid)) {
            None => SessionStatus::Closed,
            Some(Slot { remote: None, .. }) => SessionStatus::Listening,
            Some(Slot { remote: Some(remote), .. }) => SessionStatus::Connected(*remote),
        }
    }

    /// Polls for new connections and events
    pub fn poll_once(&mut self) -> bool {
        // Clears timeout connections.
        for slot in self.slots.iter_mut() {
            if let Some(v) = slot {
                if (timestamp() - v.last_event_ts) > v.timeout {
                    v.remote.map(|remote| self.connection_manager.shutdown(remote, v.port));
                    *slot = None;
                }
            }
        }

        // Checks for new events
        let Ok(Some(v)) = self.connection_manager.poll() else { return false };
        let VsockEvent { source, destination, buffer_status: _, event_type } = v;

        // Find if there is any on-going session for this event.
        let mut active_idx = None;
        for (i, v) in self.slots.iter_mut().enumerate() {
            if let Some(v) = v {
                if v.remote == Some(source) && v.port == destination.port {
                    v.last_event_ts = timestamp();
                    active_idx = Some(i);
                    break;
                }
            }
        }

        // Handles the event.
        match event_type {
            VsockEventType::ConnectionRequest => {
                // It shouldn't be tracked. If it is, we are out of sync and need to clear it.
                if let Some(i) = active_idx {
                    self.slots[i] = None;
                }
                // Check if any slot is listening on the port.
                for v in self.slots.iter_mut() {
                    if let Some(v) =
                        v.as_mut().filter(|v| v.remote.is_none() && v.port == destination.port)
                    {
                        v.remote = Some(source);
                        v.last_event_ts = timestamp();
                        return true;
                    }
                }
                // No one is listening for the port.
                let _ = self.connection_manager.shutdown(source, destination.port);
                self.connection_manager.unlisten(destination.port);
            }
            VsockEventType::Disconnected { .. } => {
                if let Some(i) = active_idx {
                    self.slots[i] = None;
                }
            }
            _ => {}
        }
        true
    }

    /// Polls for new connections and events until no more events are available.
    fn poll(&mut self) {
        while self.poll_once() {}
    }

    /// Read data from connection
    pub fn read(&mut self, target_sid: u64, buffer: &mut [u8]) -> Result<usize, Error> {
        self.poll();
        for slot in self.slots.iter_mut() {
            if let Some(v) = slot.as_mut().filter(|v| v.sid == target_sid) {
                let remote = v.remote.ok_or(Error::InvalidState)?;
                match self.connection_manager.recv(remote, v.port, buffer) {
                    Ok(sz) => {
                        if sz > 0 {
                            // Update last event timestamp if progress is made.
                            v.last_event_ts = timestamp();
                        }
                        if self
                            .connection_manager
                            .recv_buffer_available_bytes(remote, v.port)
                            .map_err(|_| {
                                Error::Other(Some("vsock recv buffer available bytes error"))
                            })?
                            == 0
                        {
                            // Update credit to allow more data to be sent.
                            self.connection_manager
                                .update_credit(remote, v.port)
                                .map_err(|_| Error::Other(Some("vsock update credit error")))?;
                        }
                        return Ok(sz);
                    }
                    Err(_e) => {
                        // Abort the connection on any error.
                        let _ = self.connection_manager.force_close(remote, v.port);
                        *slot = None;
                        return Err(Error::Other(Some("vsock recv error")));
                    }
                }
            }
        }
        Err(Error::InvalidState)
    }

    /// Write data to connection
    pub fn write(&mut self, target_sid: u64, buffer: &[u8]) -> Result<(), Error> {
        self.poll();
        for slot in self.slots.iter_mut() {
            if let Some(v) = slot.as_mut().filter(|v| v.sid == target_sid) {
                let remote = v.remote.ok_or(Error::InvalidState)?;
                match self.connection_manager.send(remote, v.port, buffer) {
                    Ok(_) => {
                        if buffer.len() > 0 {
                            v.last_event_ts = timestamp();
                        }
                        return Ok(());
                    }
                    Err(_e) => {
                        // Abort the connection on any error.
                        let _ = self.connection_manager.force_close(remote, v.port);
                        *slot = None;
                        return Err(Error::Other(Some("vsock send error")));
                    }
                }
            }
        }
        Err(Error::InvalidState)
    }

    /// Close the connection.
    pub fn close(&mut self, target_sid: u64) {
        self.poll();
        for slot in self.slots.iter_mut() {
            if let Some(v) = slot.as_mut().filter(|v| v.sid == target_sid) {
                if let Some(remote) = v.remote {
                    let _ = self.connection_manager.shutdown(remote, v.port);
                }
                *slot = None;
                return;
            }
        }
    }
}

/// Represents the global vsock manager.
struct GblVsockInitState(Option<Result<GblVsockConnectionManager, Error>>);

impl GblVsockInitState {
    /// Gets the vsock manager if it has been initialized.
    pub fn get(&mut self) -> Result<&mut GblVsockConnectionManager, Error> {
        self.0.as_mut().ok_or(Error::InvalidState)?.as_mut().map_err(|e| *e)
    }
}

static GBL_VSOCK_MANAGER: Mutex<GblVsockInitState> = Mutex::new(GblVsockInitState(None));

/// Initializes the vsock manager.
pub fn gbl_vsock_init(entry: &EfiEntry) -> Result<(), Error> {
    GBL_VSOCK_MANAGER
        .try_lock()
        .ok_or(Error::NotReady)?
        .0
        .get_or_insert_with(|| {
            let (pci_base, pci_size) = detect_ecam(entry).ok_or(Error::Unsupported)?;
            // SAFETY: pci_base is from ACPI or Device Tree and gives the correct PCI address.
            let pci_root = &mut PciRoot::new(unsafe { MmioCam::new(pci_base as _, Cam::Ecam) });
            // Iterate over all possible PCI buses within the discovered ECAM space (which allocates
            // 1MB/0x100000 per bus) to enumerate devices and find the first VirtIO VSOCK device.
            for bus in u8::MIN..=u8::MAX {
                if bus as u64 * 0x100000 >= pci_size {
                    break;
                }

                let Some((func, _info)) = pci_root
                    .enumerate_bus(bus)
                    .find(|(_, info)| virtio_device_type(info) == Some(DeviceType::Socket))
                else {
                    continue;
                };
                let transport = PciTransport::new::<GblVirtIoHal, _>(pci_root, func)
                    .map_err(|_| Error::Other(Some("Failed to create PCI transport")))?;
                let vsock = VirtIOSocket::<GblVirtIoHal, _, MAX_BUFFER_SIZE>::new(transport)
                    .map_err(|_| Error::Other(Some("Failed to create vsock")))?;
                return Ok(GblVsockConnectionManager::new(VsockConnectionManager::new(vsock)));
            }
            Err(Error::Unsupported)
        })
        .as_ref()
        .map_err(|e| *e)?;
    Ok(())
}

/// Listens for a new connection.
pub fn gbl_vsock_listen(port: u32, timeout: Duration) -> Result<u64, Error> {
    GBL_VSOCK_MANAGER.try_lock().ok_or(Error::NotReady)?.get()?.listen(port, timeout)
}

/// Returns the session status.
pub fn gbl_vsock_session_status(sid: u64) -> Result<SessionStatus, Error> {
    Ok(GBL_VSOCK_MANAGER.try_lock().ok_or(Error::NotReady)?.get()?.session_status(sid))
}

/// Reads data from the vsock.
pub fn gbl_vsock_read(sid: u64, buffer: &mut [u8]) -> Result<usize, Error> {
    GBL_VSOCK_MANAGER.try_lock().ok_or(Error::NotReady)?.get()?.read(sid, buffer)
}

/// Writes one or more buffers to the vsock.
pub fn gbl_vsock_write(sid: u64, buffers: &[&[u8]]) -> Result<(), Error> {
    let mut manager = GBL_VSOCK_MANAGER.try_lock().ok_or(Error::NotReady)?;
    let manager = manager.get()?;
    for b in buffers {
        manager.write(sid, b)?;
    }
    Ok(())
}

/// Closes the vsock.
pub fn gbl_vsock_close(sid: u64) -> Result<(), Error> {
    Ok(GBL_VSOCK_MANAGER.try_lock().ok_or(Error::NotReady)?.get()?.close(sid))
}

/// Helper function to wait for a result, yielding if it's not ready.
pub async fn wait<T>(mut f: impl FnMut() -> Result<T, Error>) -> Result<T, Error> {
    loop {
        match f() {
            Err(Error::NotReady) => gbl_async::yield_now().await,
            v => return v,
        }
    }
}

/// Reads data from the vsock until the buffer is full.
pub async fn gbl_vsock_read_exact(sid: u64, mut out: &mut [u8]) -> Result<(), Error> {
    while !out.is_empty() {
        let sz = wait(|| gbl_vsock_read(sid, out)).await?;
        if sz == 0 {
            gbl_async::yield_now().await;
            continue;
        }
        out = out.split_at_mut(sz).1;
    }
    Ok(())
}

/// Listens on a port and waits until a new connection is established.
pub async fn gbl_vsock_accept(port: u32, timeout: Duration) -> Result<u64, Error> {
    let mut sid = wait(|| gbl_vsock_listen(port, timeout)).await?;
    loop {
        match wait(|| gbl_vsock_session_status(sid)).await? {
            SessionStatus::Connected(_) => return Ok(sid),
            SessionStatus::Closed => sid = wait(|| gbl_vsock_listen(port, timeout)).await?,
            SessionStatus::Listening => {}
        }
        gbl_async::yield_now().await;
    }
}
