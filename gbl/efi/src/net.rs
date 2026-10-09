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

// Network is only allowed on dev boards.
#![cfg(feature = "gbl_dev")]

use crate::{
    efi,
    utils::{get_device_path, loop_with_timeout},
};
use alloc::{boxed::Box, vec::Vec};
use core::{
    ffi::c_void,
    ptr::null_mut,
    sync::atomic::{AtomicU64, Ordering},
    time::Duration,
};
use efi::{
    efi_println,
    protocol::{simple_network::SimpleNetworkProtocol, Protocol},
    utils::Timeout,
    DeviceHandle, EfiEntry, Event, EventNotify, EventType, Tpl,
};
use efi_types::{EfiEvent, EfiMacAddress, EFI_TIMER_DELAY_TIMER_PERIODIC};
use gbl_async::{yield_now, YieldCounter};
use liberror::{Error, Result};
use libgbl::fastboot::fuchsia_fastboot_mdns_packet;
use smoltcp::{
    iface::{Config, Interface, SocketSet, SocketStorage},
    phy,
    phy::{Device, DeviceCapabilities, Medium},
    socket::{
        tcp::{ListenError, RecvError, SendError, Socket as TcpSocket, SocketBuffer, State},
        udp::{PacketBuffer, Socket as UdpSocket, UdpMetadata},
    },
    storage::PacketMetadata,
    time::Instant,
    wire::{EthernetAddress, IpAddress, IpCidr, IpListenEndpoint, Ipv6Address},
};

/// Ethernet frame size for frame pool.
const ETHERNET_FRAME_SIZE: usize = 1536;
// Update period for `NETWORK_TIMESTAMP`.
const NETWORK_TIMESTAMP_UPDATE_PERIOD: Duration = Duration::from_millis(50);
// Size of the socket tx/rx application data buffer.
const SOCKET_TX_RX_BUFFER: usize = 256 * 1024;

/// Converts smoltcp [RecvError] to unified [Error].
fn recv_to_unified(err: RecvError) -> Error {
    match err {
        RecvError::InvalidState => Error::InvalidState,
        RecvError::Finished => Error::Finished,
    }
}

/// Converts smoltcp [SendError] to unified [Error].
fn send_to_unified(err: SendError) -> Error {
    match err {
        SendError::InvalidState => Error::InvalidState,
    }
}

/// Converts smoltcp [ListenError] to unified [Error].
fn listen_to_unified(err: ListenError) -> Error {
    match err {
        ListenError::InvalidState => Error::InvalidState,
        ListenError::Unaddressable => Error::Unaddressable,
    }
}

/// Performs a shutdown and restart of the simple network protocol.
fn reset_simple_network<'a>(snp: &Protocol<'a, SimpleNetworkProtocol>) -> Result<()> {
    match snp.shutdown() {
        Err(e) if e != Error::NotStarted => return Err(e),
        _ => {}
    };

    match snp.start() {
        Err(e) if e != Error::AlreadyStarted => return Err(e),
        _ => {}
    };
    snp.initialize(0, 0)?;
    Ok(snp.reset(true)?)
}

/// `EfiNetworkDevice` manages a frame pool and handles receiving/sending network frames.
pub struct EfiNetworkDevice<'a> {
    protocol: Protocol<'a, SimpleNetworkProtocol>,
    rx_frame: Box<[u8; ETHERNET_FRAME_SIZE]>,
    tx_frames: Vec<*mut [u8; ETHERNET_FRAME_SIZE]>,
    tx_frame_curr: usize, // Circular next index into tx_frames.
    efi_entry: &'a EfiEntry,
}

impl<'a> EfiNetworkDevice<'a> {
    /// Creates a new instance. Allocates `extra_tx_frames+1` number of TX frames.
    pub fn new(
        protocol: Protocol<'a, SimpleNetworkProtocol>,
        extra_tx_frames: usize,
        efi_entry: &'a EfiEntry,
    ) -> Self {
        let mut ret = Self {
            protocol: protocol,
            rx_frame: Box::new([0u8; ETHERNET_FRAME_SIZE]),
            tx_frames: vec![core::ptr::null_mut(); extra_tx_frames + 1],
            tx_frame_curr: 0,
            efi_entry: efi_entry,
        };
        ret.tx_frames
            .iter_mut()
            .for_each(|v| *v = Box::into_raw(Box::new([0u8; ETHERNET_FRAME_SIZE])));
        ret
    }
}

impl Drop for EfiNetworkDevice<'_> {
    fn drop(&mut self) {
        if let Err(e) = self.protocol.shutdown() {
            if e != Error::NotStarted {
                // If shutdown fails, the protocol might still be operating on transmit buffers,
                // which can cause undefined behavior. Thus we need to panic.
                panic!("Failed to shutdown EFI network. {:?}", e);
            }
        }

        // Deallocate TX frames.
        self.tx_frames.iter_mut().for_each(|v| {
            // SAFETY:
            // Each pointer is created by `Box::new()` in `EfiNetworkDevice::new()`. Thus the
            // pointer is valid and layout matches.
            drop(unsafe { Box::<[u8; ETHERNET_FRAME_SIZE]>::from_raw(*v) });
        });
    }
}

// Implements network device trait backend for the `smoltcp` crate.
impl<'a> Device for EfiNetworkDevice<'a> {
    type RxToken<'b>
        = RxToken<'b>
    where
        Self: 'b;
    type TxToken<'b>
        = TxToken<'a, 'b>
    where
        Self: 'b;

    fn capabilities(&self) -> DeviceCapabilities {
        // Taken from upstream example.
        let mut res: DeviceCapabilities = Default::default();
        res.max_transmission_unit = 65535;
        res.medium = Medium::Ethernet;
        res
    }

    fn receive(&mut self, _: Instant) -> Option<(Self::RxToken<'_>, Self::TxToken<'_>)> {
        let mut recv_size = self.rx_frame.len();
        // Receive the next packet from the device.
        self.protocol
            .receive(None, Some(&mut recv_size), &mut self.rx_frame[..], None, None, None)
            .ok()?;
        match recv_size > 0 {
            true => Some((
                RxToken(&mut self.rx_frame[..recv_size]),
                TxToken {
                    protocol: &self.protocol,
                    tx_frames: &mut self.tx_frames[..],
                    curr: &mut self.tx_frame_curr,
                    efi_entry: self.efi_entry,
                },
            )),
            _ => None,
        }
    }

    fn transmit(&mut self, _: Instant) -> Option<Self::TxToken<'_>> {
        Some(TxToken {
            protocol: &self.protocol,
            tx_frames: &mut self.tx_frames[..],
            curr: &mut self.tx_frame_curr,
            efi_entry: self.efi_entry,
        })
    }
}

/// In smoltcp, a `RxToken` is used to receive/process a frame when consumed.
pub struct RxToken<'a>(&'a mut [u8]);

impl phy::RxToken for RxToken<'_> {
    fn consume<R, F>(self, f: F) -> R
    where
        F: FnOnce(&[u8]) -> R,
    {
        f(self.0)
    }
}

/// In smoltcp, a `TxToken` is used to transmit a frame when consumed.
pub struct TxToken<'a: 'b, 'b> {
    tx_frames: &'b mut [*mut [u8; ETHERNET_FRAME_SIZE]],
    curr: &'b mut usize,
    protocol: &'b Protocol<'a, SimpleNetworkProtocol>,
    efi_entry: &'a EfiEntry,
}

impl TxToken<'_, '_> {
    /// Tries to allocate a send buffer.
    fn try_get_buffer(&mut self) -> Option<*mut [u8; ETHERNET_FRAME_SIZE]> {
        let mut ptr: *mut c_void = null_mut();
        let mut interrupt_status = 0u32;
        // Recyle a buffer or take one from `tx_frames`.
        match self.protocol.get_status(Some(&mut interrupt_status), Some(&mut ptr)) {
            Ok(()) if self.tx_frames.contains(&(ptr as *mut _)) => Some(ptr as *mut _),
            _ if *self.curr < self.tx_frames.len() => {
                // If we can't recycle a buffer, see if we can take one from the pool.
                let res = *self.curr;
                *self.curr = *self.curr + 1;
                Some(self.tx_frames[res])
            }
            _ => None,
        }
    }
}

impl phy::TxToken for TxToken<'_, '_> {
    fn consume<R, F>(mut self, len: usize, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        loop {
            match loop_with_timeout(self.efi_entry, Duration::from_secs(5), || {
                self.try_get_buffer().ok_or(false)
            }) {
                Ok(Some(send_buffer)) => {
                    // SAFETY:
                    // * The pointer is confirmed to come from one of `self.tx_frames`. It's
                    //   created via `Box::new()` in `EfiNetworkDevice::new()`. Thus it is properly
                    //   aligned, dereferenceable and initialized.
                    // * The pointer is either recycled from `self.protocol.get_status` or newly
                    //   allocated from `self.tx_frames`. Thus There's no other references to it.
                    // * The reference is only used for passing to `f` and goes out of scope
                    //   immediately after.
                    let result = f(&mut unsafe { send_buffer.as_mut() }.unwrap()[..len]);

                    // SAFETY:
                    // * `send_buffer` comes from `EfiNetworkDevice::tx_frames`. It has a valid
                    //   length at least `len`. `EfiNetworkDevice` shuts down network on drop. Thus
                    //   the transmit buffer remains valid throughout the operation of the network
                    //   protocol.
                    // * `send_buffer` is either recycled from `self.protocol.get_status()` or newly
                    //   allocated from `self.tx_frames`. There's no other references to it.
                    // * `self.curr` stricly increases for each new allocation until
                    //   `reset_simple_network()`. Thus there'll be no other references to the buffer
                    //    until it is either recycled or `reset_simple_network()` is called.
                    let _ = unsafe {
                        self.protocol.transmit(
                            0,
                            send_buffer.as_mut().unwrap().get_mut(..len).unwrap(),
                            Default::default(), // Src mac address don't care
                            Default::default(), // Dest mac address don't care
                            0,
                        )
                    };

                    return result;
                }
                Ok(None) => {
                    // Some UEFI firmware has internal network service that also recycle buffers,
                    // in which case our buffer may be hijacked and will never be returned from our
                    // call. If we run into this case, shutdown and restart the network and try
                    // again. Shutting down network releases all pending send/receive buffers
                    // internally retained.
                    efi_println!(
                        self.efi_entry,
                        "Timeout recycling TX buffers. Resetting network."
                    );
                    // Panics if this fails, as we have effectively lost control over network's
                    // used of buffers.
                    reset_simple_network(self.protocol).unwrap();
                    *self.curr = 0;
                }
                _ => {} // `loop_with_timeout` failure. Try again.
            };
        }
    }
}

/// Find the first available network device with an active link, falling back to the first root
/// network device if no link is detected.
fn find_net_device(efi_entry: &EfiEntry) -> Result<DeviceHandle> {
    let bs = efi_entry.system_table().boot_services();
    let mut candidates: Vec<_> = bs
        .locate_handle_buffer_by_protocol::<SimpleNetworkProtocol>()?
        .handles()
        .iter()
        .filter_map(|handle| {
            let path = get_device_path(efi_entry, *handle).ok()?;
            path.text().is_some().then_some((*handle, path))
        })
        .collect();

    // Sort by device path text lexicographically so parent device paths precede any child virtual
    // network device nodes (e.g., e1000 adds child nodes for IPv4 and IPv6 configuration).
    candidates.sort_by(|(_, a), (_, b)| a.text().cmp(&b.text()));

    // Deduplicate child network device handles whose path starts with the preceding root parent
    // device path. Note that `dedup_by` passes `(child, root)` in reverse slice order.
    candidates.dedup_by(|(_, child), (_, root)| {
        if let (Some(child_text), Some(root_text)) = (child.text(), root.text()) {
            !root_text.is_empty() && child_text.starts_with(root_text)
        } else {
            false
        }
    });

    let first_handle = candidates.first().ok_or(Error::NotFound)?.0;

    // Find the first root NIC handle with an active link, falling back to the first root handle.
    let has_active_link = |&handle: &DeviceHandle| {
        bs.open_protocol::<SimpleNetworkProtocol>(handle)
            .and_then(|snp| {
                reset_simple_network(&snp)?;
                // Prod the driver to refresh its cached status (including Mode->MediaPresent).
                // Some UEFI drivers require non-null status/buffer pointers even though they
                // are optional in the spec.
                let mut interrupt_status = 0u32;
                let mut recycle_buffer = null_mut();
                snp.get_status(Some(&mut interrupt_status), Some(&mut recycle_buffer))?;
                let mode = snp.mode()?;
                Ok(!mode.media_present_supported || mode.media_present)
            })
            .unwrap_or(false)
    };
    Ok(candidates.into_iter().map(|(h, _)| h).find(has_active_link).unwrap_or(first_handle))
}

/// Derives a link local ethernet mac address and IPv6 address from `EfiMacAddress`.
fn ll_mac_ip6_addr_from_efi_mac(mac: EfiMacAddress) -> (EthernetAddress, IpAddress) {
    let ll_mac_bytes = &mac.addr[..6];
    let mut ip6_bytes = [0u8; 16];
    ip6_bytes[0] = 0xfe;
    ip6_bytes[1] = 0x80;
    ip6_bytes[8] = ll_mac_bytes[0] ^ 2;
    ip6_bytes[9] = ll_mac_bytes[1];
    ip6_bytes[10] = ll_mac_bytes[2];
    ip6_bytes[11] = 0xff;
    ip6_bytes[12] = 0xfe;
    ip6_bytes[13] = ll_mac_bytes[3];
    ip6_bytes[14] = ll_mac_bytes[4];
    ip6_bytes[15] = ll_mac_bytes[5];

    (EthernetAddress::from_bytes(ll_mac_bytes), IpAddress::Ipv6(Ipv6Address::from(ip6_bytes)))
}

/// `EfiTcpSocket` groups together necessary components for performing TCP.
pub struct EfiTcpSocket<'a, 'b> {
    pub(crate) efi_entry: &'a EfiEntry,
    efi_net_dev: &'b mut EfiNetworkDevice<'a>,
    interface: Interface,
    socket_set: SocketSet<'b>,
    io_yield_counter: YieldCounter,
    last_listen_timestamp: Option<u64>,
    _time_update_event: Event<'a, 'b>,
    timestamp: &'b AtomicU64,
    fuchsia_fastboot_mdns_packet: Vec<u8>,
}

impl<'a, 'b> EfiTcpSocket<'a, 'b> {
    /// Resets the socket and starts listening for new TCP connection.
    pub fn listen(&mut self, port: u16) -> Result<()> {
        self.get_socket().abort();
        self.get_socket().listen(port).map_err(listen_to_unified)?;
        self.last_listen_timestamp = Some(self.timestamp(0).as_millis() as u64);
        Ok(())
    }

    /// Returns the amount of time elapsed since last call to `Self::listen()`. If `listen()` has
    /// never been called, `Duration::MAX` is returned.
    pub fn time_since_last_listen(&mut self) -> Duration {
        self.last_listen_timestamp.map(|v| self.timestamp(v)).unwrap_or(Duration::MAX)
    }

    /// Polls network device.
    pub fn poll(&mut self) {
        self.interface.poll(self.instant(), self.efi_net_dev, &mut self.socket_set);
    }

    /// Gets a reference to the smoltcp socket object.
    pub fn get_socket(&mut self) -> &mut TcpSocket<'b> {
        // We only consider single socket use case for now.
        let handle = self.socket_set.iter().next().unwrap().0;
        self.socket_set.get_mut::<TcpSocket>(handle)
    }

    /// Checks whether a socket connection is established.
    pub fn is_established(&mut self) -> bool {
        self.get_socket().state() == State::Established
    }

    /// Checks whether a socket is closed.
    pub fn is_closed(&mut self) -> bool {
        return !self.get_socket().is_open() || self.get_socket().state() == State::CloseWait;
    }

    /// Sets the maximum number of bytes to read or write before a force await.
    pub fn set_io_yield_threshold(&mut self, threshold: u64) {
        self.io_yield_counter = YieldCounter::new(threshold)
    }

    /// Receives any non-zero amount of data.
    ///
    /// Returns Ok(0) if `out` is empty;
    pub async fn receive(&mut self, out: &mut [u8], timeout: Duration) -> Result<usize> {
        let timer = Timeout::new(self.efi_entry, timeout)?;
        let mut curr = &mut out[..];
        while !curr.is_empty() {
            self.poll();

            let mut recv_size = 0;
            if self.is_closed() {
                return Err(Error::Disconnected);
            } else if timer.check()? {
                return Err(Error::Timeout);
            } else if self.get_socket().can_recv() {
                recv_size = self.get_socket().recv_slice(curr).map_err(recv_to_unified)?;
                curr = curr.get_mut(recv_size..).ok_or(Error::BadIndex(recv_size))?;
                // Forces a yield to the executor if the data received/sent reaches a certain
                // threshold. This is to prevent the async code from holding up the CPU for too long
                // in case IO speed is high and the executor uses cooperative scheduling.
                self.io_yield_counter.increment(recv_size.try_into().unwrap()).await;
            }

            match recv_size > 0 {
                true => return Ok(recv_size),
                _ => yield_now().await,
            }
        }
        Ok(out.len())
    }

    /// Sends exactly `data.len()` number of bytes from `data`.
    pub async fn send_exact(&mut self, data: &[u8], timeout: Duration) -> Result<()> {
        let timer = Timeout::new(self.efi_entry, timeout)?;
        let mut curr = &data[..];
        let mut last_send_queue = self.get_socket().send_queue();
        loop {
            self.poll();
            if curr.is_empty() && self.get_socket().send_queue() == 0 {
                return Ok(());
            } else if self.is_closed() {
                return Err(Error::Disconnected.into());
            } else if timer.check()? {
                return Err(Error::Timeout.into());
            }

            let mut has_progress = false;
            // Checks if any data in the queue is sent.
            if self.get_socket().send_queue() != last_send_queue {
                last_send_queue = self.get_socket().send_queue();
                has_progress = true;
            }
            // Checks if there are more data to be queued.
            if self.get_socket().can_send() && !curr.is_empty() {
                let sent = self.get_socket().send_slice(curr).map_err(send_to_unified)?;
                curr = curr.get(sent..).ok_or(Error::BadIndex(sent))?;
                // Forces a yield to the executor if the data received/sent reaches a certain
                // threshold. This is to prevent the async code from holding up the CPU for too long
                // in case IO speed is high and the executor uses cooperative scheduling.
                self.io_yield_counter.increment(sent.try_into().unwrap()).await;
                has_progress |= sent > 0;
            }

            match has_progress {
                true => timer.reset(timeout)?,
                _ => yield_now().await,
            }
        }
    }

    /// Gets the smoltcp `Interface` for this socket.
    pub fn interface(&self) -> &Interface {
        &self.interface
    }

    /// Returns the duration elapsed since the `base` timestamp.
    pub fn timestamp(&self, base_in_millis: u64) -> Duration {
        let curr = self.timestamp.load(Ordering::Relaxed);
        // Assume there can be at most one overflow.
        Duration::from_millis(match curr < base_in_millis {
            true => u64::MAX - (base_in_millis - curr),
            false => curr - base_in_millis,
        })
    }

    /// Returns a smoltcp time `Instant` value.
    fn instant(&self) -> Instant {
        to_smoltcp_instant(self.timestamp(0).as_millis() as u64)
    }

    /// Broadcasts Fuchsia Fastboot MDNS service once.
    pub fn broadcast_fuchsia_fastboot_mdns(&mut self) {
        const MDNS_PORT: u16 = 5353;
        const IP6_BROADCAST_ADDR: [u8; 16] =
            [0xFF, 0x02, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xFB];
        let ip6_broadcast = Ipv6Address::from(IP6_BROADCAST_ADDR);
        let meta = UdpMetadata::from((ip6_broadcast, MDNS_PORT));
        let handle = self.socket_set.iter().nth(1).unwrap().0;
        let socket = self.socket_set.get_mut::<UdpSocket>(handle);
        if !socket.is_open() {
            match socket.bind(IpListenEndpoint { addr: None, port: MDNS_PORT }) {
                Err(e) => efi_println!(self.efi_entry, "bind error: {:?}", e),
                _ => {}
            }
        }
        if socket.can_send() {
            match socket.send_slice(&self.fuchsia_fastboot_mdns_packet, meta) {
                Err(e) => efi_println!(self.efi_entry, "UDP send error: {:?}", e),
                _ => {}
            }
        }
    }
}

/// Returns a smoltcp time `Instant` value from a u64 timestamp.
fn to_smoltcp_instant(ts: u64) -> Instant {
    Instant::from_millis(i64::try_from(ts).unwrap())
}

/// Internal type that contains net driver interfaces and buffers for creating GBL network and
/// sockets.
///
/// # Lifetimes
///
/// * `'a`: Lifetime of [EfiEntry] borrowed.
/// * `'b`: Lifetime of [SocketStorage<'b>], which eventually refers to Self.
/// * `'c`: Lifetime of [AtomicU64] borrowed.
struct EfiGblNetworkInternal<'a, 'b, 'c> {
    efi_entry: &'a EfiEntry,
    tcp_tx_buffer: Vec<u8>,
    tcp_rx_buffer: Vec<u8>,
    udp_tx_payload_buffer: Vec<u8>,
    udp_rx_payload_buffer: Vec<u8>,
    udp_tx_metadata_buffer: Vec<PacketMetadata<UdpMetadata>>,
    udp_rx_metadata_buffer: Vec<PacketMetadata<UdpMetadata>>,
    socket_storage: [SocketStorage<'b>; 2],
    efi_net_dev: EfiNetworkDevice<'a>,
    timestamp: &'c AtomicU64,
    notify_fn: Option<Box<dyn FnMut(EfiEvent) + Sync + 'c>>,
    notify: Option<EventNotify<'b>>,
}

impl<'a, 'b, 'c> EfiGblNetworkInternal<'a, 'b, 'c> {
    /// Creates a new instance of [EfiGblNetworkInternal].
    fn new(efi_entry: &'a EfiEntry, timestamp: &'c AtomicU64) -> Result<Self> {
        // Creates and initializes simple network protocol.
        let snp_dev = find_net_device(efi_entry)?;
        let snp = efi_entry
            .system_table()
            .boot_services()
            .open_protocol::<SimpleNetworkProtocol>(snp_dev)?;
        reset_simple_network(&snp)?;

        // The TCP stack requires ICMP6 solicitation for discovery. Enable promiscuous mode so that
        // all uni/multicast packets can be captured.
        match snp.set_promiscuous_mode() {
            Err(e) => efi_println!(
                efi_entry,
                "Warning: Failed to set promiscuous mode {e:?}. Device may be undiscoverable",
            ),
            _ => {}
        }

        Ok(Self {
            efi_entry,
            tcp_tx_buffer: vec![0u8; SOCKET_TX_RX_BUFFER],
            tcp_rx_buffer: vec![0u8; SOCKET_TX_RX_BUFFER],
            udp_tx_payload_buffer: vec![0u8; ETHERNET_FRAME_SIZE],
            udp_rx_payload_buffer: vec![0u8; ETHERNET_FRAME_SIZE],
            udp_tx_metadata_buffer: vec![PacketMetadata::EMPTY; 1],
            udp_rx_metadata_buffer: vec![PacketMetadata::EMPTY; 1],
            socket_storage: Default::default(),
            // Allocates 7(chosen randomly) extra TX frames. Revisits if it is not enough.
            efi_net_dev: EfiNetworkDevice::new(snp, 7, &efi_entry),
            timestamp,
            notify_fn: None,
            notify: None,
        })
    }

    /// Creates an instance of [EfiTcpSocket].
    fn create_socket(&'b mut self) -> Result<EfiTcpSocket<'a, 'b>> {
        // Resets network timestamp to 0.
        let _ = self.timestamp.swap(0, Ordering::Relaxed);

        // Initializes notification functions.
        if self.notify_fn.is_none() {
            self.notify_fn = Some(Box::new(|_: EfiEvent| {
                self.timestamp.fetch_add(
                    NETWORK_TIMESTAMP_UPDATE_PERIOD.as_millis() as u64,
                    Ordering::Relaxed,
                );
            }));
            self.notify = Some(EventNotify::new(Tpl::Callback, self.notify_fn.as_mut().unwrap()));
        }

        // Creates a timer event for updating the global timestamp.
        let bs = self.efi_entry.system_table().boot_services();
        // SAFETY: the notification callback in `notify_fn` initialized above never allocates,
        // deallocates, or panics.
        let _time_update_event = unsafe {
            bs.create_event_with_notification(
                EventType::TimerNotifySignal,
                self.notify.as_mut().unwrap(),
            )
        }?;
        bs.set_timer(
            &_time_update_event,
            EFI_TIMER_DELAY_TIMER_PERIODIC,
            NETWORK_TIMESTAMP_UPDATE_PERIOD,
        )?;

        // Gets our MAC address and IPv6 address.
        // We can also consider getting this from vendor configuration.
        let (ll_mac, ll_ip6_addr) =
            ll_mac_ip6_addr_from_efi_mac(self.efi_net_dev.protocol.mode()?.current_address);
        let IpAddress::Ipv6(ll_ip6_addr_v6) = ll_ip6_addr else {
            unreachable!();
        };
        // Configures smoltcp network interface.
        let mut interface = Interface::new(
            Config::new(ll_mac.into()),
            &mut self.efi_net_dev,
            to_smoltcp_instant(0),
        );
        interface.update_ip_addrs(|ip_addrs| ip_addrs.push(IpCidr::new(ll_ip6_addr, 64)).unwrap());

        // Generates Fuchsia Fastboot MDNS packet.
        let eth_mac = ll_mac.as_bytes();
        let fuchsia_node_name = format!(
            "fuchsia-{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}",
            eth_mac[0], eth_mac[1], eth_mac[2], eth_mac[3], eth_mac[4], eth_mac[5]
        );
        let fuchsia_fastboot_mdns_packet =
            fuchsia_fastboot_mdns_packet(fuchsia_node_name.as_str(), &ll_ip6_addr_v6.octets())?
                .into();

        // Creates sockets.
        let mut socket_set = SocketSet::new(&mut self.socket_storage[..]);
        // Creates a TCP socket for fastboot over TCP.
        let tx_socket_buffer = SocketBuffer::new(&mut self.tcp_tx_buffer[..]);
        let rx_socket_buffer = SocketBuffer::new(&mut self.tcp_rx_buffer[..]);
        let tcp_socket = TcpSocket::new(rx_socket_buffer, tx_socket_buffer);
        let _ = socket_set.add(tcp_socket);
        // Creates a UDP socket for MDNS broadcast.
        let udp_tx_packet_buffer = PacketBuffer::new(
            &mut self.udp_tx_metadata_buffer[..],
            &mut self.udp_tx_payload_buffer[..],
        );
        let udp_rx_packet_buffer = PacketBuffer::new(
            &mut self.udp_rx_metadata_buffer[..],
            &mut self.udp_rx_payload_buffer[..],
        );
        let udp_socket = UdpSocket::new(udp_rx_packet_buffer, udp_tx_packet_buffer);
        let _ = socket_set.add(udp_socket);
        Ok(EfiTcpSocket {
            efi_entry: self.efi_entry,
            efi_net_dev: &mut self.efi_net_dev,
            interface,
            socket_set,
            io_yield_counter: YieldCounter::new(u64::MAX),
            last_listen_timestamp: None,
            _time_update_event,
            timestamp: self.timestamp,
            fuchsia_fastboot_mdns_packet,
        })
    }
}

/// The GBL network stack.
///
/// # Lifetimes
///
/// * `'a`: Lifetime of `efi_entry` borrowed.
/// * `'b`: Lifetime of Self.
/// * `'c`: Lifetime of external timestamp borrowed.
#[derive(Default)]
pub struct EfiGblNetwork<'a, 'b, 'c>(Option<EfiGblNetworkInternal<'a, 'b, 'c>>);

impl<'a, 'b, 'c: 'b> EfiGblNetwork<'a, 'b, 'c> {
    /// Initializes GBL network and creates GBL sockets.
    ///
    /// # Args:
    ///
    /// * `efi_entry`: A [EfiEntry].
    /// * `ts`: A reference to an [AtomicU64].
    pub fn init(
        &'b mut self,
        efi_entry: &'a EfiEntry,
        timestamp: &'c AtomicU64,
    ) -> Result<EfiTcpSocket<'a, 'b>> {
        // Drops any existing network first to release the global event notify function.
        self.0 = None;
        self.0 = Some(EfiGblNetworkInternal::new(efi_entry, timestamp)?);
        self.0.as_mut().unwrap().create_socket()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use efi_mocks::{
        protocol::device_path::{DevicePathProtocol, DevicePathText, DevicePathToTextProtocol},
        MockEfi, MockLocatedHandles,
    };
    use efi_types::EfiSimpleNetworkMode;

    fn make_handle(id: usize) -> DeviceHandle {
        DeviceHandle::new(id as _)
    }

    fn make_snp(media_present_supported: bool, media_present: bool) -> SimpleNetworkProtocol {
        let mut snp = SimpleNetworkProtocol::default();
        snp.expect_shutdown().returning(|| Ok(()));
        snp.expect_start().returning(|| Ok(()));
        snp.expect_initialize().returning(|_, _| Ok(()));
        snp.expect_reset().returning(|_| Ok(()));
        snp.expect_get_status_raw().returning(|int_sts, tx_buf| {
            assert!(!int_sts.is_null());
            assert!(!tx_buf.is_null());
            Ok(())
        });
        snp.expect_mode().returning(move || {
            Ok(EfiSimpleNetworkMode {
                media_present_supported,
                media_present,
                ..Default::default()
            })
        });
        snp
    }

    fn setup_device_paths(mock_efi: &mut MockEfi, devices: &[(usize, &'static [u16])]) {
        let ids: Vec<usize> = devices.iter().map(|(id, _)| *id).collect();
        mock_efi
            .boot_services
            .expect_locate_handle_buffer_by_protocol::<SimpleNetworkProtocol>()
            .times(1)
            .return_once(move || {
                Ok(MockLocatedHandles(ids.into_iter().map(make_handle).collect()))
            });

        for &(id, path_u16) in devices {
            mock_efi
                .boot_services
                .expect_open_protocol::<DevicePathProtocol>()
                .times(1)
                .return_once(move |h| {
                    assert_eq!(h, make_handle(id));
                    Ok(DevicePathProtocol::default())
                });
            mock_efi
                .boot_services
                .expect_find_first_and_open::<DevicePathToTextProtocol>()
                .times(1)
                .return_once(move || {
                    let mut path_to_text = DevicePathToTextProtocol::default();
                    path_to_text.expect_convert_device_path_to_text().times(1).return_once(
                        move |_, _, _| {
                            let mut text = DevicePathText::default();
                            text.expect_text().return_const(Some(path_u16));
                            Ok(text)
                        },
                    );
                    Ok(path_to_text)
                });
        }
    }

    const NIC1_PATH: &[u16] = &[b'P' as u16, b'c' as u16, b'i' as u16, b'1' as u16];
    const NIC1_IPV4_PATH: &[u16] = &[
        b'P' as u16,
        b'c' as u16,
        b'i' as u16,
        b'1' as u16,
        b'/' as u16,
        b'I' as u16,
        b'P' as u16,
        b'v' as u16,
        b'4' as u16,
    ];
    const NIC1_IPV6_PATH: &[u16] = &[
        b'P' as u16,
        b'c' as u16,
        b'i' as u16,
        b'1' as u16,
        b'/' as u16,
        b'I' as u16,
        b'P' as u16,
        b'v' as u16,
        b'6' as u16,
    ];
    const NIC2_PATH: &[u16] = &[b'P' as u16, b'c' as u16, b'i' as u16, b'2' as u16];
    const NIC2_IPV4_PATH: &[u16] = &[
        b'P' as u16,
        b'c' as u16,
        b'i' as u16,
        b'2' as u16,
        b'/' as u16,
        b'I' as u16,
        b'P' as u16,
        b'v' as u16,
        b'4' as u16,
    ];

    #[test]
    fn test_find_net_device_ignores_child_paths() {
        let mut mock_efi = MockEfi::new();
        let nic1_ipv6_id = 1;
        let nic1_id = 2;
        let nic1_ipv4_id = 3;

        // Provide handles out of order; child IPv4/IPv6 handles must be deduplicated and never
        // opened for SimpleNetworkProtocol.
        setup_device_paths(
            &mut mock_efi,
            &[(nic1_ipv6_id, NIC1_IPV6_PATH), (nic1_id, NIC1_PATH), (nic1_ipv4_id, NIC1_IPV4_PATH)],
        );

        mock_efi
            .boot_services
            .expect_open_protocol::<SimpleNetworkProtocol>()
            .times(1)
            .return_once(move |h| {
                assert_eq!(h, make_handle(nic1_id));
                Ok(make_snp(true, true))
            });

        let installed = mock_efi.install();
        assert_eq!(find_net_device(installed.entry()), Ok(make_handle(nic1_id)));
    }

    #[test]
    fn test_find_net_device_selects_second_nic_with_media_present() {
        let mut mock_efi = MockEfi::new();
        let nic1_id = 1;
        let nic1_ipv4_id = 2;
        let nic2_id = 3;
        let nic2_ipv4_id = 4;

        setup_device_paths(
            &mut mock_efi,
            &[
                (nic1_ipv4_id, NIC1_IPV4_PATH),
                (nic2_id, NIC2_PATH),
                (nic1_id, NIC1_PATH),
                (nic2_ipv4_id, NIC2_IPV4_PATH),
            ],
        );

        // First root NIC has no link (media_present == false).
        mock_efi
            .boot_services
            .expect_open_protocol::<SimpleNetworkProtocol>()
            .times(1)
            .return_once(move |h| {
                assert_eq!(h, make_handle(nic1_id));
                Ok(make_snp(true, false))
            });

        // Second root NIC has link (media_present == true).
        mock_efi
            .boot_services
            .expect_open_protocol::<SimpleNetworkProtocol>()
            .times(1)
            .return_once(move |h| {
                assert_eq!(h, make_handle(nic2_id));
                Ok(make_snp(true, true))
            });

        let installed = mock_efi.install();
        assert_eq!(find_net_device(installed.entry()), Ok(make_handle(nic2_id)));
    }

    #[test]
    fn test_find_net_device_fallback_to_first_root_nic() {
        let mut mock_efi = MockEfi::new();
        let nic1_id = 1;
        let nic1_ipv6_id = 2;
        let nic2_id = 3;

        setup_device_paths(
            &mut mock_efi,
            &[(nic2_id, NIC2_PATH), (nic1_ipv6_id, NIC1_IPV6_PATH), (nic1_id, NIC1_PATH)],
        );

        // Neither root NIC reports media_present == true.
        mock_efi
            .boot_services
            .expect_open_protocol::<SimpleNetworkProtocol>()
            .times(1)
            .return_once(move |h| {
                assert_eq!(h, make_handle(nic1_id));
                Ok(make_snp(true, false))
            });
        mock_efi
            .boot_services
            .expect_open_protocol::<SimpleNetworkProtocol>()
            .times(1)
            .return_once(move |h| {
                assert_eq!(h, make_handle(nic2_id));
                Ok(make_snp(true, false))
            });

        let installed = mock_efi.install();
        assert_eq!(find_net_device(installed.entry()), Ok(make_handle(nic1_id)));
    }
}
