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

use crate::{
    error::{EfiAppError, Result},
    utils::{get_device_path, loop_with_timeout, ms_to_100ns, Timeout},
};
use alloc::{boxed::Box, vec::Vec};
use core::{
    fmt::Write,
    sync::atomic::{AtomicU64, Ordering},
};
use efi::{
    defs::{
        EfiEvent, EfiMacAddress, EFI_STATUS_ALREADY_STARTED, EFI_STATUS_NOT_STARTED,
        EFI_TIMER_DELAY_TIMER_PERIODIC,
    },
    efi_print, efi_println,
    protocol::{simple_network::SimpleNetworkProtocol, Protocol},
    DeviceHandle, EfiEntry, EventNotify, EventType, Tpl,
};
use gbl_async::{yield_now, YieldCounter};
use smoltcp::{
    iface::{Config, Interface, SocketSet},
    phy,
    phy::{Device, DeviceCapabilities, Medium},
    socket::tcp,
    time::Instant,
    wire::{EthernetAddress, IpAddress, IpCidr, Ipv6Address},
};

/// Maintains a timestamp needed by smoltcp network. It's updated periodically during timer event.
static NETWORK_TIMESTAMP: AtomicU64 = AtomicU64::new(0);
/// Ethernet frame size for frame pool.
const ETHERNET_FRAME_SIZE: usize = 1536;
// Update period in milliseconds for `NETWORK_TIMESTAMP`.
const NETWORK_TIMESTAMP_UPDATE_PERIOD: u64 = 50;
// Size of the socket tx/rx application data buffer.
const SOCKET_TX_RX_BUFFER: usize = 64 * 1024;

/// Performs a shutdown and restart of the simple network protocol.
fn reset_simple_network<'a>(snp: &Protocol<'a, SimpleNetworkProtocol>) -> Result<()> {
    match snp.shutdown() {
        Err(e) if !e.is_efi_err(EFI_STATUS_NOT_STARTED) => return Err(e.into()),
        _ => {}
    };

    match snp.start() {
        Err(e) if !e.is_efi_err(EFI_STATUS_ALREADY_STARTED) => {
            return Err(e.into());
        }
        _ => {}
    };
    snp.initialize(0, 0).unwrap();
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
    /// Creates an new instance. Allocates `extra_tx_frames+1` number of TX frames.
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
            if !e.is_efi_err(EFI_STATUS_NOT_STARTED) {
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
            let _ = unsafe { Box::from_raw(v) };
        });
    }
}

// Implements network device trait backend for the `smoltcp` crate.
impl<'a> Device for EfiNetworkDevice<'a> {
    type RxToken<'b> = RxToken<'b> where Self: 'b;
    type TxToken<'b> = TxToken<'a, 'b> where Self: 'b;

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
        F: FnOnce(&mut [u8]) -> R,
    {
        f(self.0)
    }
}

/// In smoltcp, a `TxToken` is used to transmit a frame when consumed.
pub struct TxToken<'a: 'b, 'b> {
    tx_frames: &'b mut [*mut [u8; ETHERNET_FRAME_SIZE]],
    curr: &'b mut usize,
    protocol: &'b Protocol<'a, SimpleNetworkProtocol>,
    efi_entry: &'b EfiEntry,
}

impl TxToken<'_, '_> {
    /// Tries to allocate a send buffer.
    fn try_get_buffer(&mut self) -> Option<*mut [u8; ETHERNET_FRAME_SIZE]> {
        let mut ptr: *mut core::ffi::c_void = core::ptr::null_mut();
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
            match loop_with_timeout(self.efi_entry, 5000, || self.try_get_buffer().ok_or(false)) {
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

/// Returns the current value of timestamp.
fn timestamp() -> u64 {
    NETWORK_TIMESTAMP.load(Ordering::Relaxed)
}

/// Returns a smoltcp time `Instant` value.
fn time_instant() -> Instant {
    Instant::from_millis(i64::try_from(timestamp()).unwrap())
}

/// Find the first available network device.
fn find_net_device(efi_entry: &EfiEntry) -> Result<DeviceHandle> {
    // Find the device whose path is the "smallest" lexicographically, this ensures that it's not
    // any child network device of some other node. e1000 tends to add a child network device for
    // ipv4 and ipv6 configuration information.
    efi_entry
        .system_table()
        .boot_services()
        .locate_handle_buffer_by_protocol::<SimpleNetworkProtocol>()?
        .handles()
        .iter()
        .map(|handle| (*handle, get_device_path(efi_entry, *handle)))
        // Ignore devices that fail to get device path.
        .filter_map(|(handle, path)| path.ok().map(|v| (handle, v)))
        // Ignore devices that have NULL path.
        .filter_map(|(handle, path)| path.text().is_some().then(|| (handle, path)))
        // Finds the minimum path lexicographically.
        .min_by(|lhs, rhs| Ord::cmp(lhs.1.text().unwrap(), rhs.1.text().unwrap()))
        .map(|(h, _)| h)
        .ok_or(EfiAppError::NotFound.into())
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

    (
        EthernetAddress::from_bytes(ll_mac_bytes),
        IpAddress::Ipv6(Ipv6Address::from_bytes(&ip6_bytes[..])),
    )
}

/// `EfiTcpSocket` groups together necessary components for performing TCP.
pub struct EfiTcpSocket<'a, 'b> {
    efi_net_dev: &'b mut EfiNetworkDevice<'a>,
    interface: &'b mut Interface,
    sockets: &'b mut SocketSet<'b>,
    efi_entry: &'a EfiEntry,
    io_yield_counter: YieldCounter,
}

impl<'a, 'b> EfiTcpSocket<'a, 'b> {
    /// Resets the socket and starts listening for new TCP connection.
    pub fn listen(&mut self, port: u16) -> Result<()> {
        self.get_socket().abort();
        self.get_socket().listen(port)?;
        Ok(())
    }

    /// Polls network device.
    pub fn poll(&mut self) {
        self.interface.poll(time_instant(), self.efi_net_dev, self.sockets);
    }

    /// Polls network and check if the socket is in an active state.
    pub fn check_active(&mut self) -> bool {
        self.poll();
        self.get_socket().is_active()
    }

    /// Gets a reference to the smoltcp socket object.
    pub fn get_socket(&mut self) -> &mut tcp::Socket<'b> {
        // We only consider single socket use case for now.
        let handle = self.sockets.iter().next().unwrap().0;
        self.sockets.get_mut::<tcp::Socket>(handle)
    }

    /// Checks whether a socket is closed.
    fn is_closed(&mut self) -> bool {
        return !self.get_socket().is_open() || self.get_socket().state() == tcp::State::CloseWait;
    }

    /// Sets the maximum number of bytes to read or write before a force await.
    pub fn set_io_yield_threshold(&mut self, threshold: u64) {
        self.io_yield_counter = YieldCounter::new(threshold)
    }

    /// Receives exactly `out.len()` number of bytes to `out`.
    pub async fn receive_exact(&mut self, out: &mut [u8], timeout: u64) -> Result<()> {
        let timer = Timeout::new(self.efi_entry, timeout)?;
        let mut curr = &mut out[..];
        while !curr.is_empty() {
            self.poll();
            let mut has_progress = false;

            if self.is_closed() {
                return Err(EfiAppError::PeerClosed.into());
            } else if timer.check()? {
                return Err(EfiAppError::Timeout.into());
            } else if self.get_socket().can_recv() {
                let recv_size = self.get_socket().recv_slice(curr)?;
                curr = curr.get_mut(recv_size..).ok_or(EfiAppError::ArithmeticOverflow)?;
                has_progress = recv_size > 0;
                // Forces a yield to the executor if the data received/sent reaches a certain
                // threshold. This is to prevent the async code from holding up the CPU for too long
                // in case IO speed is high and the executor uses cooperative scheduling.
                self.io_yield_counter.increment(recv_size.try_into().unwrap()).await;
            }

            match has_progress {
                true => timer.reset(timeout)?,
                _ => yield_now().await,
            }
        }
        Ok(())
    }

    /// Sends exactly `data.len()` number of bytes from `data`.
    pub async fn send_exact(&mut self, data: &[u8], timeout: u64) -> Result<()> {
        let timer = Timeout::new(self.efi_entry, timeout)?;
        let mut curr = &data[..];
        let mut last_send_queue = self.get_socket().send_queue();
        loop {
            self.poll();
            if curr.is_empty() && self.get_socket().send_queue() == 0 {
                return Ok(());
            } else if self.is_closed() {
                return Err(EfiAppError::PeerClosed.into());
            } else if timer.check()? {
                return Err(EfiAppError::Timeout.into());
            }

            let mut has_progress = false;
            // Checks if any data in the queue is sent.
            if self.get_socket().send_queue() != last_send_queue {
                last_send_queue = self.get_socket().send_queue();
                has_progress = true;
            }
            // Checks if there are more data to be queued.
            if self.get_socket().can_send() && !curr.is_empty() {
                let sent = self.get_socket().send_slice(curr)?;
                curr = curr.get(sent..).ok_or(EfiAppError::ArithmeticOverflow)?;
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
        self.interface
    }

    /// Returns the number of milliseconds elapsed since the `base` timestamp.
    pub fn timestamp(base: u64) -> u64 {
        let curr = timestamp();
        // Assume there can be at most one overflow.
        match curr < base {
            true => u64::MAX - (base - curr),
            false => curr - base,
        }
    }
}

/// Initializes network environment and provides a TCP socket for callers to run a closure. The API
/// handles clean up automatically after returning.
pub fn with_efi_network<F, R>(efi_entry: &EfiEntry, mut f: F) -> Result<R>
where
    F: FnMut(&mut EfiTcpSocket) -> R,
{
    let bs = efi_entry.system_table().boot_services();

    // Creates timestamp update event.
    let _ = NETWORK_TIMESTAMP.swap(0, Ordering::Relaxed);
    let mut notify_fn = |_: EfiEvent| {
        NETWORK_TIMESTAMP.fetch_add(NETWORK_TIMESTAMP_UPDATE_PERIOD, Ordering::Relaxed);
    };
    let mut notify = EventNotify::new(Tpl::Callback, &mut notify_fn);
    let timer = bs.create_event(EventType::TimerNotifySignal, Some(&mut notify))?;
    bs.set_timer(
        &timer,
        EFI_TIMER_DELAY_TIMER_PERIODIC,
        ms_to_100ns(NETWORK_TIMESTAMP_UPDATE_PERIOD)?,
    )?;

    // Creates and initializes simple network protocol.
    let snp_dev = find_net_device(efi_entry)?;
    let snp = bs.open_protocol::<SimpleNetworkProtocol>(snp_dev)?;
    reset_simple_network(&snp)?;

    // Gets our MAC address and IPv6 address.
    // We can also consider getting this from vendor configuration.
    let (ll_mac, ll_ip6_addr) = ll_mac_ip6_addr_from_efi_mac(snp.mode()?.current_address);

    // Creates an `EfiNetworkDevice`.
    // Allocates 7(chosen randomly) extra TX frames. Revisits if it is not enough.
    let mut efi_net_dev = EfiNetworkDevice::new(snp, 7, &efi_entry);
    // Configures smoltcp network interface.
    let mut interface =
        Interface::new(Config::new(ll_mac.into()), &mut efi_net_dev, time_instant());
    interface.update_ip_addrs(|ip_addrs| ip_addrs.push(IpCidr::new(ll_ip6_addr, 64)).unwrap());
    // Creates an instance of socket.
    let mut tx_buffer = vec![0u8; SOCKET_TX_RX_BUFFER];
    let mut rx_buffer = vec![0u8; SOCKET_TX_RX_BUFFER];
    let tx_socket_buffer = tcp::SocketBuffer::new(&mut tx_buffer[..]);
    let rx_socket_buffer = tcp::SocketBuffer::new(&mut rx_buffer[..]);
    let socket = tcp::Socket::new(rx_socket_buffer, tx_socket_buffer);
    let mut sockets: [_; 1] = Default::default();
    let mut sockets = SocketSet::new(&mut sockets[..]);
    let _ = sockets.add(socket);
    let mut socket = EfiTcpSocket {
        efi_net_dev: &mut efi_net_dev,
        interface: &mut interface,
        sockets: &mut sockets,
        efi_entry: efi_entry,
        io_yield_counter: YieldCounter::new(u64::MAX),
    };

    Ok(f(&mut socket))
}
