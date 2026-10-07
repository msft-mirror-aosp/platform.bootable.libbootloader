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

//! This library provides APIs for receiving, processing and replying to fastboot commands. To use
//! the library:
//!
//! 1. Provide a transport backend by implementing the `Transport` trait.
//!
//! ```
//!
//! struct FastbootTransport {}
//!
//! impl Transport<MyErrorType> for TestTransport {
//!     fn receive_packet(&mut self, out: &mut [u8]) -> Result<usize, TransportError> {
//!         todo!();
//!     }
//!
//!     fn send_packet(&mut self, packet: &[u8]) -> Result<(), TransportError> {
//!         todo!();
//!     }
//! }
//! ```
//!
//! 2. Provide a fastboot command backend by implementing the `FastbootImplementation` trait.
//!    i.e.
//!
//! ```
//!
//! struct FastbootCommand {}
//!
//! impl FastbootImplementation for FastbootTest {
//!     fn get_var(
//!         &mut self,
//!         var: &str,
//!         args: Split<char>,
//!         out: &mut [u8],
//!     ) -> CommandResult<usize> {
//!         todo!();
//!     }
//!
//!     ...
//! }
//!```
//!
//! 3. Construct a `Fastboot` object with a given download buffer. Pass the transport, command
//!    implementation and call the `run()` method:
//!
//! ```
//! let mut fastboot_impl: FastbootCommand = ...;
//! let mut transport: TestTransport = ...;
//! let download_buffer: &mut [u8] = ...;
//! let mut fastboot = Fastboot::new();
//! let result = run(&mut transport, &mut fastboot_impl, &[]);
//! ```

#![feature(never_type)]
#![cfg_attr(not(test), no_std)]
#![allow(async_fn_in_trait)]

use core::{
    cmp::min,
    ffi::CStr,
    fmt::{Debug, Display, Formatter, Write},
    mem::size_of,
    str::{from_utf8, Split},
};
use gbl_async::block_on;
use liberror::{Error, Result};
use libutils::{next_arg, FormattedBytes, FromHexStr};

/// Maximum packet size that can be accepted from the host.
///
/// The transport layer may have its own size limits that reduce the packet size further.
pub const MAX_COMMAND_SIZE: usize = 4096;
/// Maximum packet size that will be sent to the host.
///
/// The `fastboot` host tool originally had a 64-byte packet size max, but this was increased
/// to 256 in 2020, so any reasonably recent host binary should be able to support 256.
///
/// The transport layer may have its own size limits that reduce the packet size further.
pub const MAX_RESPONSE_SIZE: usize = 256;

/// Trait to provide the transport layer for a fastboot implementation.
///
/// Fastboot supports transports:
/// * Any GblFastbootTransport implementation: provided by UEFI drivers
/// * TCP: provided by GBL for dev build only.
pub trait Transport {
    /// Reads the next data packet. Reads up to the next packet or provided buffer.
    ///
    /// # Returns
    ///
    /// * On success, returns `(actual received size, remaining size of the current packet)`
    /// * Returns `Error::BufferTooSmall()` if partial receive is not supported and 'out' is
    ///   too small for one packet.
    async fn receive(&mut self, out: &mut [u8]) -> Result<(usize, usize)>;

    /// Fetches the entire next fastboot packet into `out`.
    ///
    /// Returns the actual size of the packet on success.
    async fn receive_packet(&mut self, mut out: &mut [u8]) -> Result<usize> {
        let (recv, rem) = self.receive(out).await?;
        out = out.split_at_mut_checked(recv).ok_or(Error::Other(Some("Invalid recv size")))?.1;
        out = out.get_mut(..rem).ok_or(Error::BufferTooSmall(recv.checked_add(rem)))?;
        while !out.is_empty() {
            let (sz, _) = self.receive(out).await?;
            out = out.split_at_mut_checked(sz).ok_or(Error::Other(Some("Invalid recv size")))?.1;
        }
        Ok(recv + rem)
    }

    /// Sends a fastboot packet.
    ///
    /// The method assumes `packet` is sent or at least copied to queue after it returns, where
    /// the buffer can go out of scope without affecting anything.
    async fn send_packet(&mut self, packet: &[u8]) -> Result<()>;
}

/// For now, we hardcode the expected version, until we need to distinguish between multiple
/// versions.
const TCP_HANDSHAKE_MESSAGE: &[u8] = b"FB01";

// Check if command is protected from overriding
fn is_protected_command<'a>(mut args: impl Iterator<Item = &'a CStr> + Clone) -> bool {
    const PROTECTED_FASTBOOT_COMMANDS: &[&CStr] = &[
        // LINT.IfChange
        c"continue",
        c"download",
        c"fetch",
        c"getvar",
        c"reboot",
        c"reboot-bootloader",
        c"reboot-fastboot",
        c"reboot-recovery",
        c"set_active",
        c"upload",
        // LINT.ThenChange(/gbl/docs/gbl_efi_fastboot_protocol.md)
    ];

    if let Some(cmd) = args.next() {
        PROTECTED_FASTBOOT_COMMANDS.contains(&cmd)
    } else {
        false
    }
}

/// A trait representing a TCP stream reader/writer. Fastboot over TCP has additional handshake
/// process and uses a length-prefixed wire message format. It is recommended that caller
/// implements this trait instead of `Transport`, and uses the API `Fastboot::run_tcp_session()`
/// to perform fastboot over TCP. It internally handles handshake and wire message parsing.
pub trait TcpStream {
    /// Read data from the TCP connection.
    ///
    /// On success, returns the actual amount read.
    async fn read(&mut self, out: &mut [u8]) -> Result<usize>;

    /// Reads to `out` for exactly `out.len()` number bytes from the TCP connection.
    async fn read_exact(&mut self, mut out: &mut [u8]) -> Result<()> {
        while !out.is_empty() {
            let sz = self.read(out).await?;
            out = out.split_at_mut(sz).1;
        }
        Ok(())
    }

    /// Sends exactly `data.len()` number bytes from `data` to the TCP connection.
    async fn write_exact(&mut self, data: &[u8]) -> Result<()>;
}

/// Implements [Transport] on a [TcpStream].
pub struct TcpTransport<'a, T: TcpStream> {
    tcp: &'a mut T,
    remaining_packet: usize,
}

impl<'a, T: TcpStream> TcpTransport<'a, T> {
    /// Creates an instance from a newly connected TcpStream and performs handshake.
    pub fn new_and_handshake(tcp_stream: &'a mut T) -> Result<Self> {
        let mut handshake = [0u8; 4];
        block_on(tcp_stream.write_exact(TCP_HANDSHAKE_MESSAGE))?;
        block_on(tcp_stream.read_exact(&mut handshake[..]))?;
        match handshake == *TCP_HANDSHAKE_MESSAGE {
            true => Ok(Self { tcp: tcp_stream, remaining_packet: 0 }),
            _ => Err(Error::InvalidHandshake),
        }
    }
}

impl<'a, T: TcpStream> Transport for TcpTransport<'a, T> {
    async fn receive(&mut self, out: &mut [u8]) -> Result<(usize, usize)> {
        if self.remaining_packet == 0 {
            let mut length_prefix = [0u8; 8];
            self.tcp.read_exact(&mut length_prefix[..]).await?;
            self.remaining_packet = u64::from_be_bytes(length_prefix).try_into()?;
        }
        let to_read = min(self.remaining_packet, out.len());
        let sz = self.tcp.read(&mut out[..to_read]).await?;
        self.remaining_packet -= sz;
        Ok((sz, self.remaining_packet))
    }

    async fn send_packet(&mut self, packet: &[u8]) -> Result<()> {
        self.tcp.write_exact(&mut u64::try_from(packet.len())?.to_be_bytes()[..]).await?;
        self.tcp.write_exact(packet).await
    }
}

const COMMAND_ERROR_LENGTH: usize = MAX_RESPONSE_SIZE - 4;

/// `CommandError` is the return error type for methods in trait `FastbootImplementation` when
/// they fail. It will be converted into string and sent as fastboot error message "FAIL<string>".
///
/// Any type that implements `Display` trait can be converted into it. However, because fastboot
/// response message is limited to `MAX_RESPONSE_SIZE`. If the final displayed string length
/// exceeds it, the rest of the content is ignored.
pub struct CommandError(FormattedBytes<[u8; COMMAND_ERROR_LENGTH]>);

impl CommandError {
    /// Returns the `FormattedBytes` object.
    pub fn formatted_bytes(&mut self) -> &mut FormattedBytes<impl AsMut<[u8]> + AsRef<[u8]>> {
        &mut self.0
    }

    /// Returns the parsed string representation of self.
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl AsRef<[u8]> for CommandError {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl PartialEq for CommandError {
    fn eq(&self, other: &Self) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl Clone for CommandError {
    /// Clones the error.
    fn clone(&self) -> Self {
        self.as_str().into()
    }
}

impl Debug for CommandError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl<T: Display> From<T> for CommandError {
    fn from(val: T) -> Self {
        let mut res = CommandError(FormattedBytes::new([0u8; COMMAND_ERROR_LENGTH]));
        write!(res.0, "{}", val).unwrap();
        res
    }
}

/// Type alias for Result that wraps a CommandError
pub type CommandResult<T> = core::result::Result<T, CommandError>;

/// Fastboot reboot mode
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum RebootMode {
    /// "fastboot reboot". Normal reboot.
    Normal,
    /// "fastboot reboot-bootloader". Reboot to bootloader.
    Bootloader,
    /// "fastboot reboot-fastboot". Reboot to userspace fastboot.
    Fastboot,
    /// "fastboot reboot-recovery". Reboot to recovery.
    Recovery,
}

/// Specifies the type of lock for `FastbootImplementation::flashing_write_lock_state`.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum LockType {
    /// Locking or unlocking the device.
    Device,
    /// Locking or unlocking the critical partitions
    Critical,
}

/// Specifies the state of lock for `FastbootImplementation::flashing_write_lock_state`.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum LockState {
    /// locked
    Locked,
    /// Unlocked
    Unlocked,
}

/// Specifies whether the device can be unlocked.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Unlockability {
    /// Unlockable
    Allowed,
    /// Not unlockable
    Prohibited,
}

/// Specifies command implementation to be used
#[derive(Copy, Clone, Debug, Default, PartialEq)]
pub enum CommandExecType {
    /// Default GBL implementation
    #[default]
    DefaultImpl,
    /// Custom vendor implementation
    CustomImpl,
    /// Command is not allowed
    Prohibited,
}

/// Implementation for Fastboot command backends.
pub trait FastbootImplementation {
    /// Backend for `fastboot getvar ...`
    ///
    /// Gets the value of a variable specified by name and configuration represented by list of
    /// additional arguments in `args`.
    ///
    /// Variable `max-download-size`, `version` are reserved by the library.
    ///
    /// # Args
    ///
    /// * `var`: Name of the variable.
    /// * `args`: Additional arguments.
    /// * `out`: Output buffer for storing the variable value.
    /// * `responder`: An instance of `InfoSender`.
    ///
    /// TODO(b/322540167): Figure out other reserved variables.
    async fn get_var(
        &mut self,
        var: &CStr,
        args: impl Iterator<Item = &'_ CStr> + Clone,
        out: &mut [u8],
        responder: impl InfoSender,
    ) -> CommandResult<usize>;

    /// A helper API for getting the value of a fastboot variable and decoding it into string.
    async fn get_var_as_str<'s>(
        &mut self,
        var: &CStr,
        args: impl Iterator<Item = &'_ CStr> + Clone,
        responder: impl InfoSender,
        out: &'s mut [u8],
    ) -> CommandResult<&'s str> {
        let size = self.get_var(var, args, out, responder).await?;
        Ok(from_utf8(out.get(..size).ok_or("Invalid variable size")?)
            .map_err(|_| "Value is not string")?)
    }

    /// Backend for `fastboot getvar all`.
    ///
    /// Iterates all combinations of fastboot variable, configurations and values that need to be
    /// included in the response to `fastboot getvar all`.
    ///
    /// # Args
    ///
    /// * `responder`: An implementation VarInfoSender. Implementation should call
    ///   `VarInfoSender::send` for all combinations of Fastboot variable/argument/value that needs
    ///   to be included in the response to `fastboot getvarl all`:
    ///
    ///   async fn get_var_all(&mut self, f: F, resp: impl VarInfoSender)
    ///     -> CommandResult<()> {
    ///       resp.send("partition-size", &["boot_a"], /* size of boot_a */).await?;
    ///       resp.send("partition-size", &["boot_b"], /* size of boot_b */).await?;
    ///       resp.send("partition-size", &["init_boot_a"], /* size of init_boot_a */).await?;
    ///       resp.send("partition-size", &["init_boot_b"], /* size of init_boot_b */).await?;
    ///       Ok(())
    ///   }
    ///
    ///   will generates the following outputs for `fastboot getvar all`:
    ///
    ///   ...
    ///   (bootloader) partition-size:boot_a: <size of boot_a>
    ///   (bootloader) partition-size:boot_b: <size of boot_b>
    ///   (bootloader) partition-size:init_boot_a: <size of init_boot_a>
    ///   (bootloader) partition-size:init_boot_b: <size of init_boot_b>
    ///   ...
    ///
    /// TODO(b/322540167): This and `get_var()` contain duplicated logic. Investigate if there can
    /// be better solutions for doing the combination traversal.
    async fn get_var_all(&mut self, responder: impl VarInfoSender) -> CommandResult<()>;

    /// Backend for `fastboot flash ...`
    ///
    /// # Args
    ///
    /// * `part`: Name of the partition.
    /// * `responder`: An instance of `InfoSender`.
    async fn flash(&mut self, part: &str, responder: impl InfoSender) -> CommandResult<()>;

    /// Backend for `fastboot erase ...`
    ///
    /// # Args
    ///
    /// * `part`: Name of the partition.
    /// * `responder`: An instance of `InfoSender`.
    async fn erase(&mut self, part: &str, responder: impl InfoSender) -> CommandResult<()>;

    /// Backend for `fastboot download`
    ///
    /// # Args
    ///
    /// * `responder`: An instance of `DownloadBuilder + InfoSender` for initiating and downloading
    ///   data.
    async fn download(&mut self, responder: impl DownloadBuilder + InfoSender)
        -> CommandResult<()>;

    /// Backend for `fastboot stream-flash ...` and `fastboot stream-fill ...`
    ///
    /// # Args
    ///
    /// * `command`: The write or stream command.
    /// * `responder`: An instance of `InfoSender`.
    async fn stream<'a>(
        &mut self,
        command: StreamCommand<&'a str>,
        responder: impl InfoSender,
    ) -> CommandResult<()>;

    /// Helper API for providing download from buffer
    async fn set_download(&mut self, data: &[u8]) -> CommandResult<()> {
        self.download(RamDownloader(data)).await
    }

    /// Backend for `fastboot get_staged ...`
    ///
    /// # Args
    ///
    /// * `responder`: An instance of `UploadBuilder + InfoSender` for initiating and uploading
    ///   data. For example:
    ///
    ///   ```
    ///   async fn upload(
    ///       &mut self,
    ///       responder: impl UploadBuilder + InfoSender,
    ///   ) -> CommandResult<()> {
    ///       let data = ..;
    ///       // Sends a total of 1024 bytes data.
    ///       responder.send_info("About to upload...").await?;
    ///       let mut uploader = responder.initiate_upload(1024).await?;
    ///       // Can upload in multiple batches.
    ///       uploader.upload(&data[..512]).await?;
    ///       uploader.upload(&data[512..]).await?;
    ///       Ok(())
    ///   }
    ///   ```
    ///
    ///   If implementation fails to upload enough, or attempts to upload more than expected data
    ///   with `Uploader::upload()`, an error will be returned.
    async fn upload(&mut self, responder: impl UploadBuilder + InfoSender) -> CommandResult<()>;

    /// Backend for `fastboot fetch ...`
    ///
    /// # Args
    ///
    /// * `part`: The partition name.
    /// * `offset`: The offset into the partition for upload.
    /// * `size`: The number of bytes to upload.
    /// * `responder`: An instance of `UploadBuilder + InfoSender` for initiating and uploading data.
    async fn fetch(
        &mut self,
        part: &str,
        offset: u64,
        size: u32,
        responder: impl UploadBuilder + InfoSender,
    ) -> CommandResult<()>;

    /// Backend for `fastboot reboot/reboot-bootloader/reboot-fastboot/reboot-recovery`
    ///
    /// # Args
    ///
    /// * `mode`: A `RebootMode` specifying the reboot mode.
    /// * `responder`: An instance of `InfoSender + OkaySender`. Implementation should call
    ///   `responder.send_okay("")` right before reboot to notify the remote host that the
    ///   operation is successful.
    ///
    /// # Returns
    ///
    /// * The method is not expected to return if reboot is successful.
    /// * Returns `Err(e)` on error.
    async fn reboot(
        &mut self,
        mode: RebootMode,
        responder: impl InfoSender + OkaySender,
    ) -> CommandResult<!>;

    /// Method for handling `fastboot continue` clean up.
    ///
    /// `run()` and `run_tcp_session()` exit after receiving `fastboot continue.` The method is for
    /// implementation to perform necessary clean up.
    ///
    /// # Args
    ///
    /// * `responder`: An instance of `InfoSender`.
    async fn r#continue(&mut self, responder: impl InfoSender) -> CommandResult<()>;

    /// Backend for `fastboot set_active`.
    async fn set_active(&mut self, slot: &str, responder: impl InfoSender) -> CommandResult<()>;

    /// Backend for `fastboot boot`
    ///
    /// # Args
    ///
    /// * `responder`: An instance of `InfoSender + OkaySender`. Implementation should call
    ///   `responder.send_okay("")` right before boot to notify the remote host that the
    ///   operation is successful.
    ///
    /// # Returns
    ///
    /// * The method always returns OK to let fastboot continue.
    /// * Returns `Err(e)` on error.
    async fn boot(&mut self, responder: impl InfoSender + OkaySender) -> CommandResult<()>;

    /// Backend for `fastboot oem ...`.
    ///
    /// # Args
    ///
    /// * `cmd`: The OEM command string that comes after "oem ".
    /// * `responder`: An instance of `InfoSender + OkaySender + FailSender`.
    ///
    /// * If backend does not plan to return from the function, or wants to construct custom result
    ///   message, it should send either an OKAY or FAIL message with `responder`, otherwise host
    ///   may hang waiting for reply.
    /// * If implementation returns Ok(()) without sending an OKAY message via `responder`,
    ///   an empty OKAY message will be sent by `process_next_command()`.
    /// * If implementation returns Err(e) without sending a FAIL message via `responder`,
    ///   a FAIL message of `e` will be sent.
    async fn oem(
        &mut self,
        cmd: &str,
        responder: impl InfoSender + OkaySender + FailSender,
    ) -> CommandResult<()>;

    /// Handler for `fastboot flashing lock|unlock` and
    /// `fastboot flashing lock_critical|unlock_critical`.
    ///
    /// # Args
    ///
    /// * `critical`: Whether the operation is for critical partitions.
    /// * `lock`: True to lock, false to unlock.
    ///
    /// # Returns
    ///
    /// Ok(()) if call succeeded, Err on error.
    async fn flashing_write_lock_state(
        &mut self,
        lock_type: LockType,
        lock_state: LockState,
        responder: impl InfoSender,
    ) -> CommandResult<()>;

    /// Handler for `fastboot flashing get_unlock_ability`.
    ///
    /// # Returns
    ///
    /// Ok(Unlockability),
    /// Err on error.
    async fn flashing_get_unlock_ability(&mut self) -> CommandResult<Unlockability>;

    /// Checks whether a command is allowed and if to use custom implementation or default.
    ///
    /// # Args
    ///
    /// * `args`: The command string.
    /// * `responder`: An instance of `InfoSender + OkaySender + FailSender`.
    ///
    /// Returns CommandExecType
    ///
    /// * DefaultImpl - Default implementation will run for the command if available.
    /// * CustomImpl - Vendor has overridden the command. `fastboot oem ...` is one of the cases
    /// that is implemented using this approach.
    /// * Prohibited - shortcut for CustomImpl that just bans the command.
    async fn command_exec(
        &mut self,
        args: impl Iterator<Item = &'_ CStr> + Clone,
        responder: impl InfoSender + OkaySender + FailSender,
    ) -> CommandResult<CommandExecType>;

    /// Logs message if implementation is provided
    ///
    /// # Args
    ///
    /// * `message`: A displayable object to be printed.
    fn log_line(&mut self, message: impl Display);

    // TODO(b/322540167): Add methods for other commands.
}

/// A download builder/downloader with data from buffer.
struct RamDownloader<'a>(&'a [u8]);

impl DownloadBuilder for RamDownloader<'_> {
    async fn initiate_download(self) -> Result<impl Downloader> {
        Ok(self)
    }

    fn total(&self) -> usize {
        self.0.len()
    }
}

impl Downloader for RamDownloader<'_> {
    async fn download(&mut self, out: &mut [u8]) -> Result<usize> {
        let to_read = min(out.len(), self.0.len());
        let (this, rem) = self.0.split_at(to_read);
        out[..to_read].copy_from_slice(this);
        self.0 = rem;
        Ok(to_read)
    }

    fn remaining(&self) -> usize {
        self.0.len()
    }
}

impl InfoSender for RamDownloader<'_> {
    async fn send_formatted_info<F: FnOnce(&mut dyn Write)>(&mut self, _: F) -> Result<()> {
        Ok(())
    }
}

/// An internal convenient macro helper for `fastboot_okay`, `fastboot_fail` and `fastboot_info`.
macro_rules! fastboot_msg {
    ( $arr:expr, $msg_type:expr, $( $x:expr ),* $(,)? ) => {
        {
            let mut formatted_bytes = FormattedBytes::new(&mut $arr[..]);
            write!(formatted_bytes, $msg_type).unwrap();
            write!(formatted_bytes, $($x,)*).unwrap();
            let size = formatted_bytes.size();
            &mut $arr[..size]
        }
    };
}

/// An internal convenient macro that constructs a formatted fastboot OKAY message.
macro_rules! fastboot_okay {
    ( $arr:expr, $( $x:expr ),* $(,)?) => { fastboot_msg!($arr, "OKAY", $($x,)*) };
}

/// An internal convenient macro that constructs a formatted fastboot FAIL message.
macro_rules! fastboot_fail {
    ( $arr:expr, $( $x:expr ),* $(,)?) => { fastboot_msg!($arr, "FAIL", $($x,)*) };
}

/// `VarInfoSender` provide an interface for sending variable/args/value combination during the
/// processing of `fastboot getvar all`
pub trait VarInfoSender {
    /// Send a combination of variable name, arguments and value.
    ///
    /// The method sends a fastboot message "INFO<var>:<args>:<val>" to the host.
    ///
    /// # Args
    ///
    /// * `name`: Name of the fastboot variable.
    /// * `args`: An iterator to additional arguments.
    /// * `val`: Value of the variable.
    async fn send_var_info(
        &mut self,
        name: &str,
        args: impl IntoIterator<Item = &'_ str>,
        val: &str,
    ) -> Result<()>;
}

/// Provides an API for sending fastboot INFO messages.
pub trait InfoSender {
    /// Sends formatted INFO message.
    ///
    /// # Args:
    ///
    /// * `cb`: A closure provided by the caller for constructing the formatted message.
    async fn send_formatted_info<F: FnOnce(&mut dyn Write)>(&mut self, cb: F) -> Result<()>;

    /// Sends a Fastboot "INFO<`msg`>" packet.
    async fn send_info(&mut self, msg: &str) -> Result<()> {
        self.send_formatted_info(|w| write!(w, "{}", msg).unwrap()).await
    }
}

/// Provides an API for sending fastboot OKAY messages.
pub trait OkaySender {
    /// Sends formatted Okay message.
    ///
    /// # Args:
    ///
    /// * `cb`: A closure provided by the caller for constructing the formatted message.
    async fn send_formatted_okay<F: FnOnce(&mut dyn Write)>(self, cb: F) -> Result<()>;

    /// Sends a fastboot OKAY<msg> packet. `Self` is consumed.
    async fn send_okay(self, msg: &str) -> Result<()>
    where
        Self: Sized,
    {
        self.send_formatted_okay(|w| write!(w, "{}", msg).unwrap()).await
    }
}

/// Provides an API for sending fastboot FAIL messages.
pub trait FailSender {
    /// Sends formatted FAIL message.
    ///
    /// # Args:
    ///
    /// * `cb`: A closure provided by the caller for constructing the formatted message.
    async fn send_formatted_fail<F: FnOnce(&mut dyn Write)>(self, cb: F) -> Result<()>;

    /// Sends a fastboot FAIL<msg> packet. `Self` is consumed.
    async fn send_fail(self, msg: &str) -> Result<()>
    where
        Self: Sized,
    {
        self.send_formatted_fail(|w| write!(w, "{}", msg).unwrap()).await
    }
}

/// `DownloadBuilder` provides API for initiating a fastboot download.
pub trait DownloadBuilder {
    /// Starts the download process.
    ///
    /// In a real fastboot context, the method should send `DATAXXXXXXXX` to the remote host to
    /// start the download.
    ///
    /// On success returns a `Downloader` implementation.
    async fn initiate_download(self) -> Result<impl Downloader>;

    /// Returns the total download size.
    fn total(&self) -> usize;
}

/// `Downloader` provides API for downloading data
pub trait Downloader {
    /// Receives download data.
    ///
    /// On success, returns the actual received size.
    async fn download(&mut self, out: &mut [u8]) -> Result<usize>;

    /// Returns the remaining size of the downloaded data
    fn remaining(&self) -> usize;
}

/// `UploadBuilder` provides API for initiating a fastboot upload.
pub trait UploadBuilder {
    /// Starts the upload.
    ///
    /// In a real fastboot context, the method should send `DATA0xXXXXXXXX` to the remote host to
    /// start the upload. An `Uploader` implementation should be returned for uploading payload.
    async fn initiate_upload(self, data_size: u32) -> Result<impl Uploader>;
}

/// `UploadBuilder` provides API for uploading payload.
pub trait Uploader {
    /// Uploads data to the Fastboot host.
    async fn upload(&mut self, data: &[u8]) -> Result<()>;
}

// Represents download state.
#[derive(Copy, Clone)]
enum DownloadState {
    // Download is not started. Value represents total size
    NotStarted(usize),
    // Download is in progress. Value represents remaining size.
    InProgress(usize),
    Completed,
}

/// `Responder` implements APIs for fastboot backend to send fastboot messages and uploading data.
struct Responder<'a, T: Transport> {
    result_message_sent: bool,
    buffer: [u8; MAX_RESPONSE_SIZE],
    transport: &'a mut T,
    transport_error: Result<()>,
    remaining_upload: u64,
    download_state: DownloadState,
}

impl<'a, T: Transport> Responder<'a, T> {
    fn new(transport: &'a mut T) -> Self {
        Self {
            result_message_sent: false,
            buffer: [0u8; MAX_RESPONSE_SIZE],
            transport,
            transport_error: Ok(()),
            remaining_upload: 0,
            download_state: DownloadState::Completed,
        }
    }

    /// A helper for sending a fastboot message in the buffer.
    async fn send_buffer(&mut self, size: usize) -> Result<()> {
        self.transport_error?;
        assert!(size < self.buffer.len());
        self.transport_error = self.transport.send_packet(&self.buffer[..size]).await;
        Ok(self.transport_error?)
    }

    /// Helper for sending a formatted fastboot message.
    ///
    /// # Args:
    ///
    /// * `cb`: A closure provided by the caller for constructing the formatted message.
    async fn send_formatted_msg<F: FnOnce(&mut dyn Write)>(
        &mut self,
        msg_type: &str,
        cb: F,
    ) -> Result<()> {
        let mut formatted_bytes = FormattedBytes::new(&mut self.buffer);
        write!(formatted_bytes, "{}", msg_type).unwrap();
        cb(&mut formatted_bytes);
        let size = formatted_bytes.size();
        self.send_buffer(size).await
    }

    /// Sends a fastboot DATA message.
    async fn send_data_message(&mut self, data_size: u32) -> Result<()> {
        self.send_formatted_msg("DATA", |v| write!(v, "{:08x}", data_size).unwrap()).await
    }
}

impl<'a, T: Transport> VarInfoSender for &mut Responder<'a, T> {
    async fn send_var_info(
        &mut self,
        name: &str,
        args: impl IntoIterator<Item = &'_ str>,
        val: &str,
    ) -> Result<()> {
        // Sends a "INFO<var>:<':'-separated args>:<val>" packet to the host.
        Ok(self
            .send_formatted_msg("INFO", |v| {
                write!(v, "{}", name).unwrap();
                args.into_iter().for_each(|arg| write!(v, ":{}", arg).unwrap());
                write!(v, ": {}", val).unwrap();
            })
            .await?)
    }
}

/// An internal convenient macro that sends a formatted fastboot OKAY message via a `Responder`
macro_rules! reply_okay {
    ( $resp:expr, $( $x:expr ),* $(,)?) => {
        {
            let len = fastboot_okay!($resp.buffer, $($x,)*).len();
            $resp.send_buffer(len).await
        }
    };
}

/// An internal convenient macro that sends a formatted fastboot FAIL message via a `Responder`
macro_rules! reply_fail {
    ( $resp:expr, $( $x:expr ),* $(,)?) => {
        {
            let len = fastboot_fail!($resp.buffer, $($x,)*).len();
            $resp.send_buffer(len).await
        }
    };
}

impl<T: Transport> InfoSender for &mut Responder<'_, T> {
    async fn send_formatted_info<F: FnOnce(&mut dyn Write)>(&mut self, cb: F) -> Result<()> {
        Ok(self.send_formatted_msg("INFO", cb).await?)
    }
}

impl<T: Transport> OkaySender for &mut Responder<'_, T> {
    async fn send_formatted_okay<F: FnOnce(&mut dyn Write)>(self, cb: F) -> Result<()> {
        self.result_message_sent = true;
        Ok(self.send_formatted_msg("OKAY", cb).await?)
    }
}

impl<T: Transport> FailSender for &mut Responder<'_, T> {
    async fn send_formatted_fail<F: FnOnce(&mut dyn Write)>(self, cb: F) -> Result<()> {
        self.result_message_sent = true;
        Ok(self.send_formatted_msg("FAIL", cb).await?)
    }
}

impl<'a, T: Transport> DownloadBuilder for &mut Responder<'a, T> {
    async fn initiate_download(self) -> Result<impl Downloader> {
        self.send_data_message(self.total().try_into()?).await?;
        self.download_state = DownloadState::InProgress(self.total());
        Ok(self)
    }

    fn total(&self) -> usize {
        match self.download_state {
            DownloadState::NotStarted(v) => v,
            _ => unreachable!(),
        }
    }
}

impl<'a, T: Transport> Downloader for &mut Responder<'a, T> {
    async fn download(&mut self, out: &mut [u8]) -> Result<usize> {
        self.transport_error?;
        let to_recv = min(self.remaining(), out.len());
        if to_recv == 0 {
            return Ok(0);
        }
        match self.transport.receive(&mut out[..to_recv]).await {
            Ok((v, rem)) => {
                self.download_state = DownloadState::InProgress(
                    v.try_into()
                        .ok()
                        .and_then(|v| self.remaining().checked_sub(v))
                        .ok_or(Error::Other(Some("Invalid receive size")))?,
                );
                if self.remaining() == 0 {
                    if rem > 0 {
                        self.transport_error =
                            Err(Error::Other(Some("Received more data than expected")));
                        return self.transport_error.map(|_| v);
                    }
                    self.download_state = DownloadState::Completed;
                }
                Ok(v)
            }
            Err(e) => {
                self.transport_error = Err(e);
                Err(e)
            }
        }
    }

    fn remaining(&self) -> usize {
        match self.download_state {
            DownloadState::InProgress(v) => v,
            DownloadState::Completed => 0,
            _ => unreachable!(),
        }
    }
}

impl<'a, T: Transport> UploadBuilder for &mut Responder<'a, T> {
    async fn initiate_upload(self, data_size: u32) -> Result<impl Uploader> {
        self.send_data_message(data_size).await?;
        self.remaining_upload = data_size.into();
        Ok(self)
    }
}

impl<'a, T: Transport> Uploader for &mut Responder<'a, T> {
    /// Uploads data. Returns error if accumulative amount exceeds `data_size` passed to
    /// `UploadBuilder::start()`.
    async fn upload(&mut self, data: &[u8]) -> Result<()> {
        self.transport_error?;
        if data.is_empty() {
            return Ok(());
        }
        self.remaining_upload = self
            .remaining_upload
            .checked_sub(data.len().try_into().map_err(|_| "")?)
            .ok_or(Error::Other(Some("Invalid size of upload data")))?;
        self.transport_error = self.transport.send_packet(data).await;
        Ok(())
    }
}

pub mod test_utils {
    //! Test utilities to help users of this library write unit tests.

    use crate::{InfoSender, UploadBuilder, Uploader};
    use core::fmt::Write;
    use liberror::Error;

    /// A test implementation of `UploadBuilder` for unittesting
    /// `FastbootImplementation::upload()`.
    ///
    /// The test uploader simply uploads to a user provided buffer.
    pub struct TestUploadBuilder<'a>(pub &'a mut [u8]);

    impl<'a> UploadBuilder for TestUploadBuilder<'a> {
        async fn initiate_upload(self, _: u32) -> Result<impl Uploader, Error> {
            Ok(TestUploader(0, self.0))
        }
    }

    impl<'a> InfoSender for TestUploadBuilder<'a> {
        async fn send_formatted_info<F: FnOnce(&mut dyn Write)>(
            &mut self,
            _: F,
        ) -> Result<(), Error> {
            // Not needed currently.
            Ok(())
        }
    }

    // (Bytes sent, upload buffer)
    struct TestUploader<'a>(usize, &'a mut [u8]);

    impl Uploader for TestUploader<'_> {
        async fn upload(&mut self, data: &[u8]) -> Result<(), Error> {
            self.1[self.0..][..data.len()].copy_from_slice(data);
            self.0 = self.0.checked_add(data.len()).unwrap();
            Ok(())
        }
    }
}

/// Converts a null-terminated command line string where arguments are separated by ':' into an
/// iterator of individual argument as CStr.
///
/// Returns the iterator and the string length.
fn cmd_to_c_string_args(cmd: &mut [u8]) -> (impl Iterator<Item = &CStr> + Clone, usize) {
    let end = cmd.iter().position(|v| *v == 0).unwrap();
    // Replace ':' with NULL.
    cmd.iter_mut().filter(|v| **v == b':').for_each(|v| *v = 0);
    (
        cmd[..end + 1].split_inclusive(|v| *v == 0).map(|v| CStr::from_bytes_until_nul(v).unwrap()),
        end,
    )
}

/// Helper for handling "fastboot getvar ..."
async fn get_var(
    cmd: &mut [u8],
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    let mut resp = Responder::new(transport);
    let mut args = cmd_to_c_string_args(cmd).0.skip(1);
    let Some(var) = args.next() else {
        return reply_fail!(resp, "Missing variable");
    };

    match var.to_str()? {
        "all" => return get_var_all(transport, fb_impl).await,
        _ => {
            let mut val = [0u8; MAX_RESPONSE_SIZE];
            match fb_impl.get_var_as_str(var, args, &mut resp, &mut val[..]).await {
                Ok(s) => reply_okay!(resp, "{}", s),
                Err(e) => reply_fail!(resp, "{}", e.as_str()),
            }
        }
    }
}

/// Method for handling "fastboot getvar all"
async fn get_var_all(
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    let mut resp = Responder::new(transport);
    // Don't allow custom INFO messages because variable values are sent as INFO messages.
    let get_res = fb_impl.get_var_all(&mut resp).await;
    match get_res {
        Ok(()) => reply_okay!(resp, ""),
        Err(e) => reply_fail!(resp, "{}", e.as_str()),
    }
}

/// Helper for handling "fastboot download:...".
async fn download(
    mut args: Split<'_, char>,
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    let mut resp = Responder::new(transport);
    let total_download_size = match (|| -> CommandResult<usize> {
        Ok(usize::try_from_hex_str(args.next().ok_or("Not enough arguments")?)?)
    })() {
        Err(e) => return reply_fail!(resp, "{}", e.as_str()),
        Ok(v) => {
            // Can't compare directly against u32::MAX because that's a u32, and
            // usize does not impl From<u32>
            if v > 0xFFFFFFFF {
                return reply_fail!(resp, "Download size overflows u32 (can't fit DATA message)");
            } else {
                v
            }
        }
    };
    if total_download_size == 0 {
        return reply_fail!(resp, "Zero download size");
    }

    let mut resp = Responder::new(transport);
    resp.download_state = DownloadState::NotStarted(total_download_size);
    let res = fb_impl.download(&mut resp).await;
    resp.transport_error?;
    if let DownloadState::InProgress(v) = resp.download_state {
        fb_impl.log_line(format_args!(
            "Caller did not read all download. {}/{} bytes",
            total_download_size - v,
            total_download_size
        ));
        return Err(Error::InvalidState);
    }
    match res {
        Err(e) => reply_fail!(resp, "{}", e.as_str()),
        _ => reply_okay!(resp, ""),
    }
}

/// Helper for handling "fastboot flash ...".
async fn flash(
    cmd: &str,
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    let mut resp = Responder::new(transport);
    let flash_res =
        match cmd.strip_prefix("flash:").ok_or::<CommandError>("Missing partition".into()) {
            Ok(part) => fb_impl.flash(part, &mut resp).await,
            Err(e) => Err(e),
        };
    match flash_res {
        Err(e) => reply_fail!(resp, "{}", e.as_str()),
        _ => reply_okay!(resp, ""),
    }
}

/// Helper for handling "fastboot:stream-flash:..." and "fastboot:stream-fill:...".
async fn handle_stream_command<'a>(
    cmd: &'a str,
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    let mut resp = Responder::new(transport);
    let stream_res = match StreamCommand::try_from(cmd) {
        Ok(cmd) => fb_impl.stream(cmd, &mut resp).await,
        Err(e) => Err(e.into()),
    };

    if let Err(e) = stream_res {
        reply_fail!(resp, "{}", e.as_str())
    } else {
        reply_okay!(resp, "")
    }
}

/// Helper for handling "fastboot erase ...".
async fn erase(
    cmd: &str,
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    let mut resp = Responder::new(transport);
    let flash_res =
        match cmd.strip_prefix("erase:").ok_or::<CommandError>("Missing partition".into()) {
            Ok(part) => fb_impl.erase(part, &mut resp).await,
            Err(e) => Err(e),
        };
    match flash_res {
        Err(e) => reply_fail!(resp, "{}", e.as_str()),
        _ => reply_okay!(resp, ""),
    }
}

/// Helper for handling "fastboot get_staged ...".
async fn upload(
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    let mut resp = Responder::new(transport);
    let upload_res = fb_impl.upload(&mut resp).await;
    match resp.remaining_upload > 0 {
        true => return Err(Error::InvalidInput),
        _ => match upload_res {
            Err(e) => reply_fail!(resp, "{}", e.as_str()),
            _ => reply_okay!(resp, ""),
        },
    }
}

/// Helper for handling "fastboot fetch ...".
async fn fetch(
    cmd: &str,
    args: Split<'_, char>,
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    let mut resp = Responder::new(transport);
    let fetch_res = async {
        let cmd = cmd.strip_prefix("fetch:").ok_or::<CommandError>("Missing arguments".into())?;
        if args.clone().count() < 3 {
            return Err("Not enough arguments".into());
        }
        // Parses backward. Parses size, offset first and treats the remaining string as
        // partition name. This allows ":" in partition name.
        let mut rev = args.clone().rev();
        let sz_arg = next_arg(&mut rev).ok_or("Missing size")?;
        let off = next_arg(&mut rev).ok_or("Missing offset")?;
        let part = &cmd[..cmd.len() - (off.len() + sz_arg.len() + 2)];
        fb_impl
            .fetch(
                part,
                FromHexStr::try_from_hex_str(off).map_err(|_| "Invalid offset")?,
                FromHexStr::try_from_hex_str(sz_arg).map_err(|_| "Invalid size")?,
                &mut resp,
            )
            .await
    }
    .await;
    match resp.remaining_upload > 0 {
        true => return Err(Error::InvalidInput),
        _ => match fetch_res {
            Err(e) => reply_fail!(resp, "{}", e.as_str()),
            _ => reply_okay!(resp, ""),
        },
    }
}

// Handles `fastboot reboot*`
async fn reboot(
    mode: RebootMode,
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<!> {
    let mut resp = Responder::new(transport);
    let Err(e) = fb_impl.reboot(mode, &mut resp).await;
    reply_fail!(resp, "{}", e.as_str())?;
    Err(Error::Aborted)
}

// Handles `fastboot boot`
async fn boot(
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<bool> {
    let mut resp = Responder::new(transport);
    let boot_res = async { fb_impl.boot(&mut resp).await }.await;
    match boot_res {
        Err(ref e) => reply_fail!(resp, "{}", e.as_str()),
        _ => reply_okay!(resp, ""),
    }?;
    Ok(boot_res.is_ok())
}

// Handles `fastboot continue`
async fn r#continue(
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    let mut resp = Responder::new(transport);
    match fb_impl.r#continue(&mut resp).await {
        Ok(_) => reply_okay!(resp, ""),
        Err(e) => reply_fail!(resp, "{}", e.as_str()),
    }
}

// Handles `fastboot set_active`
async fn set_active(
    mut args: Split<'_, char>,
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    let mut resp = Responder::new(transport);
    let res = async {
        let slot = next_arg(&mut args).ok_or("Missing slot")?;
        fb_impl.set_active(slot, &mut resp).await
    };
    match res.await {
        Ok(_) => reply_okay!(resp, ""),
        Err(e) => reply_fail!(resp, "{}", e.as_str()),
    }
}

/// Helper for handling "fastboot oem ...".
async fn oem(
    cmd: &str,
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    let mut resp = Responder::new(transport);
    let oem_res = fb_impl.oem(cmd, &mut resp).await;
    match oem_res {
        _ if resp.result_message_sent => Ok(()), // Assumes backend has handled the error.
        Ok(()) => reply_okay!(resp, ""),
        Err(e) => reply_fail!(resp, "{}", e.as_str()),
    }
}

/// Helper for handling command execute
///
/// # Returns
/// * Ok(CommandExecType) with value requested by fastboot implementation
/// * Err() on error
async fn command_exec(
    args: impl Iterator<Item = &'_ CStr> + Clone,
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<CommandExecType> {
    if is_protected_command(args.clone()) {
        return Ok(CommandExecType::DefaultImpl);
    }

    let mut resp = Responder::new(transport);
    let cmd_res = fb_impl.command_exec(args, &mut resp).await;
    if resp.result_message_sent {
        match cmd_res {
            Ok(CommandExecType::DefaultImpl) => fb_impl.log_line(
                "ERROR: Incorrect `DefaultImpl` usage. Custom result message is not allowed.",
            ),
            Ok(CommandExecType::CustomImpl) => (),
            Ok(CommandExecType::Prohibited) => fb_impl.log_line(
                "ERROR: Incorrect `Prohibited` usage. Custom result message is not allowed.",
            ),
            Err(_) => fb_impl.log_line("ERROR: Result message sent but `command_exec()` failed"),
        }
        Err(Error::Other(None))
    } else {
        match cmd_res {
            Ok(CommandExecType::DefaultImpl) => (),
            Ok(CommandExecType::CustomImpl) => {
                reply_okay!(resp, "")?;
            }
            Ok(CommandExecType::Prohibited) => {
                reply_fail!(resp, "Command not allowed.")?;
            }
            Err(ref e) => {
                reply_fail!(resp, "{}", e.as_str())?;
            }
        }
        cmd_res.map_err(|_| Error::Other(None))
    }
}

async fn lock_helper<T: Transport>(
    fb_impl: &mut impl FastbootImplementation,
    lock_type: LockType,
    lock_state: LockState,
    resp: &mut Responder<'_, T>,
) -> CommandResult<&'static str> {
    fb_impl.flashing_write_lock_state(lock_type, lock_state, &mut *resp).await.map(|_| "")
}

/// Handler for "fastboot flashing ..."
async fn flashing(
    cmd: &str,
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    let mut resp = Responder::new(transport);
    let res = match cmd {
        "lock" => lock_helper(fb_impl, LockType::Device, LockState::Locked, &mut resp).await,
        "unlock" => lock_helper(fb_impl, LockType::Device, LockState::Unlocked, &mut resp).await,
        "lock_critical" => {
            lock_helper(fb_impl, LockType::Critical, LockState::Locked, &mut resp).await
        }
        "unlock_critical" => {
            lock_helper(fb_impl, LockType::Critical, LockState::Unlocked, &mut resp).await
        }
        "get_unlock_ability" => fb_impl.flashing_get_unlock_ability().await.map(|u| match u {
            Unlockability::Allowed => "1",
            Unlockability::Prohibited => "0",
        }),
        "" => Err("missing argument".into()),
        _ => Err("Invalid flashing arg".into()),
    };
    match res {
        Ok(s) => reply_okay!(resp, "{}", s),
        Err(e) => reply_fail!(resp, "{}", e.as_str()),
    }
}

/// The parsed representation of a stream flash or fill subcommand
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum StreamOperation {
    /// A flash operation
    Flash {
        /// Checksum for the downloaded data
        checksum: u32,
    },
    /// A fill operation
    Fill {
        /// Size in bytes of the fill
        size: u64,
        /// The fill payload
        payload: u32,
    },
}

/// The total parsed representation of a streaming flash or fill.
#[derive(Copy, Clone, Debug, Eq)]
pub struct StreamCommand<P: AsRef<str>> {
    /// The name of the partition to write to
    pub partition: P,
    /// The offset from the start of the partition
    pub offset: u64,
    /// The write operation, fill or flash
    pub operation: StreamOperation,
}

impl<A: AsRef<str>, B: AsRef<str>> PartialEq<StreamCommand<B>> for StreamCommand<A> {
    fn eq(&self, other: &StreamCommand<B>) -> bool {
        self.partition.as_ref() == other.partition.as_ref()
            && self.offset == other.offset
            && self.operation == other.operation
    }
}

impl<'a, P: From<&'a str> + AsRef<str>> TryFrom<&'a str> for StreamCommand<P> {
    type Error = Error;

    // Expects a string of the form
    //
    // "stream-flash:<partition name>:<partition offset>:<checksum>"
    //
    // or
    //
    // "stream-fill:<partition name>:<partition offset>:<size bytes>:<payload>"
    fn try_from(cmd_str: &'a str) -> Result<Self> {
        let args = &mut cmd_str.split(':');
        let command = next_arg(args).ok_or(Error::InvalidInput)?;
        let partition = next_arg(args).ok_or(Error::InvalidInput)?.into();
        let offset = FromHexStr::try_parse_next(args)?;
        let command = match command {
            "stream-flash" => Self {
                partition,
                offset,
                operation: StreamOperation::Flash { checksum: FromHexStr::try_parse_next(args)? },
            },
            "stream-fill" => Self {
                partition,
                offset,
                operation: StreamOperation::Fill {
                    // Attempting to write a partial fill value is an error.
                    size: FromHexStr::try_parse_next(args).and_then(|s| {
                        if s % (size_of::<u32>() as u64) == 0 {
                            Ok(s)
                        } else {
                            Err(Error::InvalidInput)
                        }
                    })?,
                    payload: FromHexStr::try_parse_next(args)?,
                },
            },
            _ => Err(Error::InvalidInput)?,
        };

        if args.next().is_none() {
            Ok(command)
        } else {
            Err(Error::InvalidInput)
        }
    }
}

/// Process the next Fastboot command from  the transport.
///
/// # Returns
///
/// * Returns Ok(is_continue) on success where `is_continue` is true if command is
///   `fastboot continue`.
/// * Returns Err() on errors.
pub async fn process_next_command(
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<bool> {
    let mut packet = [0u8; MAX_COMMAND_SIZE + 1];
    let cmd_size = match transport.receive_packet(&mut packet[..MAX_COMMAND_SIZE]).await? {
        0 => return Ok(false),
        v => v,
    };
    // Checks utf8 encoding first. This is required by `cmd_to_c_string_args`.
    match from_utf8(&packet[..cmd_size]) {
        Ok(v) => fb_impl.log_line(format_args!("Fastboot Command: {v}")),
        _ => {
            transport.send_packet(fastboot_fail!(packet, "Invalid Command")).await?;
            return Ok(false);
        }
    }
    let (cmd_c_args, cmd_len) = cmd_to_c_string_args(&mut packet[..]);
    match command_exec(cmd_c_args, transport, fb_impl).await {
        Ok(CommandExecType::DefaultImpl) => (),
        Ok(CommandExecType::CustomImpl) | Ok(CommandExecType::Prohibited) | Err(_) => {
            return Ok(false);
        }
    }
    packet[..cmd_len].iter_mut().filter(|v| **v == 0).for_each(|v| *v = b':');
    let cmd_str = from_utf8(&packet[..cmd_size]).unwrap();
    let mut args = cmd_str.split(':');
    let Some(cmd) = args.next() else {
        let mut fail_packet = [0u8; 24];
        return transport
            .send_packet(fastboot_fail!(fail_packet, "No command"))
            .await
            .map(|_| false);
    };
    match cmd {
        "boot" => return boot(transport, fb_impl).await.map(|v| v),
        "continue" => {
            r#continue(transport, fb_impl).await?;
            return Ok(true);
        }
        "download" => download(args, transport, fb_impl).await,
        "erase" => erase(cmd_str, transport, fb_impl).await,
        "fetch" => fetch(cmd_str, args, transport, fb_impl).await,
        "flash" => flash(cmd_str, transport, fb_impl).await,
        "stream-flash" | "stream-fill" => handle_stream_command(cmd_str, transport, fb_impl).await,
        "getvar" => get_var(&mut packet[..], transport, fb_impl).await,
        "reboot" => reboot(RebootMode::Normal, transport, fb_impl).await?,
        "reboot-bootloader" => reboot(RebootMode::Bootloader, transport, fb_impl).await?,
        "reboot-fastboot" => reboot(RebootMode::Fastboot, transport, fb_impl).await?,
        "reboot-recovery" => reboot(RebootMode::Recovery, transport, fb_impl).await?,
        "set_active" => set_active(args, transport, fb_impl).await,
        "upload" => upload(transport, fb_impl).await,
        _ if cmd_str.starts_with("flashing ") => {
            flashing(cmd_str.strip_prefix("flashing ").unwrap(), transport, fb_impl).await
        }
        _ if cmd_str.starts_with("oem ") => oem(&cmd_str[4..], transport, fb_impl).await,
        _ => transport.send_packet(fastboot_fail!(packet, "Command not found")).await,
    }?;
    Ok(false)
}

/// Keeps polling and processing fastboot commands from the transport.
///
/// # Returns
///
/// * Returns Ok(()) if "fastboot continue" is received.
/// * Returns Err() on errors.
pub async fn run(
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    while !process_next_command(transport, fb_impl).await? {}
    Ok(())
}

/// Runs a fastboot over TCP session.
///
/// The method performs fastboot over TCP handshake and then call `run(...)`.
///
/// Returns Ok(()) if "fastboot continue" is received.
pub async fn run_tcp_session(
    tcp_stream: &mut impl TcpStream,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    run(&mut TcpTransport::new_and_handshake(tcp_stream)?, fb_impl).await
}

#[cfg(test)]
mod test {
    use super::*;
    use std::{
        collections::{BTreeMap, VecDeque},
        io::Read,
    };

    enum OemResponse {
        Okay(String),
        Fail(String),
    }

    impl From<StreamCommand<&'_ str>> for StreamCommand<String> {
        fn from(value: StreamCommand<&'_ str>) -> Self {
            Self {
                partition: value.partition.into(),
                offset: value.offset,
                operation: value.operation,
            }
        }
    }

    #[derive(Default)]
    struct FastbootTest<'a> {
        // A mapping from (variable name, argument) to variable value.
        vars: BTreeMap<(&'static str, &'static [&'static str]), &'static str>,
        // The partition arg from Fastboot flash command
        flash_partition: String,
        // The partition arg from Fastboot erase command
        erase_partition: String,
        // The command from a Fastboot stream-flash or stream-fill
        stream_command: Option<StreamCommand<String>>,
        // Upload size, batches of data to upload,
        upload_config: (u32, Vec<Vec<u8>>),
        // A map from partition name to (upload size override, partition data)
        fetch_data: BTreeMap<&'static str, (u32, Vec<u8>)>,
        // OKAY/FAIL messages, INFO messages, result.
        oem_output: (Option<OemResponse>, Vec<String>, Option<CommandResult<()>>),
        oem_command: String,
        reboot_mode: Option<RebootMode>,
        active_slot: Option<String>,
        boot_result: Option<CommandResult<()>>,
        unlockability: Option<Unlockability>,
        last_write_lock_state_call: Option<(LockType, LockState)>,
        command_exec_args: String,
        command_exec_res: Option<CommandResult<CommandExecType>>,
        log_lines: Vec<String>,
        predownload_handler: Option<&'a mut dyn FnMut(&mut dyn TestInfoSender) -> Result<()>>,
        download_handler: Option<&'a mut dyn FnMut(&mut dyn TestDownloader, usize) -> Result<()>>,
    }

    /// Synced version of InfoSender that is object-safe.
    trait TestInfoSender {
        fn send_info(&mut self, msg: &dyn Display) -> Result<()>;
    }

    impl<T: InfoSender> TestInfoSender for T {
        fn send_info(&mut self, msg: &dyn Display) -> Result<()> {
            block_on(self.send_formatted_info(|v| write!(v, "{msg}").unwrap()))
        }
    }

    /// Synced version of Downloader that is object-safe.
    trait TestDownloader {
        fn download(&mut self, out: &mut [u8]) -> Result<usize>;

        fn download_all(&mut self, out: &mut [u8]) -> Result<()>;
    }

    impl<T: Downloader> TestDownloader for T {
        fn download(&mut self, out: &mut [u8]) -> Result<usize> {
            block_on(Downloader::download(self, out))
        }

        fn download_all(&mut self, out: &mut [u8]) -> Result<()> {
            let mut curr = out
                .get_mut(..self.remaining())
                .ok_or(Error::BufferTooSmall(Some(self.remaining())))?;
            while !curr.is_empty() {
                let sz = block_on(Downloader::download(self, curr))?;
                curr = &mut curr[sz..];
            }
            Ok(())
        }
    }

    impl<'a> FastbootImplementation for FastbootTest<'a> {
        async fn get_var(
            &mut self,
            var: &CStr,
            args: impl Iterator<Item = &'_ CStr> + Clone,
            out: &mut [u8],
            _: impl InfoSender,
        ) -> CommandResult<usize> {
            let args = args.map(|v| v.to_str().unwrap()).collect::<Vec<_>>();
            match self.vars.get(&(var.to_str()?, &args[..])) {
                Some(v) => {
                    out[..v.len()].copy_from_slice(v.as_bytes());
                    Ok(v.len())
                }
                _ => Err("Not Found".into()),
            }
        }

        async fn get_var_all(&mut self, mut responder: impl VarInfoSender) -> CommandResult<()> {
            for ((var, config), value) in &self.vars {
                responder.send_var_info(var, config.iter().copied(), value).await?;
            }
            Ok(())
        }

        async fn flash(&mut self, part: &str, _: impl InfoSender) -> CommandResult<()> {
            self.flash_partition = part.into();
            Ok(())
        }

        async fn erase(&mut self, part: &str, _: impl InfoSender) -> CommandResult<()> {
            self.erase_partition = part.into();
            Ok(())
        }

        async fn download(
            &mut self,
            mut responder: impl DownloadBuilder + InfoSender,
        ) -> CommandResult<()> {
            self.predownload_handler.as_mut().map(|f| f(&mut responder)).transpose()?;
            let total = responder.total();
            let mut downloader = responder.initiate_download().await?;
            self.download_handler.as_mut().map(|f| f(&mut downloader, total)).transpose()?;
            Ok(())
        }

        async fn upload(&mut self, responder: impl UploadBuilder) -> CommandResult<()> {
            let (size, batches) = &self.upload_config;
            let mut uploader = responder.initiate_upload(*size).await?;
            for ele in batches {
                uploader.upload(&ele[..]).await?;
            }
            Ok(())
        }

        async fn fetch(
            &mut self,
            part: &str,
            offset: u64,
            size: u32,
            responder: impl UploadBuilder + InfoSender,
        ) -> CommandResult<()> {
            let (size_override, data) = self.fetch_data.get(part).ok_or("Not Found")?;
            let mut uploader = responder.initiate_upload(*size_override).await?;
            Ok(uploader
                .upload(&data[offset.try_into().unwrap()..][..size.try_into().unwrap()])
                .await?)
        }

        async fn boot(&mut self, _: impl InfoSender + OkaySender) -> CommandResult<()> {
            self.boot_result.take().unwrap_or(Ok(()))
        }

        async fn reboot(
            &mut self,
            mode: RebootMode,
            responder: impl InfoSender + OkaySender,
        ) -> CommandResult<!> {
            responder.send_okay("").await.unwrap();
            self.reboot_mode = Some(mode);
            Err("reboot-return".into())
        }

        async fn r#continue(&mut self, mut responder: impl InfoSender) -> CommandResult<()> {
            Ok(responder.send_info("Continuing to boot...").await?)
        }

        async fn set_active(&mut self, slot: &str, _: impl InfoSender) -> CommandResult<()> {
            self.active_slot = Some(slot.into());
            Ok(())
        }

        async fn oem(
            &mut self,
            cmd: &str,
            mut responder: impl InfoSender + OkaySender + FailSender,
        ) -> CommandResult<()> {
            let (resp, infos, res) = &mut self.oem_output;
            self.oem_command = cmd.into();
            for ele in infos {
                responder.send_info(ele.as_ref()).await?;
            }
            match resp {
                Some(OemResponse::Okay(v)) => responder.send_okay(v as _).await.unwrap(),
                Some(OemResponse::Fail(v)) => responder.send_fail(v as _).await.unwrap(),
                _ => {}
            }
            res.take().unwrap_or(Ok(()))
        }

        async fn stream<'b>(
            &mut self,
            command: StreamCommand<&'b str>,
            _responder: impl InfoSender,
        ) -> CommandResult<()> {
            self.stream_command = Some(command.into());
            Ok(())
        }

        async fn flashing_write_lock_state(
            &mut self,
            lock_type: LockType,
            lock_state: LockState,
            _responder: impl InfoSender,
        ) -> CommandResult<()> {
            self.last_write_lock_state_call = Some((lock_type, lock_state));
            Ok(())
        }

        async fn flashing_get_unlock_ability(&mut self) -> CommandResult<Unlockability> {
            self.unlockability.ok_or("Cannot get unlockability".into())
        }

        async fn command_exec(
            &mut self,
            args: impl Iterator<Item = &'_ CStr> + Clone,
            _responder: impl InfoSender + OkaySender + FailSender,
        ) -> CommandResult<CommandExecType> {
            self.command_exec_args =
                args.map(|v| String::from(v.to_str().unwrap())).collect::<Vec<_>>().join(":");
            self.command_exec_res.take().unwrap_or(Ok(Default::default()))
        }

        fn log_line(&mut self, message: impl Display) {
            println!("{message}");
            self.log_lines.push(message.to_string());
        }
    }

    struct TestTransport {
        in_queue: VecDeque<VecDeque<u8>>,
        out_queue: VecDeque<Vec<u8>>,
    }

    impl TestTransport {
        fn new() -> Self {
            Self { in_queue: VecDeque::new(), out_queue: VecDeque::new() }
        }

        fn add_input(&mut self, packet: &[u8]) {
            self.in_queue.push_back(packet.to_vec().into());
        }
    }

    impl Transport for TestTransport {
        async fn receive(&mut self, out: &mut [u8]) -> Result<(usize, usize)> {
            match self.in_queue.front_mut() {
                Some(v) => {
                    let (sz, rem) = v.read(out).map(|s| (s, v.len())).unwrap();
                    (rem == 0).then(|| self.in_queue.pop_front());
                    Ok((sz, rem))
                }
                _ => Err(Error::Other(Some("No more data"))),
            }
        }

        async fn send_packet(&mut self, packet: &[u8]) -> Result<()> {
            self.out_queue.push_back(packet.into());
            Ok(())
        }
    }

    #[derive(Default)]
    struct TestTcpStream {
        in_queue: VecDeque<u8>,
        out_queue: VecDeque<u8>,
    }

    impl TestTcpStream {
        /// Adds bytes to input stream.
        fn add_input(&mut self, data: &[u8]) {
            data.iter().for_each(|v| self.in_queue.push_back(*v));
        }

        /// Adds a length pre-fixed bytes stream.
        fn add_length_prefixed_input(&mut self, data: &[u8]) {
            self.add_input(&(data.len() as u64).to_be_bytes());
            self.add_input(data);
        }
    }

    impl TcpStream for TestTcpStream {
        async fn read(&mut self, out: &mut [u8]) -> Result<usize> {
            match self.in_queue.read(out).unwrap() {
                0 => Err(Error::OperationProhibited),
                v => Ok(v),
            }
        }

        async fn write_exact(&mut self, data: &[u8]) -> Result<()> {
            data.iter().for_each(|v| self.out_queue.push_back(*v));
            Ok(())
        }
    }

    #[test]
    fn test_boot() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"boot");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(transport.out_queue, VecDeque::<Vec<u8>>::from([b"OKAY".into()]));
    }

    #[test]
    fn test_boot_not_exit_if_failed() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.boot_result = Some(Err("Test".into()));
        fastboot_impl.vars = BTreeMap::from([(("max-download-size", &[][..]), "0x400")]);
        let mut transport = TestTransport::new();
        transport.add_input(b"boot");
        transport.add_input(b"getvar:max-download-size");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([b"FAILTest".into(), b"OKAY0x400".into(),])
        );
    }

    #[test]
    fn test_non_exist_command() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"non_exist");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(transport.out_queue, [b"FAILCommand not found"]);
    }

    #[test]
    fn test_non_ascii_command_string() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"\xff\xff\xff");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(transport.out_queue, [b"FAILInvalid Command"]);
    }

    #[test]
    fn test_get_var() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let vars: [((&str, &[&str]), &str); 4] = [
            (("var_0", &[]), "val_0"),
            (("var_1", &["a", "b"]), "val_1_a_b"),
            (("var_1", &["c", "d"]), "val_1_c_d"),
            (("var_2", &["e", "f"]), "val_2_e_f"),
        ];
        fastboot_impl.vars = BTreeMap::from(vars);

        let mut transport = TestTransport::new();
        transport.add_input(b"getvar:var_0");
        transport.add_input(b"getvar:var_1:a:b");
        transport.add_input(b"getvar:var_1:c:d");
        transport.add_input(b"getvar:var_1"); // Not Found
        transport.add_input(b"getvar:var_2:e:f");
        transport.add_input(b"getvar:var_3"); // Not Found
        transport.add_input(b"getvar"); // Not Found

        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([
                b"OKAYval_0".into(),
                b"OKAYval_1_a_b".into(),
                b"OKAYval_1_c_d".into(),
                b"FAILNot Found".into(),
                b"OKAYval_2_e_f".into(),
                b"FAILNot Found".into(),
                b"FAILMissing variable".into(),
            ])
        );
    }

    #[test]
    fn test_get_var_all() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let vars: [((&str, &[&str]), &str); 4] = [
            (("var_0", &[]), "val_0"),
            (("var_1", &["a", "b"]), "val_1_a_b"),
            (("var_1", &["c", "d"]), "val_1_c_d"),
            (("var_2", &["e", "f"]), "val_2_e_f"),
        ];
        fastboot_impl.vars = BTreeMap::from(vars);

        let mut transport = TestTransport::new();
        transport.add_input(b"getvar:all");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([
                b"INFOvar_0: val_0".into(),
                b"INFOvar_1:a:b: val_1_a_b".into(),
                b"INFOvar_1:c:d: val_1_c_d".into(),
                b"INFOvar_2:e:f: val_2_e_f".into(),
                b"OKAY".into(),
            ])
        );
    }

    /// Generates a readable string for a fastboot packet
    pub(crate) fn dump_transport(queue: &VecDeque<Vec<u8>>) -> String {
        use std::ascii::escape_default;
        let mut res = "".into();
        for v in queue {
            let s = v.iter().map(|v| escape_default(*v).to_string()).collect::<Vec<_>>().concat();
            res += format!("b{:?},\n", s).as_ref();
        }
        res
    }

    #[test]
    fn test_download() {
        let download_content: Vec<u8> = (0..1024).into_iter().map(|v| v as u8).collect();
        let mut transport = TestTransport::new();
        // Splits download into two batches.
        let (first, second) = download_content.as_slice().split_at(download_content.len() / 2);
        transport.add_input(format!("download:{:#x}", download_content.len()).as_bytes());
        transport.add_input(first);
        transport.add_input(second);
        let mut predownload_handler =
            |info: &mut dyn TestInfoSender| info.send_info(&"Info before download");
        let mut out = vec![];
        let mut download_handler = |dl: &mut dyn TestDownloader, total: usize| {
            out.resize(total, 0);
            // Download 1 byte twice and then all remaining.
            assert_eq!(dl.download(&mut out[..1]).unwrap(), 1);
            assert_eq!(dl.download(&mut out[1..2]).unwrap(), 1);
            dl.download_all(&mut out[2..]).unwrap();
            // Further calls are noop.
            assert_eq!(dl.download(&mut out[..]), Ok(0));
            assert_eq!(dl.download_all(&mut out[..]), Ok(()));
            Ok(())
        };
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_handler = Some(&mut download_handler);
        fastboot_impl.predownload_handler = Some(&mut predownload_handler);
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        let expected = VecDeque::<Vec<u8>>::from([
            b"INFOInfo before download".into(),
            b"DATA00000400".into(),
            b"OKAY".into(),
        ]);
        assert_eq!(
            transport.out_queue,
            expected,
            "expected:\n{}\nactual:\n{}",
            dump_transport(&expected),
            dump_transport(&transport.out_queue)
        );
        assert_eq!(out, download_content);
    }

    #[test]
    fn test_download_custom_failure_before_initiate() {
        let mut transport = TestTransport::new();
        transport.add_input(format!("download:{:#x}", 1024).as_bytes());
        let mut predownload_handler = |_: &mut dyn TestInfoSender| Err(Error::Aborted);
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.predownload_handler = Some(&mut predownload_handler);
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        let expected = VecDeque::<Vec<u8>>::from([b"FAILAborted".into()]);
        assert_eq!(
            transport.out_queue,
            expected,
            "expected:\n{}\nactual:\n{}",
            dump_transport(&expected),
            dump_transport(&transport.out_queue)
        );
    }

    #[test]
    fn test_download_not_enough_args() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"download");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(transport.out_queue, [b"FAILNot enough arguments"]);
    }

    #[test]
    fn test_download_invalid_hex_string() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"download:hhh");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(transport.out_queue.len(), 1);
        assert!(transport.out_queue[0].starts_with(b"FAIL"));
    }

    #[test]
    fn test_download_more_than_expected() {
        let mut download = vec![0u8; 2048];
        let mut download_handler =
            |dl: &mut dyn TestDownloader, _: usize| dl.download_all(&mut download);
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_handler = Some(&mut download_handler);
        let download_content: Vec<u8> = vec![0u8; 1024];
        let mut transport = TestTransport::new();
        transport.add_input(format!("download:{:#x}", download_content.len() - 1).as_bytes());
        transport.add_input(&download_content[..]);
        assert_eq!(
            block_on(run(&mut transport, &mut fastboot_impl)),
            Err(Error::Other(Some("Received more data than expected")))
        );
    }

    #[test]
    fn test_download_size_overflows_u32() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"download:100000000");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([
                b"FAILDownload size overflows u32 (can't fit DATA message)".into(),
            ])
        );
    }

    #[test]
    fn test_oem_cmd_oem_send_okay_info() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"oem oem-command");
        fastboot_impl.oem_output = (
            Some(OemResponse::Okay("oem-return".into())),
            vec!["oem-info-1".into(), "oem-info-2".into()],
            None,
        );
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(fastboot_impl.oem_command, "oem-command");
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([
                b"INFOoem-info-1".into(),
                b"INFOoem-info-2".into(),
                b"OKAYoem-return".into(),
            ])
        );
    }

    #[test]
    fn test_oem_cmd_send_default_okay_info() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"oem oem-command");
        fastboot_impl.oem_output = (None, vec!["oem-info-1".into(), "oem-info-2".into()], None);
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(fastboot_impl.oem_command, "oem-command");
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([
                b"INFOoem-info-1".into(),
                b"INFOoem-info-2".into(),
                b"OKAY".into(),
            ])
        );
    }

    #[test]
    fn test_oem_cmd_oem_send_fail_info() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"oem oem-command");
        fastboot_impl.oem_output = (
            Some(OemResponse::Fail("oem-return".into())),
            vec!["oem-info-1".into(), "oem-info-2".into()],
            None,
        );
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(fastboot_impl.oem_command, "oem-command");
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([
                b"INFOoem-info-1".into(),
                b"INFOoem-info-2".into(),
                b"FAILoem-return".into(),
            ])
        );
    }

    #[test]
    fn test_oem_cmd_oem_send_default_fail_info() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"oem oem-command");
        fastboot_impl.oem_output =
            (None, vec!["oem-info-1".into(), "oem-info-2".into()], Some(Err("error".into())));
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(fastboot_impl.oem_command, "oem-command");
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([
                b"INFOoem-info-1".into(),
                b"INFOoem-info-2".into(),
                b"FAILerror".into(),
            ])
        );
    }

    #[test]
    fn test_flash() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"flash:boot_a:0::");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(fastboot_impl.flash_partition, "boot_a:0::");
        assert_eq!(transport.out_queue, VecDeque::<Vec<u8>>::from([b"OKAY".into()]));
    }

    #[test]
    fn test_flash_missing_partition() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"flash");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(transport.out_queue, [b"FAILMissing partition"]);
    }

    #[test]
    fn test_erase() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"erase:boot_a:0::");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(fastboot_impl.erase_partition, "boot_a:0::");
        assert_eq!(transport.out_queue, VecDeque::<Vec<u8>>::from([b"OKAY".into()]));
    }

    #[test]
    fn test_erase_missing_partition() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"erase");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(transport.out_queue, [b"FAILMissing partition"]);
    }

    #[test]
    fn test_upload() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let upload_content: Vec<u8> = (0..1024).into_iter().map(|v| v as u8).collect();
        let mut transport = TestTransport::new();
        transport.add_input(b"upload");
        fastboot_impl.upload_config = (
            upload_content.len().try_into().unwrap(),
            vec![
                upload_content[..upload_content.len() / 2].to_vec(),
                upload_content[upload_content.len() / 2..].to_vec(),
            ],
        );
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([
                b"DATA00000400".into(),
                upload_content[..upload_content.len() / 2].to_vec(),
                upload_content[upload_content.len() / 2..].to_vec(),
                b"OKAY".into(),
            ])
        );
    }

    #[test]
    fn test_upload_not_enough_data() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"upload");
        fastboot_impl.upload_config = (0x400, vec![vec![0u8; 0x400 - 1]]);
        assert!(block_on(run(&mut transport, &mut fastboot_impl)).is_err());
    }

    #[test]
    fn test_upload_more_data() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"upload");
        fastboot_impl.upload_config = (0x400, vec![vec![0u8; 0x400 + 1]]);
        assert!(block_on(run(&mut transport, &mut fastboot_impl)).is_err());
    }

    #[test]
    fn test_fetch() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"fetch:boot_a:0:::200:400");
        fastboot_impl
            .fetch_data
            .insert("boot_a:0::", (0x400, vec![vec![0u8; 0x200], vec![1u8; 0x400]].concat()));
        block_on(process_next_command(&mut transport, &mut fastboot_impl)).unwrap();
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([
                b"DATA00000400".into(),
                [1u8; 0x400].to_vec(),
                b"OKAY".into(),
            ])
        );
    }

    #[test]
    fn test_fetch_not_enough_data() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"fetch:boot_a:0:::200:400");
        fastboot_impl
            .fetch_data
            .insert("boot_a:0::", (0x400 - 1, vec![vec![0u8; 0x200], vec![1u8; 0x400]].concat()));
        assert!(block_on(process_next_command(&mut transport, &mut fastboot_impl)).is_err());
    }

    #[test]
    fn test_fetch_more_data() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"fetch:boot_a:0:::200:400");
        fastboot_impl
            .fetch_data
            .insert("boot_a:0::", (0x400 + 1, vec![vec![0u8; 0x200], vec![1u8; 0x400]].concat()));
        assert!(block_on(process_next_command(&mut transport, &mut fastboot_impl)).is_err());
    }

    #[test]
    fn test_fetch_invalid_args() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"fetch");
        transport.add_input(b"fetch:");
        transport.add_input(b"fetch:boot_a");
        transport.add_input(b"fetch:boot_a:200");
        transport.add_input(b"fetch:boot_a::400");
        transport.add_input(b"fetch:boot_a::");
        transport.add_input(b"fetch:boot_a:xxx:400");
        transport.add_input(b"fetch:boot_a:200:xxx");
        transport.add_input(b"fetch:boot_a:0:100000000"); // u32 overflows
        let _ = block_on(run(&mut transport, &mut fastboot_impl));

        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([
                b"FAILMissing arguments".into(),
                b"FAILNot enough arguments".into(),
                b"FAILNot enough arguments".into(),
                b"FAILNot enough arguments".into(),
                b"FAILMissing offset".into(),
                b"FAILMissing size".into(),
                b"FAILInvalid offset".into(),
                b"FAILInvalid size".into(),
                b"FAILInvalid size".into(),
            ])
        );
    }

    #[test]
    fn test_fastboot_tcp() {
        let mut download = vec![];
        let mut download_handler = |dl: &mut dyn TestDownloader, total: usize| {
            download.resize(total, 0);
            dl.download_all(&mut download).unwrap();
            Ok(())
        };
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_handler = Some(&mut download_handler);
        fastboot_impl.vars = BTreeMap::from([(("max-download-size", &[][..]), "0x400")]);
        let download_content: Vec<u8> = (0..1024).into_iter().map(|v| v as u8).collect();
        let mut tcp_stream: TestTcpStream = Default::default();
        tcp_stream.add_input(TCP_HANDSHAKE_MESSAGE);
        // Add two commands and verify both are executed.
        tcp_stream.add_length_prefixed_input(b"getvar:max-download-size");
        tcp_stream.add_length_prefixed_input(
            format!("download:{:#x}", download_content.len()).as_bytes(),
        );
        tcp_stream.add_length_prefixed_input(&download_content[..]);
        let _ = block_on(run_tcp_session(&mut tcp_stream, &mut fastboot_impl));
        let expected: &[&[u8]] = &[
            b"FB01",
            b"\x00\x00\x00\x00\x00\x00\x00\x09OKAY0x400",
            b"\x00\x00\x00\x00\x00\x00\x00\x0cDATA00000400",
            b"\x00\x00\x00\x00\x00\x00\x00\x04OKAY",
        ];
        assert_eq!(tcp_stream.out_queue, VecDeque::from(expected.concat()));
        assert_eq!(download, download_content);
    }

    #[test]
    fn test_fastboot_tcp_invalid_handshake() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut tcp_stream: TestTcpStream = Default::default();
        tcp_stream.add_input(b"ABCD");
        assert_eq!(
            block_on(run_tcp_session(&mut tcp_stream, &mut fastboot_impl)).unwrap_err(),
            Error::InvalidHandshake
        );
    }

    #[test]
    fn test_fastboot_tcp_packet_size_exceeds_buffer() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut tcp_stream: TestTcpStream = Default::default();
        tcp_stream.add_input(TCP_HANDSHAKE_MESSAGE);
        tcp_stream.add_input(&(MAX_COMMAND_SIZE + 1).to_be_bytes());
        tcp_stream.add_input(&vec![0u8; MAX_COMMAND_SIZE + 1]);
        assert_eq!(
            block_on(run_tcp_session(&mut tcp_stream, &mut fastboot_impl)).unwrap_err(),
            Error::BufferTooSmall(Some(4097))
        );
    }

    #[test]
    fn test_reboot() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"reboot");
        let res = block_on(process_next_command(&mut transport, &mut fastboot_impl));
        assert_eq!(res, Err(Error::Aborted));
        assert_eq!(fastboot_impl.reboot_mode, Some(RebootMode::Normal));
        assert_eq!(transport.out_queue[0], b"OKAY");
        // Failure is expected here because test reboot implementation always returns, which
        // automatically generates a fastboot failure packet.
        assert!(transport.out_queue[1].starts_with(b"FAIL"));
    }

    #[test]
    fn test_reboot_bootloader() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"reboot-bootloader");
        let res = block_on(process_next_command(&mut transport, &mut fastboot_impl));
        assert_eq!(res, Err(Error::Aborted));
        assert_eq!(fastboot_impl.reboot_mode, Some(RebootMode::Bootloader));
        assert_eq!(transport.out_queue[0], b"OKAY");
        // Failure is expected here because test reboot implementation always returns, which
        // automatically generates a fastboot failure packet.
        assert!(transport.out_queue[1].starts_with(b"FAIL"));
    }

    #[test]
    fn test_reboot_fastboot() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"reboot-fastboot");
        let res = block_on(process_next_command(&mut transport, &mut fastboot_impl));
        assert_eq!(res, Err(Error::Aborted));
        assert_eq!(fastboot_impl.reboot_mode, Some(RebootMode::Fastboot));
        assert_eq!(transport.out_queue[0], b"OKAY");
        // Failure is expected here because test reboot implementation always returns, which
        // automatically generates a fastboot failure packet.
        assert!(transport.out_queue[1].starts_with(b"FAIL"));
    }

    #[test]
    fn test_reboot_recovery() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"reboot-recovery");
        let res = block_on(process_next_command(&mut transport, &mut fastboot_impl));
        assert_eq!(res, Err(Error::Aborted));
        assert_eq!(fastboot_impl.reboot_mode, Some(RebootMode::Recovery));
        assert_eq!(transport.out_queue[0], b"OKAY");
        // Failure is expected here because test reboot implementation always returns, which
        // automatically generates a fastboot failure packet.
        assert!(transport.out_queue[1].starts_with(b"FAIL"));
    }

    #[test]
    fn test_continue() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.vars = BTreeMap::from([(("max-download-size", &[][..]), "0x400")]);
        let mut transport = TestTransport::new();
        transport.add_input(b"getvar:max-download-size");
        transport.add_input(b"continue");
        transport.add_input(b"getvar:max-download-size");
        block_on(run(&mut transport, &mut fastboot_impl)).unwrap();
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([
                b"OKAY0x400".into(),
                b"INFOContinuing to boot...".into(),
                b"OKAY".into()
            ])
        );
    }

    #[test]
    fn test_continue_run_tcp() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut tcp_stream: TestTcpStream = Default::default();
        tcp_stream.add_input(TCP_HANDSHAKE_MESSAGE);
        tcp_stream.add_length_prefixed_input(b"continue");
        block_on(run_tcp_session(&mut tcp_stream, &mut fastboot_impl)).unwrap();
    }

    #[test]
    fn test_set_active() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"set_active:a");
        block_on(process_next_command(&mut transport, &mut fastboot_impl)).unwrap();
        assert_eq!(transport.out_queue, VecDeque::<Vec<u8>>::from([b"OKAY".into()]));
        assert_eq!(fastboot_impl.active_slot, Some("a".into()));
    }

    #[test]
    fn test_set_active_missing_slot() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"set_active");
        block_on(process_next_command(&mut transport, &mut fastboot_impl)).unwrap();
        assert_eq!(transport.out_queue, VecDeque::<Vec<u8>>::from([b"FAILMissing slot".into()]));
    }

    #[test]
    fn test_flashing_lock() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"flashing lock");
        block_on(process_next_command(&mut transport, &mut fastboot_impl)).unwrap();
        assert_eq!(transport.out_queue, VecDeque::<Vec<u8>>::from([b"OKAY".into()]));
        assert_eq!(
            fastboot_impl.last_write_lock_state_call,
            Some((LockType::Device, LockState::Locked))
        );
    }

    #[test]
    fn test_flashing_unlock_unlockable() {
        let mut fastboot_impl =
            FastbootTest { unlockability: Some(Unlockability::Allowed), ..Default::default() };
        let mut transport = TestTransport::new();
        transport.add_input(b"flashing unlock");
        block_on(process_next_command(&mut transport, &mut fastboot_impl)).unwrap();
        assert_eq!(transport.out_queue, VecDeque::<Vec<u8>>::from([b"OKAY".into()]));
        assert_eq!(
            fastboot_impl.last_write_lock_state_call,
            Some((LockType::Device, LockState::Unlocked))
        );
    }

    #[test]
    fn test_flashing_lock_critical() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"flashing lock_critical");
        block_on(process_next_command(&mut transport, &mut fastboot_impl)).unwrap();
        assert_eq!(transport.out_queue, VecDeque::<Vec<u8>>::from([b"OKAY".into()]));
        assert_eq!(
            fastboot_impl.last_write_lock_state_call,
            Some((LockType::Critical, LockState::Locked))
        );
    }

    #[test]
    fn test_flashing_unlock_critical() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(b"flashing unlock_critical");
        block_on(process_next_command(&mut transport, &mut fastboot_impl)).unwrap();
        assert_eq!(transport.out_queue, VecDeque::<Vec<u8>>::from([b"OKAY".into()]));
        assert_eq!(
            fastboot_impl.last_write_lock_state_call,
            Some((LockType::Critical, LockState::Unlocked))
        );
    }

    #[test]
    fn test_command_exec() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.command_exec_res = Some(Err("test".into()));
        let mut transport = TestTransport::new();
        transport.add_input(b"flash test");
        block_on(process_next_command(&mut transport, &mut fastboot_impl)).unwrap();
        assert_eq!(transport.out_queue, VecDeque::<Vec<u8>>::from([b"FAILtest".into()]));
        assert_eq!(&fastboot_impl.command_exec_args, "flash test");
    }

    fn get_unlock_ability_helper(unlockability: Unlockability, expected: &str) {
        let mut fastboot_impl =
            FastbootTest { unlockability: Some(unlockability), ..Default::default() };
        let mut transport = TestTransport::new();
        transport.add_input(b"flashing get_unlock_ability");
        block_on(process_next_command(&mut transport, &mut fastboot_impl)).unwrap();
        assert_eq!(transport.out_queue, VecDeque::<Vec<u8>>::from([expected.as_bytes().into()]));
    }

    #[test]
    fn test_get_unlock_ability_allowed() {
        get_unlock_ability_helper(Unlockability::Allowed, "OKAY1");
    }

    #[test]
    fn test_get_unlock_ability_prohibited() {
        get_unlock_ability_helper(Unlockability::Prohibited, "OKAY0");
    }

    fn stream_test_helper(input: &str, expected: Option<StreamCommand<&str>>) {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut transport = TestTransport::new();
        transport.add_input(input.as_bytes());
        let _ = block_on(run(&mut transport, &mut fastboot_impl));

        // Minor hack to get Option<StreamCommand<T>> of different types to compare.
        match (expected, fastboot_impl.stream_command) {
            (None, None) => {}
            (Some(expected), Some(actual)) => assert_eq!(expected, actual),
            _ => assert!(false, "stream command mismatch"),
        }
    }

    #[test]
    fn test_stream_flash() {
        stream_test_helper(
            "stream-flash:boot_a:0:0xefb5af2e",
            Some(StreamCommand {
                partition: "boot_a",
                offset: 0,
                operation: StreamOperation::Flash { checksum: 0xefb5af2e },
            }),
        );
    }

    #[test]
    fn test_stream_fill() {
        stream_test_helper(
            "stream-fill:boot_a:400:200:0xfafafafa",
            Some(StreamCommand {
                partition: "boot_a",
                offset: 0x400,
                operation: StreamOperation::Fill { size: 0x200, payload: 0xfafafafa },
            }),
        );
    }

    #[test]
    fn test_stream_flash_too_few_args() {
        stream_test_helper("stream-flash", None);
        stream_test_helper("stream-flash:boot_a", None);
        stream_test_helper("stream-flash:boot_a:0", None);
    }

    #[test]
    fn test_stream_flash_too_many_args() {
        stream_test_helper("stream-flash:boot_a:400:200:0xfafafafa", None);
    }

    #[test]
    fn test_stream_flash_unparseable() {
        stream_test_helper("stream-flash:boot_a:0:squid", None);
        stream_test_helper("stream-flash:boot_a:squid:0", None);
        // 68 bit int
        stream_test_helper("stream-flash:boot_a:0:0xFFFFFFFFFFFFFFFFF", None);
        stream_test_helper("stream-flash:boot_a:0xFFFFFFFFFFFFFFFFF:0", None);
    }

    #[test]
    fn test_stream_fill_too_few_args() {
        stream_test_helper("stream-fill", None);
        stream_test_helper("stream-fill:boot_a", None);
        stream_test_helper("stream-fill:boot_a:0", None);
        stream_test_helper("stream-fill:boot_a:0:200", None);
    }

    #[test]
    fn test_stream_fill_too_many_args() {
        stream_test_helper("stream-fill:boot_a:0x0:0x200:0x0:0x400", None);
    }

    #[test]
    fn test_stream_fill_unparseable() {
        stream_test_helper("stream-fill:boot_a:400:200:squid", None);
        stream_test_helper("stream-fill:boot_a:400:squid:200", None);
        stream_test_helper("stream-fill:boot_a:squid:400:200", None);

        // 68 bit int
        stream_test_helper("stream-fill:boot_a:0xFFFFFFFFFFFFFFFFF:400:200", None);
        stream_test_helper("stream-fill:boot_a:0:0xFFFFFFFFFFFFFFFFF:200", None);
        stream_test_helper("stream-fill:boot_a:0:200:0xFFFFFFFFFFFFFFFFF", None);

        // Size is not a multiple of 4.
        stream_test_helper("stream-fill:boot_a:400:5:200", None);
    }
}
