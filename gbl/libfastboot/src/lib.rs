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

#![cfg_attr(not(test), no_std)]
#![allow(async_fn_in_trait)]

use core::{
    cmp::min,
    fmt::{Debug, Display, Formatter, Write},
    str::{from_utf8, Split},
};
use gbl_async::{block_on, yield_now};
use liberror::{Error, Result};

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
/// Fastboot supports these transports:
/// * USB
/// * TCP
/// * UDP
pub trait Transport {
    /// Fetches the next fastboot packet into `out`.
    ///
    /// Returns the actual size of the packet on success.
    ///
    /// TODO(b/322540167): In the future, we may want to support using `[MaybeUninit<u8>]` as the
    /// download buffer to avoid expensive initialization at the beginning. This would require an
    /// interface where the implementation provides the buffer for us to copy instead of us.
    async fn receive_packet(&mut self, out: &mut [u8]) -> Result<usize>;

    /// Sends a fastboot packet.
    ///
    /// The method assumes `packet` is sent or at least copied to queue after it returns, where
    /// the buffer can go out of scope without affecting anything.
    async fn send_packet(&mut self, packet: &[u8]) -> Result<()>;
}

/// For now, we hardcode the expected version, until we need to distinguish between multiple
/// versions.
const TCP_HANDSHAKE_MESSAGE: &[u8] = b"FB01";

/// A trait representing a TCP stream reader/writer. Fastboot over TCP has additional handshake
/// process and uses a length-prefixed wire message format. It is recommended that caller
/// implements this trait instead of `Transport`, and uses the API `Fastboot::run_tcp_session()`
/// to perform fastboot over TCP. It internally handles handshake and wire message parsing.
pub trait TcpStream {
    /// Reads to `out` for exactly `out.len()` number bytes from the TCP connection.
    async fn read_exact(&mut self, out: &mut [u8]) -> Result<()>;

    /// Sends exactly `data.len()` number bytes from `data` to the TCP connection.
    async fn write_exact(&mut self, data: &[u8]) -> Result<()>;
}

/// Implements [Transport] on a [TcpStream].
pub struct TcpTransport<'a, T: TcpStream>(&'a mut T);

impl<'a, T: TcpStream> TcpTransport<'a, T> {
    /// Creates an instance from a newly connected TcpStream and performs handshake.
    pub fn new_and_handshake(tcp_stream: &'a mut T) -> Result<Self> {
        let mut handshake = [0u8; 4];
        block_on(tcp_stream.write_exact(TCP_HANDSHAKE_MESSAGE))?;
        block_on(tcp_stream.read_exact(&mut handshake[..]))?;
        match handshake == *TCP_HANDSHAKE_MESSAGE {
            true => Ok(Self(tcp_stream)),
            _ => Err(Error::InvalidHandshake),
        }
    }
}

impl<'a, T: TcpStream> Transport for TcpTransport<'a, T> {
    async fn receive_packet(&mut self, out: &mut [u8]) -> Result<usize> {
        let mut length_prefix = [0u8; 8];
        self.0.read_exact(&mut length_prefix[..]).await?;
        let packet_size: usize = u64::from_be_bytes(length_prefix).try_into()?;
        match out.len() < packet_size {
            true => Err(Error::InvalidInput),
            _ => {
                self.0.read_exact(&mut out[..packet_size]).await?;
                Ok(packet_size)
            }
        }
    }

    async fn send_packet(&mut self, packet: &[u8]) -> Result<()> {
        self.0.write_exact(&mut u64::try_from(packet.len())?.to_be_bytes()[..]).await?;
        self.0.write_exact(packet).await
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
    /// Converts to string.
    pub fn to_str(&self) -> &str {
        from_utf8(&self.0 .0[..self.0 .1]).unwrap_or("")
    }

    /// Clones the error.
    pub fn clone(&self) -> Self {
        self.to_str().into()
    }
}

impl Debug for CommandError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.to_str())
    }
}

impl<T: Display> From<T> for CommandError {
    fn from(val: T) -> Self {
        let mut res = CommandError(FormattedBytes([0u8; COMMAND_ERROR_LENGTH], 0));
        write!(res.0, "{}", val).unwrap();
        res
    }
}

/// Type alias for Result that wraps a CommandError
pub type CommandResult<T> = core::result::Result<T, CommandError>;

/// Fastboot reboot mode
#[derive(Debug, Copy, Clone, PartialEq)]
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
        var: &str,
        args: Split<char>,
        out: &mut [u8],
        responder: impl InfoSender,
    ) -> CommandResult<usize>;

    /// A helper API for getting the value of a fastboot variable and decoding it into string.
    async fn get_var_as_str<'s>(
        &mut self,
        var: &str,
        args: Split<'_, char>,
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

    /// Backend for getting download buffer
    async fn get_download_buffer(&mut self) -> &mut [u8];

    /// Called when a download is completed.
    async fn download_complete(
        &mut self,
        download_size: usize,
        responder: impl InfoSender,
    ) -> CommandResult<()>;

    /// Backend for `fastboot flash ...`
    ///
    /// # Args
    ///
    /// * `part`: Name of the partition.
    /// * `responder`: An instance of `InfoSender`.
    async fn flash(&mut self, part: &str, responder: impl InfoSender) -> CommandResult<()>;

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
        size: u64,
        responder: impl UploadBuilder + InfoSender,
    ) -> CommandResult<()>;

    /// Backend for `fastboot reboot/reboot-bootloader/reboot-fastboot/reboot-recovery`
    ///
    /// # Args
    ///
    /// * `mode`: An `RebootMode` specifying the reboot mode.
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
    ) -> CommandError;

    /// Backend for `fastboot oem ...`.
    ///
    /// # Args
    ///
    /// * `cmd`: The OEM command string that comes after "oem ".
    /// * `responder`: An instance of `InfoSender`.
    /// * `res`: The responder buffer. Upon success, implementation can use the buffer to
    ///   construct a valid UTF8 string which will be sent as "OKAY<string>"
    ///
    /// # Returns
    ///
    /// On success, returns the portion of `res` used by the construction of string message.
    async fn oem<'a>(
        &mut self,
        cmd: &str,
        responder: impl InfoSender,
        res: &'a mut [u8],
    ) -> CommandResult<&'a [u8]>;

    // TODO(b/322540167): Add methods for other commands.
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
    /// In actual fastboot context, the method should send an "INFO<var>:<args>:<val>" message to
    /// the host.
    async fn send_var_info(&mut self, name: &str, args: &[&str], val: &str) -> CommandResult<()>;
}

/// Provides an API for sending fastboot INFO messages.
pub trait InfoSender {
    /// Sends formatted INFO message.
    ///
    /// # Args:
    ///
    /// * `cb`: A closure provided by the caller for constructing the formatted messagae.
    async fn send_formatted_info<F: FnOnce(&mut dyn Write)>(&mut self, cb: F) -> CommandResult<()>;

    /// Sends a Fastboot "INFO<`msg`>" packet.
    async fn send_info(&mut self, msg: &str) -> CommandResult<()> {
        self.send_formatted_info(|w| write!(w, "{}", msg).unwrap()).await
    }
}

/// Provides an API for sending fastboot OKAY messages.
pub trait OkaySender {
    /// Sends formatted Okay message.
    ///
    /// # Args:
    ///
    /// * `cb`: A closure provided by the caller for constructing the formatted messagae.
    async fn send_formatted_okay<F: FnOnce(&mut dyn Write)>(self, cb: F) -> CommandResult<()>;

    /// Sends a fastboot OKAY<msg> packet. `Self` is consumed.
    async fn send_okay(self, msg: &str) -> CommandResult<()>
    where
        Self: Sized,
    {
        self.send_formatted_okay(|w| write!(w, "{}", msg).unwrap()).await
    }
}

/// `UploadBuilder` provides API for initiating a fastboot upload.
pub trait UploadBuilder {
    /// Starts the upload.
    ///
    /// In a real fastboot context, the method should send `DATA0xXXXXXXXX` to the remote host to
    /// start the download. An `Uploader` implementation should be returned for uploading payload.
    async fn initiate_upload(self, data_size: u64) -> CommandResult<impl Uploader>;
}

/// `UploadBuilder` provides API for uploading payload.
pub trait Uploader {
    /// Uploads data to the Fastboot host.
    async fn upload(&mut self, data: &[u8]) -> CommandResult<()>;
}

/// `Responder` implements APIs for fastboot backend to send fastboot messages and uploading data.
struct Responder<'a, T: Transport> {
    buffer: [u8; MAX_RESPONSE_SIZE],
    transport: &'a mut T,
    transport_error: Result<()>,
    remaining_upload: u64,
}

impl<'a, T: Transport> Responder<'a, T> {
    fn new(transport: &'a mut T) -> Self {
        Self {
            buffer: [0u8; MAX_RESPONSE_SIZE],
            transport,
            transport_error: Ok(()),
            remaining_upload: 0,
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
    /// * `cb`: A closure provided by the caller for constructing the formatted messagae.
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
    async fn send_data_message(&mut self, data_size: u64) -> Result<()> {
        self.send_formatted_msg("DATA", |v| write!(v, "{:08x}", data_size).unwrap()).await
    }
}

impl<'a, T: Transport> VarInfoSender for &mut Responder<'a, T> {
    async fn send_var_info(&mut self, name: &str, args: &[&str], val: &str) -> CommandResult<()> {
        // Sends a "INFO<var>:<':'-separated args>:<val>" packet to the host.
        Ok(self
            .send_formatted_msg("INFO", |v| {
                write!(v, "{}", name).unwrap();
                args.iter().for_each(|arg| write!(v, ":{}", arg).unwrap());
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
    async fn send_formatted_info<F: FnOnce(&mut dyn Write)>(&mut self, cb: F) -> CommandResult<()> {
        Ok(self.send_formatted_msg("INFO", cb).await?)
    }
}

impl<T: Transport> OkaySender for &mut Responder<'_, T> {
    async fn send_formatted_okay<F: FnOnce(&mut dyn Write)>(self, cb: F) -> CommandResult<()> {
        Ok(self.send_formatted_msg("OKAY", cb).await?)
    }
}

impl<'a, T: Transport> UploadBuilder for &mut Responder<'a, T> {
    async fn initiate_upload(self, data_size: u64) -> CommandResult<impl Uploader> {
        self.send_data_message(data_size).await?;
        self.remaining_upload = data_size;
        Ok(self)
    }
}

impl<'a, T: Transport> Uploader for &mut Responder<'a, T> {
    /// Uploads data. Returns error if accumulative amount exceeds `data_size` passed to
    /// `UploadBuilder::start()`.
    async fn upload(&mut self, data: &[u8]) -> CommandResult<()> {
        self.transport_error?;
        self.remaining_upload = self
            .remaining_upload
            .checked_sub(data.len().try_into().map_err(|_| "")?)
            .ok_or::<CommandError>("".into())?;
        self.transport_error = self.transport.send_packet(data).await;
        Ok(())
    }
}

pub mod test_utils {
    //! Test utilities to help users of this library write unit tests.

    use crate::{CommandResult, InfoSender, UploadBuilder, Uploader};
    use core::fmt::Write;

    /// A test implementation of `UploadBuilder` for unittesting
    /// `FastbootImplementation::upload()`.
    ///
    /// The test uploader simply uploads to a user provided buffer.
    pub struct TestUploadBuilder<'a>(pub &'a mut [u8]);

    impl<'a> UploadBuilder for TestUploadBuilder<'a> {
        async fn initiate_upload(self, _: u64) -> CommandResult<impl Uploader> {
            Ok(TestUploader(0, self.0))
        }
    }

    impl<'a> InfoSender for TestUploadBuilder<'a> {
        async fn send_formatted_info<F: FnOnce(&mut dyn Write)>(
            &mut self,
            _: F,
        ) -> CommandResult<()> {
            // Not needed currently.
            Ok(())
        }
    }

    // (Bytes sent, upload buffer)
    struct TestUploader<'a>(usize, &'a mut [u8]);

    impl Uploader for TestUploader<'_> {
        async fn upload(&mut self, data: &[u8]) -> CommandResult<()> {
            self.1[self.0..][..data.len()].clone_from_slice(data);
            self.0 = self.0.checked_add(data.len()).unwrap();
            Ok(())
        }
    }
}

const MAX_DOWNLOAD_SIZE_NAME: &'static str = "max-download-size";

/// Helper for handling "fastboot getvar ..."
async fn get_var(
    mut args: Split<'_, char>,
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    let mut resp = Responder::new(transport);
    let Some(var) = args.next() else {
        return reply_fail!(resp, "Missing variable");
    };

    match var {
        "all" => return get_var_all(transport, fb_impl).await,
        MAX_DOWNLOAD_SIZE_NAME => {
            return reply_okay!(resp, "{:#x}", fb_impl.get_download_buffer().await.len());
        }
        v => {
            let mut val = [0u8; MAX_RESPONSE_SIZE];
            match fb_impl.get_var_as_str(v, args, &mut resp, &mut val[..]).await {
                Ok(s) => reply_okay!(resp, "{}", s),
                Err(e) => reply_fail!(resp, "{}", e.to_str()),
            }
        }
    }
}

/// A wrapper of `get_var_all()` that first iterates reserved variables.
async fn get_var_all_with_native(
    fb_impl: &mut impl FastbootImplementation,
    mut sender: impl VarInfoSender,
) -> CommandResult<()> {
    // Process the built-in MAX_DOWNLOAD_SIZE_NAME variable.
    let mut size_str = [0u8; 32];
    let size_str = snprintf!(size_str, "{:#x}", fb_impl.get_download_buffer().await.len());
    sender.send_var_info(MAX_DOWNLOAD_SIZE_NAME, &[], size_str).await?;
    fb_impl.get_var_all(sender).await
}

/// Method for handling "fastboot getvar all"
async fn get_var_all(
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    let mut resp = Responder::new(transport);
    // Don't allow custom INFO messages because variable values are sent as INFO messages.
    let get_res = get_var_all_with_native(fb_impl, &mut resp).await;
    match get_res {
        Ok(()) => reply_okay!(resp, ""),
        Err(e) => reply_fail!(resp, "{}", e.to_str()),
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
        usize::try_from(next_arg_u64(&mut args, Err("Not enough argument".into()))?)
            .map_err(|_| "Download size overflow".into())
    })() {
        Err(e) => return reply_fail!(resp, "{}", e.to_str()),
        Ok(v) => v,
    };
    let download_buffer = &mut fb_impl.get_download_buffer().await;
    if total_download_size > download_buffer.len() {
        return reply_fail!(resp, "Download size is too big");
    } else if total_download_size == 0 {
        return reply_fail!(resp, "Zero download size");
    }

    // Starts the download
    let download_buffer = &mut download_buffer[..total_download_size];
    // `total_download_size` is parsed from `next_arg_u64` and thus should fit into u64.
    resp.send_data_message(u64::try_from(total_download_size).unwrap()).await?;
    let mut downloaded = 0;
    while downloaded < total_download_size {
        let (_, remains) = &mut download_buffer.split_at_mut(downloaded);
        match resp.transport.receive_packet(remains).await? {
            0 => yield_now().await,
            v => match downloaded.checked_add(v) {
                Some(v) if v > total_download_size => {
                    return reply_fail!(resp, "More data received then expected");
                }
                Some(v) => downloaded = v,
                _ => return Err(Error::Other(Some("Invalid read size from transport"))),
            },
        };
    }
    match fb_impl.download_complete(downloaded, &mut resp).await {
        Ok(()) => reply_okay!(resp, ""),
        Err(e) => reply_fail!(resp, "{}", e.to_str()),
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
        Err(e) => reply_fail!(resp, "{}", e.to_str()),
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
            Err(e) => reply_fail!(resp, "{}", e.to_str()),
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
            return Err("Not enough argments".into());
        }
        // Parses backward. Parses size, offset first and treats the remaining string as
        // partition name. This allows ":" in partition name.
        let mut rev = args.clone().rev();
        let sz = next_arg(&mut rev, Err("Invalid argument".into()))?;
        let off = next_arg(&mut rev, Err("Invalid argument".into()))?;
        let part = &cmd[..cmd.len() - (off.len() + sz.len() + 2)];
        fb_impl.fetch(part, hex_to_u64(off)?, hex_to_u64(sz)?, &mut resp).await
    }
    .await;
    match resp.remaining_upload > 0 {
        true => return Err(Error::InvalidInput),
        _ => match fetch_res {
            Err(e) => reply_fail!(resp, "{}", e.to_str()),
            _ => reply_okay!(resp, ""),
        },
    }
}

// Handles `fastboot reboot*`
async fn reboot(
    mode: RebootMode,
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    let mut resp = Responder::new(transport);
    let e = fb_impl.reboot(mode, &mut resp).await;
    reply_fail!(resp, "{}", e.to_str())
}

/// Helper for handling "fastboot oem ...".
async fn oem(
    cmd: &str,
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    let mut resp = Responder::new(transport);
    let mut oem_out = [0u8; MAX_RESPONSE_SIZE - 4];
    let oem_res = fb_impl.oem(cmd, &mut resp, &mut oem_out[..]).await;
    match oem_res {
        Ok(msg) => match from_utf8(msg) {
            Ok(s) => reply_okay!(resp, "{}", s),
            Err(e) => reply_fail!(resp, "Invalid return string {}", e),
        },
        Err(e) => reply_fail!(resp, "{}", e.to_str()),
    }
}

/// Process the next Fastboot command from  the transport.
pub async fn process_next_command(
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    let mut packet = [0u8; MAX_COMMAND_SIZE];
    let cmd_size = match transport.receive_packet(&mut packet[..]).await? {
        0 => return Ok(()),
        v => v,
    };
    let Ok(cmd_str) = from_utf8(&packet[..cmd_size]) else {
        return transport.send_packet(fastboot_fail!(packet, "Invalid Command")).await;
    };
    let mut args = cmd_str.split(':');
    let Some(cmd) = args.next() else {
        return transport.send_packet(fastboot_fail!(packet, "No command")).await;
    };
    match cmd {
        "getvar" => get_var(args, transport, fb_impl).await,
        "download" => download(args, transport, fb_impl).await,
        "flash" => flash(cmd_str, transport, fb_impl).await,
        "upload" => upload(transport, fb_impl).await,
        "fetch" => fetch(cmd_str, args, transport, fb_impl).await,
        "reboot" => reboot(RebootMode::Normal, transport, fb_impl).await,
        "reboot-bootloader" => reboot(RebootMode::Bootloader, transport, fb_impl).await,
        "reboot-fastboot" => reboot(RebootMode::Fastboot, transport, fb_impl).await,
        "reboot-recovery" => reboot(RebootMode::Recovery, transport, fb_impl).await,
        _ if cmd_str.starts_with("oem ") => oem(&cmd_str[4..], transport, fb_impl).await,
        _ => transport.send_packet(fastboot_fail!(packet, "Command not found")).await,
    }
}

/// Keeps polling and processing fastboot commands from the transport.
pub async fn run(
    transport: &mut impl Transport,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    loop {
        process_next_command(transport, fb_impl).await?;
    }
}

/// Runs a fastboot over TCP session.
///
/// The method performs fastboot over TCP handshake and then call `Self::run(...)`.
pub async fn run_tcp_session(
    tcp_stream: &mut impl TcpStream,
    fb_impl: &mut impl FastbootImplementation,
) -> Result<()> {
    run(&mut TcpTransport::new_and_handshake(tcp_stream)?, fb_impl).await
}

/// A helper data structure for writing formatted string to fixed size bytes array.
#[derive(Debug)]
pub struct FormattedBytes<T: AsMut<[u8]>>(T, usize);

impl<T: AsMut<[u8]>> FormattedBytes<T> {
    /// Create an instance.
    pub fn new(buf: T) -> Self {
        Self(buf, 0)
    }

    /// Get the size of content.
    pub fn size(&self) -> usize {
        self.1
    }

    /// Appends the given `bytes` to the contents.
    ///
    /// If `bytes` exceeds the remaining buffer space, any excess bytes are discarded.
    ///
    /// Returns the resulting contents.
    pub fn append(&mut self, bytes: &[u8]) -> &mut [u8] {
        let buf = &mut self.0.as_mut()[self.1..];
        // Only write as much as the size of the bytes buffer. Additional write is silently
        // ignored.
        let to_write = min(buf.len(), bytes.len());
        buf[..to_write].clone_from_slice(&bytes[..to_write]);
        self.1 += to_write;
        &mut self.0.as_mut()[..self.1]
    }
}

impl<T: AsMut<[u8]>> core::fmt::Write for FormattedBytes<T> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.append(s.as_bytes());
        Ok(())
    }
}

/// A convenient macro that behaves similar to snprintf in C.
#[macro_export]
macro_rules! snprintf {
    ( $arr:expr, $( $x:expr ),* ) => {
        {
            let mut formatted_bytes = FormattedBytes::new(&mut $arr[..]);
            write!(formatted_bytes, $($x,)*).unwrap();
            let size = formatted_bytes.size();
            from_utf8(&$arr[..size]).unwrap()
        }
    };
}

/// A helper to convert a hex string into u64.
pub(crate) fn hex_to_u64(s: &str) -> CommandResult<u64> {
    Ok(u64::from_str_radix(s.strip_prefix("0x").unwrap_or(s), 16)?)
}

/// A helper to check and fetch the next argument or fall back to the default if not available.
///
/// # Args
///
/// args: A string iterator.
/// default: This will be returned as it is if args doesn't have the next element(). Providing a
///   Ok(str) is equivalent to providing a default value. Providing an Err() is equivalent to
///   requiring that the next argument is mandatory.
pub fn next_arg<'a, T: Iterator<Item = &'a str>>(
    args: &mut T,
    default: CommandResult<&'a str>,
) -> CommandResult<&'a str> {
    args.next().filter(|v| *v != "").ok_or("").or(default.map_err(|e| e.into()))
}

/// A helper to check and fetch the next argument as a u64 hex string.
///
/// # Args
///
/// args: A string iterator.
/// default: This will be returned as it is if args doesn't have the next element(). Providing a
///   Ok(u64) is equivalent to providing a default value. Providing an Err() is equivalent to
///   requiring that the next argument is mandatory.
///
/// Returns error if the next argument is not a valid hex string.
pub fn next_arg_u64<'a, T: Iterator<Item = &'a str>>(
    args: &mut T,
    default: CommandResult<u64>,
) -> CommandResult<u64> {
    match next_arg(args, Err("".into())) {
        Ok(v) => hex_to_u64(v),
        _ => default.map_err(|e| e.into()),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::collections::{BTreeMap, VecDeque};

    #[derive(Default)]
    struct FastbootTest {
        // A mapping from (variable name, argument) to variable value.
        vars: BTreeMap<(&'static str, &'static [&'static str]), &'static str>,
        // The partition arg from Fastboot command
        flash_partition: String,
        // Upload size, batches of data to upload,
        upload_config: (u64, Vec<Vec<u8>>),
        // A map from partition name to (upload size override, partition data)
        fetch_data: BTreeMap<&'static str, (u64, Vec<u8>)>,
        // result string, INFO strings.
        oem_output: (String, Vec<String>),
        oem_command: String,
        download_buffer: Vec<u8>,
        downloaded_size: usize,
        reboot_mode: Option<RebootMode>,
    }

    impl FastbootImplementation for FastbootTest {
        async fn get_var(
            &mut self,
            var: &str,
            args: Split<'_, char>,
            out: &mut [u8],
            _: impl InfoSender,
        ) -> CommandResult<usize> {
            let args = args.collect::<Vec<_>>();
            match self.vars.get(&(var, &args[..])) {
                Some(v) => {
                    out[..v.len()].clone_from_slice(v.as_bytes());
                    Ok(v.len())
                }
                _ => Err("Not Found".into()),
            }
        }

        async fn get_var_all(&mut self, mut responder: impl VarInfoSender) -> CommandResult<()> {
            for ((var, config), value) in &self.vars {
                responder.send_var_info(var, config, value).await?;
            }
            Ok(())
        }

        async fn get_download_buffer(&mut self) -> &mut [u8] {
            self.download_buffer.as_mut_slice()
        }

        async fn download_complete(
            &mut self,
            download_size: usize,
            _: impl InfoSender,
        ) -> CommandResult<()> {
            self.downloaded_size = download_size;
            Ok(())
        }

        async fn flash(&mut self, part: &str, _: impl InfoSender) -> CommandResult<()> {
            self.flash_partition = part.into();
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
            size: u64,
            responder: impl UploadBuilder + InfoSender,
        ) -> CommandResult<()> {
            let (size_override, data) = self.fetch_data.get(part).ok_or("Not Found")?;
            let mut uploader = responder.initiate_upload(*size_override).await?;
            uploader.upload(&data[offset.try_into().unwrap()..][..size.try_into().unwrap()]).await
        }

        async fn reboot(
            &mut self,
            mode: RebootMode,
            responder: impl InfoSender + OkaySender,
        ) -> CommandError {
            responder.send_okay("").await.unwrap();
            self.reboot_mode = Some(mode);
            "reboot-return".into()
        }

        async fn oem<'b>(
            &mut self,
            cmd: &str,
            mut responder: impl InfoSender,
            res: &'b mut [u8],
        ) -> CommandResult<&'b [u8]> {
            let (res_str, infos) = &mut self.oem_output;
            self.oem_command = cmd.into();
            for ele in infos {
                responder.send_info(ele.as_str()).await?;
            }
            Ok(snprintf!(res, "{}", *res_str).as_bytes())
        }
    }

    struct TestTransport {
        in_queue: VecDeque<Vec<u8>>,
        out_queue: VecDeque<Vec<u8>>,
    }

    impl TestTransport {
        fn new() -> Self {
            Self { in_queue: VecDeque::new(), out_queue: VecDeque::new() }
        }

        fn add_input(&mut self, packet: &[u8]) {
            self.in_queue.push_back(packet.into());
        }
    }

    impl Transport for TestTransport {
        async fn receive_packet(&mut self, out: &mut [u8]) -> Result<usize> {
            match self.in_queue.pop_front() {
                Some(v) => {
                    let size = min(out.len(), v.len());
                    out[..size].clone_from_slice(&v[..size]);
                    // Returns the input length so that we can test bogus download size.
                    Ok(v.len())
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
        async fn read_exact(&mut self, out: &mut [u8]) -> Result<()> {
            for ele in out {
                *ele = self.in_queue.pop_front().ok_or(Error::OperationProhibited)?;
            }
            Ok(())
        }

        async fn write_exact(&mut self, data: &[u8]) -> Result<()> {
            data.iter().for_each(|v| self.out_queue.push_back(*v));
            Ok(())
        }
    }

    #[test]
    fn test_non_exist_command() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; 1024];
        let mut transport = TestTransport::new();
        transport.add_input(b"non_exist");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(transport.out_queue, [b"FAILCommand not found"]);
    }

    #[test]
    fn test_non_ascii_command_string() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; 1024];
        let mut transport = TestTransport::new();
        transport.add_input(b"\xff\xff\xff");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(transport.out_queue, [b"FAILInvalid Command"]);
    }

    #[test]
    fn test_get_var_max_download_size() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; 1024];
        let mut transport = TestTransport::new();
        transport.add_input(b"getvar:max-download-size");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(transport.out_queue, [b"OKAY0x400"]);
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

        fastboot_impl.download_buffer = vec![0u8; 1024];
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

        fastboot_impl.download_buffer = vec![0u8; 1024];
        let mut transport = TestTransport::new();
        transport.add_input(b"getvar:all");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([
                b"INFOmax-download-size: 0x400".into(),
                b"INFOvar_0: val_0".into(),
                b"INFOvar_1:a:b: val_1_a_b".into(),
                b"INFOvar_1:c:d: val_1_c_d".into(),
                b"INFOvar_2:e:f: val_2_e_f".into(),
                b"OKAY".into(),
            ])
        );
    }

    #[test]
    fn test_download() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; 1024];
        let download_content: Vec<u8> =
            (0..fastboot_impl.download_buffer.len()).into_iter().map(|v| v as u8).collect();
        let mut transport = TestTransport::new();
        // Splits download into two batches.
        let (first, second) = download_content.as_slice().split_at(download_content.len() / 2);
        transport.add_input(format!("download:{:#x}", download_content.len()).as_bytes());
        transport.add_input(first);
        transport.add_input(second);
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([b"DATA00000400".into(), b"OKAY".into(),])
        );
        assert_eq!(fastboot_impl.downloaded_size, download_content.len());
        assert_eq!(fastboot_impl.download_buffer, download_content);
    }

    #[test]
    fn test_download_not_enough_args() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; 1024];
        let mut transport = TestTransport::new();
        transport.add_input(b"download");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(transport.out_queue, [b"FAILNot enough argument"]);
    }

    #[test]
    fn test_download_invalid_hex_string() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; 1024];
        let mut transport = TestTransport::new();
        transport.add_input(b"download:hhh");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(transport.out_queue.len(), 1);
        assert!(transport.out_queue[0].starts_with(b"FAIL"));
    }

    fn test_download_size(download_buffer_size: usize, download_size: usize, msg: &str) {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; download_buffer_size];
        let mut transport = TestTransport::new();
        transport.add_input(format!("download:{:#x}", download_size).as_bytes());
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(transport.out_queue, VecDeque::<Vec<u8>>::from([msg.as_bytes().into()]));
    }

    #[test]
    fn test_download_download_size_too_big() {
        test_download_size(1024, 1025, "FAILDownload size is too big");
    }

    #[test]
    fn test_download_zero_download_size() {
        test_download_size(1024, 0, "FAILZero download size");
    }

    #[test]
    fn test_download_more_than_expected() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; 1024];
        let download_content: Vec<u8> = vec![0u8; fastboot_impl.download_buffer.len()];
        let mut transport = TestTransport::new();
        transport.add_input(format!("download:{:#x}", download_content.len() - 1).as_bytes());
        transport.add_input(&download_content[..]);
        // State should be reset to command state.
        transport.add_input(b"getvar:max-download-size");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([
                b"DATA000003ff".into(),
                b"FAILMore data received then expected".into(),
                b"OKAY0x400".into(),
            ])
        );
    }

    #[test]
    fn test_oem_cmd() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; 2048];
        let mut transport = TestTransport::new();
        transport.add_input(b"oem oem-command");
        fastboot_impl.oem_output =
            ("oem-return".into(), vec!["oem-info-1".into(), "oem-info-2".into()]);
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
    fn test_flash() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; 2048];
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
        fastboot_impl.download_buffer = vec![0u8; 2048];
        let mut transport = TestTransport::new();
        transport.add_input(b"upload");
        fastboot_impl.upload_config = (0x400, vec![vec![0u8; 0x400 - 1]]);
        assert!(block_on(run(&mut transport, &mut fastboot_impl)).is_err());
    }

    #[test]
    fn test_upload_more_data() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; 2048];
        let mut transport = TestTransport::new();
        transport.add_input(b"upload");
        fastboot_impl.upload_config = (0x400, vec![vec![0u8; 0x400 + 1]]);
        assert!(block_on(run(&mut transport, &mut fastboot_impl)).is_err());
    }

    #[test]
    fn test_fetch() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; 2048];
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
        fastboot_impl.download_buffer = vec![0u8; 2048];
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
        fastboot_impl.download_buffer = vec![0u8; 2048];
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
        fastboot_impl.download_buffer = vec![0u8; 2048];
        let mut transport = TestTransport::new();
        transport.add_input(b"fetch");
        transport.add_input(b"fetch:");
        transport.add_input(b"fetch:boot_a");
        transport.add_input(b"fetch:boot_a:200");
        transport.add_input(b"fetch:boot_a::400");
        transport.add_input(b"fetch:boot_a::");
        transport.add_input(b"fetch:boot_a:xxx:400");
        transport.add_input(b"fetch:boot_a:200:xxx");
        let _ = block_on(run(&mut transport, &mut fastboot_impl));
        assert!(transport.out_queue.iter().all(|v| v.starts_with(b"FAIL")));
    }

    #[test]
    fn test_fastboot_tcp() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; 1024];
        let download_content: Vec<u8> =
            (0..fastboot_impl.download_buffer.len()).into_iter().map(|v| v as u8).collect();
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
        assert_eq!(fastboot_impl.download_buffer, download_content);
    }

    #[test]
    fn test_fastboot_tcp_invalid_handshake() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; 1024];
        let mut tcp_stream: TestTcpStream = Default::default();
        tcp_stream.add_input(b"ABCD");
        assert_eq!(
            block_on(run_tcp_session(&mut tcp_stream, &mut fastboot_impl)).unwrap_err(),
            Error::InvalidHandshake
        );
    }

    #[test]
    fn test_fastboot_tcp_packet_size_exceeds_maximum() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; 1024];
        let mut tcp_stream: TestTcpStream = Default::default();
        tcp_stream.add_input(TCP_HANDSHAKE_MESSAGE);
        tcp_stream.add_input(&(MAX_COMMAND_SIZE + 1).to_be_bytes());
        assert_eq!(
            block_on(run_tcp_session(&mut tcp_stream, &mut fastboot_impl)).unwrap_err(),
            Error::InvalidInput
        );
    }

    #[test]
    fn test_reboot() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; 2048];
        let mut transport = TestTransport::new();
        transport.add_input(b"reboot");
        block_on(process_next_command(&mut transport, &mut fastboot_impl)).unwrap();
        assert_eq!(fastboot_impl.reboot_mode, Some(RebootMode::Normal));
        assert_eq!(transport.out_queue[0], b"OKAY");
        // Failure is expected here because test reboot implementation always returns, which
        // automatically generates a fastboot failure packet.
        assert!(transport.out_queue[1].starts_with(b"FAIL"));
    }

    #[test]
    fn test_reboot_bootloader() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; 2048];
        let mut transport = TestTransport::new();
        transport.add_input(b"reboot-bootloader");
        block_on(process_next_command(&mut transport, &mut fastboot_impl)).unwrap();
        assert_eq!(fastboot_impl.reboot_mode, Some(RebootMode::Bootloader));
        assert_eq!(transport.out_queue[0], b"OKAY");
        // Failure is expected here because test reboot implementation always returns, which
        // automatically generates a fastboot failure packet.
        assert!(transport.out_queue[1].starts_with(b"FAIL"));
    }

    #[test]
    fn test_reboot_fastboot() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; 2048];
        let mut transport = TestTransport::new();
        transport.add_input(b"reboot-fastboot");
        block_on(process_next_command(&mut transport, &mut fastboot_impl)).unwrap();
        assert_eq!(fastboot_impl.reboot_mode, Some(RebootMode::Fastboot));
        assert_eq!(transport.out_queue[0], b"OKAY");
        // Failure is expected here because test reboot implementation always returns, which
        // automatically generates a fastboot failure packet.
        assert!(transport.out_queue[1].starts_with(b"FAIL"));
    }

    #[test]
    fn test_reboot_recovery() {
        let mut fastboot_impl: FastbootTest = Default::default();
        fastboot_impl.download_buffer = vec![0u8; 2048];
        let mut transport = TestTransport::new();
        transport.add_input(b"reboot-recovery");
        block_on(process_next_command(&mut transport, &mut fastboot_impl)).unwrap();
        assert_eq!(fastboot_impl.reboot_mode, Some(RebootMode::Recovery));
        assert_eq!(transport.out_queue[0], b"OKAY");
        // Failure is expected here because test reboot implementation always returns, which
        // automatically generates a fastboot failure packet.
        assert!(transport.out_queue[1].starts_with(b"FAIL"));
    }
}
