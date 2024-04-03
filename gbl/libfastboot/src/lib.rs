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
//!     ) -> Result<usize, CommandError> {
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
//! let mut fastboot = Fastboot::new(&mut download_buffer[..]);
//! let result = fastboot.run(&mut transport, &mut fastboot_impl, &[]);
//! ```

#![cfg_attr(not(test), no_std)]

use core::fmt::{Debug, Display, Error, Formatter, Write};
use core::str::{from_utf8, Split};

pub const MAX_COMMAND_SIZE: usize = 4096;
pub const MAX_RESPONSE_SIZE: usize = 256;
const OKAY: &'static str = "OKAY";

/// Transport errors.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum TransportError {
    InvalidHanshake,
    PacketSizeOverflow,
    PacketSizeExceedMaximum,
    NotEnoughUpload,
    Others(&'static str),
}

impl Display for TransportError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "{:?}", self)
    }
}

/// Implementation for Fastboot transport interfaces.
pub trait Transport {
    /// Fetches the next fastboot packet into `out`.
    ///
    /// Returns the actual size of the packet on success.
    ///
    /// TODO(b/322540167): In the future, we may want to support using `[MaybeUninit<u8>]` as the
    /// download buffer to avoid expensive initialization at the beginning. This would require an
    /// interface where the implementation provides the buffer for us to copy instead of us.
    fn receive_packet(&mut self, out: &mut [u8]) -> Result<usize, TransportError>;

    /// Sends a fastboot packet.
    ///
    /// The method assumes `packet` is sent or at least copied to queue after it returns, where
    /// the buffer can go out of scope without affecting anything.
    fn send_packet(&mut self, packet: &[u8]) -> Result<(), TransportError>;
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
    fn read_exact(&mut self, out: &mut [u8]) -> Result<(), TransportError>;

    /// Sends exactly `data.len()` number bytes from `data` to the TCP connection.
    fn write_exact(&mut self, data: &[u8]) -> Result<(), TransportError>;
}

impl Transport for &mut dyn TcpStream {
    fn receive_packet(&mut self, out: &mut [u8]) -> Result<usize, TransportError> {
        let mut length_prefix = [0u8; 8];
        self.read_exact(&mut length_prefix[..])?;
        let packet_size: usize = u64::from_be_bytes(length_prefix)
            .try_into()
            .map_err(|_| TransportError::PacketSizeOverflow)?;
        match out.len() < packet_size {
            true => Err(TransportError::PacketSizeExceedMaximum),
            _ => {
                self.read_exact(&mut out[..packet_size])?;
                Ok(packet_size)
            }
        }
    }

    fn send_packet(&mut self, packet: &[u8]) -> Result<(), TransportError> {
        self.write_exact(
            &mut u64::try_from(packet.len())
                .map_err(|_| TransportError::PacketSizeOverflow)?
                .to_be_bytes()[..],
        )?;
        self.write_exact(packet)
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
}

impl Debug for CommandError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
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
    /// * `utils`: A mutable reference to an instance of `FastbootUtils`.
    ///
    /// TODO(b/322540167): Figure out other reserved variables.
    fn get_var(
        &mut self,
        var: &str,
        args: Split<char>,
        out: &mut [u8],
        utils: &mut FastbootUtils,
    ) -> Result<usize, CommandError>;

    /// A helper API for getting the value of a fastboot variable and decoding it into string.
    fn get_var_as_str<'s>(
        &mut self,
        var: &str,
        args: Split<char>,
        out: &'s mut [u8],
        utils: &mut FastbootUtils,
    ) -> Result<&'s str, CommandError> {
        let size = self.get_var(var, args, out, utils)?;
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
    /// * `f`: A closure that takes 3 arguments: 1. variable name, 2. an array of string
    ///   arguments and 3. the corresponding variable value. Implementation should call this for
    ///   all combinations that need to be returned for `fastboot getvar all`. If `f` returns
    ///   error, the implementation should return it immediately. For example the following
    ///   implementation:
    ///
    ///   fn get_var_all(&mut self, f: F, utils: &mut FastbootUtils) -> Result<(), CommandError> {
    ///       f("partition-size", &["boot_a"], /* size string of boot_a */)?;
    ///       f("partition-size", &["boot_b"], /* size string of boot_b */)?;
    ///       f("partition-size", &["init_boot_a"], /* size string of init_boot_a */)?;
    ///       f("partition-size", &["init_boot_b"], /* size string of init_boot_b */)?;
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
    /// * `utils`: A mutable reference to an instance of `FastbootUtils`.
    ///
    /// TODO(b/322540167): This and `get_var()` contain duplicated logic. Investigate if there can
    /// be better solutions for doing the combination traversal.
    fn get_var_all(
        &mut self,
        f: &mut dyn FnMut(&str, &[&str], &str) -> Result<(), CommandError>,
        utils: &mut FastbootUtils,
    ) -> Result<(), CommandError>;

    /// Backend for `fastboot flash ...`
    ///
    /// # Args
    ///
    /// * `part`: Name of the partition.
    /// * `utils`: A mutable reference to an instance of `FastbootUtils`.
    fn flash(&mut self, part: &str, utils: &mut FastbootUtils) -> Result<(), CommandError>;

    /// Backend for `fastboot get_staged ...`
    ///
    /// # Args
    ///
    /// * `upload_builder`: An instance of `UploadBuilder` for initiating and uploading data. For
    ///   example:
    ///
    ///   ```
    ///   fn upload(
    ///       &mut self,
    ///       upload_builder: UploadBuilder,
    ///       utils: &mut FastbootUtils,
    ///   ) -> Result<(), CommandError> {
    ///       // Sends a total of 1024 bytes data.
    ///       let mut uploader = upload_builder.start(1024)?;
    ///       // Can upload in multiple batches.
    ///       uploader.upload(&utils.download_buffer[..512])?;
    ///       uploader.upload(&utils.download_buffer[512..])?;
    ///       Ok(())
    ///   }
    ///   ```
    ///
    ///   If implementation fails to upload enough, or attempts to upload more than expected data
    ///   with `Uploader::upload()`, an error will be returned.
    ///
    /// * `utils`: A mutable reference to an instance of `FastbootUtils`.
    fn upload(
        &mut self,
        upload_builder: UploadBuilder,
        utils: &mut FastbootUtils,
    ) -> Result<(), CommandError>;

    /// Backend for `fastboot fetch ...`
    ///
    /// # Args
    ///
    /// * `part`: The partition name.
    /// * `offset`: The offset into the partition for upload.
    /// * `size`: The number of bytes to upload.
    /// * `upload_builder`: An instance of `UploadBuilder` for initiating and uploading data.
    /// * `utils`: A mutable reference to an instance of `FastbootUtils`.
    fn fetch(
        &mut self,
        part: &str,
        offset: u64,
        size: u64,
        upload_builder: UploadBuilder,
        utils: &mut FastbootUtils,
    ) -> Result<(), CommandError>;

    /// Backend for `fastboot oem ...`.
    ///
    /// # Args
    ///
    /// * `cmd`: The OEM command string that comes after "oem ".
    /// * `utils`: A mutable reference to an instance of `FastbootUtils`.
    /// * `res`: The response buffer. Upon success, implementation can use the buffer to
    ///   construct a valid UTF8 string which will be sent as "OKAY<string>"
    ///
    /// # Returns
    ///
    /// On success, returns the portion of `res` used by the construction of string message.
    fn oem<'a>(
        &mut self,
        cmd: &str,
        utils: &mut FastbootUtils,
        res: &'a mut [u8],
    ) -> Result<&'a [u8], CommandError>;

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
    ( $arr:expr, $( $x:expr ),* ) => { fastboot_msg!($arr, "OKAY", $($x,)*) };
}

/// An internal convenient macro that constructs a formatted fastboot FAIL message.
macro_rules! fastboot_fail {
    ( $arr:expr, $( $x:expr ),* ) => { fastboot_msg!($arr, "FAIL", $($x,)*) };
}

/// An internal convenient macro that constructs a formatted fastboot INFO message.
macro_rules! fastboot_info {
    ( $arr:expr, $( $x:expr ),* ) => { fastboot_msg!($arr, "INFO", $($x,)*) };
}

/// `FastbootInfoSender` defines a method for sending Fastboot INFO messages.
///
/// The trait is for user to implement their mock `FastbootUtils` for testing implementation
/// of the `FastbootImplementation` trait.
pub trait FastbootInfoSend {
    /// Sends a Fastboot "INFO<`msg`>" packet
    fn send(&mut self, msg: &str) -> Result<(), CommandError>;
}

/// `FastbootUtils` contains download data/buffer and a `FastbootInfoSend` trait object for sending
/// Fastboot INFO messages. It can be used in the implementation of `FastbootImplementation`.
pub struct FastbootUtils<'a> {
    // TODO(b/328784766): Consider using arrayvec crate or similar instead of passing download
    // buffer and size separately.
    // The total download buffer.
    download_buffer: &'a mut [u8],
    // Current downloaded data size.
    download_data_size: &'a mut usize,
    /// When available, a trait object `FastbootInfoSend` for sending Fastboot INFO messages.
    fb_info: Option<&'a mut dyn FastbootInfoSend>,
}

impl<'a> FastbootUtils<'a> {
    /// Creates a new instance.
    pub fn new(
        download_buffer: &'a mut [u8],
        download_data_size: &'a mut usize,
        fb_info: Option<&'a mut dyn FastbootInfoSend>,
    ) -> Self {
        Self { download_buffer, download_data_size, fb_info }
    }

    /// Returns the current downloaded data.
    pub fn download_data(&mut self) -> &mut [u8] {
        &mut self.download_buffer[..*self.download_data_size]
    }

    /// Returns the entire download buffer and the size of the download data. The method assumes
    /// that callers will modify the download buffer and therefore will no longer consider the
    /// download data valid, i.e. future calls of FastbootUtils::download_data() will only return
    /// an empty slice.
    pub fn take_download_buffer(&mut self) -> (&mut [u8], usize) {
        let download_data_size = *self.download_data_size;
        *self.download_data_size = 0;
        (self.download_buffer, download_data_size)
    }

    /// Sends a Fastboot INFO message.
    ///
    /// Returns Ok(true) if successful, Ok(false) if INFO messages are not supported in the context
    /// of the current command, error otherwise.
    pub fn info_send(&mut self, msg: &str) -> Result<bool, CommandError> {
        match self.fb_info {
            Some(ref mut send) => send.send(msg).map(|_| true),
            _ => Ok(false),
        }
    }
}

/// `FastbootInfoSender` is an internal type that implements `FastbootInfoSend` with a `Transport`
/// trait object.
struct FastbootInfoSender<'a> {
    transport: &'a mut dyn Transport,
    transport_error: Result<(), TransportError>,
}

impl<'a> FastbootInfoSender<'a> {
    /// Creates an new instance
    fn new(transport: &'a mut dyn Transport) -> Self {
        Self { transport: transport, transport_error: Ok(()) }
    }

    /// Returns the `Self:;transport_error`.
    fn transport_error(&self) -> Result<(), TransportError> {
        self.transport_error
    }
}

impl FastbootInfoSend for FastbootInfoSender<'_> {
    fn send(&mut self, msg: &str) -> Result<(), CommandError> {
        self.transport_error?;
        let mut res = [0u8; MAX_RESPONSE_SIZE];
        self.transport_error = self.transport.send_packet(fastboot_info!(res, "{}", msg));
        Ok(self.transport_error?)
    }
}

/// `UploadBuilder` can be consumed to create an `Uploader` for sending data to the host during
/// handling of command `fastboot get_staged`.
pub struct UploadBuilder<'a> {
    remaining: &'a mut u64,
    // `send` sends a bytes array as fastboot packet.
    send: &'a mut dyn FnMut(&[u8]) -> Result<(), CommandError>,
}

impl<'a> UploadBuilder<'a> {
    /// Consumes the builder to create an `Uploader` to start uploading data.
    pub fn start(self, data_size: u64) -> Result<Uploader<'a>, CommandError> {
        let mut res = [0u8; 16];
        (self.send)(snprintf!(res, "DATA{:08x}", data_size).as_bytes())?;
        *self.remaining = data_size;
        Ok(Uploader { remaining: self.remaining, send: self.send })
    }
}

/// `UploadBuilder` provides APIs for sending data from the device in response to
/// `fastboot get_staged`
pub struct Uploader<'a> {
    remaining: &'a mut u64,
    send: &'a mut dyn FnMut(&[u8]) -> Result<(), CommandError>,
}

impl<'a> Uploader<'a> {
    /// Uploads data. Returns error if accumulative amount exceeds `data_size` passed to
    /// `UploadBuilder::start()`.
    pub fn upload(&mut self, data: &[u8]) -> Result<(), CommandError> {
        *self.remaining = self
            .remaining
            .checked_sub(data.len().try_into().map_err(|_| "")?)
            .ok_or::<CommandError>("".into())?;
        (self.send)(data)
    }
}

/// A helper function that creates an `UploadBuilder` from a `Transport` and runs a closure with
/// it. The helper internally checks that the closure uploads enough data it specifies.
fn with_upload_builder<F, R>(
    transport: &mut impl Transport,
    mut f: F,
) -> Result<Result<R, CommandError>, TransportError>
where
    F: FnMut(UploadBuilder) -> Result<R, CommandError>,
{
    let mut transport_error = Ok(());
    let mut remaining = 0u64;
    let mut send = |data: &[u8]| -> Result<(), CommandError> {
        transport_error?;
        transport_error = transport.send_packet(data);
        Ok(transport_error?)
    };
    let upload_builder = UploadBuilder { remaining: &mut remaining, send: &mut send };
    let res = f(upload_builder);
    transport_error?;
    // Failing to upload enough data should be considered a transport error. Because the remote
    // host will hang as long as the connection is still active.
    match remaining > 0 {
        true => Err(TransportError::NotEnoughUpload),
        _ => Ok(res),
    }
}

pub mod test_utils {
    use crate::{CommandError, UploadBuilder};

    /// Runs a closure with a mock uploader for user implementation to test
    /// `FastbootImplementation::upload()`.
    ///
    /// The mock uploader simply uploads to a user provided buffer.
    ///
    /// Returns the total uploaded size and remaining size.
    pub fn with_mock_upload_builder<F>(buffer: &mut [u8], mut f: F) -> (usize, usize)
    where
        F: FnMut(UploadBuilder),
    {
        let mut remaining = 0u64;
        let mut sent = 0;
        let mut send = |data: &[u8]| -> Result<(), CommandError> {
            // Skips the first 12 bytes "DATAXXXXXXXX" fastboot message.
            match sent == 0 {
                true => {
                    assert_eq!(data.len(), 12);
                    assert!(data.starts_with(b"DATA"));
                    sent += data.len()
                }
                _ => {
                    buffer[sent - 12..][..data.len()].clone_from_slice(data);
                    sent += data.len();
                }
            };
            Ok(())
        };
        f(UploadBuilder { remaining: &mut remaining, send: &mut send });
        (core::cmp::max(sent, 12) - 12, remaining.try_into().unwrap())
    }
}

const MAX_DOWNLOAD_SIZE_NAME: &'static str = "max-download-size";

/// State of the fastboot protocol.
enum ProtocolState {
    Command,
    Download,
}

/// `Fastboot` provides methods for receiving/processing/replying fastboot commands from a
/// transport.
pub struct Fastboot<'a> {
    state: ProtocolState,
    download_buffer: &'a mut [u8],
    downloaded_size: usize,
    total_download_size: usize,
}

impl<'a> Fastboot<'a> {
    /// Creates an instance with a given download buffer.
    pub fn new(download_buffer: &'a mut [u8]) -> Self {
        Self {
            state: ProtocolState::Command,
            download_buffer: download_buffer,
            downloaded_size: 0,
            total_download_size: 0,
        }
    }

    /// Process fastboot command/data from a given transport.
    ///
    /// # Args
    ///
    ///   * `transport`: An implementation of `Transport`
    ///   * `fb_impl`: An implementation of `FastbootImplementation`.
    ///
    /// # Returns
    ///
    ///   The method returns on any errors from calls to `transport` methods.
    pub fn run(
        &mut self,
        transport: &mut impl Transport,
        fb_impl: &mut impl FastbootImplementation,
    ) -> Result<(), TransportError> {
        loop {
            match self.state {
                ProtocolState::Command => {
                    let mut packet = [0u8; MAX_COMMAND_SIZE];
                    let cmd_size = transport.receive_packet(&mut packet[..])?;
                    if cmd_size == 0 {
                        continue;
                    }

                    let mut res = [0u8; MAX_RESPONSE_SIZE];
                    let cmd_str = match from_utf8(&packet[..cmd_size]) {
                        Ok(s) => s,
                        _ => {
                            transport.send_packet(fastboot_fail!(res, "Invalid Command"))?;
                            continue;
                        }
                    };
                    let mut args = cmd_str.split(':');
                    let Some(cmd) = args.next() else {
                        transport.send_packet(fastboot_fail!(res, "No command"))?;
                        continue;
                    };
                    match cmd {
                        "getvar" => self.get_var(args, transport, fb_impl)?,
                        "download" => self.download(args, transport, fb_impl)?,
                        "flash" => self.flash(cmd_str, transport, fb_impl)?,
                        "upload" => self.upload(transport, fb_impl)?,
                        "fetch" => self.fetch(&cmd_str, args, transport, fb_impl)?,
                        _ if cmd_str.starts_with("oem ") => {
                            self.oem(&cmd_str[4..], transport, fb_impl)?
                        }
                        _ => {
                            transport.send_packet(fastboot_fail!(res, "Command not found"))?;
                        }
                    }
                }
                ProtocolState::Download => {
                    let (_, remains) = &mut self.download_buffer[..self.total_download_size]
                        .split_at_mut(self.downloaded_size);
                    match transport.receive_packet(remains) {
                        Ok(size) if size > remains.len() => {
                            let mut res = [0u8; MAX_RESPONSE_SIZE];
                            transport.send_packet(
                                snprintf!(res, "FAILMore data received then expected").as_bytes(),
                            )?;
                            self.total_download_size = 0;
                            self.downloaded_size = 0;
                            self.state = ProtocolState::Command;
                        }
                        Ok(size) => {
                            self.downloaded_size = self.downloaded_size.checked_add(size).unwrap();
                            if self.downloaded_size == self.total_download_size {
                                self.state = ProtocolState::Command;
                                transport.send_packet(OKAY.as_bytes())?;
                            }
                        }
                        Err(e) => {
                            self.total_download_size = 0;
                            self.downloaded_size = 0;
                            return Err(e);
                        }
                    }
                }
            }
        }
    }

    /// Runs a fastboot over TCP session.
    ///
    /// The method performs fastboot over TCP handshake and then call `Self::run(...)`.
    pub fn run_tcp_session(
        &mut self,
        mut tcp_stream: &mut dyn TcpStream,
        fb_impl: &mut impl FastbootImplementation,
    ) -> Result<(), TransportError> {
        let mut handshake = [0u8; 4];
        tcp_stream.write_exact(TCP_HANDSHAKE_MESSAGE)?;
        tcp_stream.read_exact(&mut handshake[..])?;
        match handshake == *TCP_HANDSHAKE_MESSAGE {
            true => self.run(&mut tcp_stream, fb_impl),
            _ => Err(TransportError::InvalidHanshake),
        }
    }

    /// Method for handling "fastboot getvar ..."
    fn get_var(
        &mut self,
        mut args: Split<char>,
        transport: &mut impl Transport,
        fb_impl: &mut impl FastbootImplementation,
    ) -> Result<(), TransportError> {
        let mut res = [0u8; MAX_RESPONSE_SIZE];
        let Some(var) = args.next() else {
            return transport.send_packet(fastboot_fail!(res, "Missing variable"));
        };

        if var == "all" {
            return self.get_var_all(transport, fb_impl);
        } else if var == MAX_DOWNLOAD_SIZE_NAME {
            return transport.send_packet(fastboot_okay!(res, "{:#x}", self.download_buffer.len()));
        }

        let mut val = [0u8; MAX_RESPONSE_SIZE];
        match self.get_var_str(var, args, &mut val[..], transport, fb_impl) {
            Ok(s) => transport.send_packet(fastboot_okay!(res, "{}", s)),
            Err(e) => transport.send_packet(fastboot_fail!(res, "{}", e.to_str())),
        }
    }

    /// A helper for getting the string version of a fastboot variable value.
    fn get_var_str<'s>(
        &mut self,
        var: &str,
        args: Split<char>,
        out: &'s mut [u8],
        transport: &mut impl Transport,
        fb_impl: &mut impl FastbootImplementation,
    ) -> Result<&'s str, CommandError> {
        let mut info_sender = FastbootInfoSender::new(transport);
        let mut utils = self.utils(Some(&mut info_sender));
        fb_impl.get_var_as_str(var, args, out, &mut utils)
    }

    /// A wrapper of `get_var_all()` that first iterates reserved variables.
    fn get_var_all_with_native(
        &mut self,
        fb_impl: &mut impl FastbootImplementation,
        f: &mut dyn FnMut(&str, &[&str], &str) -> Result<(), CommandError>,
    ) -> Result<(), CommandError> {
        // Process the built-in MAX_DOWNLOAD_SIZE_NAME variable.
        let mut size_str = [0u8; 32];
        f(MAX_DOWNLOAD_SIZE_NAME, &[], snprintf!(size_str, "{:#x}", self.download_buffer.len()))?;
        // Don't allow other custom INFO messages because variable values are sent as INFO
        // messages.
        fb_impl.get_var_all(f, &mut self.utils(None))
    }

    /// Method for handling "fastboot getvar all"
    fn get_var_all(
        &mut self,
        transport: &mut impl Transport,
        fb_impl: &mut impl FastbootImplementation,
    ) -> Result<(), TransportError> {
        let mut res = [0u8; MAX_RESPONSE_SIZE];
        let mut transport_error = Ok(());
        let get_res = self.get_var_all_with_native(fb_impl, &mut |name, args, val| {
            let mut formatted_bytes = FormattedBytes::new(&mut res);
            write!(formatted_bytes, "INFO{}", name).unwrap();
            args.iter().for_each(|arg| write!(formatted_bytes, ":{}", arg).unwrap());
            write!(formatted_bytes, ": {}", val).unwrap();
            let size = formatted_bytes.size();
            transport_error = transport.send_packet(&res[..size]);
            Ok(transport_error?)
        });
        transport_error?;
        match get_res {
            Ok(()) => transport.send_packet(fastboot_okay!(res, "")),
            Err(e) => transport.send_packet(fastboot_fail!(res, "{}", e.to_str())),
        }
    }

    /// Method for handling "fastboot download:...".
    fn download(
        &mut self,
        mut args: Split<char>,
        transport: &mut impl Transport,
        _: &mut impl FastbootImplementation,
    ) -> Result<(), TransportError> {
        let mut res = [0u8; MAX_RESPONSE_SIZE];
        let total_download_size = match (|| -> Result<usize, CommandError> {
            usize::try_from(next_arg_u64(&mut args, Err("Not enough argument".into()))?)
                .map_err(|_| "Download size overflow".into())
        })() {
            Err(e) => return transport.send_packet(fastboot_fail!(res, "{}", e.to_str())),
            Ok(v) => v,
        };
        if total_download_size > self.download_buffer.len() {
            return transport.send_packet(fastboot_fail!(res, "Download size is too big"));
        } else if total_download_size == 0 {
            return transport.send_packet(fastboot_fail!(res, "Zero download size"));
        }

        transport.send_packet(snprintf!(res, "DATA{:#x}", total_download_size).as_bytes())?;
        self.total_download_size = total_download_size;
        self.downloaded_size = 0;
        self.state = ProtocolState::Download;
        Ok(())
    }

    /// Method for handling "fastboot flash ...".
    fn flash(
        &mut self,
        cmd: &str,
        transport: &mut impl Transport,
        fb_impl: &mut impl FastbootImplementation,
    ) -> Result<(), TransportError> {
        let mut res = [0u8; MAX_RESPONSE_SIZE];
        match (|| -> Result<(), CommandError> {
            let part =
                cmd.strip_prefix("flash:").ok_or::<CommandError>("Missing partition".into())?;
            fb_impl.flash(part, &mut self.utils(Some(&mut FastbootInfoSender::new(transport))))
        })() {
            Err(e) => transport.send_packet(fastboot_fail!(res, "{}", e.to_str())),
            _ => transport.send_packet(fastboot_okay!(res, "")),
        }
    }

    /// Method for handling "fastboot get_staged ...".
    fn upload(
        &mut self,
        transport: &mut impl Transport,
        fb_impl: &mut impl FastbootImplementation,
    ) -> Result<(), TransportError> {
        let mut res = [0u8; MAX_RESPONSE_SIZE];
        match with_upload_builder(transport, |upload_builder| {
            // No INFO message should be sent during upload.
            let mut utils = self.utils(None);
            fb_impl.upload(upload_builder, &mut utils)
        })? {
            Err(e) => transport.send_packet(fastboot_fail!(res, "{}", e.to_str())),
            _ => transport.send_packet(fastboot_okay!(res, "")),
        }
    }

    /// Method for handling "fastboot fetch ...".
    pub fn fetch(
        &mut self,
        cmd: &str,
        args: Split<char>,
        transport: &mut impl Transport,
        fb_impl: &mut impl FastbootImplementation,
    ) -> Result<(), TransportError> {
        let mut res = [0u8; MAX_RESPONSE_SIZE];
        match with_upload_builder(transport, |upload_builder| -> Result<(), CommandError> {
            let cmd =
                cmd.strip_prefix("fetch:").ok_or::<CommandError>("Missing arguments".into())?;
            if args.clone().count() < 3 {
                return Err("Not enough argments".into());
            }
            // Parses backward. Parses size, offset first and treats the remaining string as
            // partition name. This allows ":" in partition name.
            let mut rev = args.clone().rev();
            let sz = next_arg(&mut rev, Err("Invalid argument".into()))?;
            let off = next_arg(&mut rev, Err("Invalid argument".into()))?;
            let part = &cmd[..cmd.len() - (off.len() + sz.len() + 2)];
            // No INFO message should be sent during upload.
            let mut utils = self.utils(None);
            fb_impl.fetch(part, hex_to_u64(off)?, hex_to_u64(sz)?, upload_builder, &mut utils)
        })? {
            Err(e) => transport.send_packet(fastboot_fail!(res, "{}", e.to_str())),
            _ => transport.send_packet(fastboot_okay!(res, "")),
        }
    }

    /// Method for handling "fastboot oem ...".
    fn oem(
        &mut self,
        cmd: &str,
        transport: &mut impl Transport,
        fb_impl: &mut impl FastbootImplementation,
    ) -> Result<(), TransportError> {
        let mut info_sender = FastbootInfoSender::new(transport);
        let mut utils = self.utils(Some(&mut info_sender));
        let mut oem_out = [0u8; MAX_RESPONSE_SIZE - 4];
        let oem_res = fb_impl.oem(cmd, &mut utils, &mut oem_out[..]);
        info_sender.transport_error()?;
        let mut res = [0u8; MAX_RESPONSE_SIZE];
        match oem_res {
            Ok(msg) => match from_utf8(msg) {
                Ok(s) => transport.send_packet(fastboot_okay!(res, "{}", s)),
                Err(e) => transport.send_packet(fastboot_fail!(res, "Invalid return string {}", e)),
            },
            Err(e) => transport.send_packet(fastboot_fail!(res, "{}", e.to_str())),
        }
    }

    /// Helper method to create an instance of `FastbootUtils`.
    fn utils<'b>(&'b mut self, info: Option<&'b mut dyn FastbootInfoSend>) -> FastbootUtils<'b> {
        FastbootUtils::new(self.download_buffer, &mut self.total_download_size, info.map(|v| v))
    }
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

    pub fn append(&mut self, bytes: &[u8]) -> &mut [u8] {
        let buf = &mut self.0.as_mut()[self.1..];
        // Only write as much as the size of the bytes buffer. Additional write is silently
        // ignored.
        let to_write = core::cmp::min(buf.len(), bytes.len());
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
pub(crate) fn hex_to_u64(s: &str) -> Result<u64, CommandError> {
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
    default: Result<&'a str, CommandError>,
) -> Result<&'a str, CommandError> {
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
    default: Result<u64, CommandError>,
) -> Result<u64, CommandError> {
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
    struct FastbootTest<'a> {
        // A mapping from (variable name, argument) to variable value.
        vars: BTreeMap<(&'static str, &'static [&'static str]), &'static str>,
        flash_cb: Option<&'a mut dyn FnMut(&str, &mut FastbootUtils) -> Result<(), CommandError>>,
        upload_cb: Option<
            &'a mut dyn FnMut(UploadBuilder, &mut FastbootUtils) -> Result<(), CommandError>,
        >,
        fetch_cb: Option<
            &'a mut dyn FnMut(
                &str,
                u64,
                u64,
                UploadBuilder,
                &mut FastbootUtils,
            ) -> Result<(), CommandError>,
        >,
        oem_cb: Option<
            &'a mut dyn FnMut(&str, &mut FastbootUtils, &mut [u8]) -> Result<usize, CommandError>,
        >,
    }

    impl FastbootImplementation for FastbootTest<'_> {
        fn get_var(
            &mut self,
            var: &str,
            args: Split<char>,
            out: &mut [u8],
            _: &mut FastbootUtils,
        ) -> Result<usize, CommandError> {
            let args = args.collect::<Vec<_>>();
            match self.vars.get(&(var, &args[..])) {
                Some(v) => {
                    out[..v.len()].clone_from_slice(v.as_bytes());
                    Ok(v.len())
                }
                _ => Err("Not Found".into()),
            }
        }

        fn get_var_all(
            &mut self,
            f: &mut dyn FnMut(&str, &[&str], &str) -> Result<(), CommandError>,
            _: &mut FastbootUtils,
        ) -> Result<(), CommandError> {
            for ((var, config), value) in &self.vars {
                f(var, config, value)?;
            }
            Ok(())
        }

        fn flash(&mut self, part: &str, utils: &mut FastbootUtils) -> Result<(), CommandError> {
            (self.flash_cb.as_mut().unwrap())(part, utils)
        }

        fn upload(
            &mut self,
            upload_builder: UploadBuilder,
            utils: &mut FastbootUtils,
        ) -> Result<(), CommandError> {
            (self.upload_cb.as_mut().unwrap())(upload_builder, utils)
        }

        fn fetch(
            &mut self,
            part: &str,
            offset: u64,
            size: u64,
            upload_builder: UploadBuilder,
            utils: &mut FastbootUtils,
        ) -> Result<(), CommandError> {
            (self.fetch_cb.as_mut().unwrap())(part, offset, size, upload_builder, utils)
        }

        fn oem<'b>(
            &mut self,
            cmd: &str,
            utils: &mut FastbootUtils,
            res: &'b mut [u8],
        ) -> Result<&'b [u8], CommandError> {
            let sz = (self.oem_cb.as_mut().unwrap())(cmd, utils, res)?;
            Ok(&res[..sz])
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
        fn receive_packet(&mut self, out: &mut [u8]) -> Result<usize, TransportError> {
            match self.in_queue.pop_front() {
                Some(v) => {
                    let size = core::cmp::min(out.len(), v.len());
                    out[..size].clone_from_slice(&v[..size]);
                    // Returns the input length so that we can test bogus download size.
                    Ok(v.len())
                }
                _ => Err(TransportError::Others("No more data")),
            }
        }

        fn send_packet(&mut self, packet: &[u8]) -> Result<(), TransportError> {
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
        fn read_exact(&mut self, out: &mut [u8]) -> Result<(), TransportError> {
            for ele in out {
                *ele = self.in_queue.pop_front().ok_or(TransportError::Others("No more data"))?;
            }
            Ok(())
        }

        fn write_exact(&mut self, data: &[u8]) -> Result<(), TransportError> {
            data.iter().for_each(|v| self.out_queue.push_back(*v));
            Ok(())
        }
    }

    #[test]
    fn test_non_exist_command() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut download_buffer = vec![0u8; 1024];
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut transport = TestTransport::new();
        transport.add_input(b"non_exist");
        let _ = fastboot.run(&mut transport, &mut fastboot_impl);
        assert_eq!(transport.out_queue, [b"FAILCommand not found"]);
    }

    #[test]
    fn test_non_ascii_command_string() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut download_buffer = vec![0u8; 1024];
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut transport = TestTransport::new();
        transport.add_input(b"\xff\xff\xff");
        let _ = fastboot.run(&mut transport, &mut fastboot_impl);
        assert_eq!(transport.out_queue, [b"FAILInvalid Command"]);
    }

    #[test]
    fn test_get_var_max_download_size() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut download_buffer = vec![0u8; 1024];
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut transport = TestTransport::new();
        transport.add_input(b"getvar:max-download-size");
        let _ = fastboot.run(&mut transport, &mut fastboot_impl);
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

        let mut download_buffer = vec![0u8; 1024];
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut transport = TestTransport::new();
        transport.add_input(b"getvar:var_0");
        transport.add_input(b"getvar:var_1:a:b");
        transport.add_input(b"getvar:var_1:c:d");
        transport.add_input(b"getvar:var_1"); // Not Found
        transport.add_input(b"getvar:var_2:e:f");
        transport.add_input(b"getvar:var_3"); // Not Found
        transport.add_input(b"getvar"); // Not Found

        let _ = fastboot.run(&mut transport, &mut fastboot_impl);
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

        let mut download_buffer = vec![0u8; 1024];
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut transport = TestTransport::new();
        transport.add_input(b"getvar:all");
        let _ = fastboot.run(&mut transport, &mut fastboot_impl);
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
        let mut download_buffer = vec![0u8; 1024];
        let download_content: Vec<u8> =
            (0..download_buffer.len()).into_iter().map(|v| v as u8).collect();
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut transport = TestTransport::new();
        // Splits download into two batches.
        let (first, second) = download_content.as_slice().split_at(download_content.len() / 2);
        transport.add_input(format!("download:{:#x}", download_content.len()).as_bytes());
        transport.add_input(first);
        transport.add_input(second);
        let _ = fastboot.run(&mut transport, &mut fastboot_impl);
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([b"DATA0x400".into(), b"OKAY".into(),])
        );
        assert_eq!(download_buffer, download_content);
    }

    #[test]
    fn test_download_not_enough_args() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut download_buffer = vec![0u8; 1024];
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut transport = TestTransport::new();
        transport.add_input(b"download");
        let _ = fastboot.run(&mut transport, &mut fastboot_impl);
        assert_eq!(transport.out_queue, [b"FAILNot enough argument"]);
    }

    #[test]
    fn test_download_invalid_hex_string() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut download_buffer = vec![0u8; 1024];
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut transport = TestTransport::new();
        transport.add_input(b"download:hhh");
        let _ = fastboot.run(&mut transport, &mut fastboot_impl);
        assert_eq!(transport.out_queue.len(), 1);
        assert!(transport.out_queue[0].starts_with(b"FAIL"));
    }

    fn test_download_size(download_buffer_size: usize, download_size: usize, msg: &str) {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut download_buffer = vec![0u8; download_buffer_size];
        let mut transport = TestTransport::new();
        transport.add_input(format!("download:{:#x}", download_size).as_bytes());
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let _ = fastboot.run(&mut transport, &mut fastboot_impl);
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
        let mut download_buffer = vec![0u8; 1024];
        let download_content: Vec<u8> = vec![0u8; download_buffer.len()];
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut transport = TestTransport::new();
        transport.add_input(format!("download:{:#x}", download_content.len() - 1).as_bytes());
        transport.add_input(&download_content[..]);
        // State should be reset to command state.
        transport.add_input(b"getvar:max-download-size");
        let _ = fastboot.run(&mut transport, &mut fastboot_impl);
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([
                b"DATA0x3ff".into(),
                b"FAILMore data received then expected".into(),
                b"OKAY0x400".into(),
            ])
        );
    }

    #[test]
    fn test_oem_cmd() {
        let mut fastboot_impl: FastbootTest = Default::default();
        const DOWNLOAD_BUFFER_LEN: usize = 2048;
        let mut download_buffer = vec![0u8; DOWNLOAD_BUFFER_LEN];
        let download_content: Vec<u8> = (0..1024).into_iter().map(|v| v as u8).collect();
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut transport = TestTransport::new();
        transport.add_input(format!("download:{:#x}", download_content.len()).as_bytes());
        transport.add_input(&download_content[..]);
        transport.add_input(b"oem oem-command");

        let mut oem_cb = |cmd: &str, utils: &mut FastbootUtils, res: &mut [u8]| {
            assert_eq!(cmd, "oem-command");
            assert_eq!(utils.download_buffer.len(), DOWNLOAD_BUFFER_LEN);
            assert_eq!(utils.download_data().to_vec(), download_content);
            assert!(utils.info_send("oem-info-1").unwrap());
            assert!(utils.info_send("oem-info-2").unwrap());
            Ok(snprintf!(res, "oem-return").len())
        };
        fastboot_impl.oem_cb = Some(&mut oem_cb);
        let _ = fastboot.run(&mut transport, &mut fastboot_impl);
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([
                b"DATA0x400".into(),
                b"OKAY".into(),
                b"INFOoem-info-1".into(),
                b"INFOoem-info-2".into(),
                b"OKAYoem-return".into(),
            ])
        );
    }

    #[test]
    fn test_flash() {
        let mut fastboot_impl: FastbootTest = Default::default();
        const DOWNLOAD_BUFFER_LEN: usize = 2048;
        let mut download_buffer = vec![0u8; DOWNLOAD_BUFFER_LEN];
        let download_content: Vec<u8> = (0..1024).into_iter().map(|v| v as u8).collect();
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut transport = TestTransport::new();
        transport.add_input(format!("download:{:#x}", download_content.len()).as_bytes());
        transport.add_input(&download_content[..]);
        transport.add_input(b"flash:boot_a:0::");

        let mut flash_cb = |part: &str, utils: &mut FastbootUtils| {
            assert_eq!(part, "boot_a:0::");
            assert_eq!(utils.download_data().to_vec(), download_content);
            Ok(())
        };
        fastboot_impl.flash_cb = Some(&mut flash_cb);
        let _ = fastboot.run(&mut transport, &mut fastboot_impl);
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([b"DATA0x400".into(), b"OKAY".into(), b"OKAY".into(),])
        );
    }

    #[test]
    fn test_flash_missing_partition() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut fastboot = Fastboot::new(&mut []);
        let mut transport = TestTransport::new();
        transport.add_input(b"flash");
        let mut flash_cb = |_: &str, _: &mut FastbootUtils| Ok(());
        fastboot_impl.flash_cb = Some(&mut flash_cb);
        let _ = fastboot.run(&mut transport, &mut fastboot_impl);
        assert_eq!(transport.out_queue, [b"FAILMissing partition"]);
    }

    #[test]
    fn test_upload() {
        let mut fastboot_impl: FastbootTest = Default::default();
        const DOWNLOAD_BUFFER_LEN: usize = 2048;
        let mut download_buffer = vec![0u8; DOWNLOAD_BUFFER_LEN];
        let download_content: Vec<u8> = (0..1024).into_iter().map(|v| v as u8).collect();
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut transport = TestTransport::new();
        transport.add_input(format!("download:{:#x}", download_content.len()).as_bytes());
        transport.add_input(&download_content[..]);
        transport.add_input(b"upload");

        let mut upload_cb = |upload_builder: UploadBuilder, utils: &mut FastbootUtils| {
            assert_eq!(utils.download_buffer.len(), DOWNLOAD_BUFFER_LEN);
            assert_eq!(utils.download_data().to_vec(), download_content);
            let (download_buffer, download_len) = utils.take_download_buffer();
            let to_send = &mut download_buffer[..download_len];
            let mut uploader = upload_builder.start(u64::try_from(to_send.len()).unwrap()).unwrap();
            uploader.upload(&to_send[..download_len / 2]).unwrap();
            uploader.upload(&to_send[download_len / 2..]).unwrap();
            assert!(!utils.info_send("").unwrap());
            assert_eq!(utils.download_data().len(), 0);
            Ok(())
        };
        fastboot_impl.upload_cb = Some(&mut upload_cb);
        let _ = fastboot.run(&mut transport, &mut fastboot_impl);
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([
                b"DATA0x400".into(),
                b"OKAY".into(),
                b"DATA00000400".into(),
                download_content[..download_content.len() / 2].to_vec(),
                download_content[download_content.len() / 2..].to_vec(),
                b"OKAY".into(),
            ])
        );
    }

    #[test]
    fn test_upload_not_enough_data() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut download_buffer = vec![0u8; 2048];
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut transport = TestTransport::new();
        transport.add_input(b"upload");

        let mut upload_cb = |upload_builder: UploadBuilder, _: &mut FastbootUtils| {
            let mut uploader = upload_builder.start(0x400).unwrap();
            uploader.upload(&[0u8; 0x400 - 1]).unwrap();
            Ok(())
        };
        fastboot_impl.upload_cb = Some(&mut upload_cb);
        assert!(fastboot.run(&mut transport, &mut fastboot_impl).is_err());
    }

    #[test]
    fn test_upload_more_data() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut download_buffer = vec![0u8; 2048];
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut transport = TestTransport::new();
        transport.add_input(b"upload");

        let mut upload_cb = |upload_builder: UploadBuilder, _: &mut FastbootUtils| {
            let mut uploader = upload_builder.start(0x400).unwrap();
            uploader.upload(&[0u8; 0x400 + 1])?;
            Ok(())
        };
        fastboot_impl.upload_cb = Some(&mut upload_cb);
        assert!(fastboot.run(&mut transport, &mut fastboot_impl).is_err());
    }

    #[test]
    fn test_fetch() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut download_buffer = vec![0u8; 2048];
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut transport = TestTransport::new();
        transport.add_input(b"fetch:boot_a:0:::200:400");

        let mut fetch_cb = |part: &str,
                            offset: u64,
                            size: u64,
                            upload_builder: UploadBuilder,
                            _: &mut FastbootUtils| {
            assert_eq!(part, "boot_a:0::");
            assert_eq!(offset, 0x200);
            assert_eq!(size, 0x400);
            let mut uploader = upload_builder.start(size)?;
            uploader.upload(&vec![0u8; size.try_into().unwrap()][..])?;
            Ok(())
        };
        fastboot_impl.fetch_cb = Some(&mut fetch_cb);
        let _ = fastboot.run(&mut transport, &mut fastboot_impl);
        assert_eq!(
            transport.out_queue,
            VecDeque::<Vec<u8>>::from([
                b"DATA00000400".into(),
                [0u8; 0x400].to_vec(),
                b"OKAY".into(),
            ])
        );
    }

    #[test]
    fn test_fetch_invalid_args() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut download_buffer = vec![0u8; 2048];
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut transport = TestTransport::new();
        transport.add_input(b"fetch");
        transport.add_input(b"fetch:");
        transport.add_input(b"fetch:boot_a");
        transport.add_input(b"fetch:boot_a:200");
        transport.add_input(b"fetch:boot_a::400");
        transport.add_input(b"fetch:boot_a::");
        transport.add_input(b"fetch:boot_a:xxx:400");
        transport.add_input(b"fetch:boot_a:200:xxx");
        let mut fetch_cb =
            |_: &str, _: u64, _: u64, _: UploadBuilder, _: &mut FastbootUtils| Ok(());
        fastboot_impl.fetch_cb = Some(&mut fetch_cb);
        let _ = fastboot.run(&mut transport, &mut fastboot_impl);
        assert!(transport.out_queue.iter().all(|v| v.starts_with(b"FAIL")));
    }

    #[test]
    fn test_fastboot_tcp() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut download_buffer = vec![0u8; 1024];
        let download_content: Vec<u8> =
            (0..download_buffer.len()).into_iter().map(|v| v as u8).collect();
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut tcp_stream: TestTcpStream = Default::default();
        tcp_stream.add_input(TCP_HANDSHAKE_MESSAGE);
        // Add two commands and verify both are executed.
        tcp_stream.add_length_prefixed_input(b"getvar:max-download-size");
        tcp_stream.add_length_prefixed_input(
            format!("download:{:#x}", download_content.len()).as_bytes(),
        );
        tcp_stream.add_length_prefixed_input(&download_content[..]);
        let _ = fastboot.run_tcp_session(&mut tcp_stream, &mut fastboot_impl);
        let expected: &[&[u8]] = &[
            b"FB01",
            b"\x00\x00\x00\x00\x00\x00\x00\x09OKAY0x400",
            b"\x00\x00\x00\x00\x00\x00\x00\x09DATA0x400",
            b"\x00\x00\x00\x00\x00\x00\x00\x04OKAY",
        ];
        assert_eq!(tcp_stream.out_queue, VecDeque::from(expected.concat()));
        assert_eq!(download_buffer, download_content);
    }

    #[test]
    fn test_fastboot_tcp_invalid_handshake() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut download_buffer = vec![0u8; 1024];
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut tcp_stream: TestTcpStream = Default::default();
        tcp_stream.add_input(b"ABCD");
        assert_eq!(
            fastboot.run_tcp_session(&mut tcp_stream, &mut fastboot_impl).unwrap_err(),
            TransportError::InvalidHanshake
        );
    }

    #[test]
    fn test_fastboot_tcp_packet_size_exceeds_maximum() {
        let mut fastboot_impl: FastbootTest = Default::default();
        let mut download_buffer = vec![0u8; 1024];
        let mut fastboot = Fastboot::new(&mut download_buffer[..]);
        let mut tcp_stream: TestTcpStream = Default::default();
        tcp_stream.add_input(TCP_HANDSHAKE_MESSAGE);
        tcp_stream.add_input(&(MAX_COMMAND_SIZE + 1).to_be_bytes());
        assert_eq!(
            fastboot.run_tcp_session(&mut tcp_stream, &mut fastboot_impl).unwrap_err(),
            TransportError::PacketSizeExceedMaximum
        );
    }
}
