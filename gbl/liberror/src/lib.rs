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

//! Unified error type library
//!
//! This crate defines a common error type for all of GBL.
//! It is intended to reduce conversion boilerplate and to make
//! the various GBL libraries interoperate more cleanly.
//!
//! Because of its intended broad application, certain error types will
//! be highly specific to particular libraries.
//! More specific errors can be useful when writing unit tests or when defining
//! APIs that third party code may interact with.
//! It's a judgement call whether a new variant should be added,
//! but if possible try to use an existing variant.
//!
//! It is a further judgement call whether a new variant should wrap a payload.
//! The rule of thumb is that a payload requires one of the following conditions:
//! 1) The error will be logged and the payload will help with debugging.
//! 2) The error is transient or retriable, and the payload helps with the retry.
//!
//! New error variants should be inserted alphabetically.

#![cfg_attr(not(any(test, android_dylib)), no_std)]

use core::{
    ffi::{FromBytesUntilNulError, FromBytesWithNulError},
    str::Utf8Error,
};

use efi_types as efi;

/// Gpt related errors.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum GptError {
    /// Disk size is not enough to accommodate maximum allowed entries.
    DiskTooSmall,
    /// GPT entries buffer is too small for the expected number of entries.
    EntriesTruncated,
    /// GPT header CRC is not correct.
    IncorrectHeaderCrc,
    /// GPT header MAGIC is not correct.
    IncorrectMagic(u64),
    /// GPT entries CRC doesn't match.
    IncorrectEntriesCrc,
    /// Invalid first and last usable block in the GPT header.
    InvalidFirstLastUsableBlock {
        /// The value of first usable block in the GPT header.
        first: u64,
        /// The value of last usable block in the GPT header.
        last: u64,
        /// Expected range inclusive.
        range: (u64, u64),
    },
    /// Partition range is invalid.
    InvalidPartitionRange {
        /// Partition index (1-based).
        idx: usize,
        /// Range of the partition, inclusive.
        part_range: (u64, u64),
        /// Range of usable block, inclusive.
        usable_range: (u64, u64),
    },
    /// Invalid start block for primary GPT entries.
    InvalidPrimaryEntriesStart {
        /// The entry start block value.
        value: u64,
        /// Expected range.
        expect_range: (u64, u64),
    },
    /// Invalid start block for secondary GPT entries.
    InvalidSecondaryEntriesStart {
        /// The entry start block value.
        value: u64,
        /// Expected range.
        expect_range: (u64, u64),
    },
    /// Number of entries greater than maximum allowed.
    NumberOfEntriesOverflow {
        /// Actual number of entries,
        entries: u32,
        /// Maximum allowed.
        max_allowed: u64,
    },
    /// Unexpected GPT header size.
    UnexpectedEntrySize {
        /// The actual entry size in the GPT header.
        actual: u32,
        /// The expected size.
        expect: usize,
    },
    /// Unexpected GPT header size.
    UnexpectedHeaderSize {
        /// The actual header size in the GPT header.
        actual: u32,
        /// The expected size.
        expect: usize,
    },
    /// Zero partition type GUID.
    ZeroPartitionTypeGUID {
        /// Partition index (1-based).
        idx: usize,
    },
    /// Zero partition unique GUID.
    ZeroPartitionUniqueGUID {
        /// Partition index (1-based).
        idx: usize,
    },
}

/// Common, universal error type
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// An operation has been aborted. Useful for async or IO operations.
    Aborted,
    /// Access was denied.
    AccessDenied,
    /// The protocol has already been started.
    AlreadyStarted,
    /// A checked arithmetic operation has overflowed.
    ArithmeticOverflow(safemath::Error),
    /// The buffer was not the proper size for the request (different from BufferTooSmall).
    BadBufferSize,
    /// Data verification has encountered an invalid checksum.
    BadChecksum,
    /// An operation attempted to access data outside of the valid range.
    /// Includes the problematic index.
    BadIndex(usize),
    /// Data verification has encountered an invalid magic number.
    BadMagic,
    /// Generic BlockIO error.
    BlockIoError,
    /// Generic boot failure has occurred.
    BootFailed,
    /// Buffers provided by third party code overlap.
    BufferOverlap,
    /// The provided buffer is too small.
    /// If Some(n), provides the minimum required buffer size.
    BufferTooSmall(Option<usize>),
    /// The security status of the data is unknown or compromised
    /// and the data must be updated or replaced to restore a valid security status.
    CompromisedData,
    /// The remote peer has reset the network connection.
    ConnectionReset,
    /// A relevant device encountered an error.
    DeviceError,
    /// The connected peripheral or network peer has disconnected.
    Disconnected,
    /// The end of the file was reached.
    EndOfFile,
    /// Beginning or end of media was reached
    EndOfMedia,
    /// A polled operation has finished
    Finished,
    /// GPT related errors.
    GptError(GptError),
    /// A HTTP error occurred during a network operation.
    HttpError,
    /// An ICMP error occurred during a network operation.
    IcmpError,
    /// The provided buffer or data structure is invalidly aligned.
    InvalidAlignment,
    /// A connected agent failed a multi-stage handshake.
    InvalidHandshake,
    /// At least one parameter fails preconditions.
    InvalidInput,
    /// The language specified was invalid.
    InvalidLanguage,
    /// A state machine has entered an invalid state.
    InvalidState,
    /// There was a conflict in IP address allocation.
    IpAddressConflict,
    /// Image failed to load
    LoadError,
    /// The medium in the device has changed since the last access.
    MediaChanged,
    /// Memory map error with error code.
    MemoryMapCallbackError(i64),
    /// An image required for system boot is missing.
    MissingImage,
    /// A valid Flattened Device Tree was not found.
    NoFdt,
    /// The block device does not have a valid GUID Partition Table.
    NoGpt,
    /// A mapping to a device does not exist.
    NoMapping,
    /// The device does not contain any medium to perform the operation.
    NoMedia,
    /// The server was not found or did not respond to the request.
    NoResponse,
    /// The requested element (e.g. device, partition, or value) was not found.
    NotFound,
    /// The default implementation for a trait method has not been overridden.
    NotImplemented,
    /// The polled device or future is not ready.
    NotReady,
    /// The protocol has not been started.
    NotStarted,
    /// The provided name does not uniquely describe a partition.
    NotUnique,
    /// Generic permissions failure.
    OperationProhibited,
    /// Catch-all error with optional debugging string.
    Other(Option<&'static str>),
    /// A resource has run out.
    OutOfResources,
    /// A protocol error occurred during the network operation.
    ProtocolError,
    /// The function was not performed due to a security violation.
    SecurityViolation,
    /// A TFTP error occurred during a network operation.
    TftpError,
    /// Operation has timed out.
    Timeout,
    /// The remote network endpoint is not addressable.
    Unaddressable,
    /// An unknown, unexpected EFI_STATUS error code was returned,
    UnexpectedEfiError(efi::EfiStatus),
    /// Operation is unsupported
    Unsupported,
    /// Data verification has encountered a version number that is not supported.
    UnsupportedVersion,
    /// An inconstancy was detected on the file system causing the operating to fail.
    VolumeCorrupted,
    /// There is no more space on the file system.
    VolumeFull,
    /// The device cannot be written to.
    WriteProtected,
}

impl From<Option<&'static str>> for Error {
    fn from(val: Option<&'static str>) -> Self {
        Self::Other(val)
    }
}

impl From<&'static str> for Error {
    fn from(val: &'static str) -> Self {
        Self::Other(Some(val))
    }
}

impl From<safemath::Error> for Error {
    fn from(err: safemath::Error) -> Self {
        Self::ArithmeticOverflow(err)
    }
}

impl From<core::num::TryFromIntError> for Error {
    #[track_caller]
    fn from(err: core::num::TryFromIntError) -> Self {
        Self::ArithmeticOverflow(err.into())
    }
}

impl From<FromBytesUntilNulError> for Error {
    fn from(_: FromBytesUntilNulError) -> Self {
        Self::InvalidInput
    }
}

impl From<FromBytesWithNulError> for Error {
    fn from(_: FromBytesWithNulError) -> Self {
        Self::InvalidInput
    }
}

impl From<Utf8Error> for Error {
    fn from(_: Utf8Error) -> Self {
        Self::InvalidInput
    }
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:#?}", self)
    }
}

impl From<core::fmt::Error> for Error {
    fn from(_: core::fmt::Error) -> Self {
        Self::Unsupported
    }
}

/// Helper type alias.
pub type Result<T> = core::result::Result<T, Error>;

/// Workaround for orphan rule.
pub fn efi_status_to_result(e: efi::EfiStatus) -> Result<()> {
    match e {
        efi::EFI_STATUS_SUCCESS => Ok(()),
        efi::EFI_STATUS_CRC_ERROR => Err(Error::BadChecksum),
        efi::EFI_STATUS_ABORTED => Err(Error::Aborted),
        efi::EFI_STATUS_ACCESS_DENIED => Err(Error::AccessDenied),
        efi::EFI_STATUS_ALREADY_STARTED => Err(Error::AlreadyStarted),
        efi::EFI_STATUS_BAD_BUFFER_SIZE => Err(Error::BadBufferSize),
        efi::EFI_STATUS_BUFFER_TOO_SMALL => Err(Error::BufferTooSmall(None)),
        efi::EFI_STATUS_COMPROMISED_DATA => Err(Error::CompromisedData),
        efi::EFI_STATUS_CONNECTION_FIN => Err(Error::Disconnected),
        efi::EFI_STATUS_CONNECTION_REFUSED => Err(Error::OperationProhibited),
        efi::EFI_STATUS_CONNECTION_RESET => Err(Error::ConnectionReset),
        efi::EFI_STATUS_DEVICE_ERROR => Err(Error::DeviceError),
        efi::EFI_STATUS_END_OF_FILE => Err(Error::EndOfFile),
        efi::EFI_STATUS_END_OF_MEDIA => Err(Error::EndOfMedia),
        efi::EFI_STATUS_HTTP_ERROR => Err(Error::HttpError),
        efi::EFI_STATUS_ICMP_ERROR => Err(Error::IcmpError),
        efi::EFI_STATUS_INCOMPATIBLE_VERSION => Err(Error::UnsupportedVersion),
        efi::EFI_STATUS_INVALID_LANGUAGE => Err(Error::InvalidLanguage),
        efi::EFI_STATUS_INVALID_PARAMETER => Err(Error::InvalidInput),
        efi::EFI_STATUS_IP_ADDRESS_CONFLICT => Err(Error::IpAddressConflict),
        efi::EFI_STATUS_LOAD_ERROR => Err(Error::LoadError),
        efi::EFI_STATUS_MEDIA_CHANGED => Err(Error::MediaChanged),
        efi::EFI_STATUS_NOT_FOUND => Err(Error::NotFound),
        efi::EFI_STATUS_NOT_READY => Err(Error::NotReady),
        efi::EFI_STATUS_NOT_STARTED => Err(Error::NotStarted),
        efi::EFI_STATUS_NO_MAPPING => Err(Error::NoMapping),
        efi::EFI_STATUS_NO_MEDIA => Err(Error::NoMedia),
        efi::EFI_STATUS_NO_RESPONSE => Err(Error::NoResponse),
        efi::EFI_STATUS_OUT_OF_RESOURCES => Err(Error::OutOfResources),
        efi::EFI_STATUS_PROTOCOL_ERROR => Err(Error::ProtocolError),
        efi::EFI_STATUS_SECURITY_VIOLATION => Err(Error::SecurityViolation),
        efi::EFI_STATUS_TFTP_ERROR => Err(Error::TftpError),
        efi::EFI_STATUS_TIMEOUT => Err(Error::Timeout),
        efi::EFI_STATUS_UNSUPPORTED => Err(Error::Unsupported),
        efi::EFI_STATUS_VOLUME_CORRUPTED => Err(Error::VolumeCorrupted),
        efi::EFI_STATUS_VOLUME_FULL => Err(Error::VolumeFull),
        efi::EFI_STATUS_WRITE_PROTECTED => Err(Error::WriteProtected),
        // The UEFI spec reserves part of the error space for
        // OEM defined errors and warnings.
        // We can't know in advance what these are or what they mean,
        // so just preserve them as is.
        e => Err(Error::UnexpectedEfiError(e)),
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_from_safemath_error() {
        let n = u8::try_from(safemath::SafeNum::ZERO - 1).unwrap_err();
        let _e: Error = n.into();
    }

    #[test]
    fn test_from_str() {
        let _e: Error = "error string".into();
    }

    #[test]
    fn test_from_str_option() {
        let _e: Error = Some("error string").into();
        let n: Option<&str> = None;
        let _e2: Error = n.into();
    }
}
