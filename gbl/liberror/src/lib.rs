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
    num::ParseIntError,
    str::Utf8Error,
};
use efi_types::{
    defs::EfiStatus,
    status::{EfiError, EfiResult},
};

/// Gpt related errors.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum GptError {
    /// Secondary header is valid, but different from primary.
    DifferentFromPrimary,
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
    /// The block device does not have a valid GUID Partition Table.
    NoGpt,
    /// Number of entries greater than maximum allowed.
    NumberOfEntriesOverflow {
        /// Actual number of entries,
        entries: u32,
        /// Maximum allowed.
        max_allowed: usize,
    },
    /// Two partitions overlap.
    PartitionRangeOverlap {
        /// Previous partition in overlap. (partition index, first, last)
        prev: (usize, u64, u64),
        /// Next partition in overlap. (partition index, first, last)
        next: (usize, u64, u64),
    },
    /// Unexpected GPT entry size.
    UnexpectedEntrySize {
        /// The actual entry size in the GPT header.
        actual: u32,
        /// The expected size.
        expect: usize,
    },
    /// Unexpected GPT header current LBA.
    /// The current LBA must be 1 for the primary GPT, and the last block for the secondary.
    UnexpectedHeaderLba {
        /// The actual current LBA in the GPT header.
        actual: u64,
        /// The expected LBA.
        expect: u64,
    },
    /// Unexpected GPT header size.
    UnexpectedHeaderSize {
        /// The actual header size in the GPT header.
        actual: u32,
        /// The expected size.
        expect: usize,
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
    /// A/B/R error.
    AbrError(abr::Error),
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
    /// OpenDICE error.
    DiceError(opendice::error::DiceError),
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
    /// A mapping to a device does not exist.
    NoMapping,
    /// The device does not contain any medium to perform the operation.
    NoMedia,
    /// The server was not found or did not respond to the request.
    NoResponse,
    /// The requested element (e.g. device, partition, or value) was not found.
    NotFound,
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
    /// Out of range.
    OutOfRange,
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
    /// Exceeds maximum number of partition for verification. The contained value represents the
    /// maximum allowed number of partitions.
    TooManyPartitions(usize),
    /// The remote network endpoint is not addressable.
    Unaddressable,
    /// An unknown, unexpected EFI_STATUS error code was returned,
    UnexpectedEfiError(EfiStatus),
    /// Return from function that is not expected to return.
    UnexpectedReturn,
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

impl From<ParseIntError> for Error {
    fn from(_value: ParseIntError) -> Self {
        Self::InvalidInput
    }
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

impl From<opendice::error::DiceError> for Error {
    fn from(err: opendice::error::DiceError) -> Self {
        Self::DiceError(err)
    }
}

impl From<abr::Error> for Error {
    fn from(err: abr::Error) -> Self {
        Self::AbrError(err)
    }
}

impl From<core::num::TryFromIntError> for Error {
    #[track_caller]
    fn from(err: core::num::TryFromIntError) -> Self {
        Self::ArithmeticOverflow(err.into())
    }
}

impl From<core::char::CharTryFromError> for Error {
    fn from(_: core::char::CharTryFromError) -> Self {
        Self::InvalidInput
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

/// Table mapping between [EfiError] and our [Error] types.
///
/// The purpose of this rather than a `match` statement is that we need to
/// go both ways, and this allows us to do that without writing the large
/// `match` statement twice. However, it does require special-case handling
/// for any error type that holds additional data.
const EFI_ERROR_TO_ERR_TABLE: &[(EfiError, Error)] = &[
    (EfiError::CrcError, Error::BadChecksum),
    (EfiError::Aborted, Error::Aborted),
    (EfiError::AccessDenied, Error::AccessDenied),
    (EfiError::AlreadyStarted, Error::AlreadyStarted),
    (EfiError::BadBufferSize, Error::BadBufferSize),
    (EfiError::CompromisedData, Error::CompromisedData),
    (EfiError::ConnectionFin, Error::Disconnected),
    (EfiError::ConnectionRefused, Error::OperationProhibited),
    (EfiError::ConnectionReset, Error::ConnectionReset),
    (EfiError::DeviceError, Error::DeviceError),
    (EfiError::EndOfFile, Error::EndOfFile),
    (EfiError::EndOfMedia, Error::EndOfMedia),
    (EfiError::HttpError, Error::HttpError),
    (EfiError::IcmpError, Error::IcmpError),
    (EfiError::IncompatibleVersion, Error::UnsupportedVersion),
    (EfiError::InvalidLanguage, Error::InvalidLanguage),
    (EfiError::InvalidParameter, Error::InvalidInput),
    (EfiError::IpAddressConflict, Error::IpAddressConflict),
    (EfiError::LoadError, Error::LoadError),
    (EfiError::MediaChanged, Error::MediaChanged),
    (EfiError::NotFound, Error::NotFound),
    (EfiError::NotReady, Error::NotReady),
    (EfiError::NotStarted, Error::NotStarted),
    (EfiError::NoMapping, Error::NoMapping),
    (EfiError::NoMedia, Error::NoMedia),
    (EfiError::NoResponse, Error::NoResponse),
    (EfiError::OutOfResources, Error::OutOfResources),
    (EfiError::ProtocolError, Error::ProtocolError),
    (EfiError::SecurityViolation, Error::SecurityViolation),
    (EfiError::TftpError, Error::TftpError),
    (EfiError::Timeout, Error::Timeout),
    (EfiError::Unsupported, Error::Unsupported),
    (EfiError::VolumeCorrupted, Error::VolumeCorrupted),
    (EfiError::VolumeFull, Error::VolumeFull),
    (EfiError::WriteProtected, Error::WriteProtected),
];

impl From<EfiError> for Error {
    fn from(e: EfiError) -> Self {
        match e {
            // Special-case handling for `BufferTooSmall` to retain the size.
            EfiError::BufferTooSmall(0) => Error::BufferTooSmall(None),
            EfiError::BufferTooSmall(size) => Error::BufferTooSmall(Some(size)),
            _ => EFI_ERROR_TO_ERR_TABLE
                .iter()
                .find_map(|(v, err)| (*v == e).then_some(*err))
                .unwrap_or(Error::UnexpectedEfiError(e.into())),
        }
    }
}

impl From<Error> for EfiError {
    fn from(e: Error) -> Self {
        match e {
            // Special-case handling for `BufferTooSmall` to retain the size.
            Error::BufferTooSmall(size) => EfiError::BufferTooSmall(size.unwrap_or(0)),
            Error::UnexpectedEfiError(status) => {
                match status.into() {
                    // This indicates an internal error somewhere in GBL, and
                    // it's dangerous to try to guess whether it's actually an
                    // error or not. Panic to be safe.
                    Ok(()) => panic!("UnexpectedEfiError contained EFI_SUCCESS"),
                    // Snap warnings to `EfiError::DeviceError` instead to turn
                    // them into real errors.
                    Err(efi_error) if efi_error.is_warning() => EfiError::DeviceError,
                    Err(efi_error) => efi_error,
                }
            }
            _ => EFI_ERROR_TO_ERR_TABLE
                .iter()
                .find_map(|(err, v)| (*v == e).then_some(*err))
                .unwrap_or(EfiError::DeviceError),
        }
    }
}

impl From<avb::IoError> for Error {
    fn from(value: avb::IoError) -> Self {
        use avb::IoError;

        match value {
            IoError::Oom => Self::OutOfResources,
            IoError::Io => Self::BlockIoError,
            IoError::NoSuchPartition => Self::NotFound,
            IoError::RangeOutsidePartition => Self::OutOfRange,
            IoError::NoSuchValue => Self::InvalidInput,
            IoError::InvalidValueSize => Self::InvalidInput,
            IoError::InsufficientSpace(space) => Self::BufferTooSmall(Some(space)),
            IoError::NotImplemented => Self::Unsupported,
        }
    }
}

/// Maps an EfiStatus to Result<()>.
pub fn efi_status_to_result(e: EfiStatus) -> Result<()> {
    // Convert to `EfiResult` using libefi_types, then from there into our
    // GBL `Result`. Once the Rust protocol wrappers get pushed up to
    // libefi_types, we'll get an `EfiResult` directly and won't have to deal
    // with the raw `EfiStatus` here (b/413021069).
    //
    // This does incur a double-lookup, but it's easier to not have to maintain
    // mappings to both `EfiStatus` and `EfiError`, and the extra lookup time
    // should be negligible.
    EfiResult::from(e).map_err(From::from)
}

/// Maps a Result<()> to EfiStatus.
pub fn result_to_efi_status(res: Result<()>) -> EfiStatus {
    res.map_err(From::from).into()
}

#[cfg(test)]
mod test {
    use super::*;
    use efi_types::defs::EFI_STATUS_DEVICE_ERROR;

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

    #[test]
    fn test_result_to_efi_status_unknown_efi_error_code() {
        assert_eq!(
            result_to_efi_status(Err(Error::UnexpectedEfiError(EfiStatus(0xc000000000000000)))),
            EfiStatus(0xc000000000000000)
        );
    }

    #[test]
    fn test_result_to_efi_status_unknown_non_efi_error_code_map_to_device_error() {
        assert_eq!(
            result_to_efi_status(Err(Error::UnexpectedEfiError(EfiStatus(1)))),
            EFI_STATUS_DEVICE_ERROR
        );
    }
}
