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

/// Common, universal error type
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// An operation has been aborted. Useful for async or IO operations.
    Aborted,
    /// A checked arithmetic operation has overflowed.
    ArithmeticOverflow(safemath::Error),
    /// Data verification has encountered an invalid checksum.
    BadChecksum,
    /// An operation attempted to access data outside of the valid range.
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
    /// The connected peripheral or network peer has disconnected.
    Disconnected,
    /// x86 memory map error with error code.
    E820MemoryMapCallbackError(i64),
    /// The provided buffer or data structure is invalidly aligned.
    InvalidAlignment,
    /// At least one parameter fails preconditions.
    InvalidInput,
    /// An image required for system boot is missing.
    MissingImage,
    /// A valid Flattened Device Tree was not found.
    NoFdt,
    /// The block device does not have a valid GUID Partition Table.
    NoGpt,
    /// The requested device was not found.
    NotFound,
    /// The default implementation for a trait method has not been overridden.
    NotImplemented,
    /// The provided name does not uniquely describe a partition.
    NotUnique,
    /// Generic permissions failure.
    OperationProhibited,
    /// Catch-all error with optional debugging string.
    Other(Option<&'static str>),
    /// Operation has timed out.
    Timeout,
    /// Data verification has encountered a version number that is not supported.
    UnsupportedVersion,
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

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:#?}", self)
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
