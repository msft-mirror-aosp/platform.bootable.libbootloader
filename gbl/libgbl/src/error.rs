// Copyright 2023, The Android Open Source Project
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

//! Error types used in libgbl.

use core::fmt::{Debug, Display, Formatter};

/// Helper type GBL functions will return.
pub type Result<T> = core::result::Result<T, Error>;

#[derive(Debug, PartialEq)]
/// Error values that can be returned by function in this library
pub enum Error {
    /// Generic error
    Error,
    /// Missing all images required to boot system
    MissingImage,
    /// Functionality is not implemented
    NotImplemented,
    /// Some combination of parameters and global state prohibits the operation
    OperationProhibited,
}

// Unfortunately thiserror is not available in `no_std` world.
// Thus `Display` implementation is required.
impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let str = match self {
            Error::Error => "Generic error",
            Error::MissingImage => "Missing image required to boot system",
            Error::NotImplemented => "Functionality is not implemented",
            Error::OperationProhibited => "Operation is prohibited",
        };
        write!(f, "{str}")
    }
}
