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

use avb::{DescriptorError, IoError, SlotVerifyError};
use core::fmt::{Debug, Display, Formatter};

/// A helper macro for declaring a composite enum type that simply wraps other types as entries.
/// It auto-generate `From<...>` implementation for each entry type. The type for each entry must
/// be different from each other. i.e.:
///
/// ```rust
///   composite_enum! {
///       pub enum MyEnum {
///           Usize(usize),
///           I64(i64),
///       }
///   }
/// ```
///
/// expands to
///
/// ```rust
///   pub enum MyEnum {
///       Usize(usize),
///       I64(i64),
///   }
///
///   impl From<usize> for MyEnum {
///       fn from(ent: usize) -> MyEnum {
///           MyEnum::Usize(ent)
///       }
///   }
///
///   impl From<i64> for MyEnum {
///       fn from(ent: i64) -> MyEnum {
///           MyEnum::I64(ent)
///       }
///   }
/// ```
#[macro_export]
macro_rules! composite_enum {
    (
        $(#[$outer:meta])*
        $vis:vis enum $name:ident {
            $(
                $(#[$inner:ident $($args:tt)*])*
                $ent:ident($ent_t:ty)
            ),*
            $(,)*
        }
    ) => {
        #[allow(missing_docs)]
        // Copy over enum declaration as it is.
        $(#[$outer])*
        $vis enum $name {
            $(
                $(#[$inner $($args)*])*
                $ent($ent_t)
            ),*
        }

        // Generate `From<...>` implementation.
        composite_enum!{$name,  $($ent($ent_t)),*}
    };
    // `From<>` implementation generation. Base case.
    ($name:ident, $ent:ident($ent_t:ty)) => {
        impl From<$ent_t> for $name {
            fn from(ent: $ent_t) -> $name {
                $name::$ent(ent)
            }
        }
    };
    // `From<>` implementation generation. Recursive case.
    ($name:ident, $ent:ident($ent_t:ty), $($next:ident($next_t:ty)),+) => {
        composite_enum!{$name, $ent($ent_t)}
        composite_enum!{$name, $($next($next_t)),*}
    };
}

composite_enum! {
    /// Top level error type that integrates errors from various dependency libraries.
    #[derive(Debug, PartialEq, Eq)]
    pub enum IntegrationError {
        /// Failed to get descriptor from AvbMeta
        AvbDescriptorError(DescriptorError),
        AvbIoError(IoError),
        /// Avb slot verification failed.
        /// SlotVerifyError is used without verify data.
        AvbSlotVerifyError(SlotVerifyError<'static>),
        UnificationError(liberror::Error),
        ZbiError(zbi::ZbiError),
    }
}

impl Display for IntegrationError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// Helper type GBL functions will return.
pub type Result<T> = core::result::Result<T, IntegrationError>;
