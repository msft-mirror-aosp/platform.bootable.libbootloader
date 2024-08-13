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

use avb::{IoError, SlotVerifyError};
use efi::EfiError;
use liberror::Error;
use libgbl::composite_enum;
use smoltcp::socket::tcp::{ListenError, RecvError, SendError};
use zbi::ZbiError;

composite_enum! {
    /// A top level error type that consolidates errors from different libraries.
    #[derive(Debug)]
    pub enum GblEfiError {
        AvbIoError(IoError),
        EfiError(EfiError),
        ListenError(ListenError),
        RecvError(RecvError),
        SendError(SendError),
        SlotVerifyError(SlotVerifyError<'static>),
        UnifiedError(Error),
        ZbiError(ZbiError),
    }
}

/// Top level error type.
pub type Result<T> = core::result::Result<T, GblEfiError>;
