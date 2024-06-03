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
use boot::BootError;
use bootconfig::BootConfigError;
use bootimg::ImageError;
use efi::EfiError;
use fastboot::TransportError;
use fdt::FdtError;
use gbl_storage::StorageError;
use libgbl::composite_enum;
use misc::BcbError;
use smoltcp::socket::tcp::{ListenError, RecvError, SendError};
use zbi::ZbiError;

/// Error types for EFI application.
#[derive(Debug)]
pub enum EfiAppError {
    ArithmeticOverflow,
    BufferAlignment,
    BufferTooSmall,
    InvalidInput,
    InvalidString,
    NoFdt,
    NotFound,
    NoZbiImage,
    PeerClosed,
    Timeout,
    Unsupported,
}

composite_enum! {
    /// A top level error type that consolidates errors from different libraries.
    #[derive(Debug)]
    pub enum GblEfiError {
        AvbIoError(IoError),
        BcbError(BcbError),
        BootConfigError(BootConfigError),
        BootError(BootError),
        EfiAppError(EfiAppError),
        EfiError(EfiError),
        FdtError(FdtError),
        ImageError(ImageError),
        ListenError(ListenError),
        RecvError(RecvError),
        SendError(SendError),
        SlotVerifyError(SlotVerifyError<'static>),
        StorageError(StorageError),
        TransportError(TransportError),
        ZbiError(ZbiError),
    }
}

/// Top level error type.
pub type Result<T> = core::result::Result<T, GblEfiError>;
