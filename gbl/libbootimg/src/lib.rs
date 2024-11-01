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

//! GBL build wrapper for the Android boot image library:
//! https://cs.android.com/android/platform/superproject/main/+/main:system/tools/mkbootimg/rust/.

#![cfg_attr(not(test), no_std)]

#[rustfmt::skip]
mod bootimg;
pub use bootimg::*;
pub use bootimg_bindgen as defs;

use liberror::Error;

impl From<ImageError> for Error {
    fn from(err: ImageError) -> Error {
        match err {
            ImageError::BufferTooSmall => Error::BufferTooSmall(None),
            ImageError::BadMagic => Error::BadMagic,
            ImageError::UnexpectedVersion => Error::UnsupportedVersion,
            _ => Error::Other(None),
        }
    }
}
