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

//! Gbl AVB state (version, color, etc).

use core::fmt::{Display, Formatter};

/// https://source.android.com/docs/security/features/verifiedboot/boot-flow#communicating-verified-boot-state-to-users
#[derive(Clone, Copy, PartialEq)]
pub enum BootStateColor {
    /// Success .
    Green,
    /// Success but custom key is used.
    Yellow,
    /// Device is unlocked.
    Orange,
    /// Dm-verity is corrupted.
    RedEio,
    /// No valid OS found.
    Red,
}

/// To use in bootconfig.
impl Display for BootStateColor {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        f.write_str(match self {
            BootStateColor::Green => "green",
            BootStateColor::Yellow => "yellow",
            BootStateColor::Orange => "orange",
            BootStateColor::RedEio => "red_eio",
            BootStateColor::Red => "red",
        })
    }
}
