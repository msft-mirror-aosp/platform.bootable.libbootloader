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

use core::fmt;
use core::fmt::Debug;

// smoltcp uses an old version of bitflag (1.0). The one imported at Android is newer and does not
// provide Copy/Clone/Debug/PartialEq/Eq trait implementation by default. Thus we need to add the
// implementation here.

use crate::wire::{NdiscNeighborFlags, NdiscPrefixInfoFlags, NdiscRouterFlags};

macro_rules! bitflags_trait {
    ($name:ident) => {
        impl Copy for $name {}

        impl Clone for $name {
            fn clone(&self) -> $name {
                *self
            }
        }

        impl Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                Debug::fmt(&self.bits(), f)
            }
        }

        impl PartialEq for $name {
            fn eq(&self, other: &Self) -> bool {
                PartialEq::eq(&self.bits(), &other.bits())
            }
        }

        impl Eq for $name {}
    };
}

bitflags_trait! {NdiscNeighborFlags}
bitflags_trait! {NdiscRouterFlags}
bitflags_trait! {NdiscPrefixInfoFlags}
