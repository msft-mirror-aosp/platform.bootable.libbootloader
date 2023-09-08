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

//! # Generic Boot Loader (gbl) Library
//!
//! TODO: documentation.

// This code is intended for use in bootloaders that typically will not support
// the Rust standard library
#![cfg_attr(not(test), no_std)]

// Adding ZBI library usage to check dependencies
extern crate zbi;

/// Placeholder code to get a build rule and tests in place.
pub fn foo() -> u32 {
    42
}

/// Placeholder code to check `zbi` lib dependencies.
pub fn bar() -> usize {
    zbi::ZBI_ALIGNMENT_USIZE
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_foo() {
        assert_eq!(foo(), 42);
    }

    #[test]
    fn test_bar() {
        assert_eq!(bar(), 8);
    }
}
