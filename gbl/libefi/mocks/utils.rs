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

//! Mock utils.

use crate::MockEfiEntry;
use core::time::Duration;
use liberror::Result;
use mockall::mock;

mock! {
    /// Mock [efi::utils::Timeout].
    pub Timeout {
        /// Creates a new [MockTimeout].
        pub fn new(efi_entry: &MockEfiEntry, timeout: Duration) -> Result<Self>;
        /// Checks the timeout.
        pub fn check(&self) -> Result<bool>;
        /// Resets the timeout.
        pub fn reset(&self, timeout: Duration) -> Result<()>;
    }
}
/// Map to the libefi name so code under test can just use one name.
pub type Timeout = MockTimeout;
