// Copyright 2025, The Android Open Source Project
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

use liberror::Result;

/// Trait for a device-local fastboot-like session.
pub trait LocalSession {
    /// Updates the context of the local session.
    /// Polls inputs, updates graphics, and so forth.
    fn update(&self, buf: &mut [u8]) -> Result<usize>;
}
