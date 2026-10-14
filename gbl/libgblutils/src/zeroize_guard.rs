// Copyright 2026, The Android Open Source Project
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

//! RAII guard that zeroizes memory on drop.

use core::ops::{Deref, DerefMut};
use zeroize::Zeroize;

/// A RAII guard wrapping a mutable byte slice that zeroizes its target on drop
/// unless explicitly defused.
pub struct ZeroizeGuard<'a> {
    val: &'a mut [u8],
    defused: bool,
}

impl<'a> ZeroizeGuard<'a> {
    /// Creates a new guard that will zeroize `val` on drop.
    pub fn new(val: &'a mut [u8]) -> Self {
        Self { val, defused: false }
    }

    /// Disarms the guard so `val` is not zeroized on drop.
    pub fn defuse(&mut self) {
        self.defused = true;
    }
}

impl Drop for ZeroizeGuard<'_> {
    fn drop(&mut self) {
        if !self.defused {
            self.val.zeroize();
            #[cfg(target_arch = "aarch64")]
            crate::aarch64::flush_dcache_buffer(self.val);
        }
    }
}

impl Deref for ZeroizeGuard<'_> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.val
    }
}

impl DerefMut for ZeroizeGuard<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.val
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_zeroize_guard() {
        let mut buf = [0x5au8; 32];
        {
            let mut guard = ZeroizeGuard::new(&mut buf[..]);
            assert_eq!(guard[0], 0x5a);
            guard[0] = 0x42;
        }
        assert_eq!(buf, [0u8; 32]);
    }

    #[test]
    fn test_defuse_prevents_zeroize() {
        let mut buf = [0x5au8; 32];
        {
            let mut guard = ZeroizeGuard::new(&mut buf[..]);
            guard[0] = 0x42;
            guard.defuse();
        }
        assert_eq!(buf[0], 0x42);
        assert_eq!(buf[1], 0x5a);
    }
}
