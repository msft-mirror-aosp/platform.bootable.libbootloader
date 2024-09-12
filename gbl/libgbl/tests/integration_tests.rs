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

use libgbl::{BootImages, FuchsiaBootImages, Gbl, GblOps, GblOpsError};
use std::{
    collections::{BTreeMap, VecDeque},
    vec::Vec,
};

extern crate avb_sysdeps;

/// `TestGblOps` provides mock implementation of GblOps for integration test.
#[derive(Default)]
struct TestGblOps<'a> {
    console_out: VecDeque<u8>,
    boot_cb: Option<MustUse<&'a mut dyn FnMut(BootImages)>>,
    storage: BTreeMap<&'static str, Vec<u8>>,
}

impl GblOps for TestGblOps<'_> {
    fn console_put_char(&mut self, ch: u8) -> Result<(), GblOpsError> {
        Ok(self.console_out.push_back(ch))
    }

    fn should_stop_in_fastboot(&mut self) -> Result<bool, GblOpsError> {
        Ok(false)
    }

    fn boot(&mut self, boot_images: BootImages) -> Result<(), GblOpsError> {
        Ok((self.boot_cb.as_mut().unwrap().get())(boot_images))
    }

    async fn read_from_partition(
        &mut self,
        part: &str,
        off: u64,
        out: &mut [u8],
    ) -> Result<(), GblOpsError> {
        match self.storage.get_mut(part) {
            Some(v) => Ok(out.clone_from_slice(&v[off.try_into().unwrap()..][..out.len()])),
            _ => Err(GblOpsError(Some("Test: No such partition"))),
        }
    }

    async fn write_to_partition(
        &mut self,
        part: &str,
        off: u64,
        data: &mut [u8],
    ) -> Result<(), GblOpsError> {
        match self.storage.get_mut(part) {
            Some(v) => Ok(v[off.try_into().unwrap()..][..data.len()].clone_from_slice(data)),
            _ => Err(GblOpsError(Some("Test: No such partition"))),
        }
    }

    fn partition_size(&mut self, part: &str) -> Result<Option<usize>, GblOpsError> {
        Ok(self.storage.get_mut(part).map(|v| v.len()))
    }
}

/// `MustUse` wraps an object and checks that it is accessed at least once before it's dropped.
/// In this integration test, it is mainly used to check that test provided ops callbacks are run.
struct MustUse<T: ?Sized> {
    used: bool,
    val: T,
}

impl<T: ?Sized> MustUse<T> {
    /// Create a new instance.
    fn new(val: T) -> Self
    where
        T: Sized,
    {
        Self { used: false, val: val }
    }

    /// Returns a mutable reference to the object.
    fn get(&mut self) -> &mut T {
        self.used = true;
        &mut self.val
    }
}

impl<T: ?Sized> Drop for MustUse<T> {
    fn drop(&mut self) {
        assert!(self.used)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zircon_load_and_boot() {
        // TODO(b/334962583): Invocation test only. Update this test once
        // `Gbl::zircon_load_and_boot()` is implemented.
        let mut boot_cb = |boot_images: BootImages| {
            let BootImages::Fuchsia(FuchsiaBootImages { zbi_kernel, zbi_items }) = boot_images
            else {
                panic!("Wrong image type");
            };
            assert_eq!(zbi_kernel, include_bytes!("../testdata/zircon_a.bin"));
            assert_eq!(zbi_items, []);
        };
        let mut ops: TestGblOps = Default::default();
        ops.storage =
            BTreeMap::from([("zircon_a", include_bytes!("../testdata/zircon_a.bin").to_vec())]);
        ops.boot_cb = Some(MustUse::new(&mut boot_cb));
        let mut gbl = Gbl::new(&mut ops);
        let mut load_buffer = vec![0u8; 64 * 1024];
        let _ = gbl.zircon_load_and_boot(&mut load_buffer[..]);
    }
}
