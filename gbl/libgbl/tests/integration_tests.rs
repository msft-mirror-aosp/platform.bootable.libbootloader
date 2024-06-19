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

use gbl_storage::BlockIoSync;
use gbl_storage_testlib::TestBlockIo;
use libgbl::{BootImages, FuchsiaBootImages, GblBuilder, GblOps, GblOpsError};
use std::{collections::VecDeque, vec::Vec};

extern crate avb_sysdeps;

struct GblTestBlockIo {
    io: TestBlockIo,
    max_gpt_entries: u64,
}

/// `TestGblOps` provides mock implementation of GblOps for integration test.
#[derive(Default)]
struct TestGblOps<'a> {
    block_io: Vec<GblTestBlockIo>,
    console_out: VecDeque<u8>,
    boot_cb: Option<MustUse<&'a mut dyn FnMut(BootImages)>>,
}

impl TestGblOps<'_> {
    /// Adds a new block device.
    pub(crate) fn add_block_device<T: AsRef<[u8]>>(
        &mut self,
        alignment: u64,
        block_size: u64,
        max_gpt_entries: u64,
        data: T,
    ) {
        self.block_io.push(GblTestBlockIo {
            io: TestBlockIo::new(alignment, block_size, data.as_ref().into()),
            max_gpt_entries,
        })
    }
}

impl GblOps for TestGblOps<'_> {
    fn visit_block_devices(
        &mut self,
        f: &mut dyn FnMut(&mut dyn BlockIoSync, u64, u64),
    ) -> Result<(), GblOpsError> {
        for (idx, ele) in self.block_io.iter_mut().enumerate() {
            f(&mut ele.io, idx.try_into().unwrap(), ele.max_gpt_entries);
        }
        Ok(())
    }

    fn console_put_char(&mut self, ch: u8) -> Result<(), GblOpsError> {
        Ok(self.console_out.push_back(ch))
    }

    fn should_stop_in_fastboot(&mut self) -> Result<bool, GblOpsError> {
        Ok(false)
    }

    fn boot(&mut self, boot_images: BootImages) -> Result<(), GblOpsError> {
        Ok((self.boot_cb.as_mut().unwrap().get())(boot_images))
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
        ops.add_block_device(512, 512, 128, include_bytes!("../testdata/zircon_gpt.bin"));
        ops.boot_cb = Some(MustUse::new(&mut boot_cb));
        let mut gbl = GblBuilder::new(&mut ops).build();
        let mut load_buffer = vec![0u8; 64 * 1024];
        let _ = gbl.zircon_load_and_boot(&mut load_buffer[..]);
    }
}
