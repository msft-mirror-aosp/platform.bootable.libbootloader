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

//! GblOps trait that defines GBL callbacks.
//!
#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(test)]
extern crate static_assertions;

use crate::error::{Error, Result as GblResult};
#[cfg(feature = "alloc")]
use alloc::ffi::CString;
use core::{
    fmt::{Debug, Write},
    result::Result,
};
use gbl_storage::{
    required_scratch_size, AsBlockDevice, AsMultiBlockDevices, BlockDevice, BlockIo,
};
use safemath::SafeNum;

use super::slots;

/// `AndroidBootImages` contains references to loaded images for booting Android.
pub struct AndroidBootImages<'a> {
    pub kernel: &'a mut [u8],
    pub ramdisk: &'a mut [u8],
    pub fdt: &'a mut [u8],
}

/// `FuchsiaBootImages` contains references to loaded images for booting Zircon.
pub struct FuchsiaBootImages<'a> {
    pub zbi_kernel: &'a mut [u8],
    pub zbi_items: &'a mut [u8],
}

/// `BootImages` contains images for booting Android/Zircon kernel.
pub enum BootImages<'a> {
    Android(AndroidBootImages<'a>),
    Fuchsia(FuchsiaBootImages<'a>),
}

/// `GblOpsError` is the error type returned by required methods in `GblOps`.
#[derive(Default, Debug, PartialEq, Eq)]
pub struct GblOpsError(Option<&'static str>);

// https://stackoverflow.com/questions/41081240/idiomatic-callbacks-in-rust
// should we use traits for this? or optional/box FnMut?
//
/* TODO: b/312612203 - needed callbacks:
missing:
- validate_public_key_for_partition: None,
- key management => atx extension in callback =>  atx_ops: ptr::null_mut(), // support optional ATX.
*/
/// Trait that defines callbacks that can be provided to Gbl.
pub trait GblOps {
    /// Iterates block devices on the platform.
    ///
    /// For each block device, implementation should call `f` with its 1) `BlockIo` trait
    /// implementation, 2) a unique u64 ID and 3) maximum number of gpt entries. If the maximum
    /// entries is 0, it is considered that the block should not use GPT.
    ///
    /// The list of block devices and visit order should remain the same for the life time of the
    /// object that implements this trait. If this can not be met due to media change, error should
    /// be returned. Dynamic media change is not supported for now.
    fn visit_block_devices(
        &mut self,
        f: &mut dyn FnMut(&mut dyn BlockIo, u64, u64),
    ) -> Result<(), GblOpsError>;

    /// Prints a ASCII character to the platform console.
    fn console_put_char(&mut self, ch: u8) -> Result<(), GblOpsError>;

    /// This method can be used to implement platform specific mechanism for deciding whether boot
    /// should abort and enter Fastboot mode.
    fn should_stop_in_fastboot(&mut self) -> Result<bool, GblOpsError>;

    /// Platform specific kernel boot implementation.
    ///
    /// Implementation is not expected to return on success.
    fn boot(&mut self, boot_images: BootImages) -> Result<(), GblOpsError>;

    // TODO(b/334962570): figure out how to plumb ops-provided hash implementations into
    // libavb. The tricky part is that libavb hashing APIs are global with no way to directly
    // correlate the implementation to a particular [GblOps] object, so we'll probably have to
    // create a [Context] ahead of time and store it globally for the hashing APIs to access.
    // However this would mean that [Context] must be a standalone object and cannot hold a
    // reference to [GblOps], which may restrict implementations.
    // fn new_digest(&self) -> Option<Self::Context>;

    /// Callback for when fastboot mode is requested.
    // Nevertype could be used here when it is stable https://github.com/serde-rs/serde/issues/812
    fn do_fastboot<B: gbl_storage::AsBlockDevice>(
        &self,
        cursor: &mut slots::Cursor<B, impl slots::Manager>,
    ) -> GblResult<()> {
        Err(Error::NotImplemented.into())
    }

    /// TODO: b/312607649 - placeholder interface for Gbl specific callbacks that uses alloc.
    #[cfg(feature = "alloc")]
    fn gbl_alloc_extra_action(&mut self, s: &str) -> GblResult<()> {
        let _c_string = CString::new(s);
        Err(Error::NotImplemented.into())
    }

    /// Load and initialize a slot manager and return a cursor over the manager on success.
    fn load_slot_interface<'b, B: gbl_storage::AsBlockDevice, M: slots::Manager>(
        &mut self,
        block_device: &'b mut B,
        boot_token: slots::BootToken,
    ) -> GblResult<slots::Cursor<'b, B, M>> {
        Err(Error::OperationProhibited.into())
    }

    /// Computes the sum of required scratch size for all block devices.
    fn required_scratch_size(&mut self) -> GblResult<usize> {
        let mut total = SafeNum::ZERO;
        let mut res = Ok(());
        self.visit_block_devices(&mut |io, id, max_gpt_entries| {
            res = (|| {
                total += required_scratch_size(io, max_gpt_entries).unwrap();
                Ok(())
            })();
        })?;

        let total = usize::try_from(total).map_err(|e| e.into());
        res.and(total)
    }
}

/// `GblUtils` takes a reference to `GblOps` and implements various traits.
pub(crate) struct GblUtils<'a, 'b, T: GblOps> {
    ops: &'a mut T,
    scratch: &'b mut [u8],
}

impl<'a, 'b, T: GblOps> GblUtils<'a, 'b, T> {
    /// Create a new instance with user provided scratch buffer.
    ///
    /// # Args
    ///
    /// * `ops`: A reference to a `GblOps`,
    /// * `scratch`: A scratch buffer.
    ///
    /// # Returns
    ///
    /// Returns a new instance and the trailing unused part of the input scratch buffer.
    pub fn new(ops: &'a mut T, scratch: &'b mut [u8]) -> GblResult<(Self, &'b mut [u8])> {
        let total_scratch_size = ops.required_scratch_size()?;
        let (scratch, remaining) = scratch.split_at_mut(total_scratch_size);
        Ok((Self { ops: ops, scratch: scratch }, remaining))
    }
}

impl<T: GblOps> AsMultiBlockDevices for GblUtils<'_, '_, T> {
    fn for_each(
        &mut self,
        f: &mut dyn FnMut(&mut dyn AsBlockDevice, u64),
    ) -> core::result::Result<(), Option<&'static str>> {
        let mut scratch_offset = SafeNum::ZERO;
        self.ops
            .visit_block_devices(&mut |io, id, max_gpt_entries| {
                // Not expected to fail as `Self::new()` should have checked any overflow.
                let scratch_size: usize = required_scratch_size(io, max_gpt_entries).unwrap();
                let scratch =
                    &mut self.scratch[scratch_offset.try_into().unwrap()..][..scratch_size];
                scratch_offset += scratch_size;
                f(&mut BlockDevice::new(io, scratch, max_gpt_entries), id);
            })
            .map_err(|v| v.0)
    }
}

impl<T: GblOps> Write for GblUtils<'_, '_, T> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for ch in s.as_bytes() {
            self.ops.console_put_char(*ch).map_err(|_| core::fmt::Error {})?;
        }
        Ok(())
    }
}

/// Default [GblOps] implementation that returns errors and does nothing.
#[derive(Debug)]
pub struct DefaultGblOps {}

impl GblOps for DefaultGblOps {
    fn visit_block_devices(
        &mut self,
        f: &mut dyn FnMut(&mut dyn BlockIo, u64, u64),
    ) -> Result<(), GblOpsError> {
        Err(GblOpsError(Some("unimplemented")))
    }

    fn console_put_char(&mut self, ch: u8) -> Result<(), GblOpsError> {
        Err(GblOpsError(Some("unimplemented")))
    }

    fn should_stop_in_fastboot(&mut self) -> Result<bool, GblOpsError> {
        Err(GblOpsError(Some("unimplemented")))
    }

    fn boot(&mut self, boot_images: BootImages) -> Result<(), GblOpsError> {
        Err(GblOpsError(Some("unimplemented")))
    }
}
