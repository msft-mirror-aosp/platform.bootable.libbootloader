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

use crate::error::Result as GblResult;
#[cfg(feature = "alloc")]
use alloc::ffi::CString;
use core::{
    fmt::{Debug, Write},
    result::Result,
};
use gbl_async::block_on;
use zbi::ZbiContainer;

use super::slots;

/// `AndroidBootImages` contains references to loaded images for booting Android.
pub struct AndroidBootImages<'a> {
    /// Kernel image.
    pub kernel: &'a mut [u8],
    /// Ramdisk to pass to the kernel.
    pub ramdisk: &'a mut [u8],
    /// FDT To pass to the kernel.
    pub fdt: &'a mut [u8],
}

/// `FuchsiaBootImages` contains references to loaded images for booting Zircon.
pub struct FuchsiaBootImages<'a> {
    /// Kernel image.
    pub zbi_kernel: &'a mut [u8],
    /// ZBI container with items to pass to the kernel.
    pub zbi_items: &'a mut [u8],
}

/// Images required to boot the supported kernels.
pub enum BootImages<'a> {
    /// Android boot images.
    Android(AndroidBootImages<'a>),
    /// Fuchsia boot images.
    Fuchsia(FuchsiaBootImages<'a>),
}

/// `GblOpsError` is the error type returned by required methods in `GblOps`.
#[derive(Default, Debug, PartialEq, Eq, Copy, Clone)]
pub struct GblOpsError(pub Option<&'static str>);

impl From<&'static str> for GblOpsError {
    fn from(val: &'static str) -> Self {
        Self(Some(val))
    }
}

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
    /// Gets a console for logging messages.
    fn console_out(&mut self) -> Option<&mut dyn Write>;

    /// This method can be used to implement platform specific mechanism for deciding whether boot
    /// should abort and enter Fastboot mode.
    fn should_stop_in_fastboot(&mut self) -> Result<bool, GblOpsError>;

    /// Platform specific processing of boot images before booting.
    fn preboot(&mut self, boot_images: BootImages) -> Result<(), GblOpsError>;

    /// Reads data from a partition.
    async fn read_from_partition(
        &mut self,
        part: &str,
        off: u64,
        out: &mut [u8],
    ) -> Result<(), GblOpsError>;

    /// Reads data from a partition synchronously.
    fn read_from_partition_sync(
        &mut self,
        part: &str,
        off: u64,
        out: &mut [u8],
    ) -> Result<(), GblOpsError> {
        block_on(self.read_from_partition(part, off, out))
    }

    /// Writes data to a partition.
    async fn write_to_partition(
        &mut self,
        part: &str,
        off: u64,
        data: &mut [u8],
    ) -> Result<(), GblOpsError>;

    /// Writes data to a partition synchronously.
    fn write_to_partition_sync(
        &mut self,
        part: &str,
        off: u64,
        data: &mut [u8],
    ) -> Result<(), GblOpsError> {
        block_on(self.write_to_partition(part, off, data))
    }

    /// Returns the size of a partiiton. Returns Ok(None) if partition doesn't exist.
    fn partition_size(&mut self, part: &str) -> Result<Option<u64>, GblOpsError>;

    /// Adds device specific ZBI items to the given `container`
    fn zircon_add_device_zbi_items(
        &mut self,
        container: &mut ZbiContainer<&mut [u8]>,
    ) -> Result<(), GblOpsError>;

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
        cursor: &mut slots::Cursor<B>,
    ) -> GblResult<()>;

    /// TODO: b/312607649 - placeholder interface for Gbl specific callbacks that uses alloc.
    #[cfg(feature = "alloc")]
    fn gbl_alloc_extra_action(&mut self, s: &str) -> GblResult<()> {
        unimplemented!();
    }

    /// Load and initialize a slot manager and return a cursor over the manager on success.
    fn load_slot_interface<'a, B: gbl_storage::AsBlockDevice>(
        &'a mut self,
        block_device: &'a mut B,
        boot_token: slots::BootToken,
    ) -> GblResult<slots::Cursor<'a, B>>;
}

/// Default [GblOps] implementation that returns errors and does nothing.
#[derive(Debug)]
pub struct DefaultGblOps {}

impl GblOps for DefaultGblOps {
    fn console_out(&mut self) -> Option<&mut dyn Write> {
        unimplemented!();
    }

    fn should_stop_in_fastboot(&mut self) -> Result<bool, GblOpsError> {
        unimplemented!();
    }

    fn preboot(&mut self, boot_images: BootImages) -> Result<(), GblOpsError> {
        unimplemented!();
    }

    async fn read_from_partition(
        &mut self,
        part: &str,
        off: u64,
        out: &mut [u8],
    ) -> Result<(), GblOpsError> {
        unimplemented!();
    }

    async fn write_to_partition(
        &mut self,
        part: &str,
        off: u64,
        data: &mut [u8],
    ) -> Result<(), GblOpsError> {
        unimplemented!();
    }

    fn partition_size(&mut self, part: &str) -> Result<Option<u64>, GblOpsError> {
        unimplemented!();
    }

    fn zircon_add_device_zbi_items(
        &mut self,
        container: &mut ZbiContainer<&mut [u8]>,
    ) -> Result<(), GblOpsError> {
        unimplemented!();
    }

    fn do_fastboot<B: gbl_storage::AsBlockDevice>(
        &self,
        cursor: &mut slots::Cursor<B>,
    ) -> GblResult<()> {
        unimplemented!();
    }

    fn load_slot_interface<'a, B: gbl_storage::AsBlockDevice>(
        &'a mut self,
        block_device: &'a mut B,
        boot_token: slots::BootToken,
    ) -> GblResult<slots::Cursor<'a, B>> {
        unimplemented!();
    }
}
