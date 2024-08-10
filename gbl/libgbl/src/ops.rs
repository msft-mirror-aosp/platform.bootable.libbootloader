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

// Re-exports of types from other dependencies that appear in the APIs of this library.
pub use avb::{
    CertPermanentAttributes, IoError as AvbIoError, IoResult as AvbIoResult, SHA256_DIGEST_SIZE,
};
use liberror::Error;
pub use zbi::ZbiContainer;

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

/// `GblAvbOps` contains libavb backend interfaces needed by GBL.
///
/// The trait is a selective subset of the interfaces in `avb::Ops` and `avb::CertOps`. The rest of
/// the APIs are either not relevant to or are implemented and managed by GBL APIs.
pub trait GblAvbOps {
    /// Returns if device is in an unlocked state.
    ///
    /// The interface has the same requirement as `avb::Ops::read_is_device_unlocked`.
    fn avb_read_is_device_unlocked(&mut self) -> AvbIoResult<bool>;

    /// Reads the AVB rollback index at the given location
    ///
    /// The interface has the same requirement as `avb::Ops::read_rollback_index`.
    fn avb_read_rollback_index(&mut self, _rollback_index_location: usize) -> AvbIoResult<u64>;

    /// Writes the AVB rollback index at the given location.
    ///
    /// The interface has the same requirement as `avb::Ops::write_rollback_index`.
    fn avb_write_rollback_index(
        &mut self,
        _rollback_index_location: usize,
        _index: u64,
    ) -> AvbIoResult<()>;

    /// Reads AVB certificate extension permanent attributes.
    ///
    /// The interface has the same requirement as `avb::CertOps::read_permanent_attributes`.
    fn avb_cert_read_permanent_attributes(
        &mut self,
        attributes: &mut CertPermanentAttributes,
    ) -> AvbIoResult<()>;

    /// Reads AVB certificate extension permanent attributes hash.
    ///
    /// The interface has the same requirement as `avb::CertOps::read_permanent_attributes_hash`.
    fn avb_cert_read_permanent_attributes_hash(&mut self) -> AvbIoResult<[u8; SHA256_DIGEST_SIZE]>;
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
    fn should_stop_in_fastboot(&mut self) -> Result<bool, Error>;

    /// Platform specific processing of boot images before booting.
    fn preboot(&mut self, boot_images: BootImages) -> Result<(), Error>;

    /// Reads data from a partition.
    async fn read_from_partition(
        &mut self,
        part: &str,
        off: u64,
        out: &mut [u8],
    ) -> Result<(), Error>;

    /// Reads data from a partition synchronously.
    fn read_from_partition_sync(
        &mut self,
        part: &str,
        off: u64,
        out: &mut [u8],
    ) -> Result<(), Error> {
        block_on(self.read_from_partition(part, off, out))
    }

    /// Writes data to a partition.
    async fn write_to_partition(
        &mut self,
        part: &str,
        off: u64,
        data: &mut [u8],
    ) -> Result<(), Error>;

    /// Writes data to a partition synchronously.
    fn write_to_partition_sync(
        &mut self,
        part: &str,
        off: u64,
        data: &mut [u8],
    ) -> Result<(), Error> {
        block_on(self.write_to_partition(part, off, data))
    }

    /// Returns the size of a partiiton. Returns Ok(None) if partition doesn't exist.
    fn partition_size(&mut self, part: &str) -> Result<Option<u64>, Error>;

    /// Adds device specific ZBI items to the given `container`
    fn zircon_add_device_zbi_items(
        &mut self,
        container: &mut ZbiContainer<&mut [u8]>,
    ) -> Result<(), Error>;

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

    /// Returns an implementation of `GblAvbOps`
    ///
    /// Users that don't need verified boot can return `avb_ops_none()`.
    fn avb_ops(&mut self) -> Option<impl GblAvbOps>;
}

/// Returns a `None` instance of `Option<impl GblAvbOps>`.
///
/// This can be used as the implementation of `GblOps::avb_ops()` if users don't need verified
/// boot.
pub fn avb_ops_none() -> Option<impl GblAvbOps> {
    None::<GblAvbOpsNull>
}

/// Default [GblOps] implementation that returns errors and does nothing.
#[derive(Debug)]
pub struct DefaultGblOps {}

impl GblOps for DefaultGblOps {
    fn console_out(&mut self) -> Option<&mut dyn Write> {
        unimplemented!();
    }

    fn should_stop_in_fastboot(&mut self) -> Result<bool, Error> {
        unimplemented!();
    }

    fn preboot(&mut self, boot_images: BootImages) -> Result<(), Error> {
        unimplemented!();
    }

    async fn read_from_partition(
        &mut self,
        part: &str,
        off: u64,
        out: &mut [u8],
    ) -> Result<(), Error> {
        unimplemented!();
    }

    async fn write_to_partition(
        &mut self,
        part: &str,
        off: u64,
        data: &mut [u8],
    ) -> Result<(), Error> {
        unimplemented!();
    }

    fn partition_size(&mut self, part: &str) -> Result<Option<u64>, Error> {
        unimplemented!();
    }

    fn zircon_add_device_zbi_items(
        &mut self,
        container: &mut ZbiContainer<&mut [u8]>,
    ) -> Result<(), Error> {
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

    fn avb_ops(&mut self) -> Option<impl GblAvbOps> {
        avb_ops_none()
    }
}

/// Prints with `GblOps::console_out()`.
#[macro_export]
macro_rules! gbl_print {
    ( $ops:expr, $( $x:expr ),* $(,)? ) => {
        {
            match $ops.console_out() {
                Some(v) => write!(v, $($x,)*).unwrap(),
                _ => {}
            }
        }
    };
}

/// `GblAvbOpsNull` provides placeholder implementation for `GblAvbOps`. All methods are
/// `unimplemented!()`. The type is for plugging in `None::<GblAvbOpsNull>` which the compiler
/// requires for return by `avb_ops_none()`, .
struct GblAvbOpsNull {}

impl GblAvbOps for GblAvbOpsNull {
    fn avb_read_is_device_unlocked(&mut self) -> AvbIoResult<bool> {
        unimplemented!();
    }

    fn avb_read_rollback_index(&mut self, _rollback_index_location: usize) -> AvbIoResult<u64> {
        unimplemented!();
    }

    fn avb_write_rollback_index(
        &mut self,
        _rollback_index_location: usize,
        _index: u64,
    ) -> AvbIoResult<()> {
        unimplemented!();
    }

    fn avb_cert_read_permanent_attributes(
        &mut self,
        attributes: &mut CertPermanentAttributes,
    ) -> AvbIoResult<()> {
        unimplemented!();
    }

    fn avb_cert_read_permanent_attributes_hash(&mut self) -> AvbIoResult<[u8; SHA256_DIGEST_SIZE]> {
        unimplemented!();
    }
}
