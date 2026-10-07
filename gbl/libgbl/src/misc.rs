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

//! Helpers for manipulating the bootloader_message (BCB) in the misc partition.

use crate::GblOps;
use liberror::{Error, Result};
use zerocopy::{error::SizeError, FromBytes, FromZeros, IntoBytes};

pub use misc::{AndroidBootMode, BootloaderMessage};

/// The partition that contains the bootloader_message (BCB).
pub(crate) const MISC_PARTITION: &str = "misc";

/// Reads the bootloader_message (BCB) from `misc` partition into a buffer.
///
/// # Returns
/// * Ok(&mut BootloaderMessage) a mutable reference to the BootloaderMessage instance.
/// * Err(BufferTooSmall(_)) if buffer is too small.
/// * Err(_) if IO error.
pub fn read_bootloader_message_to<'a, 'b>(
    ops: &mut impl GblOps<'a>,
    buffer: &'b mut [u8],
) -> Result<&'b mut BootloaderMessage> {
    let (bcb, _) = BootloaderMessage::mut_from_prefix(buffer).map_err(|e| match e.into() {
        SizeError { .. } => Error::BufferTooSmall(Some(BootloaderMessage::SIZE_BYTES)),
    })?;
    bcb.zero();
    ops.read_from_partition_sync(MISC_PARTITION, 0, bcb.as_mut_bytes())?;
    Ok(bcb)
}

/// Writes the bootloader_message (BCB) to `misc` partition.
pub fn write_bootloader_message<'a>(
    ops: &mut impl GblOps<'a>,
    bcb: &mut BootloaderMessage,
) -> Result<()> {
    ops.write_to_partition_sync(MISC_PARTITION, 0, bcb.as_mut_bytes())
}

#[cfg(test)]
pub(crate) mod test {
    use super::*;
    use crate::{
        constants::KiB,
        ops::test::{FakeGblOps, FakeGblOpsStorage},
    };

    /// Reads the bootloader_message (BCB) from `misc` partition.
    pub(crate) fn read_bootloader_message<'a>(
        ops: &mut impl GblOps<'a>,
    ) -> Result<BootloaderMessage> {
        let mut bcb = BootloaderMessage::new_zeroed();
        read_bootloader_message_to(ops, bcb.as_mut_bytes())?;
        Ok(bcb)
    }

    #[test]
    fn test_read_bootloader_message_to() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"misc", [0u8; KiB!(4)]);
        let mut ops = FakeGblOps::new(&storage);
        ops.write_to_partition_sync(MISC_PARTITION, 0, &mut b"bootonce-bootloader".to_vec())
            .unwrap();

        let bcb = read_bootloader_message(&mut ops).unwrap();

        assert_eq!(bcb.boot_mode(), Ok(AndroidBootMode::BootloaderBootOnce));
    }

    #[test]
    fn test_write_bootloader_message() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"misc", [0u8; KiB!(4)]);
        let mut ops = FakeGblOps::new(&storage);

        let mut bcb = BootloaderMessage::new_zeroed();
        bcb.update_boot_command(AndroidBootMode::BootloaderBootOnce);
        write_bootloader_message(&mut ops, &mut bcb).unwrap();

        let bcb = read_bootloader_message(&mut ops).unwrap();
        assert_eq!(bcb.boot_mode(), Ok(AndroidBootMode::BootloaderBootOnce));
    }
}
