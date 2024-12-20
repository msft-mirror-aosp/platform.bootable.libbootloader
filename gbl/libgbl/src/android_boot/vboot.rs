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

use crate::{
    gbl_avb::{
        ops::{GblAvbOps, AVB_DIGEST_KEY},
        state::{BootStateColor, KeyValidationStatus},
    },
    gbl_print, gbl_println, GblOps, Result,
};
use arrayvec::ArrayVec;
use avb::{slot_verify, HashtreeErrorMode, Ops as _, SlotVerifyFlags};
use bootparams::{bootconfig::BootConfigBuilder, entry::CommandlineParser};
use core::fmt::Write;
use liberror::Error;

/// Helper function for performing libavb verification.
///
/// Currently this requires the caller to preload all relevant images from disk; in its final
/// state `ops` will provide the necessary callbacks for where the images should go in RAM and
/// which ones are preloaded.
///
/// # Arguments
/// * `ops`: [GblOps] providing device-specific backend.
/// * `kernel`: buffer containing the `boot` image loaded from disk.
/// * `vendor_boot`: buffer containing the `vendor_boot` image loaded from disk.
/// * `init_boot`: buffer containing the `init_boot` image loaded from disk.
/// * `dtbo`: buffer containing the `dtbo` image loaded from disk, if it exists.
/// * `bootconfig_builder`: object to write the bootconfig data into.
///
/// # Returns
/// `()` on success. Returns an error if verification process failed and boot cannot
/// continue, or if parsing the command line or updating the boot configuration fail.
pub(crate) fn avb_verify_slot<'a, 'b>(
    ops: &mut impl GblOps<'a, 'b>,
    kernel: &[u8],
    vendor_boot: &[u8],
    init_boot: &[u8],
    dtbo: Option<&[u8]>,
    bootconfig_builder: &mut BootConfigBuilder,
) -> Result<()> {
    // We need the list of partition names to verify with libavb, and a corresponding list of
    // (name, image) tuples to register as [GblAvbOps] preloaded data.
    let mut partitions = ArrayVec::<_, 4>::new();
    let mut preloaded = ArrayVec::<_, 4>::new();
    for (c_name, image) in [
        (c"boot", Some(kernel)),
        (c"vendor_boot", Some(vendor_boot)),
        (c"init_boot", Some(init_boot)),
        (c"dtbo", dtbo),
    ] {
        if let Some(image) = image {
            partitions.push(c_name);
            preloaded.push((c_name.to_str().unwrap(), image));
        }
    }

    let mut avb_ops = GblAvbOps::new(ops, &preloaded[..], false);
    let unlocked = avb_ops.read_is_device_unlocked()?;
    let verify_result = slot_verify(
        &mut avb_ops,
        &partitions,
        Some(c"_a"),
        // TODO(b/337846185): Pass AVB_SLOT_VERIFY_FLAGS_RESTART_CAUSED_BY_HASHTREE_CORRUPTION in
        // case verity corruption is detected by HLOS.
        match unlocked {
            true => SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_ALLOW_VERIFICATION_ERROR,
            _ => SlotVerifyFlags::AVB_SLOT_VERIFY_FLAGS_NONE,
        },
        // TODO(b/337846185): For demo, we use the same setting as Cuttlefish u-boot.
        // Pass AVB_HASHTREE_ERROR_MODE_MANAGED_RESTART_AND_EIO and handle EIO.
        HashtreeErrorMode::AVB_HASHTREE_ERROR_MODE_RESTART_AND_INVALIDATE,
    );
    let (color, verify_data) = match verify_result {
        Ok(ref verify_data) => {
            let color = match unlocked {
                false
                    if avb_ops.key_validation_status()? == KeyValidationStatus::ValidCustomKey =>
                {
                    BootStateColor::Yellow
                }
                false => BootStateColor::Green,
                true => BootStateColor::Orange,
            };

            gbl_println!(
                avb_ops.gbl_ops,
                "AVB verification passed. Device is unlocked: {unlocked}. Color: {color}"
            );

            (color, Some(verify_data))
        }
        // Non-fatal error, can continue booting since verify_data is available.
        Err(ref e) if e.verification_data().is_some() && unlocked => {
            let color = BootStateColor::Orange;

            gbl_println!(
                avb_ops.gbl_ops,
                "AVB verification failed with {e}. Device is unlocked: {unlocked}. Color: {color}. \
                Continue current boot attempt."
            );

            (color, Some(e.verification_data().unwrap()))
        }
        // Fatal error. Cannot boot.
        Err(ref e) => {
            let color = BootStateColor::Red;

            gbl_println!(
                avb_ops.gbl_ops,
                "AVB verification failed with {e}. Device is unlocked: {unlocked}. Color: {color}. \
                Cannot continue boot."
            );

            (color, None)
        }
    };

    // Gets digest from the result command line.
    let mut digest = None;
    if let Some(ref verify_data) = verify_data {
        for entry in CommandlineParser::new(verify_data.cmdline().to_str().unwrap()) {
            let entry = entry?;
            if entry.key == AVB_DIGEST_KEY {
                digest = entry.value;
            }
            write!(bootconfig_builder, "{}\n", entry).or(Err(Error::BufferTooSmall(None)))?;
        }
    }

    // Allowes FW to handle verification result.
    avb_ops.handle_verification_result(verify_data, color, digest)?;

    match color {
        BootStateColor::Red => Err(verify_result.unwrap_err().without_verify_data().into()),
        _ => {
            write!(bootconfig_builder, "androidboot.verifiedbootstate={}\n", color)
                .or(Err(Error::BufferTooSmall(None)))?;

            Ok(())
        }
    }
}

#[cfg(test)]
mod test {
    // TODO(b/384964561): Cover AVB flow using Android test artifacts
}
