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

//! Implementation of the `GblEfiBootControlProtocol` for qemu tests.

#![cfg_attr(not(test), no_std)]

use efi_types::{
    defs::{
        GblEfiLoadedOs, GblEfiOneShotBootMode, GblEfiSlotInfo,
        GBL_EFI_BOOT_CONTROL_PROTOCOL_REVISION, GBL_EFI_ONE_SHOT_BOOT_MODE_NONE,
        GBL_EFI_UNBOOTABLE_REASON_UNKNOWN_REASON,
    },
    protocol::gbl_efi_boot_control::GblEfiBootControl,
    status::{EfiError, EfiResult},
};

/// Test implementation of `GblEfiBootControl`.
pub struct GblEfiBootControlImpl;

impl GblEfiBootControl for GblEfiBootControlImpl {
    fn revision(&self) -> u64 {
        GBL_EFI_BOOT_CONTROL_PROTOCOL_REVISION
    }

    fn get_slot_count(&self) -> EfiResult<u8> {
        Ok(2)
    }

    fn get_slot_info(&self, index: u8) -> EfiResult<GblEfiSlotInfo> {
        match index {
            0 => Ok(GblEfiSlotInfo {
                suffix: 'a' as u32,
                unbootable_reason: GBL_EFI_UNBOOTABLE_REASON_UNKNOWN_REASON,
                priority: 15,
                remaining_tries: 7,
                successful: 1,
            }),
            1 => Ok(GblEfiSlotInfo {
                suffix: 'b' as u32,
                unbootable_reason: GBL_EFI_UNBOOTABLE_REASON_UNKNOWN_REASON,
                priority: 14,
                remaining_tries: 7,
                successful: 0,
            }),
            _ => Err(EfiError::InvalidParameter),
        }
    }

    fn get_current_slot(&self) -> EfiResult<GblEfiSlotInfo> {
        self.get_slot_info(0)
    }

    fn set_active_slot(&self, _index: u8) -> EfiResult<()> {
        Err(EfiError::Unsupported)
    }

    fn get_one_shot_boot_mode(&self) -> EfiResult<GblEfiOneShotBootMode> {
        Ok(GBL_EFI_ONE_SHOT_BOOT_MODE_NONE)
    }

    fn handle_loaded_os(&self, os: &GblEfiLoadedOs) -> EfiResult<()> {
        if os.kernel == 0
            || os.kernel_size == 0
            || os.ramdisk == 0
            || os.ramdisk_size == 0
            || os.device_tree == 0
            || os.device_tree_size == 0
        {
            return Err(EfiError::InvalidParameter);
        }
        semihosting::println!(
            "handle_loaded_os: kernel @ {:#x} ({:#x}), ramdisk @ {:#x} ({:#x}), fdt @ {:#x} ({:#x})",
            os.kernel,
            os.kernel_size,
            os.ramdisk,
            os.ramdisk_size,
            os.device_tree,
            os.device_tree_size,
        );
        Ok(())
    }
}
