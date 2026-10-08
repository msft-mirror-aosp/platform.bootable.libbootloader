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

//! This library provides APIs to work with data structures inside Android misc partition.
//!
//! Reference code:
//! https://cs.android.com/android/platform/superproject/main/+/main:bootable/recovery/bootloader_message/include/bootloader_message/bootloader_message.h
//!
//! TODO(b/329716686): Generate rust bindings for misc API from recovery to reuse the up to date
//! implementation

#![cfg_attr(not(test), no_std)]

use core::{ffi::CStr, mem::size_of};
use liberror::{Error, Result};
use static_assertions::const_assert;
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout, Ref, Unaligned};

/// Android boot modes type
/// Usually obtained from BCB block of misc partition
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum AndroidBootMode {
    /// Boot normally using A/B slots.
    Normal = 0,
    /// Stop in bootloader fastboot mode.
    BootloaderBootOnce,
    /// Boot into recovery mode using A/B slots.
    Recovery,
    /// Boot into userspace fastboot.
    Fastboot,
    /// Boot into rescue mode.
    Rescue,
}

const ANDROID_BOOT_MODE_CMD_NORMAL: &'static [u8] = b"";
const ANDROID_BOOT_MODE_CMD_BOOTLOADER: &'static [u8] = b"bootonce-bootloader";
const ANDROID_BOOT_MODE_CMD_RECOVERY: &'static [u8] = b"boot-recovery";
const ANDROID_BOOT_MODE_CMD_FASTBOOT: &'static [u8] = b"boot-fastboot";
const ANDROID_BOOT_MODE_CMD_RESCUE: &'static [u8] = b"boot-rescue";

impl TryFrom<&[u8]> for AndroidBootMode {
    type Error = Error;

    fn try_from(bytes: &[u8]) -> Result<Self> {
        match bytes {
            ANDROID_BOOT_MODE_CMD_NORMAL => Ok(AndroidBootMode::Normal),
            ANDROID_BOOT_MODE_CMD_BOOTLOADER => Ok(AndroidBootMode::BootloaderBootOnce),
            ANDROID_BOOT_MODE_CMD_RECOVERY => Ok(AndroidBootMode::Recovery),
            ANDROID_BOOT_MODE_CMD_FASTBOOT => Ok(AndroidBootMode::Fastboot),
            ANDROID_BOOT_MODE_CMD_RESCUE => Ok(AndroidBootMode::Rescue),
            _ => Err(Error::Other(Some("Invalid BCB command"))),
        }
    }
}

impl From<AndroidBootMode> for &'static [u8] {
    fn from(mode: AndroidBootMode) -> Self {
        match mode {
            AndroidBootMode::Normal => ANDROID_BOOT_MODE_CMD_NORMAL,
            AndroidBootMode::BootloaderBootOnce => ANDROID_BOOT_MODE_CMD_BOOTLOADER,
            AndroidBootMode::Recovery => ANDROID_BOOT_MODE_CMD_RECOVERY,
            AndroidBootMode::Fastboot => ANDROID_BOOT_MODE_CMD_FASTBOOT,
            AndroidBootMode::Rescue => ANDROID_BOOT_MODE_CMD_RESCUE,
        }
    }
}

impl AndroidBootMode {
    /// Whether the boot mode should be handled in recovery.
    pub const fn should_enter_recovery(&self) -> bool {
        match self {
            AndroidBootMode::Recovery | AndroidBootMode::Fastboot | AndroidBootMode::Rescue => true,
            AndroidBootMode::Normal | AndroidBootMode::BootloaderBootOnce => false,
        }
    }
}

/// BCB command field size in bytes.
const COMMAND_FIELD_SIZE: usize = 32;

/// Android bootloader message structure that usually placed in the first block of misc partition
///
/// Reference code:
/// https://cs.android.com/android/platform/superproject/main/+/95ec3cc1d879b92dd9db3bb4c4345c5fc812cdaa:bootable/recovery/bootloader_message/include/bootloader_message/bootloader_message.h;l=67
#[repr(C, packed)]
#[derive(Clone, Debug, PartialEq, Eq, Immutable, FromBytes, IntoBytes, KnownLayout, Unaligned)]
pub struct BootloaderMessage {
    command: [u8; COMMAND_FIELD_SIZE],
    status: [u8; 32],
    recovery: [u8; 768],
    stage: [u8; 32],
    reserved: [u8; 1184],
}

impl BootloaderMessage {
    /// BCB size in bytes
    pub const SIZE_BYTES: usize = 2048;

    /// Extract BootloaderMessage reference from bytes
    pub fn from_bytes_ref(buffer: &[u8]) -> Result<&BootloaderMessage> {
        Ok(Ref::into_ref(
            Ref::<_, BootloaderMessage>::new_from_prefix(buffer)
                .ok_or(Error::BufferTooSmall(Some(core::mem::size_of::<BootloaderMessage>())))?
                .0
                .into(),
        ))
    }

    fn command_cstr(&self) -> Result<&CStr> {
        CStr::from_bytes_until_nul(&self.command)
            .map_err(|_| Error::Other(Some("Cannot read BCB command")))
    }

    /// Extract AndroidBootMode from BCB command field
    pub fn boot_mode(&self) -> Result<AndroidBootMode> {
        self.command_cstr()?.to_bytes().try_into()
    }

    /// Get the BCB command as str.
    pub fn boot_command(&self) -> Result<&str> {
        Ok(self.command_cstr()?.to_str()?)
    }

    /// Update the BCB boot command with AndroidBootMode.
    pub fn update_boot_command(&mut self, mode: AndroidBootMode) {
        let boot_cmd: &[u8] = mode.into();
        self.command.fill(0);
        self.command[..boot_cmd.len()].copy_from_slice(boot_cmd);
    }
}

const_assert!(BootloaderMessage::SIZE_BYTES == size_of::<BootloaderMessage>());

#[cfg(test)]
mod test {
    use super::*;
    use zerocopy::{FromZeros, IntoBytes};

    fn test_parse_bcb(command: &[u8], expected_mode: Result<AndroidBootMode>) {
        let mut bcb = BootloaderMessage::new_zeroed();
        bcb.command[..command.len()].copy_from_slice(command);
        assert_eq!(
            BootloaderMessage::from_bytes_ref(bcb.as_bytes()).unwrap().boot_mode(),
            expected_mode
        );
    }

    #[test]
    fn test_bcb_empty_parsed_as_normal() {
        test_parse_bcb(b"", Ok(AndroidBootMode::Normal));
    }

    #[test]
    fn test_bcb_with_wrong_command_failed() {
        test_parse_bcb(b"boot-wrong", Err(Error::Other(Some("Invalid BCB command"))));
    }

    #[test]
    fn test_bcb_to_recovery_parsed() {
        test_parse_bcb(ANDROID_BOOT_MODE_CMD_RECOVERY, Ok(AndroidBootMode::Recovery));
    }

    #[test]
    fn test_bcb_to_fastboot_parsed() {
        test_parse_bcb(ANDROID_BOOT_MODE_CMD_FASTBOOT, Ok(AndroidBootMode::Fastboot));
    }

    #[test]
    fn test_bcb_to_bootloader_once_parsed() {
        test_parse_bcb(ANDROID_BOOT_MODE_CMD_BOOTLOADER, Ok(AndroidBootMode::BootloaderBootOnce));
    }

    #[test]
    fn test_bcb_update_boot_command() {
        macro_rules! assert_bcb_update_boot_command {
            ($mode:expr) => {
                let mut bcb = BootloaderMessage::new_zeroed();
                bcb.update_boot_command($mode);
                assert_eq!(bcb.boot_mode(), Ok($mode));
            };
        }

        assert_bcb_update_boot_command!(AndroidBootMode::Normal);
        assert_bcb_update_boot_command!(AndroidBootMode::BootloaderBootOnce);
        assert_bcb_update_boot_command!(AndroidBootMode::Recovery);
        assert_bcb_update_boot_command!(AndroidBootMode::Fastboot);
        assert_bcb_update_boot_command!(AndroidBootMode::Rescue);
    }

    #[test]
    fn test_android_boot_mode_into_from_bytes() {
        macro_rules! assert_android_boot_mode {
            ($mode:expr) => {
                let boot_cmd: &[u8] = $mode.into();
                assert!(boot_cmd.len() < COMMAND_FIELD_SIZE);
                assert_eq!(boot_cmd.try_into(), Ok($mode));
            };
        }

        assert_android_boot_mode!(AndroidBootMode::Normal);
        assert_android_boot_mode!(AndroidBootMode::BootloaderBootOnce);
        assert_android_boot_mode!(AndroidBootMode::Recovery);
        assert_android_boot_mode!(AndroidBootMode::Fastboot);
        assert_android_boot_mode!(AndroidBootMode::Normal);
    }
}
