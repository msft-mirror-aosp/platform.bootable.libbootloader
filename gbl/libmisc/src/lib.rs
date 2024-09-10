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

use core::ffi::CStr;

use zerocopy::{AsBytes, FromBytes, FromZeroes, Ref};

use liberror::{Error, Result};

/// Android boot modes type
/// Usually obtained from BCB block of misc partition
#[derive(PartialEq, Debug)]
pub enum AndroidBootMode {
    /// Boot normally using A/B slots.
    Normal = 0,
    /// Boot into recovery mode using A/B slots.
    Recovery,
    /// Stop in bootloader fastboot mode.
    BootloaderBootOnce,
}

impl core::fmt::Display for AndroidBootMode {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            AndroidBootMode::Normal => write!(f, "AndroidBootMode::Normal"),
            AndroidBootMode::Recovery => write!(f, "AndroidBootMode::Recovery"),
            AndroidBootMode::BootloaderBootOnce => write!(f, "AndroidBootMode::BootloaderBootOnce"),
        }
    }
}

/// Android bootloader message structure that usually placed in the first block of misc partition
///
/// Reference code:
/// https://cs.android.com/android/platform/superproject/main/+/95ec3cc1d879b92dd9db3bb4c4345c5fc812cdaa:bootable/recovery/bootloader_message/include/bootloader_message/bootloader_message.h;l=67
#[repr(C, packed)]
#[derive(AsBytes, FromBytes, FromZeroes, PartialEq, Copy, Clone, Debug)]
pub struct BootloaderMessage {
    command: [u8; 32],
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
        Ok(Ref::<_, BootloaderMessage>::new_from_prefix(buffer)
            .ok_or(Error::BufferTooSmall(Some(core::mem::size_of::<BootloaderMessage>())))?
            .0
            .into_ref())
    }

    /// Extract AndroidBootMode from BCB command field
    pub fn boot_mode(&self) -> Result<AndroidBootMode> {
        let command = CStr::from_bytes_until_nul(&self.command)
            .map_err(|_| Error::Other(Some("Cannot read BCB command")))?
            .to_str()
            .map_err(|_| Error::InvalidInput)?;

        match command {
            "" => Ok(AndroidBootMode::Normal),
            "boot-recovery" | "boot-fastboot" => Ok(AndroidBootMode::Recovery),
            "bootonce-bootloader" => Ok(AndroidBootMode::BootloaderBootOnce),
            _ => Err(Error::Other(Some("Wrong BCB command"))),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::AndroidBootMode;
    use crate::BootloaderMessage;
    use zerocopy::AsBytes;

    impl Default for BootloaderMessage {
        fn default() -> Self {
            BootloaderMessage {
                command: [0; 32],
                status: [0; 32],
                recovery: [0; 768],
                stage: [0; 32],
                reserved: [0; 1184],
            }
        }
    }

    #[test]
    fn test_bcb_empty_parsed_as_normal() {
        let bcb = BootloaderMessage::default();

        assert_eq!(
            BootloaderMessage::from_bytes_ref(bcb.as_bytes()).unwrap().boot_mode().unwrap(),
            AndroidBootMode::Normal
        );
    }

    #[test]
    fn test_bcb_with_wrong_command_failed() {
        let command = "boot-wrong";
        let mut bcb = BootloaderMessage::default();
        bcb.command[..command.len()].copy_from_slice(command.as_bytes());

        assert!(BootloaderMessage::from_bytes_ref(bcb.as_bytes()).unwrap().boot_mode().is_err());
    }

    #[test]
    fn test_bcb_to_recovery_parsed() {
        let command = "boot-recovery";
        let mut bcb = BootloaderMessage::default();
        bcb.command[..command.len()].copy_from_slice(command.as_bytes());

        assert_eq!(
            BootloaderMessage::from_bytes_ref(bcb.as_bytes()).unwrap().boot_mode().unwrap(),
            AndroidBootMode::Recovery
        );
    }

    #[test]
    fn test_bcb_to_fastboot_parsed_as_recovery() {
        let command = "boot-fastboot";
        let mut bcb = BootloaderMessage::default();
        bcb.command[..command.len()].copy_from_slice(command.as_bytes());

        assert_eq!(
            BootloaderMessage::from_bytes_ref(bcb.as_bytes()).unwrap().boot_mode().unwrap(),
            AndroidBootMode::Recovery
        );
    }

    #[test]
    fn test_bcb_to_bootloader_once_parsed() {
        let command = "bootonce-bootloader";
        let mut bcb = BootloaderMessage::default();
        bcb.command[..command.len()].copy_from_slice(command.as_bytes());

        assert_eq!(
            BootloaderMessage::from_bytes_ref(bcb.as_bytes()).unwrap().boot_mode().unwrap(),
            AndroidBootMode::BootloaderBootOnce
        );
    }
}
