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

//! Module for constructing kernel commandline.
//!
//! https://www.kernel.org/doc/html/v4.14/admin-guide/kernel-parameters.html

use crate::entry::{CommandlineParser, Entry};
use core::ffi::CStr;
use liberror::{Error, Error::BufferTooSmall, Error::InvalidInput, Result};

/// A class for constructing commandline section.
pub struct CommandlineBuilder<'a> {
    current_size: usize,
    buffer: &'a mut [u8],
}

/// Null terminator.
const COMMANDLINE_TRAILING_SIZE: usize = 1;

impl<'a> CommandlineBuilder<'a> {
    /// Initialize with a given buffer.
    pub fn new(buffer: &'a mut [u8]) -> Result<Self> {
        if buffer.len() < COMMANDLINE_TRAILING_SIZE {
            return Err(BufferTooSmall(Some(COMMANDLINE_TRAILING_SIZE)));
        }
        let mut ret = Self { current_size: 0, buffer: buffer };
        ret.update_null_terminator();
        Ok(ret)
    }

    /// Initialize with a provided buffer that already contains a command line.
    pub fn new_from_prefix(buffer: &'a mut [u8]) -> Result<Self> {
        let prefix = CStr::from_bytes_until_nul(buffer).map_err(Error::from)?;
        Ok(Self { current_size: prefix.to_bytes().len(), buffer: buffer })
    }

    /// Get the remaining capacity.
    pub fn remaining_capacity(&self) -> usize {
        self.buffer.len() - self.current_size - COMMANDLINE_TRAILING_SIZE
    }

    /// Get the current command line.
    pub fn as_str(&self) -> &str {
        // Maintain data null-terminated so not expecting to fail.
        CStr::from_bytes_with_nul(&self.buffer[..self.current_size + 1])
            .unwrap()
            .to_str()
            .unwrap()
            .trim()
    }

    /// Append a new command line segment via a reader callback.
    ///
    /// Callback arguments:
    /// * `&CStr`     - Current null terminated command line data.
    /// * `&mut [u8]` - Remaining buffer for reading the data into. May be an empty buffer.
    ///
    /// Callback return value:
    /// It must return the total size written or error. Null terminator must not be included in
    /// the written buffer. Attempting to return a size greater than the input buffer will cause
    /// it to panic. Empty read is allowed.
    ///
    /// It's up to the caller to make sure the read content will eventually form a valid
    /// command line (space separation is handled by the call). The API is for situations where
    /// command line is read from sources such as disk and separate buffer allocation is not
    /// possible or desired.
    pub fn add_with<F>(&mut self, reader: F) -> Result<()>
    where
        F: FnOnce(&CStr, &mut [u8]) -> Result<usize>,
    {
        let (current_buffer, mut remains_buffer) =
            self.buffer.split_at_mut(self.current_size + COMMANDLINE_TRAILING_SIZE);

        let remains_len = remains_buffer.len();
        // Don't need to reserve space for null terminator since buffer is already empty.
        // Not expecting callback to append any data in this case.
        if remains_len != 0 {
            // Existing null terminator is gonna be replaced with separator, so need
            // a space for another null terminator to append.
            remains_buffer = &mut remains_buffer[..remains_len - 1];
        }

        let current_commandline = CStr::from_bytes_with_nul(current_buffer).unwrap();
        let size = match reader(current_commandline, &mut remains_buffer[..]) {
            // Handle buffer too small to make sure we request additional space for null
            // terminator.
            Err(BufferTooSmall(Some(requested))) => Err(BufferTooSmall(Some(requested + 1))),
            other => other,
        }?;
        // Empty write, do nothing.
        if size == 0 {
            return Ok(());
        }
        // Appended command line data cannot have null terminator.
        if remains_buffer[..size].contains(&0u8) {
            return Err(InvalidInput);
        }

        assert!(size <= remains_buffer.len());

        // Replace current null terminator with space separator. This logic adding a redundant
        // leading space in case build is currently empty. Keep it as is for the simplicity.
        self.buffer[self.current_size] = b' ';
        // +1 for space separator
        self.current_size += size + 1;
        self.update_null_terminator();

        Ok(())
    }

    /// Append a new command line.
    /// Wrapper over `add_with`, so refer to its documentation for details.
    pub fn add(&mut self, commandline: &str) -> Result<()> {
        if commandline.is_empty() {
            return Ok(());
        }

        // +1 for space separator
        let required_capacity = commandline.len() + 1;
        if self.remaining_capacity() < required_capacity {
            return Err(Error::BufferTooSmall(Some(required_capacity)));
        }

        self.add_with(|_, out| {
            out[..commandline.len()].clone_from_slice(commandline.as_bytes());
            Ok(commandline.len())
        })
    }

    /// Get the parsed kernel command line entries.
    pub fn entries(&'a self) -> impl Iterator<Item = Result<Entry<'a>>> {
        CommandlineParser::new(self.as_str())
    }

    /// Update the command line null terminator at the end of the current buffer.
    fn update_null_terminator(&mut self) {
        self.buffer[self.current_size] = 0;
    }
}

impl core::fmt::Display for CommandlineBuilder<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl core::fmt::Write for CommandlineBuilder<'_> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.add(s).map_err(|_| core::fmt::Error)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use core::fmt::Write;

    const TEST_COMMANDLINE: &[u8] =
        b"video=vfb:640x400,bpp=32,memsize=3072000 console=ttyMSM0,115200n8 earlycon bootconfig\0";
    const NODE_TO_ADD: &str = "bootconfig";

    #[test]
    fn test_new_from_prefix() {
        let mut test_commandline = TEST_COMMANDLINE.to_vec();

        let builder = CommandlineBuilder::new_from_prefix(&mut test_commandline[..]).unwrap();
        assert_eq!(
            builder.as_str(),
            CStr::from_bytes_until_nul(TEST_COMMANDLINE).unwrap().to_str().unwrap()
        );
    }

    #[test]
    fn test_new_from_prefix_without_null_terminator() {
        let mut test_commandline = TEST_COMMANDLINE.to_vec();

        assert!(CommandlineBuilder::new_from_prefix(&mut test_commandline[..1]).is_err());
    }

    #[test]
    fn test_empty_initial_buffer() {
        let mut empty = [0u8; 0];

        assert!(CommandlineBuilder::new(&mut empty[..]).is_err());
    }

    #[test]
    fn test_add_incremental() {
        // 1 extra byte for leading space
        let mut buffer = [0u8; TEST_COMMANDLINE.len() + 1];
        let mut builder = CommandlineBuilder::new(&mut buffer[..]).unwrap();
        for element in
            CStr::from_bytes_until_nul(TEST_COMMANDLINE).unwrap().to_str().unwrap().split(' ')
        {
            builder.add(element).unwrap();
        }

        assert_eq!(
            builder.as_str(),
            CStr::from_bytes_until_nul(TEST_COMMANDLINE).unwrap().to_str().unwrap()
        );
    }

    #[test]
    fn test_add_incremental_via_fmt_write() {
        // 1 extra byte for leading space
        let mut buffer = [0u8; TEST_COMMANDLINE.len() + 1];
        let mut builder = CommandlineBuilder::new(&mut buffer[..]).unwrap();
        for element in
            CStr::from_bytes_until_nul(TEST_COMMANDLINE).unwrap().to_str().unwrap().split(' ')
        {
            write!(builder, "{}", element).unwrap();
        }

        assert_eq!(
            builder.as_str(),
            CStr::from_bytes_until_nul(TEST_COMMANDLINE).unwrap().to_str().unwrap()
        );
    }

    #[test]
    fn test_add_with_incremental() {
        // 1 extra byte for leading space
        let mut buffer = [0u8; TEST_COMMANDLINE.len() + 1];
        let mut builder = CommandlineBuilder::new(&mut buffer[..]).unwrap();

        let mut offset = 0;
        for element in
            CStr::from_bytes_until_nul(TEST_COMMANDLINE).unwrap().to_str().unwrap().split(' ')
        {
            builder
                .add_with(|current, out| {
                    let current = core::str::from_utf8(current.to_bytes()).unwrap().trim();
                    let expected =
                        core::str::from_utf8(&TEST_COMMANDLINE[..offset]).unwrap().trim();
                    assert_eq!(current, expected);

                    out[..element.len()].copy_from_slice(element.as_bytes());
                    Ok(element.len())
                })
                .unwrap();

            // +1 for space separator
            offset += element.len() + 1;
        }

        assert_eq!(
            builder.as_str(),
            CStr::from_bytes_until_nul(TEST_COMMANDLINE).unwrap().to_str().unwrap()
        );
    }

    #[test]
    fn test_add_single_node_to_full_buffer() {
        // 1 extra byte for leading space
        let mut buffer = [0u8; NODE_TO_ADD.len() + COMMANDLINE_TRAILING_SIZE + 1];
        let mut builder = CommandlineBuilder::new(&mut buffer[..]).unwrap();

        builder.add(NODE_TO_ADD).unwrap();
        assert_eq!(builder.as_str(), NODE_TO_ADD);
        assert_eq!(builder.remaining_capacity(), 0);
    }

    #[test]
    fn test_add_with_single_node_to_full_buffer() {
        // 1 extra byte for leading space
        let mut buffer = [0u8; NODE_TO_ADD.len() + COMMANDLINE_TRAILING_SIZE + 1];
        let mut builder = CommandlineBuilder::new(&mut buffer[..]).unwrap();

        assert!(builder
            .add_with(|current, out| {
                assert_eq!(current.to_bytes().len(), 0);
                out[..NODE_TO_ADD.len()].copy_from_slice(NODE_TO_ADD.as_bytes());
                Ok(NODE_TO_ADD.len())
            })
            .is_ok());
        assert_eq!(builder.remaining_capacity(), 0);
    }

    #[test]
    fn test_get_entries() {
        let mut test_commandline = TEST_COMMANDLINE.to_vec();
        let builder = CommandlineBuilder::new_from_prefix(&mut test_commandline[..]).unwrap();

        let data_from_builder = builder
            .entries()
            .map(|entry| entry.unwrap().to_string())
            .collect::<Vec<String>>()
            .join(" ");

        assert_eq!(
            data_from_builder,
            CStr::from_bytes_until_nul(TEST_COMMANDLINE).unwrap().to_str().unwrap()
        );
    }

    #[test]
    fn test_add_to_empty_not_enough_space() {
        let mut buffer = [0u8; COMMANDLINE_TRAILING_SIZE];
        let mut builder = CommandlineBuilder::new(&mut buffer[..]).unwrap();

        // + 1 requested for space separator
        assert_eq!(
            builder.add(NODE_TO_ADD),
            Err(Error::BufferTooSmall(Some(NODE_TO_ADD.len() + 1)))
        );
    }

    #[test]
    fn test_add_with_to_empty_not_enough_space_requested_space_for_separator() {
        let mut buffer = [0u8; COMMANDLINE_TRAILING_SIZE];
        let mut builder = CommandlineBuilder::new(&mut buffer[..]).unwrap();

        assert_eq!(
            builder.add_with(|_, _| { Err(Error::BufferTooSmall(Some(NODE_TO_ADD.len()))) }),
            Err(Error::BufferTooSmall(Some(NODE_TO_ADD.len() + 1)))
        );
    }

    #[test]
    fn test_empty_add_with_to_empty_succeed() {
        let mut buffer = [0u8; COMMANDLINE_TRAILING_SIZE];
        let mut builder = CommandlineBuilder::new(&mut buffer[..]).unwrap();

        assert!(builder.add_with(|_, _| { Ok(0) }).is_ok());
    }

    #[test]
    fn test_add_with_null_terminator_invalid_input() {
        let mut buffer = TEST_COMMANDLINE.to_vec();
        let mut builder = CommandlineBuilder::new(&mut buffer[..]).unwrap();

        assert_eq!(
            builder.add_with(|_, out| {
                let with_null_terminator = b"null\0terminator";
                out[..with_null_terminator.len()].copy_from_slice(&with_null_terminator[..]);
                Ok(with_null_terminator.len())
            }),
            Err(Error::InvalidInput)
        );
    }
}
