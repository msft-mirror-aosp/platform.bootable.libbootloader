// Copyright (C) 2025 The Android Open Source Project
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

//! Test utilities shared across multiple GBL libraries.

use safemath::SafeNum;
use std::{
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
};

/// Helper object for allocating aligned buffer.
///
/// Typically this will be used with `u8` bytes, but is generic so it can
/// also work with things like `MaybeUninit<u8>`.
///
/// Using a non-byte-size `T` will cause a runtime panic.
#[derive(Debug)]
pub struct AlignedBuffer<T = u8> {
    buffer: Vec<T>,
    size: usize,
    alignment: usize,
}

impl<T> AlignedBuffer<T> {
    /// Returns the offset to the aligned part of `buffer`.
    fn offset(&self) -> usize {
        // This math doesn't make sense for non-byte-size `T`, and since
        // this code is test-only it's easier to just panic than to try
        // to be fancier with generics to restrict the types.
        assert_eq!(size_of::<T>(), 1);
        let addr = SafeNum::from(self.buffer.as_ptr() as usize);
        (addr.round_up(self.alignment) - addr).try_into().unwrap()
    }
}

impl<T: Default + Clone> AlignedBuffer<T> {
    /// Allocates a buffer with default contents.
    pub fn new(size: usize, alignment: usize) -> Self {
        Self { buffer: vec![Default::default(); alignment + size - 1], size, alignment }
    }

    /// Allocates a buffer and initializes with data.
    pub fn new_with_data(data: &[T], alignment: usize) -> Self {
        let mut res = Self::new(data.len(), alignment);
        res.clone_from_slice(data);
        res
    }
}

impl<U> AlignedBuffer<MaybeUninit<U>>
where
    MaybeUninit<U>: Clone,
{
    /// Allocates a buffer of [MaybeUninit::uninit()].
    pub fn new_uninit(size: usize, alignment: usize) -> Self {
        let mut buffer = Vec::new();
        buffer.resize(alignment + size - 1, MaybeUninit::uninit());
        Self { buffer, size, alignment }
    }
}

impl<T> Deref for AlignedBuffer<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        let offset = self.offset();
        &self.buffer[offset..][..self.size]
    }
}

impl<T> DerefMut for AlignedBuffer<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        let offset = self.offset();
        &mut self.buffer[offset..][..self.size]
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn aligned_buffer_check_len_alignment() {
        let size = 128;
        let alignment = 8;
        let buf: AlignedBuffer<u8> = AlignedBuffer::new(size, alignment);

        assert_eq!(buf.len(), size);
        assert_eq!(buf.as_ptr().align_offset(alignment), 0);
    }

    #[test]
    fn aligned_buffer_check_alignment_data() {
        let alignment = 8;
        let data: Vec<u8> = (0..50).collect();
        let buf = AlignedBuffer::new_with_data(&data, alignment);

        assert_eq!(buf.as_ptr().align_offset(alignment), 0);
        assert_eq!(&buf[..], &data);
    }

    #[test]
    fn aligned_buffer_uninit_check_len_alignment() {
        let size = 128;
        let alignment = 8;
        let buf: AlignedBuffer<MaybeUninit<u8>> = AlignedBuffer::new_uninit(128, size);

        assert_eq!(buf.len(), size);
        assert_eq!(buf.as_ptr().align_offset(alignment), 0);
    }

    #[test]
    fn aligned_buffer_check_alignment_data_after_modification() {
        let alignment = 8;
        let mut buf = AlignedBuffer::new(10, alignment);
        let new_data: Vec<u8> = (0..10).collect();
        buf.copy_from_slice(&new_data);

        assert_eq!(buf.as_ptr().align_offset(alignment), 0);
        assert_eq!(&buf[..], &new_data);
    }
}
