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

//! ImageBuffer is helper to store uninitialized memory buffer. And work with it allowing to read
//! into the buffer and retrieve initialized part.
//!
//! Similar to [ReadBuf](https://docs.rs/tokio/latest/tokio/io/struct.ReadBuf.html) but works in
//! `no_std`.

use core::mem::MaybeUninit;
use liberror::{Error, Result};

/// Wrapper class for buffer received with [get_buffer] function.
///
/// Helps to keep track of allocated/init memory and avoid getting same buffer more than once.
#[derive(Debug)]
pub struct ImageBuffer<'a> {
    buffer: Option<&'a mut [MaybeUninit<u8>]>,
    // number of initialized and filled bytes.
    used_bytes: usize,
}

// Unstable MaybeUninit API
// feature = "maybe_uninit_slice", issue = "63569"

// Assuming all the elements are initialized, get a mutable slice to them.
//
// # Safety
//
// It is up to the caller to guarantee that the `MaybeUninit<T>` elements
// really are in an initialized state.
// Calling this when the content is not yet fully initialized causes undefined behavior.
#[inline(always)]
unsafe fn slice_assume_init_mut<T>(slice: &mut [MaybeUninit<T>]) -> &mut [T] {
    // SAFETY: Caller must make sure provided data is initialized.
    unsafe { &mut *(slice as *mut [MaybeUninit<T>] as *mut [T]) }
}

// Assuming all the elements are initialized, get a slice of them.
//
// # Safety
//
// It is up to the caller to guarantee that the `MaybeUninit<T>` elements
// really are in an initialized state.
// Calling this when the content is not yet fully initialized causes undefined behavior.
#[inline(always)]
unsafe fn slice_assume_init_ref<T>(slice: &[MaybeUninit<T>]) -> &[T] {
    // SAFETY: Caller must make sure provided data is initialized.
    unsafe { &*(slice as *const [MaybeUninit<T>] as *const [T]) }
}

impl ImageBuffer<'_> {
    /// Create new ImageBuffer from buffer and used_bytes
    pub fn new(buffer: &mut [MaybeUninit<u8>]) -> ImageBuffer {
        ImageBuffer { buffer: Some(buffer), used_bytes: 0 }
    }

    /// Total buffer capacity.
    pub fn capacity(&self) -> usize {
        self.buffer.as_ref().unwrap().len()
    }

    /// Increase used part of the buffer by `len`
    ///
    /// Return:
    /// Error() - if current used_bytes + len > capacity, or causes arithmetic overflow.
    /// Ok(()) - on success
    ///
    /// SAFETY:
    /// It is up to the user to guarantee that `len` bytes for tail was initialized and filled.
    pub unsafe fn advance_used(&mut self, len: usize) -> Result<()> {
        let Some(new_len) = self.used_bytes.checked_add(len) else {
            return Err(Error::Other(Some("Used bytes overflow")));
        };
        if new_len > self.capacity() {
            return Err(Error::BufferTooSmall(Some(new_len)));
        }
        self.used_bytes = new_len;
        Ok(())
    }

    /// Return used and tail parts of the buffer
    pub fn get_split(&self) -> (&[u8], &[MaybeUninit<u8>]) {
        let (used, tail) = self.buffer.as_ref().unwrap().split_at(self.used_bytes);
        // SAFETY:
        //
        // ImageBuffer user guarantees that changing used elements means they were initialized.
        // And object assumes initialized only for slice [..used_bytes]
        let initialized = unsafe { slice_assume_init_ref(used) };
        (initialized, tail)
    }

    /// Return used and tail parts of the buffer
    pub fn get_split_mut(&mut self) -> (&mut [u8], &mut [MaybeUninit<u8>]) {
        let (used, tail) = self.buffer.as_mut().unwrap().split_at_mut(self.used_bytes);
        // SAFETY:
        //
        // ImageBuffer user guaranties that changing used elements means they were initialized.
        // And object assumes initialized only for slice [..used_bytes]
        let initialized = unsafe { slice_assume_init_mut(used) };
        (initialized, tail)
    }

    /// Slice of the buffer that is used
    pub fn used(&self) -> &[u8] {
        let (used, _) = self.get_split();
        used
    }

    /// Slice of the buffer that is used
    pub fn used_mut(&mut self) -> &mut [u8] {
        let (used, _) = self.get_split_mut();
        used
    }

    /// Return part of the buffer that is not used
    pub fn tail(&mut self) -> &mut [MaybeUninit<u8>] {
        let (_, tail) = self.get_split_mut();
        tail
    }
}

impl AsRef<[MaybeUninit<u8>]> for ImageBuffer<'_> {
    fn as_ref(&self) -> &[MaybeUninit<u8>] {
        self.buffer.as_ref().unwrap()
    }
}

impl AsMut<[MaybeUninit<u8>]> for ImageBuffer<'_> {
    fn as_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.buffer.as_mut().unwrap()
    }
}

impl PartialEq for ImageBuffer<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.used() == other.used()
    }
}

#[cfg(test)]
/// Helper to create ImageBuffers from Vec<u8>
pub struct ImageBufferVec {
    buf: Vec<u8>,
}

#[cfg(test)]
impl ImageBufferVec {
    pub fn new(buf: Vec<u8>) -> Self {
        Self { buf }
    }

    pub fn get(&mut self) -> ImageBuffer {
        ImageBuffer::new(Self::slice_assume_not_init_mut(self.buf.as_mut_slice()))
    }

    fn slice_assume_not_init_mut<T>(slice: &mut [T]) -> &mut [MaybeUninit<T>] {
        // SAFETY: similar to safety notes for `slice_get_ref`, but we have a
        // mutable reference which is also guaranteed to be valid for writes.
        unsafe { &mut *(slice as *mut [T] as *mut [MaybeUninit<T>]) }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_image_buffer_capacity() {
        assert_eq!(ImageBufferVec::new(vec![0u8; 0]).get().capacity(), 0);
        assert_eq!(ImageBufferVec::new(vec![0u8; 0]).get().capacity(), 0);
        assert_eq!(ImageBufferVec::new(vec![0u8; 1]).get().capacity(), 1);
        assert_eq!(ImageBufferVec::new(vec![0u8; 100]).get().capacity(), 100);
        assert_eq!(
            ImageBufferVec::new(vec![0u8; 128 * 1024 * 1024]).get().capacity(),
            128 * 1024 * 1024
        );
    }

    #[test]
    fn test_image_buffer_used() {
        let mut img_buf_vec = ImageBufferVec::new(vec![0u8; 100]);
        let mut img_buf = img_buf_vec.get();
        assert_eq!(img_buf.used().len(), 0);
        assert_eq!(img_buf.used_mut().len(), 0);
        // SAFETY:
        // All data in img_buf is initialized since it was created from vec
        unsafe { img_buf.advance_used(1).unwrap() };
        assert_eq!(img_buf.used().len(), 1);
        assert_eq!(img_buf.used_mut().len(), 1);
        // SAFETY:
        // All data in img_buf is initialized since it was created from vec
        unsafe { img_buf.advance_used(3).unwrap() };
        assert_eq!(img_buf.used().len(), 4);
        assert_eq!(img_buf.used_mut().len(), 4);
        assert_eq!(
            // SAFETY:
            // All data in img_buf is initialized since it was created from vec
            unsafe { img_buf.advance_used(1024) },
            Err(Error::BufferTooSmall(Some(1028)))
        );
        assert_eq!(img_buf.used().len(), 4);
        assert_eq!(img_buf.used_mut().len(), 4);
    }

    #[test]
    fn test_image_buffer_get_split() {
        let mut img_buf_vec = ImageBufferVec::new(vec![0u8, 1, 2, 3]);
        let mut img_buf = img_buf_vec.get();

        assert_eq!(img_buf.used(), [].as_slice());
        assert_eq!(img_buf.used_mut(), [].as_mut_slice());
        assert_eq!(img_buf.tail().len(), 4);
        let (used, tail) = img_buf.get_split();
        assert_eq!(used, [].as_slice());
        assert_eq!(tail.len(), 4);

        let (used, tail) = img_buf.get_split_mut();
        assert_eq!(used, [].as_mut_slice());
        assert_eq!(tail.len(), 4);

        // SAFETY:
        // All data in img_buf is initialized since it was created from vec
        unsafe { img_buf.advance_used(2).unwrap() };
        assert_eq!(img_buf.used(), [0, 1].as_slice());
        assert_eq!(img_buf.used_mut(), [0, 1].as_mut_slice());
        assert_eq!(img_buf.tail().len(), 2);
        let (used, tail) = img_buf.get_split();
        assert_eq!(used, [0, 1].as_slice());
        assert_eq!(tail.len(), 2);
        let (used, tail) = img_buf.get_split_mut();
        assert_eq!(used, [0, 1].as_mut_slice());
        assert_eq!(tail.len(), 2);

        // SAFETY:
        // All data in img_buf is initialized since it was created from vec
        unsafe { img_buf.advance_used(2).unwrap() };
        assert_eq!(img_buf.used(), [0, 1, 2, 3].as_slice());
        assert_eq!(img_buf.used_mut(), [0, 1, 2, 3].as_mut_slice());
        assert_eq!(img_buf.tail().len(), 0);
        let (used, tail) = img_buf.get_split();
        assert_eq!(used, [0, 1, 2, 3].as_slice());
        assert_eq!(tail.len(), 0);
        let (used, tail) = img_buf.get_split_mut();
        assert_eq!(used, [0, 1, 2, 3].as_mut_slice());
        assert_eq!(tail.len(), 0);
    }

    #[test]
    fn test_image_buffer_eq_not_init() {
        assert_eq!(
            ImageBufferVec::new(vec![0u8, 1, 2]).get(),
            ImageBufferVec::new(vec![0u8, 1, 2]).get()
        );
    }

    #[test]
    fn test_image_buffer_eq_init_same() {
        let mut v1 = ImageBufferVec::new(vec![0u8, 1, 2]);
        let mut v2 = ImageBufferVec::new(vec![0u8, 1, 2]);
        let mut image_buffer_1 = v1.get();
        let mut image_buffer_2 = v2.get();

        // SAFETY:
        // Buffers initialised on creation.
        unsafe {
            image_buffer_1.advance_used(3).unwrap();
            image_buffer_2.advance_used(3).unwrap();
        }

        assert_eq!(image_buffer_1, image_buffer_2);
    }

    #[test]
    fn test_image_buffer_eq_diff_capacity() {
        let mut v1 = ImageBufferVec::new(vec![0u8, 1, 2]);
        let mut v2 = ImageBufferVec::new(vec![0u8, 1, 2, 3]);
        let mut image_buffer_1 = v1.get();
        let mut image_buffer_2 = v2.get();

        // SAFETY:
        // Buffers initialised on creation.
        unsafe {
            image_buffer_1.advance_used(2).unwrap();
            image_buffer_2.advance_used(2).unwrap();
        }

        assert_eq!(image_buffer_1, image_buffer_2);
    }
}
