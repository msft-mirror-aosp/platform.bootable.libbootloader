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

use super::shared::Shared;
use core::{
    mem::{swap, take},
    ops::{Deref, DerefMut},
};
use gbl_async::yield_now;

/// Provides interfaces for allocating and deallocating buffers.
pub trait BufferPool {
    /// The type that can be dereferenced into a buffer.
    type Buffer: DerefMut<Target = [u8]>;

    /// Allocates a buffer.
    ///
    /// * Returns Some(_) on success.
    /// * Returns None if buffer is not available.
    fn allocate(&mut self) -> Option<Self::Buffer>;

    /// Deallocates a buffer.
    fn deallocate(&mut self, buf: Self::Buffer);
}

// Implements for all types of fixed size preallocated buffers, including `&mut [&mut [u8]]`,
// `Vec<Vec<u8>`, `&mut [Vec<u8>]` and `Vec<&mut [u8]>`.
impl<B, T> BufferPool for T
where
    B: DerefMut<Target = [u8]> + Default, // Can be `&mut [u8]`, `Vec<u8>`
    T: DerefMut<Target = [B]>,            // Can be `&mut [B]`, `Vec<B>`
{
    type Buffer = B;

    fn allocate(&mut self) -> Option<B> {
        self.iter_mut().find_map(|v| (v.len() > 0).then_some(take(v)))
    }

    fn deallocate(&mut self, mut buf: B) {
        swap(&mut buf, self.iter_mut().find(|v| v.len() == 0).unwrap());
    }
}

impl<T: BufferPool> Shared<T> {
    // Try allocate a [ScopedBuffer]
    pub(crate) fn allocate(&self) -> Option<ScopedBuffer<T>> {
        self.borrow_mut().allocate().map(|v| ScopedBuffer { buf: Some(v), pool: self })
    }

    // Allocates a [ScopedBuffer] and waits until succeed.
    pub(crate) async fn allocate_async(&self) -> ScopedBuffer<T> {
        loop {
            match self.allocate() {
                Some(v) => return v,
                _ => yield_now().await,
            }
        }
    }
}

/// Represents a scoped buffer allocated by `BufferPool`.
pub(crate) struct ScopedBuffer<'a, T: BufferPool> {
    buf: Option<T::Buffer>,
    pool: &'a Shared<T>,
}

impl<T: BufferPool> Drop for ScopedBuffer<'_, T> {
    fn drop(&mut self) {
        self.pool.borrow_mut().deallocate(self.buf.take().unwrap())
    }
}

impl<T: BufferPool> Deref for ScopedBuffer<'_, T> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.buf.as_ref().unwrap()
    }
}

impl<T: BufferPool> DerefMut for ScopedBuffer<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.buf.as_mut().unwrap()
    }
}
