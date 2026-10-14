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

use crate::shared::Shared;
use core::{
    cell::RefMut,
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

    /// Verify that there is at least one buffer and that
    /// all buffers are at least as large as `size`.
    fn check_buffer_sizes(&self, size: usize) -> bool;
}

/// Implements for all types of fixed size preallocated buffers.
/// The buffer type `B` can be any of the following (not exhaustive):
/// * &mut [u8]
/// * Vec<u8>
/// * Box<[u8]>
/// * ArrayVec<u8>
///
/// And the buffer container type `T` can be any of the following (not exhaustive):
/// * &mut [Option<B>]
/// * Vec<Option<B>>
/// * Box<[Option<B>]>
/// * ArrayVec<Option<B>>
impl<B, T> BufferPool for T
where
    B: DerefMut<Target = [u8]>,        // Buffer type
    T: DerefMut<Target = [Option<B>]>, // Buffer container type
{
    type Buffer = B;

    fn allocate(&mut self) -> Option<B> {
        self.iter_mut().find_map(|v| take(v))
    }

    fn deallocate(&mut self, buf: B) {
        swap(&mut Some(buf), self.iter_mut().find(|v| v.is_none()).unwrap());
    }

    fn check_buffer_sizes(&self, size: usize) -> bool {
        // No buffers means there aren't any buffers of our requested size.
        !self.is_empty()
            && self
                .iter()
                .filter_map(|v| if let Some(v) = v { Some(v.len()) } else { None })
                .all(|l| l >= size)
    }
}

/// Newtype wrapper around RefMut<P: BufferPool>
/// in order to forward implementation of BufferPool.
pub struct PoolRef<'a, P>(RefMut<'a, P>);

impl<'a, P: BufferPool> PoolRef<'a, P> {
    /// Construct a new PoolRef around a given RefMut<P>
    pub fn new(pool: RefMut<'a, P>) -> Self {
        Self(pool)
    }
}

impl<'a, P: BufferPool> BufferPool for PoolRef<'a, P> {
    type Buffer = P::Buffer;

    fn allocate(&mut self) -> Option<Self::Buffer> {
        self.0.allocate()
    }

    fn deallocate(&mut self, buf: Self::Buffer) {
        self.0.deallocate(buf)
    }

    fn check_buffer_sizes(&self, size: usize) -> bool {
        self.0.check_buffer_sizes(size)
    }
}

impl<T: BufferPool> Shared<T> {
    /// Try to allocate a [ScopedBuffer]
    pub fn allocate(&self) -> Option<ScopedBuffer<'_, T>> {
        self.borrow_mut().allocate().map(|v| ScopedBuffer::new(v, self))
    }

    /// Allocates a [ScopedBuffer] and waits until succeeded.
    pub async fn allocate_async(&self) -> ScopedBuffer<'_, T> {
        loop {
            match self.allocate() {
                Some(v) => return v,
                _ => yield_now().await,
            }
        }
    }
}

/// Represents a scoped buffer allocated by `BufferPool`.
pub struct ScopedBuffer<'a, T: BufferPool> {
    // Never None except during drop.
    buf: Option<T::Buffer>,
    pool: &'a Shared<T>,
}

impl<'a, T: BufferPool> ScopedBuffer<'a, T> {
    /// Create a new scoped buffer
    pub fn new(buf: T::Buffer, pool: &'a Shared<T>) -> Self {
        Self { buf: Some(buf), pool }
    }
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
