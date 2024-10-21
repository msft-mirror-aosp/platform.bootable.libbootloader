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

use core::{future::Future, pin::Pin};
use gbl_async::poll;

/// A container abstraction that takes input of dynamically typed [Future]s and stores them at
/// pinned memory locations.
pub trait PinFutContainer<'a> {
    /// Adds and pins a new [Future] of any type generated by the given closure `f`.
    ///
    /// If operation cannot be performed, such as due to no capacity, `f` should not be called.
    fn add_with<F: Future<Output = ()> + 'a>(&mut self, f: impl FnOnce() -> F);

    /// Calls the closure on each element in the container. Removes the element if it returns true.
    fn for_each_remove_if(
        &mut self,
        cb: impl FnMut(&mut Pin<&mut (dyn Future<Output = ()> + 'a)>) -> bool,
    );
}

/// An internal container abstraction that takes input of a specific type of [Future] and stores
/// them at pinned memory locations.
pub(crate) trait PinFutContainerTyped<'a, F: Future + 'a> {
    /// Adds and pins a new [Future] of type T into the container returned by `f`.
    ///
    /// If operation cannot be performed, such as due to no capacity, `f` should not be called.
    fn add_with(&mut self, f: impl FnOnce() -> F);

    /// Calls the closure on each element in the container. Removes the element if it returns true.
    fn for_each_remove_if(
        &mut self,
        cb: impl FnMut(&mut Pin<&mut (dyn Future<Output = ()> + 'a)>) -> bool,
    );

    /// Returns the number of items
    fn size(&mut self) -> usize {
        let mut res = 0;
        self.for_each_remove_if(|_| {
            res += 1;
            false
        });
        res
    }

    /// Polls all the [Future] once. Returns the number or unfinished ones.
    fn poll_all(&mut self) -> usize {
        let mut res = 0;
        self.for_each_remove_if(|v| {
            let finished = poll(v).is_some();
            res += usize::from(!finished);
            finished
        });
        res
    }

    /// Runs until all futures are finished
    fn run(&mut self) {
        while self.poll_all() > 0 {}
    }
}

/// `PinFutContainer` can implement `PinFutContainerTyped` for any [Future] type.
impl<'a, F: Future<Output = ()> + 'a, T: PinFutContainer<'a>> PinFutContainerTyped<'a, F> for T {
    fn add_with(&mut self, f: impl FnOnce() -> F) {
        PinFutContainer::add_with(self, move || f())
    }

    fn for_each_remove_if(
        &mut self,
        cb: impl FnMut(&mut Pin<&mut (dyn Future<Output = ()> + 'a)>) -> bool,
    ) {
        PinFutContainer::for_each_remove_if(self, cb)
    }
}

/// An implementation of `PinFutContainerTyped` backed by a preallocated slice.
pub(crate) struct PinFutSlice<'a, F> {
    arr: &'a mut [Pin<&'a mut F>],
    used: usize,
}

impl<'a, F> PinFutSlice<'a, F> {
    /// Creates a new instance
    pub fn new(arr: &'a mut [Pin<&'a mut F>]) -> Self {
        Self { arr, used: 0 }
    }
}

impl<'a, F: Future<Output = ()> + 'a> PinFutContainerTyped<'a, F> for PinFutSlice<'a, F> {
    fn add_with(&mut self, f: impl FnOnce() -> F) {
        if self.used < self.arr.len() {
            self.arr[self.used].set(f());
            self.used += 1;
        }
    }

    fn for_each_remove_if(
        &mut self,
        mut cb: impl FnMut(&mut Pin<&mut (dyn Future<Output = ()> + 'a)>) -> bool,
    ) {
        // Iterates from the end because we swap remove with the last.
        for idx in (0..self.used).rev() {
            if cb(&mut (self.arr[idx].as_mut() as _)) {
                // Swaps remove with the last element
                self.used -= 1;
                self.arr.swap(idx, self.used);
            }
        }
    }
}