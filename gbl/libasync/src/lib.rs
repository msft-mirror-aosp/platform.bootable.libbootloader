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

//! This file provides async utility APIs used by GBL.
//!
//! They are mainly barebone APIs for busy waiting and polling Futures. There is no support for
//! sleep/wake or threading.

#![cfg_attr(not(test), no_std)]

use core::{
    future::Future,
    pin::{pin, Pin},
    ptr::null,
    task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
};

/// Clone method for `NOOP_VTABLE`.
fn noop_clone(_: *const ()) -> RawWaker {
    noop_raw_waker()
}

/// Noop method for `wake`, `wake_by_ref` and `drop` in `RawWakerVTable`.
fn noop_wake_method(_: *const ()) {}

/// A noop `RawWakerVTable`
const NOOP_VTABLE: RawWakerVTable =
    RawWakerVTable::new(noop_clone, noop_wake_method, noop_wake_method, noop_wake_method);

/// Creates a noop instance that does nothing.
fn noop_raw_waker() -> RawWaker {
    RawWaker::new(null(), &NOOP_VTABLE)
}

/// Repetitively polls and blocks until a future completes.
pub fn block_on<O>(fut: impl Future<Output = O>) -> O {
    let mut fut = pin!(fut);
    loop {
        match poll(&mut fut) {
            Some(res) => return res,
            _ => {}
        }
    }
}

/// Polls a Future.
///
/// Returns Some(_) if ready, None otherwise.
pub fn poll<F: Future<Output = O> + ?Sized, O>(fut: &mut Pin<&mut F>) -> Option<O> {
    // SAFETY:
    // * All methods for noop_raw_waker() are either noop or have no shared state. Thus they are
    //   thread-safe.
    let waker = unsafe { Waker::from_raw(noop_raw_waker()) };
    let mut context = Context::from_waker(&waker);
    match fut.as_mut().poll(&mut context) {
        Poll::Pending => None,
        Poll::Ready(res) => Some(res),
    }
}

/// `Yield` implements a simple API for yielding control once to the executor.
struct Yield(bool);

impl Future for Yield {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Self::Output> {
        self.0 = !self.0;
        match self.0 {
            true => Poll::Pending,
            _ => Poll::Ready(()),
        }
    }
}

/// Yield the execution once.
pub async fn yield_now() {
    Yield(false).await
}

/// `YieldCounter` maintains a counter and yield control to executor once it overflows a given
/// threshold. When overflow occurs, the counter value is reset and the carry over is discarded.
pub struct YieldCounter {
    threshold: u64,
    current: u64,
}

impl YieldCounter {
    /// Creates an instance with a given threshold.
    pub fn new(threshold: u64) -> Self {
        Self { threshold, current: 0 }
    }

    /// Increments the current counter and yield execution if the value overflows the threshold.
    pub async fn increment(&mut self, inc: u64) {
        self.current = self.current.saturating_sub(inc);
        if self.current == 0 {
            self.current = self.threshold;
            yield_now().await;
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn test() {
        let mut counter = YieldCounter::new(1);
        let mut fut = pin!(async move {
            counter.increment(2).await;
            counter.increment(2).await;
        });

        assert!(poll(&mut fut).is_none());
        assert!(poll(&mut fut).is_none());
        assert!(poll(&mut fut).is_some());
    }
}
