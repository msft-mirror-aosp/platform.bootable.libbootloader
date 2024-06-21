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
pub fn poll<F: Future<Output = O>, O>(fut: &mut Pin<&mut F>) -> Option<O> {
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
