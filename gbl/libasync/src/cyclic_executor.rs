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

//! This library implements a simple executor using cyclic scheduling.

#![cfg_attr(not(test), no_std)]

extern crate alloc;
use alloc::{boxed::Box, vec::Vec};
use core::{future::Future, pin::Pin};
use gbl_async::poll;

/// `CyclicExecutor` is a simple single thread executor that simply cyclically polls all Futures.
#[derive(Default)]
pub struct CyclicExecutor<'a> {
    tasks: Vec<Pin<Box<dyn Future<Output = ()> + 'a>>>,
}

impl<'a> CyclicExecutor<'a> {
    /// Adds a new task.
    pub fn spawn_task(&mut self, task: impl Future<Output = ()> + 'a) {
        let mut task = Box::pin(task);
        // Schedule the task once.
        poll(&mut task.as_mut());
        self.tasks.push(task);
    }

    /// Polls all `Future`s once.
    pub fn poll(&mut self) {
        let mut idx = 0;
        while let Some(task) = self.tasks.get_mut(idx) {
            if poll(&mut task.as_mut()).is_some() {
                let _ = self.tasks.swap_remove(idx);
            } else {
                idx += 1;
            }
        }
    }

    /// Runs all `Future`s until completion.
    pub fn run(&mut self) {
        while !self.tasks.is_empty() {
            self.poll();
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use gbl_async::yield_now;
    use std::sync::Mutex;

    #[test]
    fn test_spawn_and_poll_task() {
        let val1 = Mutex::new(0);
        let val2 = Mutex::new(1);

        let mut executor: CyclicExecutor = Default::default();
        // Spawns 2 tasks.
        executor.spawn_task(async {
            *val1.try_lock().unwrap() += 1;
            yield_now().await;
            *val1.try_lock().unwrap() += 1;
            yield_now().await;
            *val1.try_lock().unwrap() += 1;
            yield_now().await;
        });
        executor.spawn_task(async {
            *val2.try_lock().unwrap() += 1;
            yield_now().await;
            *val2.try_lock().unwrap() += 1;
            yield_now().await;
            *val2.try_lock().unwrap() += 1;
            yield_now().await;
        });

        // Test that spawning a task schedules it immediately.
        assert_eq!(*val1.try_lock().unwrap(), 1);
        assert_eq!(*val2.try_lock().unwrap(), 2);

        // Polls all Futures once.
        executor.poll();
        assert_eq!(*val1.try_lock().unwrap(), 2);
        assert_eq!(*val2.try_lock().unwrap(), 3);

        // Runs to completion.
        executor.run();
        assert_eq!(*val1.try_lock().unwrap(), 3);
        assert_eq!(*val2.try_lock().unwrap(), 4);
    }
}
