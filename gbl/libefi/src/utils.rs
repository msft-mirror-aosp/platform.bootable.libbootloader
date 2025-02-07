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

//! This file provides some utilities built on EFI APIs.

use crate::{EfiEntry, Event, EventType};
use core::{future::Future, time::Duration};
use efi_types::{EFI_TIMER_DELAY_TIMER_PERIODIC, EFI_TIMER_DELAY_TIMER_RELATIVE};
use gbl_async::{select, yield_now};
use liberror::Result;

/// `Timeout` provide APIs for checking timeout.
pub struct Timeout<'a> {
    efi_entry: &'a EfiEntry,
    timer: Event<'a, 'static>,
}

impl<'a> Timeout<'a> {
    /// Creates a new instance and starts the timeout timer.
    pub fn new(efi_entry: &'a EfiEntry, timeout: Duration) -> Result<Self> {
        let bs = efi_entry.system_table().boot_services();
        let timer = bs.create_event(EventType::Timer)?;
        bs.set_timer(&timer, EFI_TIMER_DELAY_TIMER_RELATIVE, timeout)?;
        Ok(Self { efi_entry, timer })
    }

    /// Checks if it has timeout.
    pub fn check(&self) -> Result<bool> {
        Ok(self.efi_entry.system_table().boot_services().check_event(&self.timer)?)
    }

    /// Resets the timeout.
    pub fn reset(&self, timeout: Duration) -> Result<()> {
        let bs = self.efi_entry.system_table().boot_services();
        bs.set_timer(&self.timer, EFI_TIMER_DELAY_TIMER_RELATIVE, timeout)?;
        Ok(())
    }
}

/// Waits for a given amount of time.
pub async fn wait(efi_entry: &EfiEntry, duration: Duration) -> Result<()> {
    // EFI boot service has a `stall` API. But it's not async.
    let timeout = Timeout::new(efi_entry, duration)?;
    while !timeout.check()? {
        yield_now().await;
    }
    Ok(())
}

/// Runs a future with timeout.
///
/// # Returns
///
/// * Returns Ok(Some(R)) if the future finishes before timeout.
/// * Returns Ok(None) if the future didn't finish before timeout.
/// * Returns Err if internal error occurs while handling EFI timer event.
pub async fn with_timeout<F: Future<Output = R>, R>(
    efi_entry: &EfiEntry,
    fut: F,
    timeout: Duration,
) -> Result<Option<R>> {
    let (timeout_res, res) = select(wait(efi_entry, timeout), fut).await;
    match timeout_res {
        Some(Err(e)) => return Err(e),
        _ => Ok(res),
    }
}

/// Wrapper helping for a periodic timer.
pub struct RecurringTimer<'a> {
    efi_entry: &'a EfiEntry,
    timer: Event<'a, 'static>,
}

impl<'a> RecurringTimer<'a> {
    /// Constructs and starts a new periodic timer.
    pub fn new(efi_entry: &'a EfiEntry, timeout: Duration) -> Result<Self> {
        let bs = efi_entry.system_table().boot_services();
        let timer = bs.create_event(EventType::Timer)?;
        bs.set_timer(&timer, EFI_TIMER_DELAY_TIMER_PERIODIC, timeout)?;
        Ok(Self { efi_entry, timer })
    }

    /// Checks whether the timer has expried.
    pub fn check(&self) -> Result<bool> {
        Ok(self.efi_entry.system_table().boot_services().check_event(&self.timer)?)
    }
}
