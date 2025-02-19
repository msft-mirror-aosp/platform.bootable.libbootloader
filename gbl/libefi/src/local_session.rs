// Copyright 2025, The Android Open Source Project
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

use crate::{
    protocol::{
        gbl_efi_fastboot::{GblFastbootProtocol, LocalSessionContext},
        Protocol,
    },
    utils::RecurringTimer,
    EfiEntry,
};
use core::time::Duration;
use fastboot::local_session::LocalSession;
use liberror::Result;

/// Represents a local, usually graphically driven fastboot/bootmenu session.
pub struct LocalFastbootSession<'a> {
    timer: RecurringTimer<'a>,
    protocol: Protocol<'a, GblFastbootProtocol>,
    context: LocalSessionContext,
}

impl<'a> LocalFastbootSession<'a> {
    /// Starts a local fastboot session.
    pub fn start(efi_entry: &'a EfiEntry, timeout: Duration) -> Result<Self> {
        let timer = RecurringTimer::new(efi_entry, timeout)?;
        let protocol = efi_entry
            .system_table()
            .boot_services()
            .find_first_and_open::<GblFastbootProtocol>()?;
        let context = protocol.start_local_session()?;
        Ok(Self { timer, protocol, context })
    }
}

impl LocalSession for LocalFastbootSession<'_> {
    async fn update(&mut self, buf: &mut [u8]) -> Result<usize> {
        self.timer.wait().await?;
        let bufsize = self.protocol.update_local_session(&self.context, buf)?;
        Ok(bufsize)
    }
}

impl Drop for LocalFastbootSession<'_> {
    fn drop(&mut self) {
        let _ = self.protocol.close_local_session(&self.context);
    }
}
