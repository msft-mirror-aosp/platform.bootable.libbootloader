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

//! UEFI object mocks to support unit tests.
//!
//! This module aliases mock objects to their standard names, so that code can just unconditionally
//! use e.g. `EfiEntry` and in test code it will switch to `MockEfiEntry`.

#![feature(negative_impls)]

pub mod protocol;
pub mod utils;

use efi_types::{EfiConfigurationTable, EfiTimerDelay};
use liberror::Result;
use mockall::mock;
use protocol::simple_text_output::{passthrough_con_out, MockSimpleTextOutputProtocol};
use std::cell::RefCell;

/// libefi types that can be used in tests as-is.
pub use efi::{efi_print, efi_println, DeviceHandle, EventNotify, EventType};

/// Holds state to set up a mock UEFI environment.
///
/// Parts of the libefi API surface doesn't translate super well to mocks, so this struct helps
/// cover over some of the awkwardness. In particular, APIs that return "views" over what is
/// really a singleton object are difficult to mock properly.
///
/// For example, the [efi::EfiEntry::system_table()] function returns a full [efi::SystemTable]
/// object, not a reference. This means that our mocks have to do the same, and return a new
/// [MockSystemTable] object - but this sort of defeats the purpose of mocks, which is to have
/// a mock that you can set up expectations ahead of time.
///
/// You can get around this in a limited fashion if the code under test only needs to grab the
/// system table once; in this case you can use the `return_once()` expectation to move the mock
/// around. But this will cause a runtime error if the code under test tries to grab the system
/// table more than once, since the mock will have been moved out already. And since grabbing the
/// system table is very common, this really restricts what you can do in a test.
///
/// [MockEfi] works around this by stashing objects like this in `thread_local` state, and the
/// mocks created at runtime just forward all their calls to this shared state. This allows
/// expectations to be placed at the EFI system level, and ignore any intermediate "view" mocks
/// that get created and destroyed over the course of the test.
pub struct MockEfi {
    /// The global [MockEfiEntry] to set expectations on.
    pub entry: MockEfiEntry,
    /// The global [MockSystemTable] to set expectations on.
    pub system_table: MockSystemTable,
    /// The global [MockSimpleTextOutputProtocol] to set expectations on.
    pub con_out: MockSimpleTextOutputProtocol,
}

thread_local! {
    pub(crate) static MOCK_EFI: RefCell<Option<MockEfi>> = RefCell::new(None);
}

impl MockEfi {
    /// Creates a new [MockEfi].
    ///
    /// The following expectations will be set by this function, and should generally not be
    /// adjusted by the caller:
    /// * `entry.system_table()` will automatically forward to `system_table`
    /// * `system_table.con_out()` will automatically forward to `con_out`
    ///
    /// Other than that, callers may set the other expectations as needed on these mocks.
    ///
    /// Once the mocks are ready, call [install] to install the thread-local state.
    pub fn new() -> Self {
        let mut entry = MockEfiEntry::default();
        entry.expect_system_table().returning(|| passthrough_system_table());

        let mut system_table = MockSystemTable::default();
        system_table.expect_con_out().returning(|| Ok(passthrough_con_out()));

        let con_out = MockSimpleTextOutputProtocol::default();

        Self { entry, system_table, con_out }
    }

    /// Installs the [MockEfi] in thread-local state.
    ///
    /// Only one [MockEfi] can be installed at a time (per thread). Attempting to install a
    /// second will panic.
    ///
    /// Returns an [InstalledMockEfi] which automatically unregisters the state on drop.
    pub fn install(self) -> InstalledMockEfi {
        MOCK_EFI.with_borrow_mut(|efi| {
            // If this error message changes the unittest will need to change as well.
            assert!(efi.is_none(), "Only one MockEfi can be installed at a time (per-thread)");
            *efi = Some(self)
        });
        InstalledMockEfi { entry: passthrough_efi_entry() }
    }
}

/// Scoped wrapper to automatically unregister the global [MockEfi] on drop.
pub struct InstalledMockEfi {
    entry: MockEfiEntry,
}

impl InstalledMockEfi {
    /// The user-facing [MockEfiEntry] to use in the code under test.
    ///
    /// This is a const ref so you cannot place expectations here, all calls will be forwarded to
    /// the installed [MockEfi] mocks.
    pub fn entry(&self) -> &MockEfiEntry {
        &self.entry
    }
}

/// [InstalledMockEfi] uses thread-local state so cannot be sent to another thread.
impl !Send for InstalledMockEfi {}

impl Drop for InstalledMockEfi {
    fn drop(&mut self) {
        MOCK_EFI.with_borrow_mut(|efi| *efi = None);
    }
}

mock! {
    /// Mock [efi::EfiEntry].
    pub EfiEntry {
        /// Returns a [MockSystemTable].
        pub fn system_table(&self) -> MockSystemTable;

        /// Returns a real [efi::DeviceHandle], which is data-only so isn't mocked.
        pub fn image_handle(&self) -> DeviceHandle;
    }
}
/// Map to the libefi name so code under test can just use one name.
pub type EfiEntry = MockEfiEntry;

/// While this mock itself isn't necessarily thread-local, passing through to the thread-local state
/// is our primary use case, so we just disallow [Send] entirely.
impl !Send for MockEfiEntry {}

/// Returns a [MockEfiEntry] that forwards all calls to `MOCK_EFI`.
fn passthrough_efi_entry() -> MockEfiEntry {
    let mut entry = MockEfiEntry::default();
    entry
        .expect_system_table()
        .returning(|| MOCK_EFI.with_borrow_mut(|efi| efi.as_mut().unwrap().entry.system_table()));
    entry
        .expect_image_handle()
        .returning(|| MOCK_EFI.with_borrow_mut(|efi| efi.as_mut().unwrap().entry.image_handle()));
    entry
}

mock! {
    /// Mock [efi::SystemTable].
    pub SystemTable {
        /// Returns a [MockBootServices].
        pub fn boot_services(&self) -> MockBootServices;

        /// Returns a [MockRuntimeServices].
        pub fn runtime_services(&self) -> MockRuntimeServices;

        /// Returns a [MockSimpleTextOutputProtocol]. This is a singleton protocol which is
        /// always-open, as opposed to most protocols which need to be opened explicitly.
        pub fn con_out(&self) -> Result<MockSimpleTextOutputProtocol>;

        /// Returns a real [efi::EfiConfigurationTable], which is data-only so isn't mocked.
        pub fn configuration_table(&self) -> Option<&'static [EfiConfigurationTable]>;
    }
}
/// Map to the libefi name so code under test can just use one name.
pub type SystemTable = MockSystemTable;

/// While this mock itself isn't necessarily thread-local, passing through to the thread-local state
/// is our primary use case, so we just disallow [Send] entirely.
impl !Send for MockSystemTable {}

/// Returns a [MockSystemTable] that forwards all calls to `MOCK_EFI`.
fn passthrough_system_table() -> MockSystemTable {
    let mut table = MockSystemTable::default();
    table
        .expect_con_out()
        .returning(|| MOCK_EFI.with_borrow_mut(|efi| efi.as_mut().unwrap().system_table.con_out()));
    table
}

mock! {
    /// Mock [efi::BootServices].
    pub BootServices {
        /// Returns an instance of the requested type `T`.
        ///
        /// This is slightly different than the original API because it's difficult to mock an
        /// [efi::Protocol] wrapping [efi::ProtocolInfo]. To simplify, we just return a mock
        /// that looks like the protocol object.
        pub fn open_protocol<T: 'static>(&self, handle: DeviceHandle) -> Result<T>;

        /// Similar to [open_protocol], returns the type `T`.
        pub fn find_first_and_open<T: 'static>(&self) -> Result<T>;

        /// Returns a [MockEvent].
        pub fn create_event(
            &self,
            event_type: EventType,
            mut cb: Option<&'static mut EventNotify<'static>>,
        ) -> Result<MockEvent>;

        /// Sets a [MockEvent] timer.
        pub fn set_timer(
            &self,
            event: &MockEvent,
            delay_type: EfiTimerDelay,
            trigger_time: u64,
        ) -> Result<()>;
    }
}
/// Map to the libefi name so code under test can just use one name.
pub type BootServices = MockBootServices;

mock! {
    /// Mock [efi::LocatedHandles].
    pub LocatedHandles {}
}
/// Map to the libefi name so code under test can just use one name.
pub type LocatedHandles = MockLocatedHandles;

mock! {
    /// Mock [efi::Event].
    pub Event {}
}
/// Map to the libefi name so code under test can just use one name.
pub type Event = MockEvent;

mock! {
    /// Mock [efi::RuntimeServices].
    pub RuntimeServices {
        /// Performs a cold reset.
        pub fn cold_reset(&self);
    }
}

/// Map to the libefi name so code under test can just use one name.
pub type RuntimeServices = MockRuntimeServices;

#[cfg(test)]
pub mod test {
    use super::*;
    use mockall::predicate::eq;
    use std::fmt::Write;

    #[test]
    fn efi_state_install() {
        MOCK_EFI.with_borrow_mut(|efi| assert!(efi.is_none()));

        // Global should still be `None` until we call `install()`.
        let mock_efi = MockEfi::new();
        MOCK_EFI.with_borrow_mut(|efi| assert!(efi.is_none()));

        let installed = mock_efi.install();
        MOCK_EFI.with_borrow_mut(|efi| assert!(efi.is_some()));

        // Global goes back to `None` once the install goes out of scope.
        drop(installed);
        MOCK_EFI.with_borrow_mut(|efi| assert!(efi.is_none()));
    }

    #[test]
    #[should_panic(expected = "Only one MockEfi can be installed at a time (per-thread)")]
    fn efi_state_double_install_fails() {
        let mock_efi = MockEfi::new();
        let mock_efi_2 = MockEfi::new();

        let installed = mock_efi.install();
        mock_efi_2.install();

        // Explicit drop to keep it in scope until here.
        drop(installed);
    }

    #[test]
    fn efi_state_con_out_write_once() {
        let mut mock_efi = MockEfi::new();
        mock_efi.con_out.expect_write_str().once().with(eq("foo 123")).return_const(Ok(()));

        let installed = mock_efi.install();
        let efi_entry = installed.entry();

        assert!(write!(efi_entry.system_table().con_out().unwrap(), "{} {}", "foo", 123).is_ok());
    }

    #[test]
    fn efi_state_con_out_write_twice_same_mock() {
        let mut mock_efi = MockEfi::new();
        mock_efi.con_out.expect_write_str().once().with(eq("foo 123")).return_const(Ok(()));
        mock_efi.con_out.expect_write_str().once().with(eq("bar 456")).return_const(Ok(()));

        let installed = mock_efi.install();
        let efi_entry = installed.entry();

        let mut con_out = efi_entry.system_table().con_out().unwrap();
        assert!(write!(con_out, "{} {}", "foo", 123).is_ok());
        assert!(write!(con_out, "{} {}", "bar", 456).is_ok());
    }

    #[test]
    fn efi_state_con_out_write_twice_different_mock() {
        let mut mock_efi = MockEfi::new();
        mock_efi.con_out.expect_write_str().once().with(eq("foo 123")).return_const(Ok(()));
        mock_efi.con_out.expect_write_str().once().with(eq("bar 456")).return_const(Ok(()));

        let installed = mock_efi.install();
        let efi_entry = installed.entry();

        // Call `write!` on two separate passthrough mocks, both should forward the calls to
        // the "real" global mock.
        //
        // A common instance of this is `efi_print!` which fetches a new `con_out` on every call.
        assert!(write!(efi_entry.system_table().con_out().unwrap(), "{} {}", "foo", 123).is_ok());
        assert!(write!(efi_entry.system_table().con_out().unwrap(), "{} {}", "bar", 456).is_ok());
    }
}
