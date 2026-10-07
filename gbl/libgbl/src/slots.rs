// Copyright 2023, The Android Open Source Project
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

//! Containing types and traits for querying and modifying slotted boot behavior.

use arrayvec::ArrayString;
use core::fmt::Write;
use liberror::Error;

/// A type safe container for describing the number of retries a slot has left
/// before it becomes unbootable.
/// Slot tries can only be compared to, assigned to, or assigned from other
/// tries.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct Tries(pub usize);

impl From<usize> for Tries {
    fn from(u: usize) -> Self {
        Self(u)
    }
}
impl From<u8> for Tries {
    fn from(u: u8) -> Self {
        Self(u.into())
    }
}

/// A type safe container for describing the priority of a slot.
/// Slot priorities can only be compared to, assigned to, or assigned from
/// other priorities.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Priority(usize);

impl From<usize> for Priority {
    fn from(u: usize) -> Self {
        Self(u)
    }
}
impl From<u8> for Priority {
    fn from(u: u8) -> Self {
        Self(u.into())
    }
}

/// A type safe container for describing a slot's suffix.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Suffix(char);

impl Suffix {
    /// Creates a new instance from slot suffix char.
    pub fn from_char(suffix: char) -> Result<Self, Error> {
        match suffix.is_ascii_lowercase() {
            true => Ok(Self(suffix)),
            false => Err(Error::Other(Some("Invalid slot suffix char"))),
        }
    }

    /// Returns the slot name as char.
    pub fn as_char(&self) -> char {
        self.0
    }
}

impl Default for Suffix {
    fn default() -> Self {
        Self('a')
    }
}

impl TryFrom<char> for Suffix {
    type Error = Error;

    fn try_from(suffix: char) -> Result<Self, Self::Error> {
        Self::from_char(suffix)
    }
}

/// Slot metadata describing why that slot is unbootable.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum UnbootableReason {
    /// No information is given about why this slot is not bootable.
    Unknown,
    /// This slot has exhausted its retry budget and cannot be booted.
    NoMoreTries,
    /// As part of a system update, the update agent downloads
    /// an updated image and stores it into a slot other than the current
    /// active slot.
    SystemUpdate,
    /// This slot has been marked unbootable by user request,
    /// usually as part of a system test.
    UserRequested,
    /// This slot has failed a verification check as part of
    /// Android Verified Boot.
    VerificationFailure,
}

impl Default for UnbootableReason {
    fn default() -> Self {
        Self::Unknown
    }
}

/// Describes whether a slot has successfully booted and, if not,
/// why it is not a valid boot target OR the number of attempts it has left.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Bootability {
    /// This slot has successfully booted. Carries the remaining tries value
    /// from the underlying metadata (used for informational reporting).
    Successful(Tries),
    /// This slot cannot be booted.
    Unbootable(UnbootableReason),
    /// This slot has not successfully booted yet but has
    /// one or more attempts left before either successfully booting,
    /// and being marked successful, or failing, and being marked
    /// unbootable due to having no more tries.
    Retriable(Tries),
}

impl Default for Bootability {
    fn default() -> Self {
        Self::Retriable(7u8.into())
    }
}

/// User-visible representation of a boot slot.
/// Describes the slot's moniker (i.e. the suffix),
/// its priority,
/// and information about its bootability.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct Slot {
    /// The partition suffix for the slot.
    pub suffix: Suffix,
    /// The slot's priority for booting.
    pub priority: Priority,
    /// Information about a slot's boot eligibility and history.
    pub bootability: Bootability,
}

/// Returns a slotted partition name.
pub(crate) fn slotted_part(
    part: &str,
    slot: Option<Suffix>,
) -> ArrayString<{ crate::partition::RAW_PARTITION_NAME_LEN }> {
    let mut res = ArrayString::new_const();
    match slot {
        None => write!(res, "{part}").unwrap(),
        Some(s) => write!(res, "{part}_{}", s.as_char()).unwrap(),
    }
    res
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ops::test::slot;

    #[test]
    fn test_suffix_from_char() {
        assert_eq!(Suffix::from_char('a'), Ok(Suffix('a')), "lowercase");
        assert_eq!(Suffix::from_char('b'), Ok(Suffix('b')), "lowercase");
        assert!(Suffix::from_char('A').is_err(), "uppercase");
        assert!(Suffix::from_char('%').is_err(), "not alphabet");
        assert!(Suffix::from_char('🦑').is_err(), "UTF-8 emoji");
    }

    #[test]
    fn test_slotted_part() {
        assert_eq!(slotted_part("boot", Some(slot('a').suffix)).as_ref(), "boot_a");
        assert_eq!(slotted_part("boot", Some(slot('b').suffix)).as_ref(), "boot_b");
        assert_eq!(slotted_part("boot", None).as_ref(), "boot");
    }
}
