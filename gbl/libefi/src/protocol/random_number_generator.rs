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

//! Rust wrapper for `EFI_RANDOM_NUMBER_GENERATOR_PROTOCOL`.

use crate::efi_call;
use crate::protocol::{MaybeVersioned, Protocol, ProtocolInfo};
use core::default::Default;
use efi_types::{
    EfiGuid, EfiRngProtocol, EFI_RNG_ALGORITHM_RAW_GUID_U64_0, EFI_RNG_ALGORITHM_RAW_GUID_U64_1,
    EFI_RNG_PROTOCOL_GUID_U64_0, EFI_RNG_PROTOCOL_GUID_U64_1,
};
use liberror::Result;
use zerocopy::{FromBytes, IntoBytes};

impl MaybeVersioned for EfiRngProtocol {}

/// Wraps `EFI_RANDOM_NUMBER_GENERATOR_PROTOCOL`
pub struct RandomNumberGeneratorProtocol;

impl ProtocolInfo for RandomNumberGeneratorProtocol {
    type InterfaceType = EfiRngProtocol;

    const GUID: EfiGuid =
        EfiGuid::from_u64s(EFI_RNG_PROTOCOL_GUID_U64_0, EFI_RNG_PROTOCOL_GUID_U64_1);
}

/// Requested random number generator algorithm.
pub enum RngAlgorithm {
    /// No specific algorithm is required. Up to FW to decide.
    Default,
    /// Entropy directly from the source, without it going through some deterministic
    /// random bit generator.
    Raw,
}

/// Raw entropy GUID:
/// https://uefi.org/specs/UEFI/2.10/37_Secure_Technologies.html#efi-rng-algorithm-definitions
const RAW_ALGORITHM_GUID: EfiGuid =
    EfiGuid::from_u64s(EFI_RNG_ALGORITHM_RAW_GUID_U64_0, EFI_RNG_ALGORITHM_RAW_GUID_U64_1);

impl Protocol<'_, RandomNumberGeneratorProtocol> {
    // `get_info` is deliberately not provided. See b/413744208 for details.

    /// Wrapper of `EFI_RANDOM_NUMBER_GENERATOR_PROTOCOL.get_rng()` which fills a
    /// byte slice.
    pub fn get_rng_bytes(
        &self,
        algorithm: RngAlgorithm,
        mut buffer: impl AsMut<[u8]>,
    ) -> Result<()> {
        // SAFETY:
        // * `self.interface_ptr()` points to a valid object
        //   established by `Protocol::new()`.
        // * `self.interface_ptr()` is an input parameter and will not be retained.
        //   It outlives the call.
        // * `rng_algorithm` is optional. Null is a valid value.
        // * `buffer.as_mut().as_mut_ptr()` is a non-null writable buffer.
        //   It is not retained, outlives the call, and points to `buffer.as_mut().len()`
        //   bytes that will be written to.
        unsafe {
            efi_call!(
                self.interface().get_rng,
                self.interface_ptr(),
                match algorithm {
                    RngAlgorithm::Default => core::ptr::null(),
                    RngAlgorithm::Raw => &RAW_ALGORITHM_GUID as _,
                },
                buffer.as_mut().len(),
                buffer.as_mut().as_mut_ptr(),
            )?;
        }
        Ok(())
    }

    /// Wrapper of `EFI_RANDOM_NUMBER_GENERATOR_PROTOCOL.get_rng()`
    pub fn get_rng<T: FromBytes + IntoBytes + Default>(
        &self,
        algorithm: RngAlgorithm,
    ) -> Result<T> {
        let mut value = T::default();
        self.get_rng_bytes(algorithm, value.as_bytes_mut())?;
        Ok(value)
    }
}
