// Copyright (C) 2025 The Android Open Source Project
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

//! GBL BoringSSL wrapper utilities.

#![no_std]

// SAFETY: `CRYPTO_has_asm` is a pure function defined by BoringSSL (`src/crypto/crypto.cc`)
// that takes no parameters, accesses no mutable state or pointers, and simply returns a
// compile-time constant (`1` if assembly optimizations are enabled, or `0` if compiled with
// `OPENSSL_NO_ASM`). Therefore, it has no preconditions and is always safe to call.
unsafe extern "C" {
    /// Returns 1 if BoringSSL was built with assembly optimizations enabled, or 0 if built
    /// with `OPENSSL_NO_ASM`.
    pub safe fn CRYPTO_has_asm() -> core::ffi::c_int;
}
