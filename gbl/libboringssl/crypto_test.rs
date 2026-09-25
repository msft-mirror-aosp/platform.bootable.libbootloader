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

//! Presubmit verification tests for BoringSSL assembly acceleration and test vectors.

use bssl_sys::{
    SHA256_Final, SHA256_Init, SHA256_Update, SHA512_Final, SHA512_Init, SHA512_Update, SHA256_CTX,
    SHA512_CTX,
};
use libboringssl::CRYPTO_has_asm;

fn sha256(data: &[u8]) -> [u8; 32] {
    let mut ctx = std::mem::MaybeUninit::<SHA256_CTX>::uninit();
    let mut digest = [0u8; 32];
    // SAFETY: Initializing and running BoringSSL SHA256 C API with valid context pointer,
    // data buffer, and 32-byte output digest buffer.
    unsafe {
        SHA256_Init(ctx.as_mut_ptr());
        SHA256_Update(ctx.as_mut_ptr(), data.as_ptr() as *const core::ffi::c_void, data.len());
        SHA256_Final(digest.as_mut_ptr(), ctx.as_mut_ptr());
    }
    digest
}

fn sha512(data: &[u8]) -> [u8; 64] {
    let mut ctx = std::mem::MaybeUninit::<SHA512_CTX>::uninit();
    let mut digest = [0u8; 64];
    // SAFETY: Initializing and running BoringSSL SHA512 C API with valid context pointer,
    // data buffer, and 64-byte output digest buffer.
    unsafe {
        SHA512_Init(ctx.as_mut_ptr());
        SHA512_Update(ctx.as_mut_ptr(), data.as_ptr() as *const core::ffi::c_void, data.len());
        SHA512_Final(digest.as_mut_ptr(), ctx.as_mut_ptr());
    }
    digest
}

#[test]
fn test_assembly_enabled() {
    let has_asm = CRYPTO_has_asm();
    assert_eq!(has_asm, 1, "BoringSSL must be compiled with assembly support enabled!");
}

#[test]
fn test_sha256_vectors() {
    // Empty string
    assert_eq!(
        sha256(b""),
        [
            0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f,
            0xb9, 0x24, 0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 0xa4, 0x95, 0x99, 0x1b,
            0x78, 0x52, 0xb8, 0x55,
        ]
    );

    // "The quick brown fox jumps over the lazy dog"
    assert_eq!(
        sha256(b"The quick brown fox jumps over the lazy dog"),
        [
            0xd7, 0xa8, 0xfb, 0xb3, 0x07, 0xd7, 0x80, 0x94, 0x69, 0xca, 0x9a, 0xbc, 0xb0, 0x08,
            0x2e, 0x4f, 0x8d, 0x56, 0x51, 0xe4, 0x6d, 0x3c, 0xdb, 0x76, 0x2d, 0x02, 0xd0, 0xbf,
            0x37, 0xc9, 0xe5, 0x92,
        ]
    );
}

#[test]
fn test_sha512_vectors() {
    // Empty string
    assert_eq!(
        sha512(b""),
        [
            0xcf, 0x83, 0xe1, 0x35, 0x7e, 0xef, 0xb8, 0xbd, 0xf1, 0x54, 0x28, 0x50, 0xd6, 0x6d,
            0x80, 0x07, 0xd6, 0x20, 0xe4, 0x05, 0x0b, 0x57, 0x15, 0xdc, 0x83, 0xf4, 0xa9, 0x21,
            0xd3, 0x6c, 0xe9, 0xce, 0x47, 0xd0, 0xd1, 0x3c, 0x5d, 0x85, 0xf2, 0xb0, 0xff, 0x83,
            0x18, 0xd2, 0x87, 0x7e, 0xec, 0x2f, 0x63, 0xb9, 0x31, 0xbd, 0x47, 0x41, 0x7a, 0x81,
            0xa5, 0x38, 0x32, 0x7a, 0xf9, 0x27, 0xda, 0x3e,
        ]
    );

    // "The quick brown fox jumps over the lazy dog"
    assert_eq!(
        sha512(b"The quick brown fox jumps over the lazy dog"),
        [
            0x07, 0xe5, 0x47, 0xd9, 0x58, 0x6f, 0x6a, 0x73, 0xf7, 0x3f, 0xba, 0xc0, 0x43, 0x5e,
            0xd7, 0x69, 0x51, 0x21, 0x8f, 0xb7, 0xd0, 0xc8, 0xd7, 0x88, 0xa3, 0x09, 0xd7, 0x85,
            0x43, 0x6b, 0xbb, 0x64, 0x2e, 0x93, 0xa2, 0x52, 0xa9, 0x54, 0xf2, 0x39, 0x12, 0x54,
            0x7d, 0x1e, 0x8a, 0x3b, 0x5e, 0xd6, 0xe1, 0xbf, 0xd7, 0x09, 0x78, 0x21, 0x23, 0x3f,
            0xa0, 0x53, 0x8f, 0x3d, 0xb8, 0x54, 0xfe, 0xe6,
        ]
    );
}
