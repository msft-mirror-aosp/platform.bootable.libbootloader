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

//! Standalone performance benchmark for BoringSSL SHA-256 and SHA-512 throughput.

use bssl_sys::{
    SHA256_Final, SHA256_Init, SHA256_Update, SHA512_Final, SHA512_Init, SHA512_Update, SHA256_CTX,
    SHA512_CTX,
};
use libboringssl::CRYPTO_has_asm;
use libutils::constants::{KiB, MiB};
use std::time::Instant;

fn sha256_bench(data: &[u8], iterations: usize) {
    let start = Instant::now();
    let mut digest = [0u8; 32];
    for _ in 0..iterations {
        let mut ctx = std::mem::MaybeUninit::<SHA256_CTX>::uninit();
        // SAFETY: Initializing and running BoringSSL SHA256 C API with valid context pointer,
        // data buffer, and 32-byte output digest buffer.
        unsafe {
            SHA256_Init(ctx.as_mut_ptr());
            SHA256_Update(ctx.as_mut_ptr(), data.as_ptr() as *const core::ffi::c_void, data.len());
            SHA256_Final(digest.as_mut_ptr(), ctx.as_mut_ptr());
        }
    }
    let elapsed = start.elapsed();
    let total_mb = (data.len() * iterations) as f64 / MiB!(1) as f64;
    let mb_per_sec = total_mb / elapsed.as_secs_f64();
    println!(
        "  SHA-256: {:.1} MB/s ({:.2} ms for {:.1} MB, {} iterations of {} MB)",
        mb_per_sec,
        elapsed.as_secs_f64() * 1000.0,
        total_mb,
        iterations,
        data.len() / MiB!(1)
    );
}

fn sha512_bench(data: &[u8], iterations: usize) {
    let start = Instant::now();
    let mut digest = [0u8; 64];
    for _ in 0..iterations {
        let mut ctx = std::mem::MaybeUninit::<SHA512_CTX>::uninit();
        // SAFETY: Initializing and running BoringSSL SHA512 C API with valid context pointer,
        // data buffer, and 64-byte output digest buffer.
        unsafe {
            SHA512_Init(ctx.as_mut_ptr());
            SHA512_Update(ctx.as_mut_ptr(), data.as_ptr() as *const core::ffi::c_void, data.len());
            SHA512_Final(digest.as_mut_ptr(), ctx.as_mut_ptr());
        }
    }
    let elapsed = start.elapsed();
    let total_mb = (data.len() * iterations) as f64 / MiB!(1) as f64;
    let mb_per_sec = total_mb / elapsed.as_secs_f64();
    println!(
        "  SHA-512: {:.1} MB/s ({:.2} ms for {:.1} MB, {} iterations of {} MB)",
        mb_per_sec,
        elapsed.as_secs_f64() * 1000.0,
        total_mb,
        iterations,
        data.len() / MiB!(1)
    );
}

fn main() {
    let has_asm = CRYPTO_has_asm();
    println!("=== BoringSSL Performance Benchmark ===");
    println!("Assembly Enabled: {}", if has_asm == 1 { "YES" } else { "NO" });

    const CHUNK_SIZE: usize = MiB!(32);
    const ITERATIONS: usize = 8;
    let data = vec![0x5au8; CHUNK_SIZE];

    println!(
        "\nRunning throughput benchmark (Total: {} MB)...",
        (CHUNK_SIZE * ITERATIONS) / MiB!(1)
    );
    sha256_bench(&data, ITERATIONS);
    sha512_bench(&data, ITERATIONS);
    println!("========================================");
}
