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

//! Safe wrappers for avb hash functions

use avb_bindgen::{
    avb_sha256_final, avb_sha256_init, avb_sha256_update, avb_sha512_final, avb_sha512_init,
    avb_sha512_update, AvbSHA256Ctx, AvbSHA512Ctx, AVB_SHA256_DIGEST_SIZE, AVB_SHA512_DIGEST_SIZE,
};

// TODO: replace this with a dedicated hash crate (b/578053216).

pub(crate) trait Hasher {
    const DIGEST_SIZE: usize;
    type Output;

    /// Create and initialize the hasher
    fn new() -> Self;

    /// Update the hasher with more data
    fn update(&mut self, data: &[u8]);

    /// Return hash value
    fn finish(&mut self) -> Self::Output;
}

macro_rules! impl_hasher {
    (
        $hasher_name:ident,                // e.g., Sha512
        $ctx_type:ty,                      // e.g., AvbSHA512Ctx
        $digest_size_const:ident,          // e.g., AVB_SHA512_DIGEST_SIZE
        $init_fn:ident,                    // e.g., avb_sha512_init
        $update_fn:ident,                  // e.g., avb_sha512_update
        $final_fn:ident                    // e.g., avb_sha512_final
    ) => {
        pub(crate) struct $hasher_name($ctx_type);

        // Generate the implementation block
        impl Hasher for $hasher_name {
            const DIGEST_SIZE: usize = $digest_size_const as usize;
            type Output = [u8; Self::DIGEST_SIZE];

            /// Create and initialize the hasher
            fn new() -> Self {
                let mut ctx = <$ctx_type>::default();
                // Safety: We are passing a non-null, aligned pointer to a valid, stack-allocated
                // instance. The pointer is valid for the duration of the C call.
                unsafe { $init_fn(&mut ctx as *mut $ctx_type) };
                Self(ctx)
            }

            /// Update the hasher with more data
            fn update(&mut self, data: &[u8]) {
                // Safety: The first argument is a non-null, aligned pointer to `self.0`, which is
                // a valid context guaranteed to be initialized by the `new()` constructor.
                // `data.as_ptr()` points to a valid buffer (a byte slice), which is guaranteed to
                // be readable for `data.len()` bytes.
                unsafe { $update_fn(&mut self.0 as *mut $ctx_type, data.as_ptr(), data.len()) };
            }

            /// Return hash value
            fn finish(&mut self) -> Self::Output {
                // Safety: The first argument is a non-null, aligned pointer to `self.0`, which is
                // a valid context guaranteed to be initialized by the `new()` constructor. The C
                // function `$final_fn` returns a valid, non-null pointer to an internal buffer
                // containing the final digest. The C API guarantees this buffer is at least
                // `DIGEST_SIZE` bytes. The pointer's lifetime is tied to `&mut self`. It is used
                // immediately with `from_raw_parts` to create a slice and copy the data into an
                // array (via `try_into`).
                unsafe {
                    let ptr = $final_fn(&mut self.0 as *mut $ctx_type);
                    core::slice::from_raw_parts(ptr, Self::DIGEST_SIZE).try_into().unwrap()
                }
            }
        }
    };
}

impl_hasher!(
    Sha512,
    AvbSHA512Ctx,
    AVB_SHA512_DIGEST_SIZE,
    avb_sha512_init,
    avb_sha512_update,
    avb_sha512_final
);

impl_hasher!(
    Sha256,
    AvbSHA256Ctx,
    AVB_SHA256_DIGEST_SIZE,
    avb_sha256_init,
    avb_sha256_update,
    avb_sha256_final
);

/// Implements `liblp::HashOps` for `Sha256` to enable parsing super partition metadata.
///
/// The `liblp` crate requires a SHA256 hasher to verify metadata checksums when parsing
/// the Logical Partition (LP) metadata from the super partition. By implementing this
/// trait, we can reuse the existing AVB-based `Sha256` hasher instead of creating a
/// separate implementation.
impl liblp::HashOps for Sha256 {
    fn sha256_init(&mut self) {
        *self = Self::new();
    }

    fn sha256_update(&mut self, data: &[u8]) {
        self.update(data);
    }

    fn sha256_final(&mut self) -> [u8; 32] {
        self.finish()
    }
}
