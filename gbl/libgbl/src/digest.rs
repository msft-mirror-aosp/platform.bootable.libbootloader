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

//! GBL Digest trait that defines interface for hash computation.
//!

// TODO: b/312606477 - SW implementation should be behind feature

extern crate ring;
pub use ring::digest::Algorithm;

/// Digest output trait that return algorithm and ref to the value
pub trait Digest: AsRef<[u8]> {
    /// Get digest algorithm
    fn algorithm(&self) -> &'static Algorithm;
}

/// Context trait that implements digesting.
/// Sha256 or Sha512.
pub trait Context<D: Digest> {
    /// Create [Context] object that can calculate digest with requested algorithm.
    ///
    /// # Arguments
    ///
    /// * algorithm - requested algorithm
    fn new(algorithm: &'static Algorithm) -> Self;

    /// Process next portion of data for the digest.
    ///
    /// # Arguments
    ///
    /// * input - block of data to be processed
    fn update(&mut self, input: &[u8]);

    /// Finalise digest computation.
    ///
    /// Object is consumed to prevent reusing.
    fn finish(self) -> D;

    /// The algorithm that this context is using.
    fn algorithm(&self) -> &'static Algorithm;
}

/// Software implementation for digest Context
pub struct SwContext {
    ring_context: ring::digest::Context,
}
impl Context<SwDigest> for SwContext {
    fn new(algorithm: &'static Algorithm) -> Self
    where
        Self: Sized,
    {
        Self { ring_context: ring::digest::Context::new(algorithm) }
    }

    fn update(&mut self, input: &[u8]) {
        self.ring_context.update(input)
    }

    fn finish(self) -> SwDigest {
        SwDigest { ring_digest: self.ring_context.finish() }
    }

    fn algorithm(&self) -> &'static Algorithm {
        self.ring_context.algorithm()
    }
}

/// Software implementation of Digest.
pub struct SwDigest {
    ring_digest: ring::digest::Digest,
}
impl AsRef<[u8]> for SwDigest {
    fn as_ref(&self) -> &[u8] {
        self.ring_digest.as_ref()
    }
}
impl Digest for SwDigest {
    fn algorithm(&self) -> &'static Algorithm {
        self.ring_digest.algorithm()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Compute digest on provided input using algorithm
    fn digest(algorithm: &'static Algorithm, input: &[u8]) -> SwDigest {
        let mut ctx = SwContext::new(algorithm);
        ctx.update(input);
        ctx.finish()
    }

    #[test]
    fn test_swdigest_sha256() {
        let input = b"abc";
        let expected =
            hex::decode("BA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015AD")
                .unwrap();
        assert_eq!(digest(&ring::digest::SHA256, input).as_ref(), expected);
    }

    #[test]
    fn test_swdigest_sha512() {
        assert_eq!(
            digest(&ring::digest::SHA512, b"abc").as_ref(),
            hex::decode(concat!(
                "DDAF35A193617ABACC417349AE20413112E6FA4E89A97EA2",
                "0A9EEEE64B55D39A2192992A274FC1A836BA3C23A3FEEBBD",
                "454D4423643CE80E2A9AC94FA54CA49F",
            ))
            .unwrap()
        );
    }

    #[test]
    fn test_swdigest_sha_partial() {
        let input = b"abc";
        let expected =
            hex::decode("BA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015AD")
                .unwrap();

        let mut ctx = SwContext::new(&ring::digest::SHA256);
        for i in input.chunks(input.len()) {
            ctx.update(i);
        }

        assert_eq!(ctx.finish().as_ref(), expected);
    }
}
