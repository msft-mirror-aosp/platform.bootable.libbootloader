/*
 * Copyright (C) 2025 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//! Test cases for liblp using AvbSHA256 from libavb.
#[cfg(test)]
mod tests {
    extern crate avb_sysdeps;
    extern crate boringssl_sysdeps;
    use avb_bindgen::avb_sha256_final;
    use avb_bindgen::avb_sha256_init;
    use avb_bindgen::avb_sha256_update;
    use avb_bindgen::AvbSHA256Ctx;
    use liblp::HashOps;
    use std::ffi::CStr;
    use std::ffi::FromBytesUntilNulError;
    use std::fs;
    use zerocopy::transmute_ref;
    #[derive(Default)]
    struct AvbHashOps {
        ctx: AvbSHA256Ctx,
    }
    impl HashOps for AvbHashOps {
        fn sha256_init(&mut self) {
            unsafe {
                avb_sha256_init(&mut self.ctx);
            }
        }

        fn sha256_update(&mut self, data: &[u8]) {
            unsafe {
                avb_sha256_update(&mut self.ctx, data.as_ptr(), data.len());
            }
        }

        fn sha256_final(&mut self) -> [u8; 32] {
            unsafe {
                avb_sha256_final(&mut self.ctx);
            }
            self.ctx.buf
        }
    }

    fn to_cstr(name: &[i8]) -> Result<&CStr, FromBytesUntilNulError> {
        CStr::from_bytes_until_nul(transmute_ref!(name))
    }

    #[test]
    fn buffer_too_small_for_version() {
        let buffer = [0; liblp::LP_PARTITION_RESERVED_BYTES as usize - 1];
        let mut hasher = AvbHashOps::default();
        assert_eq!(liblp::parse(&buffer[..], &mut hasher), Err(liblp::LiblpError::BufferTooSmall));
    }

    const TEST_DATA_PATH: &str = "../gbl+/liblp/testdata";

    #[test]
    fn parse_super_bin() {
        let buffer = fs::read(format!("{}/super.bin", TEST_DATA_PATH))
            .expect("Failed to read testdata/super.bin");

        // You can now use the file content for your test.
        let mut hasher = AvbHashOps::default();
        let metadata = liblp::parse(&buffer, &mut hasher)
            .unwrap_or_else(|_| panic!("Failed to parse super.bin with size {}", buffer.len()));

        // Add assertions to verify the parsed data.
        let magic = metadata.geometry.magic;
        assert_eq!(magic, liblp::LP_METADATA_GEOMETRY_MAGIC);
        assert_ne!(metadata.partitions.len(), 0);
        let partition = metadata.partitions[0];
        let partition_name = to_cstr(&partition.name).unwrap().to_str().unwrap();
        assert_eq!(partition_name, "system_a");
    }
}
