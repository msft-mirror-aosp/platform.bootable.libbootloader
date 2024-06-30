# Copyright (C) 2024 The Android Open Source Project
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

rust_library(
    name = "libgbl",
    srcs = glob(
        ["**/*.rs"],
        exclude = ["tests/**/*.rs"],
    ),
    aliases = {"@itertools_noalloc": "itertools_noalloc"},
    edition = "2021",
    visibility = ["//visibility:public"],
    deps = [
        "@avb",
        "@bitflags",
        "@crc32fast",
        "@cstr",
        "@gbl//libasync",
        "@gbl//libfastboot",
        "@gbl//libsafemath",
        "@gbl//libstorage",
        "@gbl//third_party/libzbi",
        "@itertools_noalloc",
        "@spin",
        "@static_assertions",
        "@zerocopy",
    ],
)

rust_test(
    name = "libgbl_test",
    aliases = {"@itertools_noalloc": "itertools_noalloc"},
    compile_data = ["@gbl//libstorage/test:test_data"],
    crate = ":libgbl",
    crate_features = ["uuid"],
    data = [
        "@gbl//libgbl/testdata:cert_metadata.bin",
        "@gbl//libgbl/testdata:cert_permanent_attributes.bad.bin",
        "@gbl//libgbl/testdata:cert_permanent_attributes.bad.hash",
        "@gbl//libgbl/testdata:cert_permanent_attributes.bin",
        "@gbl//libgbl/testdata:cert_permanent_attributes.hash",
        "@gbl//libgbl/testdata:sparse_test.bin",
        "@gbl//libgbl/testdata:sparse_test_blk1024.bin",
        "@gbl//libgbl/testdata:sparse_test_raw.bin",
        "@gbl//libgbl/testdata:testkey_rsa4096_pub.bin",
        "@gbl//libgbl/testdata:writeback_test_disk.bin",
        "@gbl//libgbl/testdata:zircon_a.bin",
        "@gbl//libgbl/testdata:zircon_a.vbmeta",
        "@gbl//libgbl/testdata:zircon_a.vbmeta.cert",
    ],
    deps = [
        "@avb//:avb_crypto_ops_sha_impl_staticlib",
        "@avb//:avb_test",
        "@gbl//libavb:sysdeps",
        "@gbl//libstorage:libstorage_testlib",
        "@itertools",
        "@itertools_noalloc",
        "@static_assertions",
        "@uuid",
    ],
)

rust_test(
    name = "integration_test",
    srcs = ["tests/integration_tests.rs"],
    compile_data = [
        "@gbl//libgbl/testdata:zircon_a.bin",
        "@gbl//libgbl/testdata:zircon_b.bin",
        "@gbl//libgbl/testdata:zircon_r.bin",
        "@gbl//libgbl/testdata:zircon_gpt.bin",
    ],
    deps = [
        ":libgbl",
        "@avb//:avb_crypto_ops_sha_impl_staticlib",
        "@gbl//libavb:sysdeps",
        "@gbl//libstorage",
        "@gbl//libstorage:libstorage_testlib",
    ],
)
