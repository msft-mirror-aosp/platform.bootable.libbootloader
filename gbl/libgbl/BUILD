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

load("@gbl//toolchain:gbl_workspace_util.bzl", "ANDROID_RUST_LINTS")
load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

rust_library(
    name = "libgbl",
    srcs = glob(
        ["**/*.rs"],
        exclude = ["tests/**/*.rs"],
    ),
    aliases = {"@itertools_noalloc": "itertools_noalloc"},
    edition = "2021",
    rustc_flags = ANDROID_RUST_LINTS,
    visibility = ["//visibility:public"],
    deps = [
        "@arrayvec",
        "@avb",
        "@avb//:avb_bindgen",
        "@bitflags",
        "@crc32fast",
        "@cstr",
        "@gbl//libabr",
        "@gbl//libasync",
        "@gbl//libboot",
        "@gbl//libbootimg",
        "@gbl//libbootparams",
        "@gbl//libdttable",
        "@gbl//liberror",
        "@gbl//libfastboot",
        "@gbl//libfdt",
        "@gbl//libmisc",
        "@gbl//libsafemath",
        "@gbl//libstorage",
        "@gbl//libutils",
        "@itertools_noalloc",
        "@lz4_flex",
        "@spin",
        "@static_assertions",
        "@uuid",
        "@zbi",
        "@zerocopy",
        "@zune_inflate",
    ],
)

rust_test(
    name = "libgbl_test",
    aliases = {"@itertools_noalloc": "itertools_noalloc"},
    compile_data = [
        "@gbl//libstorage/test:test_data",
    ],
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
        "@gbl//libgbl/testdata:vbmeta_a.bin",
        "@gbl//libgbl/testdata:vbmeta_b.bin",
        "@gbl//libgbl/testdata:vbmeta_r.bin",
        "@gbl//libgbl/testdata:vbmeta_slotless.bin",
        "@gbl//libgbl/testdata:writeback_test_disk.bin",
        "@gbl//libgbl/testdata:zircon_a.vbmeta",
        "@gbl//libgbl/testdata:zircon_a.vbmeta.cert",
        "@gbl//libgbl/testdata:zircon_a.zbi",
        "@gbl//libgbl/testdata:zircon_b.zbi",
        "@gbl//libgbl/testdata:zircon_r.zbi",
        "@gbl//libgbl/testdata:zircon_slotless.zbi",
    ],
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        "@avb//:avb_crypto_ops_sha_impl_staticlib",
        "@avb//:avb_test",
        "@gbl//libasync:cyclic_executor",
        "@gbl//libavb:sysdeps",
        "@gbl//libstorage:libstorage_testlib",
        "@itertools",
        "@itertools_noalloc",
        "@static_assertions",
        "@uuid",
    ],
)
