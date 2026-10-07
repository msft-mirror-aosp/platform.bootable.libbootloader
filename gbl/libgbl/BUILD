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

load("@gbl//toolchain:gbl_toolchain.bzl", "dev_test")
load("@gbl//toolchain:gbl_workspace_util.bzl", "ANDROID_RUST_LINTS")
load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_applicable_licenses = ["@gbl//licensing:gbl_license"],
    default_visibility = ["//visibility:public"],
)

filegroup(
    name = "libgbl_prod_files",
    srcs = glob(
        ["src/**/*.rs"],
        exclude = [
            "tests/**/*.rs",
            "fuchsia_boot/**/*.rs",
        ],
    ),
)

filegroup(
    name = "libgbl_dev_files",
    srcs = glob(
        ["src/**/*.rs"],
        exclude = ["tests/**/*.rs"],
    ),
)

rust_library(
    name = "libgbl",
    srcs = select({
        "@gbl//toolchain:dev": [":libgbl_dev_files"],
        "@gbl//toolchain:prod": [":libgbl_prod_files"],
    }),
    # Used by fake avb flow on dev GBL.
    compile_data = select({
        "@gbl//toolchain:dev": ["@gbl//libgbl/testdata:android/vbmeta_disabled.img"],
        "@gbl//toolchain:prod": [],
    }),
    edition = "2024",
    proc_macro_deps = ["@gbl//libprofile:libprofile_macros"],
    rustc_flags = ANDROID_RUST_LINTS,
    visibility = ["//visibility:public"],
    deps = [
        "@arrayvec",
        "@avb",
        "@avb//:avb_bindgen",
        "@base64",
        "@bitflags",
        "@bytes",
        "@cfg_if",
        "@crc32fast",
        "@gbl//libabr",
        "@gbl//libasync",
        "@gbl//libboot",
        "@gbl//libbootimg",
        "@gbl//libbootparams",
        "@gbl//libbuild_number",
        "@gbl//libdttable",
        "@gbl//liberror",
        "@gbl//libfastboot",
        "@gbl//libfdt",
        "@gbl//libfit",
        "@gbl//liblp",
        "@gbl//libmisc",
        "@gbl//libopendice",
        "@gbl//libprofile",
        "@gbl//libpvmfwconfig",
        "@gbl//libsafemath",
        "@gbl//libstorage",
        "@gbl//libtrace",
        "@gbl//libutils",
        "@lz4_flex",
        "@static_assertions",
        "@uuid",
        "@zerocopy",
        "@zune_inflate",
    ] + select({
        "@gbl//toolchain:dev": [
            "@zbi",
        ],
        "@gbl//toolchain:prod": [],
    }),
)

rust_test(
    name = "libgbl_test",
    compile_data = [
        "@gbl//libstorage/test:test_data",
        "@gbl//libdttable/test/data:all",
        "@gbl//libfdt/test/data:all",
        "@gbl//libgbl/testdata",
    ],
    crate = ":libgbl",
    crate_features = ["uuid"],
    data = ["//libgbl/testdata"],
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        "@avb//:avb_crypto_ops_for_test",
        "@avb//:avb_test",
        "@cfg_if",
        "@gbl//libasync:cyclic_executor",
        "@gbl//libavb:sysdeps",
        "@gbl//libboringssl:sysdeps",
        "@gbl//libc:libc_deps_posix",
        "@gbl//libutils:libtestutils",
        "@spin",
    ],
)

dev_test(
    name = "libgbl_test_dev",
    target = ":libgbl_test",
)
