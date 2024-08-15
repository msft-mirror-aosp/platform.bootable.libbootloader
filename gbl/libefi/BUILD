# Copyright (C) 2023 The Android Open Source Project
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

package(
    default_visibility = ["//visibility:public"],
)

rust_library(
    name = "libefi",
    srcs = glob(["**/*.rs"]),
    crate_name = "efi",
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        "@arrayvec",
        "@gbl//libasync",
        "@gbl//libefi_types",
        "@gbl//liberror",
        "@gbl//libgbl",
        "@gbl//libsafemath",
        "@gbl//libstorage",
        "@spin",
        "@zerocopy",
    ],
)

rust_test(
    name = "libefi_test",
    crate = ":libefi",
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        "@gbl//libavb:sysdeps",
        "@gbl//libstorage:libstorage_testlib",
        "@gbl//third_party/libzbi",
    ],
)
