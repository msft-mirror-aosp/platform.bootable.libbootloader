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

package(
    default_applicable_licenses = ["@gbl//licensing:gbl_license"],
)

rust_library(
    name = "libutils",
    srcs = glob([
        "src/**/*.rs",
    ]),
    edition = "2021",
    rustc_flags = ANDROID_RUST_LINTS,
    visibility = ["//visibility:public"],
    deps = [
        "@gbl//libasync",
        "@gbl//liberror",
        "@gbl//libsafemath",
        "@static_assertions",
        "@zeroize",
    ] + select({
        "@gbl//toolchain:gbl_rust_uefi_aarch64": [
            "@gbl//libboot/aarch64_cache_helper:aarch64_cache_helper_staticlib",
        ],
        "@gbl//toolchain:gbl_rust_uefi_aarch64_debug": [
            "@gbl//libboot/aarch64_cache_helper:aarch64_cache_helper_staticlib",
        ],
        "//conditions:default": [],
    }),
)

rust_library(
    name = "libtestutils",
    testonly = True,
    srcs = [
        "test/lib.rs",
    ],
    edition = "2021",
    rustc_flags = ANDROID_RUST_LINTS,
    visibility = ["//visibility:public"],
    deps = [
        "@gbl//libsafemath",
    ],
)

rust_test(
    name = "test",
    crate = ":libutils",
    rustc_flags = ANDROID_RUST_LINTS,
    visibility = ["//visibility:public"],
    deps = [
        ":libtestutils",
    ],
)

rust_test(
    name = "testutils_test",
    crate = ":libtestutils",
    rustc_flags = ANDROID_RUST_LINTS,
    visibility = ["//visibility:public"],
)
