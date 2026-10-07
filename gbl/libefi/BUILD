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

load("@gbl//toolchain:gbl_toolchain.bzl", "dev_test")
load("@gbl//toolchain:gbl_workspace_util.bzl", "ANDROID_RUST_LINTS")
load(
    "@rules_cc//cc:defs.bzl",
    "cc_library",
    "cc_test",
)
load("@rules_rust//rust:defs.bzl", "rust_library", "rust_static_library", "rust_test")

package(
    default_applicable_licenses = ["@gbl//licensing:gbl_license"],
    default_visibility = ["//visibility:public"],
)

rust_library(
    name = "libefi",
    srcs = glob(
        ["src/**/*.rs"],
        exclude = ["src/efi_rng_c.rs"],
    ),
    crate_name = "efi",
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        "@arrayvec",
        "@avb//:avb_bindgen",
        "@bytes",
        "@cfg_if",
        "@gbl//libasync",
        "@gbl//libefi_types",
        "@gbl//liberror",
        "@gbl//libfdt",
        "@gbl//libgbl",
        "@gbl//libprofile",
        "@gbl//libsafemath",
        "@gbl//libtrace",
        "@gbl//libutils",
        "@spin",
        "@static_assertions",
        "@zerocopy",
    ],
)

rust_library(
    name = "libefi_rng",
    srcs = ["src/efi_rng_c.rs"],
    crate_name = "efi_rng",
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        ":libefi",
    ],
)

cc_library(
    name = "efi_sha_header",
    hdrs = [
        "src/efi_sha_c.h",
    ],
    defines = [
        "AVB_COMPILATION",
    ],
    includes = [
        "src/",
    ],
    deps = [
        "@avb//:headers",
    ],
)

# Add this library as a dependency when writing C++ unit tests (or userspace binaries)
# that link against Rust libraries to bring in symbols for the Rust standard library.
# Best practice is to link all rust libs together into a single static library and
# link against that, but this generates an unnecessary number of mostly unused
# rust_static_library targets if there are only a few C++ targets.
rust_static_library(
    name = "rust_dep_hack_for_cc",
    srcs = ["dep_hack/lib.rs"],
    rustc_flags = ANDROID_RUST_LINTS,
)

cc_test(
    name = "efi_avb_test",
    srcs = ["src/efi_avb_test.cpp"],
    defines = [
        "AVB_COMPILATION",
    ],
    target_compatible_with = [
        "@platforms//os:linux",
    ],
    deps = [
        ":efi_sha_header",
        ":rust_dep_hack_for_cc",
        "@avb//:avb_crypto_ops",
        "@avb//:headers",
        "@avb//:libavb_c",
        "@boringssl//:crypto_baremetal",
        "@gbl//libavb:sysdeps",
        "@gbl//libboringssl:sysdeps",
        "@gbl//libc:libc_deps_posix",
        "@gbl//libefi_types:efi_c_headers",
        "@googletest//:gtest_main",
    ],
)

rust_test(
    name = "libefi_test",
    crate = ":libefi",
    proc_macro_deps = ["@gbl//libprofile:libprofile_macros"],
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        "@avb//:libavb_c_sha_staticlib",
        "@gbl//libavb:sysdeps",
    ],
)

dev_test(
    name = "libefi_test_dev",
    target = "libefi_test",
)

rust_library(
    name = "mocks",
    testonly = True,
    srcs = glob(["mocks/**/*.rs"]),
    crate_name = "efi_mocks",
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        "@arrayvec",
        "@gbl//libefi",
        "@gbl//libefi_types",
        "@gbl//liberror",
        "@gbl//libfdt",
        "@gbl//libgbl",
        "@gbl//libprofile",
        "@mockall",
    ],
)

rust_test(
    name = "mocks_test",
    crate = ":mocks",
    rustc_flags = ANDROID_RUST_LINTS,
)
