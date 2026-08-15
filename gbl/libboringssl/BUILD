# Copyright (C) 2025 The Android Open Source Project
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

load("@gbl//toolchain:gbl_toolchain.bzl", "link_static_cc_library")
load("@gbl//toolchain:gbl_workspace_util.bzl", "ANDROID_RUST_LINTS")
load("@rules_cc//cc:defs.bzl", "cc_library")
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_test")
load("@rules_rust_bindgen//:defs.bzl", "rust_bindgen")

package(
    default_applicable_licenses = ["@gbl//licensing:gbl_license"],
    default_visibility = ["//visibility:public"],
)

exports_files(glob(["**/*"]))

rust_library(
    name = "sysdeps",
    srcs = ["@boringssl//:rust_bssl_crypto_sources"],
    crate_name = "boringssl_sysdeps",
    edition = "2021",
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        ":bssl-sys",
    ],
)

rust_test(
    name = "sysdeps_test",
    crate = ":sysdeps",
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        "@boringssl//:crypto_baremetal",
    ],
)

rust_library(
    name = "libboringssl",
    srcs = ["lib.rs"],
    edition = "2021",
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        ":libcrypto_c_baremetal_static",
    ],
)

rust_test(
    name = "crypto_test",
    srcs = ["crypto_test.rs"],
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        ":bssl-sys",
        ":libboringssl",
        "@boringssl//:crypto_baremetal",
    ],
)

link_static_cc_library(
    name = "libcrypto_c_baremetal_static",
    cc_library = "@boringssl//:crypto_baremetal",
)

# Additional stub headers to make bindgen work with wrapper.h
cc_library(
    name = "crypto_with_stubs",
    hdrs = glob(["include/**/*.h"]),
    includes = ["include"],
    deps = [
        "@boringssl//:crypto_baremetal",
    ],
)

rust_bindgen(
    name = "bssl-sys-raw__bindgen",
    bindgen_flags = [
        "--use-core",
        "--no-layout-tests",
        "--raw-line=#![no_std]",
        "--raw-line=#![allow(missing_docs)]",
        "--raw-line=#![allow(non_camel_case_types)]",
        "--raw-line=#![allow(non_snake_case)]",
        "--raw-line=#![allow(non_upper_case_globals)]",
        "--ctypes-prefix=core::ffi",
        "--default-enum-style=rust",
        "--default-macro-constant-type=signed",
    ],
    cc_lib = ":crypto_with_stubs",
    header = "@boringssl//:src/rust/bssl-sys/wrapper.h",
    wrap_static_fns = True,
)

filegroup(
    name = "bssl-sys-raw__bindgen_c_thunks",
    srcs = [":bssl-sys-raw__bindgen"],
    output_group = "bindgen_c_thunks",
)

cc_library(
    name = "bssl-sys-raw__bindgen_c_thunks_library",
    srcs = [":bssl-sys-raw__bindgen_c_thunks"],
    copts = ["-I."],
    deps = [":crypto_with_stubs"],
)

rust_library(
    name = "bssl-sys",
    srcs = [":bssl-sys-raw__bindgen"],
    crate_name = "bssl_sys",
    edition = "2021",
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        ":bssl-sys-raw__bindgen_c_thunks_library",
    ],
)

rust_binary(
    name = "crypto_bench",
    srcs = ["crypto_bench.rs"],
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        ":bssl-sys",
        ":libboringssl",
        "@boringssl//:crypto_baremetal",
        "@gbl//libutils",
    ],
)

cc_library(
    name = "nasm_config",
    hdrs = glob(["nasm_config/**/*.h"]),
    includes = ["nasm_config"],
    visibility = ["//visibility:public"],
)
