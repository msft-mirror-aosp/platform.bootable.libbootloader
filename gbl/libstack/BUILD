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

load("@gbl//toolchain:gbl_workspace_util.bzl", "ANDROID_RUST_LINTS")
load("@rules_cc//cc:defs.bzl", "cc_library")
load("@rules_rust//rust:defs.bzl", "rust_library")

package(
    default_applicable_licenses = ["@gbl//licensing:gbl_license"],
    default_visibility = ["//visibility:public"],
)

cc_library(
    name = "c_libstack",
    srcs = glob(
        ["src/*.c"],
    ),
    copts = [
        # This *is* the stack protector and UBSan trap handler;
        # if the functions provided get instrumented, it causes infinite recursion.
        "-fno-stack-protector",
        "-fno-sanitize=all",
    ],
    deps = [
        "@gbl//libefi_types:efi_c_headers",
    ],
)

rust_library(
    name = "libstack",
    srcs = glob(
        ["**/*.rs"],
    ),
    edition = "2021",
    rustc_flags = ANDROID_RUST_LINTS,
    visibility = ["//visibility:public"],
    deps = [
        ":c_libstack",
        "@gbl//libefi_types",
    ],
)
