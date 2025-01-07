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
    name = "libutils",
    srcs = [
        "src/lib.rs",
    ],
    edition = "2021",
    rustc_flags = ANDROID_RUST_LINTS,
    visibility = ["//visibility:public"],
    deps = [
        "@gbl//liberror",
        "@gbl//libsafemath",
    ],
)

rust_test(
    name = "test",
    crate = ":libutils",
    rustc_flags = ANDROID_RUST_LINTS,
    visibility = ["//visibility:public"],
)
