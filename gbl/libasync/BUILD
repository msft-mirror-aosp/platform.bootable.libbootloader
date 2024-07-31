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
    default_visibility = ["//visibility:public"],
)

rust_library(
    name = "libasync",
    srcs = ["src/lib.rs"],
    crate_name = "gbl_async",
    edition = "2021",
    rustc_flags = ANDROID_RUST_LINTS,
)

rust_test(
    name = "libasync_test",
    crate = ":libasync",
    rustc_flags = ANDROID_RUST_LINTS,
)

rust_library(
    name = "cyclic_executor",
    srcs = ["src/cyclic_executor.rs"],
    crate_name = "gbl_cyclic_executor",
    crate_root = "src/cyclic_executor.rs",
    edition = "2021",
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [":libasync"],
)

rust_test(
    name = "cyclic_executor_test",
    crate = ":cyclic_executor",
    rustc_flags = ANDROID_RUST_LINTS,
)
