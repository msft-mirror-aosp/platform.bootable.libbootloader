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

load("@gbl//toolchain:gbl_toolchain.bzl", "link_static_cc_library")
load("@gbl//toolchain:gbl_workspace_util.bzl", "ANDROID_RUST_LINTS")
load("@rules_cc//cc:defs.bzl", "cc_library", "cc_test")
load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//visibility:public"],
)

rust_library(
    name = "libc",
    srcs = glob(["src/*.rs"]),
    edition = "2021",
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        ":libc_c_staticlib",
        "@gbl//libsafemath",
    ],
)

rust_test(
    name = "libc_test",
    crate = ":libc",
    rustc_flags = ANDROID_RUST_LINTS,
)

rust_library(
    name = "libc_deps_posix",
    srcs = ["deps/posix.rs"],
    edition = "2021",
    rustc_flags = ANDROID_RUST_LINTS,
)

cc_library(
    name = "headers",
    hdrs = [
        "include/debug.h",
        "include/gbl/print.h",
        "include/inttypes.h",
        "include/limits.h",
        "include/stdio.h",
        "include/stdlib.h",
        "include/string.h",
        "include/sys/types.h",
    ],
    includes = ["include"],
)

cc_library(
    name = "libc_c",
    srcs = [
        "src/format.c",
    ],
    deps = [
        ":headers",
    ],
)

cc_test(
    name = "libc_c_test",
    srcs = ["src/format_test.cpp"],
    target_compatible_with = [
        "@platforms//os:linux",
    ],
    deps = [
        ":libc_c",
        "@googletest//:gtest_main",
    ],
)

link_static_cc_library(
    name = "libc_c_staticlib",
    cc_library = ":libc_c",
)
