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
load("@rules_cc//cc:defs.bzl", "cc_library", "cc_test")
load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_applicable_licenses = ["@gbl//licensing:gbl_license"],
    default_visibility = ["//visibility:public"],
)

rust_library(
    name = "libc",
    srcs = glob(["src/*.rs"]),
    edition = "2021",
    deps = [
        ":libc_c_staticlib",
        "@gbl//libsafemath",
    ] + select({
        "@platforms//os:linux": [":libc_deps_posix"],
        "//conditions:default": [],
    }),
)

rust_test(
    name = "libc_test",
    crate = ":libc",
    deps = [":libc_deps_posix"],
)

rust_library(
    name = "libc_deps_posix",
    srcs = ["deps/posix.rs"],
    edition = "2021",
)

cc_library(
    name = "headers",
    hdrs = [
        "include/assert.h",
        "include/bits/types/mbstate_t.h",
        "include/ctype.h",
        "include/debug.h",
        "include/errno.h",
        "include/gbl/defs.h",
        "include/gbl/print.h",
        "include/intrin.h",
        "include/inttypes.h",
        "include/locale.h",
        "include/nl_types.h",
        "include/stdio.h",
        "include/stdlib.h",
        "include/string.h",
        "include/sys/types.h",
        "include/time.h",
        "include/unistd.h",
    ],
    includes = ["include"],
)

cc_library(
    name = "libc_c",
    srcs = [
        "src/format.c",
        "src/stdlib.c",
    ],
    copts = select({
        "@platforms//os:linux": [],
        "//conditions:default": ["-D__GBL_LIBC_STUBS__"],
    }),
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
