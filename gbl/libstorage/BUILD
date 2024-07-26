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
load("@rules_rust//rust:defs.bzl", "rust_doc_test", "rust_library", "rust_test")

package(
    default_visibility = ["//visibility:public"],
)

rust_library(
    name = "libstorage",
    srcs = [
        "src/algorithm.rs",
        "src/gpt.rs",
        "src/lib.rs",
    ],
    crate_name = "gbl_storage",
    edition = "2021",
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        "@crc32fast",
        "@gbl//libasync",
        "@gbl//libsafemath",
        "@zerocopy",
    ],
)

rust_library(
    name = "libstorage_testlib",
    srcs = [
        "src/testlib.rs",
    ],
    crate_name = "gbl_storage_testlib",
    edition = "2021",
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        ":libstorage",
        "@crc32fast",
        "@gbl//libasync",
        "@gbl//libsafemath",
        "@zerocopy",
    ],
)

rust_test(
    name = "libstorage_test",
    compile_data = ["@gbl//libstorage/test:test_data"],
    crate = ":libstorage",
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        ":libstorage_testlib",
    ],
)

rust_test(
    name = "libstorage_testlib_test",
    crate = ":libstorage_testlib",
    rustc_flags = ANDROID_RUST_LINTS,
)

rust_doc_test(
    name = "libstorage_doc_test",
    crate = ":libstorage",
)
