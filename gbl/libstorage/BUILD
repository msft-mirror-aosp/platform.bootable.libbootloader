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

load("@rules_rust//rust:defs.bzl", "rust_doc_test", "rust_library", "rust_test")

package(
    default_applicable_licenses = ["@gbl//licensing:gbl_license"],
    default_visibility = ["//visibility:public"],
)

rust_library(
    name = "libstorage",
    srcs = [
        "src/algorithm.rs",
        "src/gpt.rs",
        "src/lib.rs",
        "src/ram_block.rs",
    ],
    crate_name = "gbl_storage",
    edition = "2021",
    deps = [
        "@arrayvec",
        "@bytes",
        "@crc32fast",
        "@gbl//libasync",
        "@gbl//liberror",
        "@gbl//libgblutils",
        "@gbl//libsafemath",
        "@static_assertions",
        "@zerocopy",
    ],
)

rust_test(
    name = "libstorage_test",
    compile_data = ["@gbl//libstorage/test:test_data"],
    crate = ":libstorage",
    deps = [
        "@gbl//libgblutils:libtestutils",
        "@gbl//libutils",
    ],
)

rust_doc_test(
    name = "libstorage_doc_test",
    crate = ":libstorage",
)

rust_library(
    name = "file_block_io",
    srcs = ["src/file_block.rs"],
    crate_name = "file_block_io",
    edition = "2021",
    visibility = ["//visibility:public"],
    deps = [
        ":libstorage",
        "@bytes",
        "@gbl//liberror",
    ],
)
