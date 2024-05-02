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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_static_library", "rust_test")

package(
    default_visibility = ["//visibility:public"],
)

rust_library(
    name = "libabr",
    srcs = ["src/lib.rs"],
    crate_name = "abr",
    edition = "2021",
)

rust_test(
    name = "libabr_test",
    crate = ":libabr",
)

rust_static_library(
    name = "libabr_c",
    srcs = [
        "src/c_staticlib.rs",
        "src/utils.rs",
    ],
    crate_name = "abr_c",
    crate_root = "src/c_staticlib.rs",
    edition = "2021",
    deps = [":libabr"],
)

rust_test(
    name = "libabr_c_test",
    crate = ":libabr_c",
)

test_suite(
    name = "libabr_tests",
    tests = [
        ":libabr_c_test",
        ":libabr_test",
    ],
)
