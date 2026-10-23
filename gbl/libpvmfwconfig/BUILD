# Copyright (C) 2026 The Android Open Source Project
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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_applicable_licenses = ["@gbl//licensing:gbl_license"],
    default_visibility = ["//visibility:public"],
)

rust_library(
    name = "libpvmfwconfig",
    srcs = glob(["src/**/*.rs"]),
    crate_name = "pvmfwconfig",
    edition = "2021",
    deps = [
        "@gbl//liberror",
        "@gbl//libsafemath",
        "@static_assertions",
        "@zerocopy",
    ],
)

rust_test(
    name = "libpvmfwconfig_test",
    crate = ":libpvmfwconfig",
)
