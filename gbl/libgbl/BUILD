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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

rust_library(
    name = "libgbl",
    srcs = glob(
        ["**/*.rs"],
        exclude = ["tests/**/*.rs"],
    ),
    edition = "2021",
    visibility = ["//visibility:public"],
    deps = [
        "@avb",
        "@bitflags",
        "@crc32fast",
        "@cstr",
        "@gbl//libfastboot",
        "@gbl//libstorage",
        "@gbl//third_party/libzbi",
        "@spin",
        "@zerocopy",
    ],
)

rust_test(
    name = "libgbl_test",
    compile_data = ["@gbl//libstorage/test:test_data"],
    crate = ":libgbl",
    crate_features = ["uuid"],
    data = [
        "@gbl//libgbl/testdata:test_image.img",
        "@gbl//libgbl/testdata:testkey_rsa4096.pem",
        "@gbl//libgbl/testdata:testkey_rsa4096.pub.pem",
        "@gbl//libgbl/testdata:writeback_test_disk.bin",
    ],
    deps = [
        "@avb//:avb_test",
        "@static_assertions",
        "@uuid",
    ],
)
