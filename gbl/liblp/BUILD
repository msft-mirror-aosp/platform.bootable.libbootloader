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
load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")
load("@rules_rust_bindgen//:defs.bzl", "rust_bindgen")

package(
    default_applicable_licenses = ["@gbl//licensing:gbl_license"],
    default_visibility = ["//visibility:public"],
)

# Newer version of `rust_bindgen` requires a `cc_library` target that actually produces a static
# library and instead of only headers. Thus we generate a placeholder source file to meet the
# requirement.
genrule(
    name = "bindgen_noop_cc",
    outs = ["bindgen_noop_cc.cc"],
    cmd = "touch $(OUTS)",
)

cc_library(
    name = "liblp_cc_header",
    srcs = [":bindgen_noop_cc"],
    hdrs = ["metadata_format.h"],
)

CUSTOM_STRUCT_RE = "LpMetadata.*"

CUSTOM_STRUCT_DERIVES = "Immutable,IntoBytes,FromBytes,KnownLayout,PartialEq"

rust_bindgen(
    name = "liblp_defs_bindgen",
    bindgen_flags = [
        "--ctypes-prefix",
        "core::ffi",
        "--use-core",
        "--with-derive-default",
        "--with-derive-custom-struct={}={}".format(
            CUSTOM_STRUCT_RE,
            CUSTOM_STRUCT_DERIVES,
        ),
        "--raw-line",
        """
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![cfg_attr(not(test), no_std)]
use zerocopy::{Immutable, IntoBytes, FromBytes, KnownLayout};
""",
    ],
    cc_lib = ":liblp_cc_header",
    clang_flags = [
        "-x",
        "c++",
        "-nostdinc",
        "-funsigned-char",
    ],
    header = "@gbl//liblp:metadata_format.h",
)

rust_library(
    name = "liblp_bindgen",
    srcs = [":liblp_defs_bindgen"],
    deps = ["@zerocopy"],
)

rust_library(
    name = "liblp",
    srcs = ["src/liblp.rs"],
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        ":liblp_bindgen",
        "@zerocopy",
    ],
)

rust_test(
    name = "liblp_test",
    srcs = ["src/liblp_test.rs"],
    data = ["@gbl//liblp/testdata"],
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        ":liblp",
        "@avb//:avb_bindgen",
        "@avb//:avb_crypto_ops_for_test",
        "@gbl//libavb:sysdeps",
        "@gbl//libboringssl:sysdeps",
        "@zerocopy",
    ],
)
