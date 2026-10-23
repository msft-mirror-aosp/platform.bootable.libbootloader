# Copyright (C) 2026 The Android Open Source Projec5
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

load("@gbl_llvm_prebuilts//:info.bzl", "LLVM_PREBUILTS_C_INCLUDE")
load("@rules_cc//cc:defs.bzl", "cc_library")
load("@rules_rust//rust:defs.bzl", "rust_library")
load("@rules_rust_bindgen//:defs.bzl", "rust_bindgen")

package(
    default_applicable_licenses = ["@gbl//licensing:gbl_license"],
    default_visibility = ["//visibility:public"],
)

genrule(
    name = "bindgen_noop_cc",
    outs = ["bindgen_noop_cc.cc"],
    cmd = "touch $(OUTS)",
)

cc_library(
    name = "headers",
    srcs = [":bindgen_noop_cc"],
    hdrs = ["include/gbl_trace.h"],
    includes = ["include"],
)

rust_bindgen(
    name = "gbl_trace_bindgen",
    bindgen_flags = [
        "--use-core",
        "--ctypes-prefix",
        "core::ffi",
        "--allowlist-type",
        "G[bB]lTrace.*",
        "--allowlist-var",
        "GBL_TRACE_.*",
        "--with-derive-custom-struct=GblTrace.*=IntoBytes,FromBytes,Immutable,KnownLayout,PartialEq",
        "--with-derive-custom-struct=GBlTrace.*=IntoBytes,FromBytes,Immutable,KnownLayout,PartialEq",
        "--raw-line",
        """
#![cfg_attr(not(test), no_std)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(missing_docs)]

use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};
""",
    ],
    cc_lib = ":headers",
    clang_flags = [
        "-I{}".format(LLVM_PREBUILTS_C_INCLUDE),
        "-nostdinc",
    ],
    header = "include/gbl_trace.h",
)

rust_library(
    name = "gbl_trace_format",
    srcs = [":gbl_trace_bindgen"],
    deps = ["@zerocopy"],
)

rust_library(
    name = "libtrace",
    srcs = ["src/lib.rs"],
    crate_name = "trace",
    deps = [
        ":gbl_trace_format",
        "@gbl//liberror",
        "@gbl//libsafemath",
        "@zerocopy",
    ],
)
