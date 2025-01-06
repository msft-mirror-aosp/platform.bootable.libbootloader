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

load("@gbl//toolchain:gbl_toolchain.bzl", "link_static_cc_library")
load("@gbl//toolchain:gbl_workspace_util.bzl", "ANDROID_RUST_LINTS")
load("@gbl_llvm_prebuilts//:info.bzl", "LLVM_PREBUILTS_C_INCLUDE")
load("@rules_rust//bindgen:defs.bzl", "rust_bindgen")
load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//visibility:public"],
)

link_static_cc_library(
    name = "libdttable_c_static",
    cc_library = "@libdttable_c",
)

rust_bindgen(
    name = "libdttable_c_bindgen",
    bindgen_flags = [
        "--use-core",
        "--with-derive-custom-struct=dt_table.*=IntoBytes,FromBytes,Immutable,KnownLayout,PartialEq",
        "--allowlist-type",
        "(dt_table.*)",
        "--allowlist-var",
        "(DT_TABLE.*)",
        "--raw-line",
        """
# ![cfg_attr(not(test), no_std)]

use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};
""",
    ],
    cc_lib = "@libdttable_c",
    # For x86_32, we need to explicitly specify 32bit architecture.
    clang_flags = select({
        "@gbl//toolchain:gbl_rust_uefi_x86_32": ["-m32"],
        "//conditions:default": ["-m64"],
    }) + [
        "-I{}".format(LLVM_PREBUILTS_C_INCLUDE),
        "-nostdinc",
    ],
    header = "@libdttable_c//:dt_table.h",
)

rust_library(
    name = "libdttable_bindgen",
    srcs = [":libdttable_c_bindgen"],
    deps = ["@zerocopy"],
)

rust_library(
    name = "libdttable",
    srcs = ["src/lib.rs"],
    crate_name = "dttable",
    edition = "2021",
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        ":libdttable_bindgen",
        ":libdttable_c_static",
        "@gbl//liberror",
        "@gbl//libsafemath",
        "@zerocopy",
    ],
)

rust_test(
    name = "libdttable_test",
    compile_data = [
        "@gbl//libdttable/test/data:all",
    ],
    crate = ":libdttable",
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        "@gbl//libfdt",
    ],
)
