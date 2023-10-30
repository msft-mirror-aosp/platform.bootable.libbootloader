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

"""
This file contains rules and logic for setting up GBL workspace dependencies in the AOSP
u-boot-mainline branch.
"""

load("@gbl//toolchain:gbl_workspace_util.bzl", "android_rust_prebuilts", "gbl_llvm_prebuilts")
load("@kernel_toolchain_info//:dict.bzl", "CLANG_VERSION")

def define_gbl_workspace(name = None):
    """Set up worksapce dependencies for GBL

    Dependencies are checked out during "repo init". The rule simply maps them to the correct repo
    names.

    Args:
        name (String): Placeholder for buildifier check.
    """
    native.local_repository(
        name = "rules_rust",
        path = "external/bazelbuild-rules_rust",
    )

    native.local_repository(
        name = "rules_license",
        path = "external/bazelbuild-rules_license",
    )

    native.new_local_repository(
        name = "rules_rust_tinyjson",
        path = "external/rust/crates/tinyjson",
        build_file = "@rules_rust//util/process_wrapper:BUILD.tinyjson.bazel",
    )

    native.new_local_repository(
        name = "llvm_linux_x86_64_prebuilts",
        path = "prebuilts/clang/host/linux-x86/clang-{}".format(CLANG_VERSION),
        build_file_content = "",
    )

    native.new_local_repository(
        name = "linux_x86_64_sysroot",
        path = "build/kernel/build-tools",
        build_file_content = "",
    )

    android_rust_prebuilts(
        name = "rust_prebuilts",
        path = "prebuilts/rust/",
        build_file = "@gbl//toolchain:BUILD.android_rust_prebuilts.bazel",
    )

    native.new_local_repository(
        name = "bindgen",
        path = "prebuilts/clang-tools/linux-x86/bin",
        build_file_content = """exports_files(["bindgen"])""",
    )

    native.new_local_repository(
        name = "elfutils",
        path = "external/elfutils",
        build_file_content = """
cc_library(
    name = "elf_type_header",
    hdrs = ["libelf/elf.h"],
    visibility = ["//visibility:public"],
)
""",
    )

    native.new_local_repository(
        name = "libfdt_c",
        path = "external/dtc/libfdt",
        build_file = "@gbl//libfdt:BUILD.libfdt_c.bazel",
    )

    # Following are third party rust crates dependencies.

    THIRD_PARTY_CRATES = [
        "bitflags",
        "byteorder",
        "cfg-if",
        "crc32fast",
        "hex",
        "proc-macro2",
        "quote",
        "syn",
        "unicode-ident",
        "zerocopy",
        "zerocopy-derive",
    ]

    for crate in THIRD_PARTY_CRATES:
        native.new_local_repository(
            name = crate,
            path = "external/rust/crates/{}".format(crate),
            build_file = "//external/rust/crates/{}:BUILD".format(crate),
        )

    # Set up a repo to export LLVM tool/library/header/sysroot paths
    gbl_llvm_prebuilts(name = "gbl_llvm_prebuilts")

    # We don't register GBL toolchains here because they will be masked by toolchains from
    # `build/kleaf//:` as they are registered earlier. Instead, we will pass GBL toolchains via
    # bazel commandline argument "--extra_toolchains=@gbl//toolchain:all" when building GBL
    # targets, which allows them to be evaluated first during toolchain resolution.
