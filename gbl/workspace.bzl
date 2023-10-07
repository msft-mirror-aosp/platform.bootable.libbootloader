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
This file contains rules and logic to initialize GBL workspace.
"""

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
load(
    "@gbl//toolchain:gbl_workspace_util.bzl",
    "gbl_custom_rust_sysroot",
    "gbl_llvm_prebuilts",
)

def _android_external_rust_crate_archive(name, rev, build_file):
    crate_url = "https://android.googlesource.com/platform/external/rust/crates/" + \
                "{}/+archive/{}.tar.gz".format(name, rev)

    http_archive(
        name = name,
        url = crate_url,
        build_file = build_file,
    )

def fetch_remote_dependencies():
    """Download external dpendencies needed by GBL"""

    # Bazel rust rules, i.e. `rust_library()`/`rust_binary()` etc.
    http_archive(
        name = "rules_rust",
        url = "https://android.googlesource.com/platform/external/bazelbuild-rules_rust/+archive/78760f889ea04beeb880185cdee6a0ebcc71aeb2.tar.gz",
    )

    # Dependency of `@rules_rust`.
    http_archive(
        name = "rules_rust_tinyjson",
        build_file = "@rules_rust//util/process_wrapper:BUILD.tinyjson.bazel",
        url = "https://android.googlesource.com/platform/external/rust/crates/tinyjson/+archive/bd3c80f2d602fe6aab658d32af8380febee844e2.tar.gz",
    )

    # Fetch LLVM prebuilts. We used the same prebuilt branch used by Trusty and u-boot.
    http_archive(
        name = "llvm_linux_x86_64_prebuilts",
        url = "https://android.googlesource.com/platform/prebuilts/clang/host/linux-x86/+archive/18420bf70dde33f6fae92624a1dad774aeae0e83/clang-r475365b.tar.gz",
        build_file_content = "",
    )

    # Fetch Linux sysroot which is needed to configure host toolchain.
    http_archive(
        name = "linux_x86_64_sysroot",
        url = "https://android.googlesource.com/platform/prebuilts/gcc/linux-x86/host/x86_64-linux-glibc2.17-4.8/+archive/refs/heads/main.tar.gz",
        build_file_content = "",
    )

    # Fetch Android upstream rust prebuilts:
    # https://android.googlesource.com/platform/prebuilts/rust
    http_archive(
        name = "rust_prebuilts",
        build_file = "@gbl//toolchain:BUILD.android_rust_prebuilts.bazel",
        url = "https://android.googlesource.com/platform/prebuilts/rust/+archive/72697c0b73f7df92389bdad2ba6a8a513f00269a/linux-x86/1.72.0.tar.gz",
    )

    # Fetch `bindgen` from Android upstream prebuilts. It is part of
    # https://android.googlesource.com/platform/prebuilts/clang-tools
    http_archive(
        name = "bindgen",
        build_file_content = """exports_files(["bindgen"])""",
        url = "https://android.googlesource.com/platform/prebuilts/clang-tools/+archive/820ba880a1e95afd4cb6645356f724b7898d387c/linux-x86/bin.tar.gz",
    )

    # Fetch `elfutils` repo which contains ELF definitions needed for the `libelf` library.
    http_archive(
        name = "elfutils",
        build_file_content = """
cc_library(
    name = "elf_type_header",
    hdrs = ["libelf/elf.h"],
    visibility = ["//visibility:public"],
)
""",
        url = "https://android.googlesource.com/platform/external/elfutils/+archive/refs/heads/main.tar.gz",
    )

    # Fetch `googletest` for C/C++ unit-tests
    http_archive(
        name = "googletest",
        url = "https://android.googlesource.com/platform/external/googletest/+archive/refs/heads/main.tar.gz",
    )

    # Following are third party rust crates from android/external/rust/crates used by GBL.
    #
    # Note: To pull in a new crate, Add a new _android_external_rust_crate_archive() rule below to
    # fetch the crate and provide a BUILD file for it. Android.bp is a good reference for writing
    # BUILD file as for most part it has an one-to-one mapping to a Bazel rule. If the target
    # crate has additional dependencies, repeat for all of them until all needed crates are
    # fetched.

    _android_external_rust_crate_archive(
        name = "bitflags",
        rev = "4cb5dac10a9ca8a0c9b78ea24f0f23e7972576e2",
        build_file = "@gbl//android_external_rust_crates:BUILD.bitflags.bazel",
    )

    _android_external_rust_crate_archive(
        name = "byteorder",
        rev = "69440f2e49ba4d846f091a57c1826a268d04656e",
        build_file = "@gbl//android_external_rust_crates:BUILD.byteorder.bazel",
    )

    _android_external_rust_crate_archive(
        name = "cfg-if",
        rev = "3a308fd77901411c7ed5161012cebeb2cf8dab1a",
        build_file = "@gbl//android_external_rust_crates:BUILD.cfg-if.bazel",
    )

    _android_external_rust_crate_archive(
        name = "crc32fast",
        rev = "7225fa79b53d6a75f4dadcd974ca82c666044953",
        build_file = "@gbl//android_external_rust_crates:BUILD.crc32fast.bazel",
    )

    _android_external_rust_crate_archive(
        name = "hex",
        rev = "1ddb3bec93394eeb62ee4f4187e8579b489c3d07",
        build_file = "@gbl//android_external_rust_crates:BUILD.hex.bazel",
    )

    _android_external_rust_crate_archive(
        name = "proc-macro2",
        rev = "5c471c4a5c3e80c810dadb19c5996e420426c3bc",
        build_file = "@gbl//android_external_rust_crates:BUILD.proc-macro2.bazel",
    )

    _android_external_rust_crate_archive(
        name = "quote",
        rev = "9791b3d2d985ed9aae113fc5112e9a607c6c5741",
        build_file = "@gbl//android_external_rust_crates:BUILD.quote.bazel",
    )

    _android_external_rust_crate_archive(
        name = "syn",
        rev = "035a68a559d23e0f60aa2c274a4b4c6f7247bc3b",
        build_file = "@gbl//android_external_rust_crates:BUILD.syn.bazel",
    )

    _android_external_rust_crate_archive(
        name = "unicode-ident",
        rev = "2d1f5f891da7f9645c864e54fa08a0aabc7ab65f",
        build_file = "@gbl//android_external_rust_crates:BUILD.unicode-ident.bazel",
    )

    _android_external_rust_crate_archive(
        name = "zerocopy",
        rev = "38d9439810f66c9f287a7f1caee1f6e3cf076d38",
        build_file = "@gbl//android_external_rust_crates:BUILD.zerocopy.bazel",
    )

    _android_external_rust_crate_archive(
        name = "zerocopy-derive",
        rev = "e987328e0df1334022cb8ada4233e672a2e4ea0e",
        build_file = "@gbl//android_external_rust_crates:BUILD.zerocopy-derive.bazel",
    )

def define_gbl_workspace(name = None):
    """Set up worksapce for building GBL targets

    This rule API can be used to integrate GBL build targets into other projects that use Bazel
    build system. To do so, simply call this API in the project's WORKSPACE.bazel file.

    Args:
        name (String): Placeholder for buildifier check.
    """
    fetch_remote_dependencies()

    # Set up a repo to export llvm tool/library/header/sysroot paths
    gbl_llvm_prebuilts(name = "gbl_llvm_prebuilts")

    # Setup a repo to export custom built Rust sysroot
    gbl_custom_rust_sysroot(name = "gbl_custom_rust_sysroot")

    # Register all the LLVM/Rust toolchains.
    native.register_toolchains("@gbl//toolchain:all")
