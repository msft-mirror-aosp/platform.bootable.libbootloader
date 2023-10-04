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

load("@rules_rust//rust:toolchain.bzl", "rust_toolchain", "rustfmt_toolchain")
load(":gbl_clang_cc_toolchain.bzl", "gbl_clang_cc_toolchain")

package(
    default_visibility = ["//visibility:public"],
)

# The following constraint/settings will be used in our newly defined
# toolchains, so that they only get selected by bazel when we configure
# to build GBL.
constraint_setting(name = "firmware_image_type")

constraint_value(
    name = "uefi",
    constraint_setting = ":firmware_image_type",
)

constraint_value(
    name = "elf",
    constraint_setting = ":firmware_image_type",
)

uefi_x86_64_constraint_values = [
    ":uefi",
    "@platforms//os:none",
    "@platforms//cpu:x86_64",
]

uefi_x86_32_constraint_values = [
    ":uefi",
    "@platforms//os:none",
    "@platforms//cpu:x86_32",
]

uefi_aarch64_constraint_values = [
    ":uefi",
    "@platforms//os:none",
    "@platforms//cpu:aarch64",
]

elf_riscv64_constraint_values = [
    ":elf",
    "@platforms//os:linux",
    "@platforms//cpu:riscv64",
]

config_setting(
    name = "gbl_rust_uefi_x86_64",
    constraint_values = uefi_x86_64_constraint_values,
)

config_setting(
    name = "gbl_rust_uefi_x86_32",
    constraint_values = uefi_x86_32_constraint_values,
)

config_setting(
    name = "gbl_rust_uefi_aarch64",
    constraint_values = uefi_aarch64_constraint_values,
)

config_setting(
    name = "gbl_rust_elf_riscv64",
    constraint_values = elf_riscv64_constraint_values,
)

# The following will be passed to "bazel build --platform=<>" argument to
# configure building for specific architecture and image type.
platform(
    name = "gbl_uefi_x86_64",
    constraint_values = uefi_x86_64_constraint_values,
)

platform(
    name = "gbl_uefi_x86_32",
    constraint_values = uefi_x86_32_constraint_values,
)

platform(
    name = "gbl_uefi_aarch64",
    constraint_values = uefi_aarch64_constraint_values,
)

platform(
    name = "gbl_elf_riscv64",
    constraint_values = elf_riscv64_constraint_values,
)

cc_toolchain_suite(
    name = "gbl_clang_suite",
    toolchains = {
        "x86_64": ":x86_64_uefi_clang_cc_toolchain",
        "x86_32": ":x86_32_uefi_clang_cc_toolchain",
        "aarch64": ":aarch64_uefi_clang_cc_toolchain",
        "riscv64": ":riscv64_elf_clang_cc_toolchain",
    },
)

# The following defines specialized clang C++ toolchains for GBL. They are
# mainly for making sure we pass the correct set of compiler and linking flags
# that do what we want, i.e. compile/link in baremetal environment, UEFI format
# binary, target architecture etc.

cc_flags_common = [
    "-ffreestanding",
    "-fno-common",
    "-fno-exceptions",
    "-fno-rtti",
]

gbl_clang_cc_toolchain(
    name = "x86_64_uefi_clang_cc_toolchain",
    cc_flags = cc_flags_common,
    target_cpu = "x86_64",
    target_system_triple = "x86_64-windows-msvc",
)

toolchain(
    name = "x86_64_uefi_clang",
    exec_compatible_with = ["@platforms//os:linux"],
    target_compatible_with = uefi_x86_64_constraint_values,
    toolchain = ":x86_64_uefi_clang_cc_toolchain",
    toolchain_type = "@bazel_tools//tools/cpp:toolchain_type",
)

gbl_clang_cc_toolchain(
    name = "x86_32_uefi_clang_cc_toolchain",
    cc_flags = cc_flags_common,
    target_cpu = "x86_32",
    target_system_triple = "x86-windows-msvc",
)

toolchain(
    name = "x86_32_uefi_clang",
    exec_compatible_with = ["@platforms//os:linux"],
    target_compatible_with = uefi_x86_32_constraint_values,
    toolchain = ":x86_32_uefi_clang_cc_toolchain",
    toolchain_type = "@bazel_tools//tools/cpp:toolchain_type",
)

gbl_clang_cc_toolchain(
    name = "aarch64_uefi_clang_cc_toolchain",
    cc_flags = cc_flags_common,
    target_cpu = "aarch64",
    target_system_triple = "aarch64-windows-msvc",
)

toolchain(
    name = "aarch64_uefi_clang",
    exec_compatible_with = ["@platforms//os:linux"],
    target_compatible_with = uefi_aarch64_constraint_values,
    toolchain = ":aarch64_uefi_clang_cc_toolchain",
    toolchain_type = "@bazel_tools//tools/cpp:toolchain_type",
)

gbl_clang_cc_toolchain(
    name = "riscv64_elf_clang_cc_toolchain",
    cc_flags = cc_flags_common + ["-fpie"],
    target_cpu = "riscv64",
    target_system_triple = "riscv64-unknown-linux",
)

toolchain(
    name = "riscv64_elf_clang",
    exec_compatible_with = ["@platforms//os:linux"],
    target_compatible_with = elf_riscv64_constraint_values,
    toolchain = ":riscv64_elf_clang_cc_toolchain",
    toolchain_type = "@bazel_tools//tools/cpp:toolchain_type",
)

# Rust toolchains

# Linux x86_64 Host toolchain
rust_toolchain(
    name = "x86_64_unknown_linux_gnu",
    allocator_library = None,
    binary_ext = "",
    default_edition = "2021",
    dylib_ext = ".so",
    exec_triple = "x86_64-unknown-linux-gnu",
    global_allocator_library = None,
    rust_doc = "@rust_prebuilts//:bin/rustdoc",
    rust_std = "@rust_prebuilts//:prebuilt_stdlibs",
    rustc = "@rust_prebuilts//:bin/rustc",
    staticlib_ext = ".a",
    stdlib_linkflags = [],
    target_triple = "x86_64-unknown-linux-gnu",
)

toolchain(
    name = "x86_64_unknown_linux_gnu_toolchain",
    exec_compatible_with = ["@platforms//os:linux"],
    target_compatible_with = [
        "@platforms//os:linux",
        "@platforms//cpu:x86_64",
    ],
    toolchain = ":x86_64_unknown_linux_gnu",
    toolchain_type = "@rules_rust//rust:toolchain",
)

# x86_64 UEFI toolchain
rust_toolchain(
    name = "x86_64-unknown-uefi",
    allocator_library = None,
    binary_ext = ".efi",
    default_edition = "2021",
    dylib_ext = ".so",
    exec_triple = "x86_64-unknown-linux-gnu",
    global_allocator_library = None,
    rust_doc = "@rust_prebuilts//:bin/rustdoc",
    # TODO(http://b/302569430): Switch to use prebuilt sysroot libraries once they are available.
    rust_std = "@gbl_custom_rust_sysroot//:stdlib",
    rustc = "@rust_prebuilts//:bin/rustc",
    staticlib_ext = ".a",
    stdlib_linkflags = [],
    target_triple = "x86_64-unknown-uefi",
)

toolchain(
    name = "x86_64-unknown-uefi_toolchain",
    exec_compatible_with = ["@platforms//os:linux"],
    target_settings = [":gbl_rust_uefi_x86_64"],
    toolchain = ":x86_64-unknown-uefi",
    toolchain_type = "@rules_rust//rust:toolchain",
)

# i686 UEFI toolchain
rust_toolchain(
    name = "i686-unknown-uefi",
    allocator_library = None,
    binary_ext = ".efi",
    default_edition = "2021",
    dylib_ext = ".so",
    exec_triple = "x86_64-unknown-linux-gnu",
    global_allocator_library = None,
    rust_doc = "@rust_prebuilts//:bin/rustdoc",
    # TODO(http://b/302569430): Switch to use prebuilt sysroot libraries once they are available.
    rust_std = "@gbl_custom_rust_sysroot//:stdlib",
    rustc = "@rust_prebuilts//:bin/rustc",
    staticlib_ext = ".a",
    stdlib_linkflags = [],
    target_triple = "i686-unknown-uefi",
)

toolchain(
    name = "i686-unknown-uefi_toolchain",
    exec_compatible_with = ["@platforms//os:linux"],
    target_settings = [":gbl_rust_uefi_x86_32"],
    toolchain = ":i686-unknown-uefi",
    toolchain_type = "@rules_rust//rust:toolchain",
)

# aarch64 UEFI toolchain
rust_toolchain(
    name = "aarch64-unknown-uefi",
    allocator_library = None,
    binary_ext = ".efi",
    default_edition = "2021",
    dylib_ext = ".so",
    exec_triple = "x86_64-unknown-linux-gnu",
    global_allocator_library = None,
    rust_doc = "@rust_prebuilts//:bin/rustdoc",
    # TODO(http://b/302569430): Switch to use prebuilt sysroot libraries once they are available.
    rust_std = "@gbl_custom_rust_sysroot//:stdlib",
    rustc = "@rust_prebuilts//:bin/rustc",
    staticlib_ext = ".a",
    stdlib_linkflags = [],
    target_triple = "aarch64-unknown-uefi",
)

toolchain(
    name = "aarch64-unknown-uefi_toolchain",
    exec_compatible_with = ["@platforms//os:linux"],
    target_settings = [":gbl_rust_uefi_aarch64"],
    toolchain = ":aarch64-unknown-uefi",
    toolchain_type = "@rules_rust//rust:toolchain",
)

# riscv64 PIE ELF toolchain
rust_toolchain(
    name = "riscv64gc-unknown-none-pie_elf",
    allocator_library = None,
    binary_ext = "",
    default_edition = "2021",
    dylib_ext = ".so",
    exec_triple = "x86_64-unknown-linux-gnu",
    global_allocator_library = None,
    rust_doc = "@rust_prebuilts//:bin/rustdoc",
    # Need to use our own built sysroot because we are using a custom spec below.
    rust_std = "@gbl_custom_rust_sysroot//:stdlib",
    rustc = "@rust_prebuilts//:bin/rustc",
    staticlib_ext = ".a",
    stdlib_linkflags = [],
    # The custom spec is based on builtin target "riscv64gc-unknown-none-elf" but with the
    # following changes for enabling PIE:
    #
    #   1. "relocation-model" config entry changed from "static" to "pic".
    #   2. Added "position-independent-executables": true.
    #
    # The original spec can be obtained by:
    #
    #   rustc +nightly -Z unstable-options --print target-spec-json \
    #     --target riscv64gc-unknown-none-elf
    target_json = """
                {
                    "arch": "riscv64",
                    "code-model": "medium",
                    "cpu": "generic-rv64",
                    "data-layout": "e-m:e-p:64:64-i64:64-i128:128-n32:64-S128",
                    "eh-frame-header": false,
                    "emit-debug-gdb-scripts": false,
                    "features": "+m,+a,+f,+d,+c",
                    "is-builtin": false,
                    "linker": "rust-lld",
                    "linker-flavor": "ld.lld",
                    "llvm-abiname": "lp64d",
                    "llvm-target": "riscv64-unknown-linux",
                    "max-atomic-width": 64,
                    "os": "none",
                    "panic-strategy": "abort",
                    "relocation-model": "pic",
                    "position-independent-executables": true,
                    "supported-sanitizers": [
                        "kernel-address"
                    ],
                    "target-pointer-width": "64"
                }
""",
)

toolchain(
    name = "riscv64gc-unknown-none-pie_elf_toolchain",
    exec_compatible_with = ["@platforms//os:linux"],
    target_settings = ["@gbl//toolchain:gbl_rust_elf_riscv64"],
    toolchain = ":riscv64gc-unknown-none-pie_elf",
    toolchain_type = "@rules_rust//rust:toolchain",
)

# rustfmt toolchain
rustfmt_toolchain(
    name = "rustfmt",
    rustfmt = "@rust_prebuilts//:bin/rustfmt",
)

toolchain(
    name = "rustfmt_toolchain",
    exec_compatible_with = ["@platforms//os:linux"],
    toolchain = ":rustfmt",
    toolchain_type = "@rules_rust//rust/rustfmt:toolchain_type",
)
