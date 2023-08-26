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
    #"-fno-common",
    "-fno-exceptions",
    "-fno-rtti",
]

ld_flags_common = [
    "-fuse-ld=lld",
    "-fno-exceptions",
    "-nostdlib",
    "-nostdlib++",
    "-noprofilelib",
]

ld_flags_uefi = ld_flags_common + [
    "-static",
    "-Wl,/subsystem:efi_application",
    "-Wl,/entry:efi_main",
]

gbl_clang_cc_toolchain(
    name = "x86_64_uefi_clang_cc_toolchain",
    cc_flags = cc_flags_common,
    ld_flags = ld_flags_uefi,
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
    ld_flags = ld_flags_uefi,
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
    ld_flags = ld_flags_uefi,
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
    ld_flags = ld_flags_common + ["-fpie"],
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
