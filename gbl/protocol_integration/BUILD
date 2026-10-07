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

load("@gbl//toolchain:gbl_toolchain.bzl", "build_with_platform", "extract_pdb_file")
load("@gbl//toolchain:gbl_workspace_util.bzl", "ANDROID_RUST_LINTS")
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")

package(
    default_applicable_licenses = ["@gbl//licensing:gbl_license"],
    default_visibility = ["//visibility:public"],
)

TEST_NAME = select({
    "@gbl//toolchain:gbl_rust_elf_riscv64": "gbl_riscv64",
    "@gbl//toolchain:gbl_rust_uefi_x86_64": "gbl_x86_64",
    "@gbl//toolchain:gbl_rust_uefi_aarch64": "gbl_aarch64",
    "//conditions:default": "gbl_unknown",
}) + "_protocol_integration_test"

rust_library(
    name = "libprotocol_test",
    srcs = glob(["src/**/*.rs"]),
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        "@avb//:libavb_c_sha_staticlib",
        "@gbl//libavb:sysdeps",
        "@gbl//libboringssl",
        "@gbl//libboringssl:libcrypto_c_baremetal_static",
        "@gbl//libboringssl:sysdeps",
        "@gbl//libefi",
        "@gbl//libefi:libefi_rng",
        "@gbl//liberror",
        "@gbl//libfastboot",
        "@gbl//libgbl",
        "@gbl//libstack",
        "@gbl//libutils",
    ],
)

rust_binary(
    name = "required",
    srcs = glob(["required/**/*.rs"]),
    binary_name = TEST_NAME + "_required",
    linker_script = select(
        {
            "@gbl//toolchain:gbl_rust_elf_riscv64": "@gbl//efi/arch/riscv64:riscv64_efi.lds",
            "//conditions:default": None,
        },
    ),
    rustc_flags = ANDROID_RUST_LINTS + [
        "-C",
        "panic=abort",
    ],
    deps = [
        ":libprotocol_test",
        "@gbl//libasync",
        "@gbl//libefi",
        "@gbl//libefi_types",
    ] + select(
        {
            "@gbl//toolchain:gbl_rust_elf_riscv64": [
                "@gbl//efi/arch/riscv64:efi_arch_deps_riscv64",
            ],
            "//conditions:default": [],
        },
    ),
)

extract_pdb_file(
    name = "required_pdb",
    target = ":required",
)

build_with_platform(
    name = "aarch64_required",
    mode = "dbg",
    platform = "@gbl//toolchain:gbl_uefi_aarch64_debug_prod",
    deps = [":required_pdb"],
)

build_with_platform(
    name = "x86_64_required",
    mode = "dbg",
    platform = "@gbl//toolchain:gbl_uefi_x86_64_debug_prod",
    deps = [":required_pdb"],
)

build_with_platform(
    name = "riscv64_required",
    mode = "dbg",
    platform = "@gbl//toolchain:gbl_elf_riscv64_prod",
    deps = [":required_pdb"],
)

filegroup(
    name = "protocol_integration_required",
    srcs = [
        ":aarch64_required",
        ":riscv64_required",
        ":x86_64_required",
    ],
)

rust_binary(
    name = "optional",
    srcs = glob(["optional/**/*.rs"]),
    binary_name = TEST_NAME + "_optional",
    linker_script = select(
        {
            "@gbl//toolchain:gbl_rust_elf_riscv64": "@gbl//efi/arch/riscv64:riscv64_efi.lds",
            "//conditions:default": None,
        },
    ),
    rustc_flags = ANDROID_RUST_LINTS + [
        "-C",
        "panic=abort",
    ],
    deps = [
        ":libprotocol_test",
        "@gbl//libasync",
        "@gbl//libefi",
        "@gbl//libefi_types",
    ] + select(
        {
            "@gbl//toolchain:gbl_rust_elf_riscv64": [
                "@gbl//efi/arch/riscv64:efi_arch_deps_riscv64",
            ],
            "//conditions:default": [],
        },
    ),
)

extract_pdb_file(
    name = "optional_pdb",
    target = ":optional",
)

build_with_platform(
    name = "aarch64_optional",
    mode = "dbg",
    platform = "@gbl//toolchain:gbl_uefi_aarch64_debug_prod",
    deps = [":optional_pdb"],
)

build_with_platform(
    name = "x86_64_optional",
    mode = "dbg",
    platform = "@gbl//toolchain:gbl_uefi_x86_64_debug_prod",
    deps = [":optional_pdb"],
)

build_with_platform(
    name = "riscv64_optional",
    mode = "dbg",
    platform = "@gbl//toolchain:gbl_elf_riscv64_prod",
    deps = [":optional_pdb"],
)

filegroup(
    name = "protocol_integration_optional",
    srcs = [
        ":aarch64_optional",
        ":riscv64_optional",
        ":x86_64_optional",
    ],
)
