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

load("@gbl_llvm_toolchain_info//:info.bzl", "gbl_llvm_tool_path")
load("@rules_rust//rust:defs.bzl", "rust_binary")

package(
    default_visibility = ["//visibility:public"],
)

rust_binary(
    name = "main",
    srcs = [
        "src/main.rs",
        "src/riscv64.rs",
    ],
    linker_script = select({
        "@gbl//toolchain:gbl_rust_elf_riscv64": "@gbl//efi/arch/riscv64:riscv64_efi.lds",
        "//conditions:default": None,
    }),
    rustc_flags = [
        "-C",
        "panic=abort",
    ],
    deps = [
        "@gbl//third_party/libzbi",
        "@zerocopy",
    ] + select({
        "@gbl//toolchain:gbl_rust_elf_riscv64": ["@gbl//efi/arch/riscv64:efi_arch_deps_riscv64"],
        "//conditions:default": [],
    }),
)

genrule(
    name = "gbl_efi",
    srcs = [":main"],
    outs = ["gbl.efi"],
    cmd = select({
        # For RISCV target, existing toolchain can only generate ELF format image.
        # The current solution is to manually add a PE/COFF header at image
        # start and use objcopy to remove the ELF header to make it a PE/COFF image.
        # Also use `elf_static_relocation_checker` to check that our relocation library
        # can handle all the generated relocation types. The following expands to two commands:
        #
        # 1. `llvm-objcopy <elf image> -O binary <efi image>`
        # 2. `elf_static_relocation_checker <elf image> <efi image>`
        "@gbl//toolchain:gbl_rust_elf_riscv64": "{} -O binary $(location @gbl//efi:main) $@ && $(location @gbl//libelf:elf_static_relocation_checker) $(location @gbl//efi:main) $@".format(gbl_llvm_tool_path("llvm-objcopy")),
        "//conditions:default": "cp $(location @gbl//efi:main) $@",
    }),
    tools = select({
        "@gbl//toolchain:gbl_rust_elf_riscv64": ["@gbl//libelf:elf_static_relocation_checker"],
        "//conditions:default": [],
    }),
)
