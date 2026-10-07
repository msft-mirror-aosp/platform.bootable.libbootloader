# Copyright (C) 2026 The Android Open Source Project
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

load("@gbl//toolchain:gbl_toolchain.bzl", "build_with_platform")
load("@gbl//toolchain:gbl_workspace_util.bzl", "ANDROID_RUST_LINTS")
load("@gbl_llvm_prebuilts//:info.bzl", "gbl_llvm_tool_path")
load("@rules_cc//cc:defs.bzl", "cc_library")
load("@rules_rust//rust:defs.bzl", "rust_binary")

package(
    default_applicable_licenses = ["@gbl//licensing:gbl_license"],
    default_visibility = ["//visibility:public"],
)

cc_library(
    name = "kernel_start",
    srcs = ["start.S"],
    deps = ["@gbl//libelf:relocation"],
)

rust_binary(
    name = "test_kernel_elf",
    srcs = ["main.rs"],
    linker_script = ":kernel.ld",
    rustc_flags = ANDROID_RUST_LINTS + [
        "-C",
        "panic=abort",
    ],
    deps = [
        ":kernel_start",
        "@gbl//libboot",
        "@gbl//libbootparams",
        "@gbl//libfdt",
        "@gbl//libopendice",
        "@gbl//libpvmfwconfig",
        "@gbl//libsemihosting",
        "@gbl//libtrace",
        "@gbl//libutils",
    ],
)

# Strip ELF header.
genrule(
    name = "test_kernel_gen",
    srcs = [":test_kernel_elf"],
    outs = ["test_kernel.bin"],
    cmd = "{} -O binary $< $@".format(gbl_llvm_tool_path("llvm-objcopy")),
)

build_with_platform(
    name = "test_kernel_aarch64",
    platform = "@gbl//toolchain:gbl_elf_aarch64_dev",
    deps = [":test_kernel_gen"],
)
