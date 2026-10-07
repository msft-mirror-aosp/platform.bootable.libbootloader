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
load("@rules_rust//rust:defs.bzl", "rust_binary")

package(
    default_applicable_licenses = ["@gbl//licensing:gbl_license"],
    default_visibility = ["//visibility:public"],
)

rust_binary(
    name = "gbl_launcher_bin",
    srcs = [
        "src/aarch64.rs",
        "src/main.rs",
    ],
    edition = "2024",
    rustc_flags = ANDROID_RUST_LINTS + [
        "-C",
        "panic=abort",
    ],
    deps = [
        "@avb//:libavb_c_sha_staticlib",
        "@gbl//libavb:sysdeps",
        "@gbl//libboot",
        "@gbl//libboringssl:libcrypto_c_baremetal_static",
        "@gbl//libboringssl:sysdeps",
        "@gbl//libefi",
        "@gbl//libefi:libefi_rng",
        "@gbl//libefi_types",
        "@gbl//libefi_virtio_vsock",
        "@gbl//libsemihosting",
        "@gbl//libstack",
        "@gbl//tests/qemu/gbl_efi_avf",
        "@gbl//tests/qemu/gbl_efi_boot_control",
        "@gbl//tests/qemu/gbl_efi_boot_memory",
        "@gbl//tests/qemu/gbl_efi_fastboot_protocol",
    ],
)

build_with_platform(
    name = "gbl_launcher_aarch64",
    platform = "@gbl//toolchain:gbl_uefi_aarch64_dev",
    deps = [":gbl_launcher_bin"],
)
