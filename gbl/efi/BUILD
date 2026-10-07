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

load("@gbl//licensing:licenses.bzl", "merged_license")
load("@gbl//toolchain:gbl_toolchain.bzl", "build_with_platform", "dev_test", "extract_pdb_file", "rename_output")
load("@gbl//toolchain:gbl_workspace_util.bzl", "ANDROID_RUST_LINTS")
load("@gbl_config//:variables.bzl", "IMG_ARCHIVE_TAG")
load("@gbl_llvm_prebuilts//:info.bzl", "gbl_llvm_tool_path")
load("@rules_pkg//pkg:install.bzl", "pkg_install")
load("@rules_pkg//pkg:mappings.bzl", "pkg_files", "strip_prefix")
load("@rules_pkg//pkg:zip.bzl", "pkg_zip")
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_test")

package(
    default_applicable_licenses = ["@gbl//licensing:gbl_license"],
    default_visibility = ["//visibility:public"],
)

filegroup(
    name = "libgbl_efi_prod_files",
    srcs = glob(
        ["src/**/*.rs"],
        exclude = ["src/fuchsia_boot.rs"],
    ),
)

filegroup(
    name = "libgbl_efi_dev_files",
    srcs = glob(["src/**/*.rs"]),
)

rust_library(
    name = "libgbl_efi",
    srcs = select({
        "@gbl//toolchain:dev": [":libgbl_efi_dev_files"],
        "@gbl//toolchain:prod": [":libgbl_efi_prod_files"],
    }),
    crate_name = "gbl_efi",
    edition = "2024",
    proc_macro_deps = ["@gbl//libprofile:libprofile_macros"],
    rustc_flags = ANDROID_RUST_LINTS,
    deps = [
        "@arrayvec",
        "@avb",
        "@bytes",
        "@cfg_if",
        "@gbl//libasync",
        "@gbl//libboot",
        "@gbl//libbuild_number",
        "@gbl//libefi",
        "@gbl//libefi_types",
        "@gbl//liberror",
        "@gbl//libfastboot",
        "@gbl//libfdt",
        "@gbl//libgbl",
        "@gbl//libprofile",
        "@gbl//libsafemath",
        "@gbl//libstorage",
        "@gbl//libtrace",
        "@gbl//libutils",
        "@spin",
        "@static_assertions",
        "@uuid",
        "@zerocopy",
    ] + select({
        "@gbl//toolchain:dev": [
            "@gbl//libboringssl:sysdeps",
            "@gbl//protocol_integration:libprotocol_test",
            "@smoltcp",
            "@zbi",
        ],
        "@gbl//toolchain:prod": [],
    }),
)

rust_test(
    name = "test",
    compile_data = [
        "@gbl//libfdt/test/data:all",
    ],
    crate = ":libgbl_efi",
    # TODO(b/355436086): mock out the rest of the libefi APIs and
    # remove dead-code; for now it would require a lot of invasive
    # code changes to selectively disable things on tests so this
    # is worth it to keep things more readable.
    rustc_flags = ANDROID_RUST_LINTS + [
        "-A",
        "dead-code",
    ],
    deps = [
        "@gbl//libefi:mocks",
        "@mockall",
    ],
)

dev_test(
    name = "test_dev",
    target = ":test",
)

APP_NAME = select({
    "@gbl//toolchain:gbl_rust_elf_riscv64": "gbl_riscv64",
    "@gbl//toolchain:gbl_rust_uefi_aarch64": "gbl_aarch64",
    "@gbl//toolchain:gbl_rust_uefi_x86_64": "gbl_x86_64",
    "//conditions:default": "gbl_unknown",
}) + "_" + select({
    "@gbl//toolchain:dev": "dev",
    "@gbl//toolchain:prod": "prod",
    "//conditions:default": "unknown",
}) + select({
    "@gbl//toolchain:efi_boot_stub": "_bootstub",
    "//conditions:default": "",
}) + select({
    "@gbl//toolchain:uefi_debug": "_debug",
    "//conditions:default": "",
})

# The UEFI application target.
#
# Almost all logic should be in the libgbl_efi target; this contains only the
# things that would prevent unittesting such as global allocation hooks or
# target-specific compiler dependencies.
rust_binary(
    name = "app",
    srcs = glob(["app/**/*.rs"]),
    binary_name = APP_NAME,
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
        ":libgbl_efi",
        "@avb//:libavb_c_sha_staticlib",
        "@cfg_if",
        "@gbl//libavb:sysdeps",
        "@gbl//libboringssl:libcrypto_c_baremetal_static",
        "@gbl//libboringssl:sysdeps",
        "@gbl//libefi",
        "@gbl//libefi:libefi_rng",
        "@gbl//libefi_types",
        "@gbl//libgbl",
        "@gbl//libstack",
    ] + select(
        {
            "@gbl//toolchain:gbl_rust_elf_riscv64": [
                "@gbl//efi/arch/riscv64:efi_arch_deps_riscv64",
            ],
            "@gbl//toolchain:gbl_rust_uefi_aarch64": [
                "@gbl//efi/arch/aarch64:efi_arch_deps_aarch64",
            ],
            "//conditions:default": [],
        },
    ),
)

extract_pdb_file(
    name = "app_pdb",
    target = ":app",
)

genrule(
    name = "gbl_efi",
    srcs = [":app"],
    outs = ["gbl.efi"],
    cmd = select(
        {
            # For RISCV target, existing toolchain can only generate ELF format image.
            # The current solution is to manually add a PE/COFF header at image
            # start and use objcopy to remove the ELF header to make it a PE/COFF image.
            # Also use `elf_static_relocation_checker` to check that our relocation library
            # can handle all the generated relocation types. The following expands to two commands:
            #
            # 1. `llvm-objcopy <elf image> -O binary <efi image>`
            # 2. `elf_static_relocation_checker <elf image> <efi image>`
            "@gbl//toolchain:gbl_rust_elf_riscv64": """
{} -O binary $(execpath @gbl//efi:app) $(OUTS) &&
$(execpath @gbl//libelf:elf_static_relocation_checker) $(SRCS) $(OUTS)
        """.format(
                gbl_llvm_tool_path("llvm-objcopy"),
            ),
            "//conditions:default": "cp $(SRCS) $(OUTS)",
        },
    ),
    tools = select(
        {
            "@gbl//toolchain:gbl_rust_elf_riscv64": [
                "@gbl//libelf:elf_static_relocation_checker",
            ],
            "//conditions:default": [],
        },
    ),
)

genrule(
    name = "gbl_efi_testkey",
    srcs = [":gbl_efi"],
    outs = ["testkey_signed/gbl.efi"],
    cmd = "$(execpath @gbl//signtool:gblsigntool_py) sign $(SRCS) -o $(OUTS)" +
          " --avbtool_args '--key $(execpath @gbl//signtool/testkeys:testkey_RSA4096)'" +
          " --avbtool_args '--algorithm SHA256_RSA4096'" +
          " --avbtool_args '--prop testkey:true'",
    tools = [
        "@gbl//signtool:gblsigntool_py",
        "@gbl//signtool/testkeys:testkey_RSA4096",
    ],
)

# Uses standard output name.
#
# `APP_NAME` contains `select` expression and can only be evaluated in rules.
rename_output(
    name = "gbl_signed",
    out = APP_NAME + ".efi",
    target = ":gbl_efi_testkey",
)

build_with_platform(
    name = "x86_64_dev",
    platform = "@gbl//toolchain:gbl_uefi_x86_64_dev",
    deps = [":gbl_signed"],
)

build_with_platform(
    name = "x86_64_dev_pdb",
    platform = "@gbl//toolchain:gbl_uefi_x86_64_dev",
    deps = [":app_pdb"],
)

build_with_platform(
    name = "x86_64_dev_bootstub",
    platform = "@gbl//toolchain:gbl_uefi_x86_64_dev_bootstub",
    deps = [":gbl_signed"],
)

build_with_platform(
    name = "x86_64_dev_bootstub_pdb",
    platform = "@gbl//toolchain:gbl_uefi_x86_64_dev_bootstub",
    deps = [":app_pdb"],
)

build_with_platform(
    name = "x86_64_prod",
    platform = "@gbl//toolchain:gbl_uefi_x86_64_prod",
    deps = [":gbl_signed"],
)

build_with_platform(
    name = "x86_64_prod_pdb",
    platform = "@gbl//toolchain:gbl_uefi_x86_64_prod",
    deps = [":app_pdb"],
)

build_with_platform(
    name = "x86_64_debug_dev",
    mode = "dbg",
    platform = "@gbl//toolchain:gbl_uefi_x86_64_debug_dev",
    deps = [":gbl_signed"],
)

build_with_platform(
    name = "x86_64_debug_prod",
    mode = "dbg",
    platform = "@gbl//toolchain:gbl_uefi_x86_64_debug_prod",
    deps = [":gbl_signed"],
)

build_with_platform(
    name = "aarch64_dev",
    platform = "@gbl//toolchain:gbl_uefi_aarch64_dev",
    deps = [":gbl_signed"],
)

build_with_platform(
    name = "aarch64_dev_pdb",
    platform = "@gbl//toolchain:gbl_uefi_aarch64_dev",
    deps = [":app_pdb"],
)

build_with_platform(
    name = "aarch64_dev_bootstub",
    platform = "@gbl//toolchain:gbl_uefi_aarch64_dev_bootstub",
    deps = [":gbl_signed"],
)

build_with_platform(
    name = "aarch64_dev_bootstub_pdb",
    platform = "@gbl//toolchain:gbl_uefi_aarch64_dev_bootstub",
    deps = [":app_pdb"],
)

build_with_platform(
    name = "aarch64_prod",
    platform = "@gbl//toolchain:gbl_uefi_aarch64_prod",
    deps = [":gbl_signed"],
)

build_with_platform(
    name = "aarch64_prod_pdb",
    platform = "@gbl//toolchain:gbl_uefi_aarch64_prod",
    deps = [":app_pdb"],
)

build_with_platform(
    name = "aarch64_debug_dev",
    mode = "dbg",
    platform = "@gbl//toolchain:gbl_uefi_aarch64_debug_dev",
    deps = [":gbl_signed"],
)

build_with_platform(
    name = "aarch64_debug_prod",
    mode = "dbg",
    platform = "@gbl//toolchain:gbl_uefi_aarch64_debug_prod",
    deps = [":gbl_signed"],
)

build_with_platform(
    name = "riscv64_dev",
    platform = "@gbl//toolchain:gbl_elf_riscv64_dev",
    deps = [":gbl_signed"],
)

build_with_platform(
    name = "riscv64_prod",
    platform = "@gbl//toolchain:gbl_elf_riscv64_prod",
    deps = [":gbl_signed"],
)

# Our infra tests currently fetch GBL binaries from these paths:
# * gbl_aarch64.efi
# * gbl_riscv64.efi
# * gbl_x86_64.efi
# For now copy the "dev" build to these paths so the tests can find them; once
# we modify the tests to fetch a variant expicitly we can remove these copies.
genrule(
    name = "copies_for_tests",
    srcs = [
        ":aarch64_dev",
        ":riscv64_dev",
        ":x86_64_dev",
    ],
    outs = [
        "gbl_aarch64.efi",
        "gbl_riscv64.efi",
        "gbl_x86_64.efi",
    ],
    # https://bazel.build/reference/be/general#general-advice says not to
    # create symlinks in genrules, so we do a full copy here. The images are
    # small enough that it's fine either way.
    cmd = """
        cp $(execpath :aarch64_dev) $(RULEDIR)/gbl_aarch64.efi
        cp $(execpath :riscv64_dev) $(RULEDIR)/gbl_riscv64.efi
        cp $(execpath :x86_64_dev) $(RULEDIR)/gbl_x86_64.efi
    """,
)

filegroup(
    name = "all_platforms",
    srcs = [
        ":aarch64_dev",
        ":aarch64_dev_bootstub",
        ":aarch64_dev_bootstub_pdb",
        ":aarch64_dev_pdb",
        ":aarch64_prod",
        ":aarch64_prod_pdb",
        ":copies_for_tests",
        ":riscv64_dev",
        ":riscv64_prod",
        ":x86_64_dev",
        ":x86_64_dev_bootstub",
        ":x86_64_dev_bootstub_pdb",
        ":x86_64_dev_pdb",
        ":x86_64_prod",
        ":x86_64_prod_pdb",
    ],
)

# Collects all licenses used by the GBL EFI application & its dependencies.
#
# This currently grabs all licenses used, but we could split into smaller
# scopes if we want to provide separate licenses only for particular targets
# (e.g. ARM prod build).
merged_license(
    name = "all_platforms_merged_license",
    out = "LICENSE",
    deps = [":all_platforms"],
)

filegroup(
    name = "all_platforms_prod",
    srcs = [
        ":aarch64_prod",
        ":x86_64_prod",
    ],
)

pkg_zip(
    name = "gbl_efi_prod_zip",
    srcs = [":all_platforms_prod"],
    out = "gbl-img-{}.zip".format(IMG_ARCHIVE_TAG),
    visibility = ["//visibility:private"],
)

# Export the docs and headers so that devices can easily get the exact matching
# definitions for their specific build of GBL, otherwise it's quite difficult
# to find the version needed to match a given GBL binary.
pkg_files(
    name = "resources_files",
    srcs = glob(["resources/**"]),
    strip_prefix = strip_prefix.from_pkg("resources"),
    visibility = ["//visibility:private"],
)

pkg_zip(
    name = "gbl_resources_zip",
    srcs = [
        ":resources_files",
        "@gbl//:gbl_docs_files",
        "@gbl//libefi_types:gbl_uefi_headers_files",
    ],
    out = "gbl-resources-{}.zip".format(IMG_ARCHIVE_TAG),
    visibility = ["//visibility:private"],
)

pkg_files(
    name = "gbl_efi_dist_files",
    srcs = [
        ":all_platforms",
        ":all_platforms_merged_license",
        ":gbl_efi_prod_zip",
        ":gbl_resources_zip",
    ],
    strip_prefix = strip_prefix.files_only(),
    visibility = ["//visibility:private"],
)

pkg_install(
    name = "gbl_efi_dist",
    srcs = [
        ":gbl_efi_dist_files",
        "//signtool:gblsigntool_dist_files",
    ],
    destdir = "out/gbl_efi/",
)
