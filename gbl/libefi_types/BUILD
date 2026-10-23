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

load("@gbl_llvm_prebuilts//:info.bzl", "LLVM_PREBUILTS_C_INCLUDE")
load("@rules_cc//cc:cc_library.bzl", "cc_library")
load("@rules_pkg//pkg:mappings.bzl", "pkg_files", "strip_prefix")
load("@rules_rust//rust:defs.bzl", "rust_doc_test", "rust_library", "rust_test")
load("@rules_rust_bindgen//:defs.bzl", "rust_bindgen")
load(":license.bzl", "spdx_license_test")

package(
    # The raw C headers are dual-licensed under Apache 2.0 and BSD 2-Clause to
    # make them more easily portable to other codebases, but for the GBL build
    # itself we opt to use the standard GBL Apache 2.0 license.
    default_applicable_licenses = ["@gbl//licensing:gbl_license"],
    default_visibility = ["//visibility:public"],
)

# Newer version of `rust_bindgen` requires a `cc_library` target that actually produces a static
# library and instead of only headers. Thus we generate a placeholder source file to meet the
# requirement.
genrule(
    name = "bindgen_noop_cc",
    outs = ["bindgen_noop_cc.cc"],
    cmd = "touch $(OUTS)",
)

cc_library(
    name = "efi_c_headers",
    srcs = [":bindgen_noop_cc"],
    hdrs = glob(["include/**/*.h"]),
    includes = ["include"],
)

# TODO(b/443135241): Use --new-type-alias for bitmask typedef consts, e.g GblEfiAvbBootColor
rust_bindgen(
    name = "efi_defs_bindgen",
    bindgen_flags = [
        "--ctypes-prefix",
        "core::ffi",
        "--use-core",
        "--with-derive-default",
        "--with-derive-custom-enum=EfiMemoryAttribute=Immutable,IntoBytes,FromBytes,KnownLayout",
        "--with-derive-custom-enum=EfiMemoryType=Immutable,IntoBytes,FromBytes,KnownLayout",
        "--with-derive-custom-struct=EfiDevicePathProtocol=Immutable,IntoBytes,FromBytes,KnownLayout,Unaligned,PartialEq",
        "--with-derive-custom-struct=EfiGuid=Immutable,IntoBytes,FromBytes,KnownLayout,PartialEq",
        "--with-derive-custom-struct=EfiMemoryAttributesTableHeader=Immutable,IntoBytes,FromBytes,KnownLayout",
        "--with-derive-custom-struct=EfiMemoryDescriptor=Immutable,IntoBytes,FromBytes,KnownLayout,PartialEq",
        "--with-derive-custom-struct=EfiBlockIoMedia=PartialEq",
        "--with-derive-custom-struct=GblEfiAvbProperty=PartialEq",
        "--no-prepend-enum-name",
        # Note: don't use newtype, constified-module, or bitfield
        #       because the upcase enum name becomes a necessary prefix
        #       via the module/impl name.
        "--default-enum-style",
        "newtype_global",
        # Cannot yet use arbitrary types as const generics.
        "--constified-enum",
        "EfiTpl|.*_U64_ENUM",
        "--no-layout-tests",
        "--override-abi",
        ".*=efiapi",
        "--allowlist-type",
        "(Efi.*)|(EFI.*)|(Gbl.*)|(GBL_.*)",
        "--allowlist-var",
        "PARTITION_NAME_LEN_U16|EFI_.*|GBL_.*",
        "--raw-line",
        """
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(missing_docs)]

use zerocopy::{Immutable, IntoBytes, FromBytes, KnownLayout, Unaligned};""",
    ],
    cc_lib = ":efi_c_headers",
    clang_flags = [
        "-I{}".format(LLVM_PREBUILTS_C_INCLUDE),
        "-nostdinc",
        # It's much, much easier to enable newtype enums with C++ explicit enum width
        "-x",
        "c++",
        # Allow conditional compilation so we can make C- or Rust-specific
        # definitions without polluting the other's namespace.
        "-DRUST_BINDGEN",
    ],
    header = "include/uefi/efi.h",
)

# Copy the generated source to "src/defs.rs" in the output assembly, so that libefi can include it
# as a source.
genrule(
    name = "efi_defs_genrule",
    srcs = [":efi_defs_bindgen"],
    outs = ["src/defs.rs"],
    cmd = "cat $(execpath :efi_defs_bindgen) > $@",
)

rust_library(
    name = "libefi_types",
    srcs = glob(["**/*.rs"]) + ["src/defs.rs"],
    crate_name = "efi_types",
    data = [":efi_defs_genrule"],
    deps = [
        "@spin",
        "@zerocopy",
    ],
)

rust_test(
    name = "libefi_types_test",
    crate = ":libefi_types",
    crate_features = ["mocks"],
    deps = [
        "@mockall",
    ],
)

rust_doc_test(
    name = "libefi_types_doc_test",
    crate = ":libefi_types",
)

# GBL EFI definitions and protocols must be published under both Apache-2.0 and
# BDS-2-Clause-Patent licenses.
# Refer to top-level README.md "Licesing" section.
spdx_license_test(
    name = "gbl_protocols_license_test",
    srcs = glob(["include/**/*.h"]),
    expected_spdx_identifier = "Apache-2.0 OR BSD-2-Clause-Patent",
)

# If we change the path to these files, update the top-level README to match.
# LINT.IfChange
pkg_files(
    name = "gbl_uefi_headers_files",
    srcs = glob(["include/uefi/**"]),
    strip_prefix = strip_prefix.from_pkg(),
)
# LINT.ThenChange(/gbl/efi/resources/README.md)
