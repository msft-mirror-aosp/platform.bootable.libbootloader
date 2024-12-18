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

load("@bazel_tools//tools/build_defs/repo:utils.bzl", "maybe")
load("@gbl//toolchain:gbl_workspace_util.bzl", "android_rust_prebuilts", "gbl_llvm_prebuilts")

_CLANG_VERSION = "r530567"

def rust_crate_build_file(
        name,
        rule = "rust_library",
        crate_name = "",
        deps = [],
        proc_macro_deps = [],
        features = [],
        rustc_flags = []):
    """Generate BUILD file content for a rust crate

    This helper is suitable for crates that have straightforward build rules. Specifically, the
    crate contains a single Rust target that includes all source files under the repo.
    There is not any need of preprocessing, patching or source generation.

    Args:
        name (String): name of the rust_library target.
        rule (String): Bazel Rust rule to build, defaults to `rust_library`.
        crate_name (String): name of the rust_library crate, same as name by default.
        deps (List of strings): The `deps` field.
        proc_macro_deps (List of strings): The `proc_macro_deps` field.
        features (List of strings): The `features` field.
        rustc_flags (List of strings): The `rustc_flags` field.

    Returns:
        A string for the BUILD file content.
    """
    crate_name = name if len(crate_name) == 0 else crate_name
    deps = "[{}]".format(",".join(["\"{}\"".format(ele) for ele in deps]))
    proc_macro_deps = "[{}]".format(",".join(["\"{}\"".format(ele) for ele in proc_macro_deps]))
    features = "[{}]".format(",".join(["\"{}\"".format(ele) for ele in features]))
    rustc_flags = "[{}]".format(",".join(["\"{}\"".format(ele) for ele in rustc_flags]))
    return """
load("@rules_rust//rust:defs.bzl", \"{rule}\")

{rule}(
    name = \"{}\",
    crate_name = \"{}\",
    srcs = glob(["**/*.rs"]),
    crate_features = {},
    edition = "2021",
    rustc_flags ={},
    visibility = ["//visibility:public"],
    deps = {},
    proc_macro_deps = {}
)
""".format(name, crate_name, features, rustc_flags, deps, proc_macro_deps, rule = rule)

def define_gbl_workspace(name = None):
    """Set up worksapce dependencies for GBL

    Dependencies are checked out during "repo init". The rule simply maps them to the correct repo
    names.

    Args:
        name (String): Placeholder for buildifier check.
    """
    maybe(
        repo_rule = native.local_repository,
        name = "rules_rust",
        path = "external/bazelbuild-rules_rust",
    )

    maybe(
        repo_rule = native.local_repository,
        name = "rules_license",
        path = "external/bazelbuild-rules_license",
    )

    # TODO(b/383783832): migrate to android-crates-io
    native.new_local_repository(
        name = "rules_rust_tinyjson",
        path = "external/rust/crates/tinyjson",
        build_file = "@rules_rust//util/process_wrapper:BUILD.tinyjson.bazel",
    )

    native.new_local_repository(
        name = "llvm_linux_x86_64_prebuilts",
        path = "prebuilts/clang/host/linux-x86/clang-{}".format(_CLANG_VERSION),
        build_file_content = "",
    )

    native.new_local_repository(
        name = "linux_x86_64_sysroot",
        path = "prebuilts/gcc/linux-x86/host/x86_64-linux-glibc2.17-4.8",
        build_file_content = """exports_files(glob(["**/*"]))
cc_library(
    name = "linux_x86_64_sysroot_include",
    hdrs = glob(["sysroot/usr/include/**/*.h"]),
    includes = [ "sysroot/usr/include" ],
    visibility = ["//visibility:public"],
)
""",
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
        name = "mkbootimg",
        path = "tools/mkbootimg",
        build_file_content = """exports_files(glob(["**/*"]))""",
    )

    native.new_local_repository(
        name = "libfdt_c",
        path = "external/dtc/libfdt",
        build_file = "@gbl//libfdt:BUILD.libfdt_c.bazel",
    )

    native.new_local_repository(
        name = "libufdt_c",
        path = "external/libufdt",
        build_file = "@gbl//libfdt:BUILD.libufdt_c.bazel",
    )

    native.new_local_repository(
        name = "libdttable_c",
        path = "external/libufdt/utils/src",
        build_file = "@gbl//libdttable:BUILD.libdttable_c.bazel",
    )

    native.new_local_repository(
        name = "arm_trusted_firmware",
        path = "external/arm-trusted-firmware",
        build_file = "@gbl//libboot/aarch64_cache_helper:BUILD.arm_trusted_firmware.bazel",
    )

    native.new_local_repository(
        name = "avb",
        path = "external/avb",
        build_file = "@gbl//libavb:BUILD.avb.bazel",
    )

    native.new_local_repository(
        name = "uuid",
        path = "external/rust/android-crates-io/crates/uuid",
        build_file_content = rust_crate_build_file("uuid"),
    )

    native.new_local_repository(
        name = "cstr",
        path = "packages/modules/Virtualization/libs/cstr",
        build_file_content = rust_crate_build_file("cstr"),
    )

    native.new_local_repository(
        name = "spin",
        path = "external/rust/android-crates-io/crates/spin",
        build_file_content = rust_crate_build_file(
            "spin",
            features = [
                "mutex",
                "spin_mutex",
            ],
            rustc_flags = [
                "-A",
                "unused_imports",
            ],
        ),
    )

    native.new_local_repository(
        name = "static_assertions",
        path = "external/rust/android-crates-io/crates/static_assertions",
        build_file_content = rust_crate_build_file("static_assertions"),
    )

    native.new_local_repository(
        name = "managed",
        path = "external/rust/android-crates-io/crates/managed",
        build_file_content = rust_crate_build_file(
            "managed",
            features = ["map"],
            rustc_flags = [
                "-A",
                "unused_macros",
                "-A",
                "redundant_semicolons",
            ],
        ),
    )

    native.new_local_repository(
        name = "itertools",
        path = "external/rust/android-crates-io/crates/itertools",
        build_file_content = rust_crate_build_file(
            "itertools",
            deps = ["@either"],
            features = ["default", "use_std", "use_alloc"],
            rustc_flags = ["-A", "dead_code"],
        ),
    )

    native.new_local_repository(
        name = "itertools_noalloc",
        path = "external/rust/android-crates-io/crates/itertools",
        build_file_content = rust_crate_build_file(
            "itertools_noalloc",
            crate_name = "itertools",
            features = [],
            deps = ["@either_noalloc"],
            rustc_flags = ["-A", "dead_code"],
        ),
    )

    native.new_local_repository(
        name = "either",
        path = "external/rust/android-crates-io/crates/either",
        build_file_content = rust_crate_build_file(
            "either",
            features = ["default", "use_std"],
        ),
    )

    native.new_local_repository(
        name = "either_noalloc",
        path = "external/rust/android-crates-io/crates/either",
        build_file_content = rust_crate_build_file(
            "either_noalloc",
            crate_name = "either",
            features = [],
        ),
    )

    # TODO(b/383783832): migrate to android-crates-io
    native.new_local_repository(
        name = "smoltcp",
        path = "external/rust/crates/smoltcp",
        build_file = "@gbl//smoltcp:BUILD.smoltcp.bazel",
    )

    native.new_local_repository(
        name = "arrayvec",
        path = "external/rust/android-crates-io/crates/arrayvec",
        build_file_content = rust_crate_build_file(
            "arrayvec",
            rustc_flags = ["-A", "dead_code"],
        ),
    )

    native.new_local_repository(
        name = "downcast",
        path = "external/rust/android-crates-io/crates/downcast",
        build_file_content = rust_crate_build_file(
            "downcast",
            features = ["default", "std"],
        ),
    )

    native.new_local_repository(
        name = "fragile",
        path = "external/rust/android-crates-io/crates/fragile",
        build_file_content = rust_crate_build_file("fragile"),
    )

    native.new_local_repository(
        name = "lazy_static",
        path = "external/rust/android-crates-io/crates/lazy_static",
        build_file_content = rust_crate_build_file("lazy_static"),
    )

    native.new_local_repository(
        name = "mockall",
        path = "external/rust/android-crates-io/crates/mockall",
        build_file_content = rust_crate_build_file(
            "mockall",
            deps = [
                "@cfg-if",
                "@downcast",
                "@fragile",
                "@lazy_static",
                "@predicates",
                "@predicates_tree",
            ],
            proc_macro_deps = ["@mockall_derive"],
        ),
    )

    native.new_local_repository(
        name = "mockall_derive",
        path = "external/rust/android-crates-io/crates/mockall_derive",
        build_file_content = rust_crate_build_file(
            "mockall_derive",
            rule = "rust_proc_macro",
            deps = ["@cfg-if", "@proc-macro2", "@quote", "@syn"],
        ),
    )

    native.new_local_repository(
        name = "predicates",
        path = "external/rust/android-crates-io/crates/predicates",
        build_file_content = rust_crate_build_file(
            "predicates",
            deps = ["@itertools", "@predicates_core", "@termcolor"],
        ),
    )

    native.new_local_repository(
        name = "predicates_core",
        path = "external/rust/android-crates-io/crates/predicates-core",
        build_file_content = rust_crate_build_file("predicates_core"),
    )

    native.new_local_repository(
        name = "predicates_tree",
        path = "external/rust/android-crates-io/crates/predicates-tree",
        build_file_content = rust_crate_build_file(
            "predicates_tree",
            deps = ["@predicates_core", "@termtree"],
        ),
    )

    native.new_local_repository(
        name = "termcolor",
        path = "external/rust/android-crates-io/crates/termcolor",
        build_file_content = rust_crate_build_file("termcolor"),
    )

    native.new_local_repository(
        name = "termtree",
        path = "external/rust/android-crates-io/crates/termtree",
        build_file_content = rust_crate_build_file("termtree"),
    )

    # TODO(b/383783832): migrate to android-crates-io
    native.new_local_repository(
        name = "zune_inflate",
        path = "external/rust/crates/zune-inflate",
        build_file_content = rust_crate_build_file(
            "zune_inflate",
            features = ["gzip"],
        ),
    )

    native.new_local_repository(
        name = "lz4_flex",
        path = "external/rust/android-crates-io/crates/lz4_flex",
        build_file_content = rust_crate_build_file(
            "lz4_flex",
            features = ["safe-decode"],
            rustc_flags = ["-A", "dead_code"],
        ),
    )

    native.new_local_repository(
        name = "zbi",
        path = "prebuilts/fuchsia_sdk/",
        build_file = "//prebuilts/fuchsia_sdk:BUILD.zbi.bazel",
    )

    native.new_local_repository(
        name = "zerocopy",
        path = "external/rust/android-crates-io/crates/zerocopy",
        build_file_content = rust_crate_build_file(
            "zerocopy",
            features = ["derive", "simd", "zerocopy-derive"],
            proc_macro_deps = ["@zerocopy_derive"],
        ),
    )

    native.new_local_repository(
        name = "zerocopy_derive",
        path = "external/rust/android-crates-io/crates/zerocopy-derive",
        build_file_content = rust_crate_build_file(
            "zerocopy_derive",
            rule = "rust_proc_macro",
            deps = ["@proc-macro2", "@quote", "@syn"],
        ),
    )

    # Following are third party rust crates dependencies which already contain a
    # BUILD file that we can use as-is without any modification.
    # TODO(b/383783832): migrate to android-crates-io
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
