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

def _gbl_llvm_toolchain_info_repo_impl(repo_ctx):
    """Implementation for gbl_llvm_toolchain_info_repo

    The repository rule gets the LLVM clang path from environment variable
    `GBL_LLVM_CLANG_PATH` and assembles a repo to export the value of LLVM
    tool path and builtin include directory, which are needed for toolchain
    definition.
    """

    # Get clang path from "GBL_LLVM_BIN_DIR" environment variable. Default to
    # host installed LLVM if it is not set.
    clang = repo_ctx.os.environ.get("GBL_LLVM_CLANG_PATH")
    if clang == None:
        fail("""

No LLVM clang provided in `GBL_LLVM_CLANG_PATH`.

Please set environment variable `GBL_LLVM_CLANG_PATH` to the path of the LLVM clang binary to use.

It is recommended to use the Android upstream LLVM prebuilt. For example, if you have a local Android source checkout, you can set it to:

    export GBL_LLVM_CLANG_PATH=<path to android source checkout>/prebuilts/clang/host/linux-x86/clang-r475365b/bin/clang

Note: The stable version number "clang-r475365b" might be different.

""")

    # Resolve absolute path if the given path is a symlink.
    clang = repo_ctx.execute(["readlink", "-f", clang]).stdout.strip("\n")

    # Get the directory. This assumes that the clang lives in a standard LLVM
    # distribution directory layout.
    gbl_llvm_bin_dir = repo_ctx.execute(["dirname", clang]).stdout.strip("\n")

    # Get the builtin include directory, which is required by cc_toolchain config.
    llvm_resource_dir = repo_ctx.execute([clang, "--print-resource-dir"]).stdout.strip("\n")
    builtin_include = "{}/include/".format(llvm_resource_dir)

    # Create a info.bzl file in the assembled repo to export the tool path and
    # builtin include directory.
    repo_ctx.file("info.bzl", """
def gbl_llvm_tool_path(tool_name):
    return "{}/" + tool_name

def gbl_llvm_builtin_include():
    return "{}"
""".format(gbl_llvm_bin_dir, builtin_include))

    # Add a BUILD file to make it a package
    repo_ctx.file("BUILD", "")

gbl_llvm_toolchain_info_repo = repository_rule(
    implementation = _gbl_llvm_toolchain_info_repo_impl,
    local = True,
    environ = ["GBL_LLVM_CLANG_PATH"],
)

def _gbl_custom_rust_sysroot(repo_ctx):
    """Implementation for gbl_custom_rust_sysroot

    The repository rule checks if a custom rust sysroot is provided via environmental variable
    `GBL_CUSTOM_RUST_SYSROOT`. If yes, it sets up a repo with a `rust_stdlib_filegroup` target to
    export the sysroot libraries. The rule is used when we need to export our own built sysroot
    libraries via //rust_sysroot:sysroot. See build_gbl.py for more detail.
    """
    sysroot_dir = repo_ctx.os.environ.get("GBL_CUSTOM_RUST_SYSROOT")
    if sysroot_dir:
        repo_ctx.symlink(sysroot_dir, "sysroot")

    # Always make a build file so that reference to the repository is always valid. When `sysroot`
    # does not exist, reference is a harmless noop (empty file group). This is the case when we are
    # building the sysroot itself.
    repo_ctx.file("BUILD", """
load("@rules_rust//rust:toolchain.bzl", "rust_stdlib_filegroup")

# Export all .rlib files found in this repo
rust_stdlib_filegroup(
    name = "stdlib",
    srcs = glob(
        ["**/*.rlib"],
        allow_empty = True,
    ),
    visibility = ["//visibility:public"],
)
""")

gbl_custom_rust_sysroot = repository_rule(
    implementation = _gbl_custom_rust_sysroot,
    local = True,
    environ = ["GBL_CUSTOM_RUST_SYSROOT"],
)
