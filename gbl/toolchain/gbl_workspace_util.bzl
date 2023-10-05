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

def _abs_path(repo_ctx, path):
    return repo_ctx.execute(["readlink", "-f", path]).stdout.strip("\n")

def _gbl_llvm_prebuilts_impl(repo_ctx):
    """Implementation for gbl_llvm_prebuilts

    The repository rule sets up a repo for hosting LLVM distribution. It can be provided manually
    via the `GBL_LLVM_PREBUILTS` environment variable. If it doesn't exist, the rule fetches from
    Android upstream.

    Only Linux x86_64 platform is supported.
    """
    prebuilts = repo_ctx.os.environ.get("GBL_LLVM_PREBUILTS")
    if prebuilts:
        repo_ctx.symlink(prebuilts, "llvm-linux-x86")
    else:
        # Fetch the LLVM prebuilts used by Trusty and u-boot.
        repo_ctx.download_and_extract(
            url = "https://android.googlesource.com/platform/prebuilts/clang/host/linux-x86/+archive/18420bf70dde33f6fae92624a1dad774aeae0e83/clang-r475365b.tar.gz",
            output = "llvm-linux-x86",
        )

    # Get the bin directory so that we can access other LLVM tools by path.
    gbl_llvm_bin_dir = _abs_path(repo_ctx, "llvm-linux-x86/bin")

    # Get the builtin include directory, which is required by cc_toolchain config.
    clang = repo_ctx.execute(["readlink", "-f", "llvm-linux-x86/bin/clang"]).stdout.strip("\n")
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

    # The following files are needed for defining bindgen toolchain, we symlink them out to the
    # top level directory in case the the distribution repo has its own BUILD file which blocks
    # direct access.
    repo_ctx.symlink("llvm-linux-x86/bin/clang", "clang")

    # In some prebuilt versions, "libc++.so" is a symlink to "libc++.so.1" etc. We need to use the
    # same name as the actual library file name in cc_import(). Otherwise it complains it can't
    # find the shared object.
    libcpp_sharelib_path = _abs_path(repo_ctx, "llvm-linux-x86/lib/libc++.so")
    libcpp_base_name = repo_ctx.execute(["basename", libcpp_sharelib_path]).stdout.strip("\n")
    repo_ctx.symlink(libcpp_sharelib_path, libcpp_base_name)

    # Do the same for libclang.so in case it's a symlink.
    libclang_sharelib_path = _abs_path(repo_ctx, "llvm-linux-x86/lib/libclang.so")
    libclang_basename = repo_ctx.execute(["basename", libclang_sharelib_path]).stdout.strip("\n")
    repo_ctx.symlink(libclang_sharelib_path, libclang_basename)

    # Add a BUILD file to make it a package
    repo_ctx.file("BUILD", """
package(
    default_visibility = ["//visibility:public"],
)

exports_files(glob(["**/*"]))

sh_binary(
    name = "clang-bin",
    srcs = [":clang"],
)

cc_import(
    name = "libc++",
    shared_library = ":{}",
)

cc_import(
    name = "libclang",
    shared_library = ":{}",
)
""".format(libcpp_base_name, libclang_basename))

gbl_llvm_prebuilts = repository_rule(
    implementation = _gbl_llvm_prebuilts_impl,
    local = True,
    environ = ["GBL_LLVM_PREBUILTS"],
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
