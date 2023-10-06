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

    The repository rule sets up a repo for hosting LLVM distribution and Linux sysroot. They can
    be provided manually via the `GBL_LLVM_PREBUILTS` and `GBL_LINUX_SYSROOT` environment
    variables. If they don't exist, the rule fetches them from Android upstream.

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

    # Linux host toolchain additionally needs a sysroot
    linux_glibc = repo_ctx.os.environ.get("GBL_LINUX_SYSROOT")
    if linux_glibc:
        repo_ctx.symlink(linux_glibc, "linux_glibc")
    else:
        repo_ctx.download_and_extract(
            url = "https://android.googlesource.com/platform/prebuilts/gcc/linux-x86/host/x86_64-linux-glibc2.17-4.8/+archive/refs/heads/main.tar.gz",
            output = "linux_glibc",
        )

    # Get the bin directory so that we can access other LLVM tools by path.
    gbl_llvm_bin_dir = _abs_path(repo_ctx, "llvm-linux-x86/bin")

    # Create a info.bzl file in the assembled repo to export header/library/tool paths.
    info_bzl_content = """
def gbl_llvm_tool_path(tool_name):
    return "{}/" + tool_name
""".format(gbl_llvm_bin_dir)

    # Get the builtin include directories.
    clang = _abs_path(repo_ctx, "llvm-linux-x86/bin/clang")
    llvm_resource_dir = repo_ctx.execute([clang, "--print-resource-dir"]).stdout.strip("\n")
    info_bzl_content += """
LLVM_PREBUILTS_C_INCLUDE = "{}"
LLVM_PREBUILTS_CPP_INCLUDE = "{}"
""".format(
        "{}/include".format(llvm_resource_dir),
        _abs_path(repo_ctx, "llvm-linux-x86/include/c++/v1"),
    )

    # Linux sysroot headers
    sysroot_includes = [
        _abs_path(repo_ctx, "linux_glibc/sysroot/usr/include"),
        _abs_path(repo_ctx, "linux_glibc/sysroot/usr/include/x86_64-linux-gnu"),
    ]
    info_bzl_content += """
LINUX_SYSROOT_INCLUDES = [{}]
""".format(",".join(["\"{}\"".format(inc) for inc in sysroot_includes]))

    repo_ctx.file("info.bzl", info_bzl_content)

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
    environ = ["GBL_LLVM_PREBUILTS", "GBL_LINUX_SYSROOT"],
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
