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

def _dir_of(repo_ctx, path):
    return repo_ctx.execute(["dirname", _abs_path(repo_ctx, path)]).stdout.strip("\n")

def _gbl_llvm_prebuilts_impl(repo_ctx):
    """Implementation for gbl_llvm_prebuilts

    The repository rule sets up a repo for hosting LLVM distribution and Linux sysroot. They can
    be provided manually via the `GBL_LLVM_PREBUILTS` and `GBL_LINUX_SYSROOT` environment
    variables. If they don't exist, the top-level workspace needs to define them in repo
    `@llvm_linux_x86_64_prebuilts` and `@linux_x86_64_sysroot` respectively.

    Only Linux x86_64 platform is supported.
    """
    prebuilts = repo_ctx.os.environ.get("GBL_LLVM_PREBUILTS")
    if prebuilts:
        repo_ctx.symlink(prebuilts, "llvm-linux-x86")
    else:
        path = _dir_of(repo_ctx, repo_ctx.path(Label("@llvm_linux_x86_64_prebuilts//:BUILD.bazel")))
        repo_ctx.symlink(path, "llvm-linux-x86")

    # Linux host toolchain additionally needs a sysroot
    linux_sysroot = repo_ctx.os.environ.get("GBL_LINUX_SYSROOT")
    if linux_sysroot:
        repo_ctx.symlink(linux_sysroot, "linux_sysroot")
    else:
        path = _dir_of(repo_ctx, repo_ctx.path(Label("@linux_x86_64_sysroot//:BUILD.bazel")))
        repo_ctx.symlink(path, "linux_sysroot")

    # Get the bin directory so that we can access other LLVM tools by path.
    gbl_llvm_bin_dir = _abs_path(repo_ctx, "llvm-linux-x86/bin")

    # We use MUSL C sysroot for host. Use the corresponding musl C++ config when building C++.
    x86_musl_config_inc = Label("@llvm_linux_x86_64_prebuilts//:include/x86_64-unknown-linux-musl/c++/v1")
    x86_musl_config_inc = _abs_path(repo_ctx, repo_ctx.path(x86_musl_config_inc))

    # For GBL UEFI target we use our own minimal sysroot implementation. Thus we use our custom C++
    # config.
    gbl_sysroot = _abs_path(repo_ctx, repo_ctx.path(Label("@gbl//libc:include")))
    gbl_cpp_config_inc = Label("@gbl//libc:include/cpp_config_site")
    gbl_cpp_config_inc = _abs_path(repo_ctx, repo_ctx.path(gbl_cpp_config_inc))

    # Create an info.bzl file in the assembled repo to export header/library/tool paths.
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
LLVM_PREBUILTS_LIB_DIR = "{}"
LINUX_X86_MUSL_CPP_CONFIG = "{}"
GBL_EFI_SYSROOT = "{}"
GBL_CPP_CONFIG_INC = "{}"
""".format(
        "{}/include".format(llvm_resource_dir),
        _abs_path(repo_ctx, "llvm-linux-x86/include/c++/v1"),
        _abs_path(repo_ctx, "llvm-linux-x86/lib"),
        x86_musl_config_inc,
        gbl_sysroot,
        gbl_cpp_config_inc,
    )

    # Linux sysroot headers and musl dynamic library path
    info_bzl_content += """
LINUX_SYSROOT_INCLUDES = "{}"
LINUX_SYSROOT_LIB_DIR = "{}"
""".format(
        _abs_path(repo_ctx, "linux_sysroot/include"),
        _dir_of(repo_ctx, _abs_path(repo_ctx, "linux_sysroot/lib/libc_musl.so")),
    )

    repo_ctx.file("info.bzl", info_bzl_content)

    # The following files are needed for defining bindgen toolchain, we symlink them out to the
    # top level directory in case the distribution repo has its own BUILD file which blocks
    # direct access.
    repo_ctx.symlink("llvm-linux-x86/bin/clang", "clang")

    # In some prebuilt versions, "libc++.so" is a symlink to "libc++.so.1" etc. We need to use the
    # same name as the actual library file name in cc_import(). Otherwise it complains it can't
    # find the shared object.
    libcpp_sharelib_path = _abs_path(repo_ctx, "llvm-linux-x86/lib/x86_64-unknown-linux-gnu/libc++.so")
    libcpp_base_name = repo_ctx.execute(["basename", libcpp_sharelib_path]).stdout.strip("\n")
    repo_ctx.symlink(libcpp_sharelib_path, libcpp_base_name)

    # Do the same for libclang.so in case it's a symlink.
    libclang_sharelib_path = _abs_path(repo_ctx, "llvm-linux-x86/lib/libclang.so")
    libclang_basename = repo_ctx.execute(["basename", libclang_sharelib_path]).stdout.strip("\n")
    repo_ctx.symlink(libclang_sharelib_path, libclang_basename)

    # Add a BUILD file to make it a package
    repo_ctx.file("BUILD", """
load("@rules_cc//cc:cc_import.bzl", "cc_import")
load("@rules_shell//shell:sh_binary.bzl", "sh_binary")

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

# The current rust version used by GBL. This needs to be manually updated when new version of
# prebuilts is uploaded to https://android.googlesource.com/platform/prebuilts/rust/
GBL_RUST_VERSION = "1.95.0"

def _gbl_config_impl(repo_ctx):
    """Exports configurable value to build rules."""

    img_archive_tag = repo_ctx.getenv("BUILD_NUMBER") or "eng.{}".format(repo_ctx.getenv("USER"))

    # Query rustc LLVM version
    rust_llvm_ver = ""
    rustc_path = repo_ctx.path(Label("@rust_prebuilts//:bin/rustc"))
    rustc_res = repo_ctx.execute([rustc_path, "--version", "--verbose"])
    if rustc_res.return_code == 0:
        for line in rustc_res.stdout.split("\n"):
            if line.startswith("LLVM version:"):
                rust_llvm_ver = line.split(":")[1].strip()

    # Query clang LLVM version
    clang_llvm_ver = ""
    clang_path = repo_ctx.path(Label("@llvm_linux_x86_64_prebuilts//:bin/clang"))
    clang_res = repo_ctx.execute([clang_path, "--version"])
    if clang_res.return_code == 0:
        parts = clang_res.stdout.split("clang version ")
        if len(parts) > 1:
            clang_llvm_ver = parts[1].split(" ")[0].strip()

    enable_cross_lang_lto = False
    if rust_llvm_ver and clang_llvm_ver:
        # Match the full version string (major.minor.patch) to avoid linker errors
        # due to minor/patch version mismatches (e.g. LLVM 22.0.2 vs 22.0.1).
        enable_cross_lang_lto = (rust_llvm_ver == clang_llvm_ver)

    if not enable_cross_lang_lto:
        # buildifier: disable=print
        print("\n[GBL Toolchain WARNING]: LLVM version mismatch! Rustc ({}) vs Clang ({}). Cross-language ThinLTO FFI inlining is DEACTIVATED!\n".format(rust_llvm_ver, clang_llvm_ver))

    # Create a file to export environment variables.
    variables_content = """
IMG_ARCHIVE_TAG = "{}"
ENABLE_CROSS_LANG_LTO = {}
""".format(img_archive_tag, enable_cross_lang_lto)

    repo_ctx.file("variables.bzl", variables_content)
    repo_ctx.file("BUILD", "")

gbl_config = repository_rule(
    implementation = _gbl_config_impl,
    local = True,
)

# This should match upstream Android defaults at
# https://cs.android.com/android/platform/superproject/main/+/main:build/soong/rust/config/lints.go.
#
# We can't add these to the global flags in //toolchain:common_lint_opts
# because it breaks some third-party packages which don't use these lints.
# The global options also come later on the commandline so can't be overriden
# by a package.
#
# Instead we add these to `rustc_flags` for all our modules explicitly.
ANDROID_RUST_LINTS = [
    "-A",
    "deprecated",
    "-A",
    "unknown_lints",
    "-D",
    "missing-docs",
    "-D",
    "warnings",
    "-D",
    "unsafe_op_in_unsafe_fn",
    "-A",
    "clippy::disallowed_names",
    "-A",
    "clippy::type-complexity",
    "-A",
    "clippy::unnecessary_fallible_conversions",
    "-A",
    "clippy::unnecessary-wraps",
    "-A",
    "clippy::unusual-byte-groupings",
    "-A",
    "clippy::upper-case-acronyms",
    "-D",
    "clippy::undocumented_unsafe_blocks",
]
