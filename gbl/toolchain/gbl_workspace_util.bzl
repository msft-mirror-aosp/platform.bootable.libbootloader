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

def _gbl_llvm_toolchain_info_repo_impl(repo_ctx):
    """Implementation for gbl_llvm_toolchain_info_repo

    The repository rule gets the LLVM clang path from environment variable
    `GBL_LLVM_CLANG_PATH` and assembles a repo to export the value of LLVM
    tool path and builtin include directory, which are needed for toolchain
    definition.
    """

    # Get clang path from "GBL_LLVM_BIN_DIR" environment variable. Default to
    # host installed LLVM if it is not set.
    clang = repo_ctx.os.environ.get("GBL_LLVM_CLANG_PATH", "/usr/bin/clang++")

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
    environ = ["GBL_LLVM_BIN_DIR"],
)
