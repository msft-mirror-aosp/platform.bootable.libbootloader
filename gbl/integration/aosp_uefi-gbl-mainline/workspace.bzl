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

load("@gbl//toolchain:constants.scl", "CLANG_VERSION")
load("@gbl//toolchain:gbl_new_local_repository.bzl", "gbl_new_local_repository")
load("@gbl//toolchain:gbl_workspace_util.bzl", "GBL_RUST_VERSION")

def define_gbl_workspace(name = None):
    """Set up worksapce dependencies for GBL

    Dependencies are checked out during "repo init". The rule simply maps them to the correct repo
    names.

    Args:
        name (String): Placeholder for buildifier check.
    """

    gbl_new_local_repository(
        name = "llvm_linux_x86_64_prebuilts",
        path = "prebuilts/clang/host/linux-x86/clang-{}".format(CLANG_VERSION),
        exclude_files = ["BUILD.bazel"],
        build_file = "@gbl//toolchain:BUILD.llvm_linux_x86_64_prebuilts.bazel",
    )

    gbl_new_local_repository(
        name = "rust_prebuilts",
        path = "prebuilts/rust-toolchain/linux-musl-x86/{}".format(GBL_RUST_VERSION),
        build_file = "@gbl//toolchain:BUILD.android_rust_prebuilts.bazel",
        # We replace the top-level BUILD file with our own.
        exclude_files = ["BUILD.bazel"],
    )

# buildifier: disable=unused-variable
def _gbl_repositories_ext_impl(module_ctx):
    define_gbl_workspace()

gbl_repositories_ext = module_extension(
    implementation = _gbl_repositories_ext_impl,
)
