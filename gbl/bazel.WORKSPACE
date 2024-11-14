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

"""Remaining repositories not yet migrated to bzlmod."""

local_repository(
    name = "gbl",
    path = "bootable/libbootloader/gbl",
)

# buildifier: disable=load-on-top
load("@gbl//integration/aosp_uefi-gbl-mainline:workspace.bzl", "define_gbl_workspace")

define_gbl_workspace()

load("@rules_rust//tools/rust_analyzer:deps.bzl", "rust_analyzer_dependencies")

rust_analyzer_dependencies()

load("@gbl//toolchain:gbl_workspace_util.bzl", "GBL_RUST_VERSION")
load("@rules_rust//rust:repositories.bzl", "rust_analyzer_toolchain_repository")

register_toolchains(rust_analyzer_toolchain_repository(
    name = "rust_analyzer_toolchain",
    version = GBL_RUST_VERSION,
))
