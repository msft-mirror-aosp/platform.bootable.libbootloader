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

load("@rules_pkg//pkg:install.bzl", "pkg_install")
load("@rules_pkg//pkg:mappings.bzl", "pkg_files", "strip_prefix")

pkg_files(
    name = "gbl_efi_dist_files",
    srcs = ["@gbl//efi:all_platforms"],
    strip_prefix = strip_prefix.files_only(),
    visibility = ["//visibility:private"],
)

pkg_install(
    name = "gbl_efi_dist",
    srcs = [":gbl_efi_dist_files"],
    destdir = "out/gbl_efi/",
)
