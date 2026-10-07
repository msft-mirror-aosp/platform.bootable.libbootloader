# Copyright (C) 2026 The Android Open Source Project
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

load("@gbl//toolchain:gbl_toolchain.bzl", "int_flag_to_c_def")
load("@rules_cc//cc:defs.bzl", "cc_library")

package(
    default_applicable_licenses = ["@gbl//licensing:gbl_license"],
    default_visibility = ["//visibility:public"],
)

cc_library(
    name = "efi_arch_deps_aarch64",
    srcs = select({
        "@gbl//toolchain:tracing_enabled": [
            "mcount.c",
            "mcount_entry.S",
            "switch_stack.S",
            "trace_buffer_size.h",
        ],
        "//conditions:default": [],
    }),
    copts = [
        # Stack protector and sanitizers must not call mcount again.
        "-fno-stack-protector",
        "-fno-sanitize=all",
        # Always optimize tracing code.
        "-O3",
    ],
    data = [":trace_buffer_size"],
    includes = ["."],
    visibility = ["//visibility:public"],
    deps = [
        "@gbl//libefi_types:efi_c_headers",
        "@gbl//libtrace:headers",
    ],
)

int_flag_to_c_def(
    name = "_trace_buffer_size",
    flag = "@gbl//toolchain:trace_buffer_size_mb",
    macro = "TRACE_BUFFER_SIZE_MB",
)

genrule(
    name = "trace_buffer_size",
    srcs = [":_trace_buffer_size"],
    outs = ["trace_buffer_size.h"],
    cmd = "cp $(SRCS) $(OUTS)",
)
