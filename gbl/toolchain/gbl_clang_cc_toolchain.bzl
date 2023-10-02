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

load(
    "@bazel_tools//tools/cpp:cc_toolchain_config_lib.bzl",
    "action_config",
    "flag_group",
    "flag_set",
    "tool",
    "tool_path",
)
load("@gbl_llvm_toolchain_info//:info.bzl", "gbl_llvm_builtin_include", "gbl_llvm_tool_path")
load("@rules_cc//cc:action_names.bzl", "ACTION_NAMES", "ALL_CC_COMPILE_ACTION_NAMES")

def _flag_set(flags):
    """Convert a list of compile/link flags to a flag_set type."""
    return flag_set(
        flag_groups = [
            flag_group(
                flags = flags,
            ),
        ],
    )

def _gbl_clang_cc_toolchain_config_impl(ctx):
    """Implementation for rule _gbl_clang_cc_toolchain_config()"""
    return cc_common.create_cc_toolchain_config_info(
        ctx = ctx,
        cxx_builtin_include_directories = [gbl_llvm_builtin_include()],
        toolchain_identifier = "{}_id".format(ctx.attr.cc_toolchain_name),
        host_system_name = "local",
        target_system_name = ctx.attr.target_system_triple,
        target_cpu = ctx.attr.target_cpu,
        target_libc = "unknown",
        compiler = "clang",
        abi_version = "unknown",
        abi_libc_version = "unknown",
        action_configs = [
            action_config(
                action_name = action_name,
                enabled = True,
                tools = [tool(path = gbl_llvm_tool_path("clang++"))],
                flag_sets = [
                    _flag_set([
                        "--target={}".format(ctx.attr.target_system_triple),
                        "-nostdinc",
                        "-no-canonical-prefixes",
                        "-I{}".format(gbl_llvm_builtin_include()),
                        "-Werror",
                        "-Wall",
                    ]),
                    _flag_set(ctx.attr.cc_flags),
                ],
            )
            for action_name in ALL_CC_COMPILE_ACTION_NAMES
        ] + [
            action_config(
                action_name = ACTION_NAMES.cpp_link_executable,
                enabled = True,
                tools = [tool(path = gbl_llvm_tool_path("lld"))],
                flag_sets = [] if ctx.attr.ld_flags == [] else [_flag_set(ctx.attr.ld_flags)],
            ),
        ],
        tool_paths = [
            tool_path(
                name = "ld",
                path = gbl_llvm_tool_path("clang++"),
            ),
            tool_path(
                name = "ar",
                path = gbl_llvm_tool_path("llvm-ar"),
            ),
            tool_path(
                name = "cpp",
                path = gbl_llvm_tool_path("clang++"),
            ),
            tool_path(
                name = "gcc",
                path = gbl_llvm_tool_path("clang"),
            ),
            tool_path(
                name = "gcov",
                path = gbl_llvm_tool_path("llvm-cov"),
            ),
            tool_path(
                name = "nm",
                path = gbl_llvm_tool_path("llvm-nm"),
            ),
            tool_path(
                name = "objdump",
                path = gbl_llvm_tool_path("llvm-objdump"),
            ),
            tool_path(
                name = "strip",
                path = gbl_llvm_tool_path("llvm-strip"),
            ),
        ],
    )

_gbl_clang_cc_toolchain_config = rule(
    implementation = _gbl_clang_cc_toolchain_config_impl,
    attrs = {
        "cc_toolchain_name": attr.string(),
        "target_cpu": attr.string(),
        "target_system_triple": attr.string(),
        "cc_flags": attr.string_list(),
        "ld_flags": attr.string_list(),
    },
    provides = [CcToolchainConfigInfo],
)

def gbl_clang_cc_toolchain(
        name,
        target_cpu,
        target_system_triple,
        cc_flags = None,
        ld_flags = None):
    """Configure a clang based cc_toolchain().

    Args:
        name (String): Name of the target.
        target_cpu (string): Target CPU.
        target_system_triple (string): LLVM-style target system triple.
        cc_flags (List): clang compile flags.
        ld_flags (List): clang link flags
    """
    cc_flags = cc_flags or []
    ld_flags = ld_flags or []
    config_name = "_{}_config".format(name)
    _gbl_clang_cc_toolchain_config(
        name = config_name,
        cc_toolchain_name = name,
        target_cpu = target_cpu,
        target_system_triple = target_system_triple,
        cc_flags = cc_flags,
        ld_flags = ld_flags,
    )

    empty_filegroup = "_empty_{}".format(name)
    native.filegroup(name = empty_filegroup)
    empty_filegroup_target = ":{}".format(empty_filegroup)

    native.cc_toolchain(
        name = name,
        toolchain_identifier = name,
        toolchain_config = ":{}".format(config_name),
        all_files = empty_filegroup_target,
        compiler_files = empty_filegroup_target,
        dwp_files = empty_filegroup_target,
        linker_files = empty_filegroup_target,
        objcopy_files = empty_filegroup_target,
        strip_files = empty_filegroup_target,
        supports_param_files = 0,
    )
