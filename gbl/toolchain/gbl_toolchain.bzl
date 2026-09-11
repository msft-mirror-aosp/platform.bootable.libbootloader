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
This file contains rules for defininig GBL toolchains.
"""

load("@bazel_skylib//rules:common_settings.bzl", "BuildSettingInfo")
load(
    "@bazel_tools//tools/cpp:cc_toolchain_config_lib.bzl",
    "action_config",
    "flag_group",
    "flag_set",
    "tool",
    "tool_path",
)
load("@gbl_llvm_prebuilts//:info.bzl", "LLVM_PREBUILTS_C_INCLUDE", "gbl_llvm_tool_path")
load("@rules_cc//cc:action_names.bzl", "ACTION_NAMES", "ALL_CPP_COMPILE_ACTION_NAMES")
load("@rules_cc//cc:defs.bzl", "CcToolchainConfigInfo")
load("@rules_cc//cc/common:cc_common.bzl", "cc_common")
load("@rules_cc//cc/common:cc_info.bzl", "CcInfo")
load("@rules_cc//cc/toolchains:cc_toolchain.bzl", "cc_toolchain")

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
    builtin_includes = ctx.attr.builtin_includes or [LLVM_PREBUILTS_C_INCLUDE]
    common_compile_flagset = [
        _flag_set([
            "--target={}".format(ctx.attr.target_system_triple),
            "-nostdinc",
            "-no-canonical-prefixes",
            "-Werror",
            "-Wall",
        ] + ["-I{}".format(inc) for inc in builtin_includes] + ctx.attr.cc_flags),
    ]
    return cc_common.create_cc_toolchain_config_info(
        ctx = ctx,
        cxx_builtin_include_directories = builtin_includes,
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
                flag_sets = common_compile_flagset,
            )
            for action_name in ALL_CPP_COMPILE_ACTION_NAMES +
                               [ACTION_NAMES.assemble, ACTION_NAMES.preprocess_assemble]
        ] + [
            action_config(
                action_name = ACTION_NAMES.c_compile,
                enabled = True,
                tools = [tool(path = gbl_llvm_tool_path("clang"))],
                flag_sets = common_compile_flagset,
            ),
        ] + [
            action_config(
                action_name = ACTION_NAMES.cpp_link_executable,
                enabled = True,
                tools = [tool(path = gbl_llvm_tool_path("clang++"))],
                flag_sets = [_flag_set(ctx.attr.ld_flags)] if ctx.attr.ld_flags else [],
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
        "builtin_includes": attr.string_list(),
    },
    provides = [CcToolchainConfigInfo],
)

def gbl_clang_cc_toolchain(
        name,
        target_cpu,
        target_system_triple,
        cc_flags = None,
        ld_flags = None,
        builtin_includes = None):
    """Configure a clang based cc_toolchain().

    Args:
        name (String): Name of the target.
        target_cpu (string): Target CPU.
        target_system_triple (string): LLVM-style target system triple.
        cc_flags (List): clang compile flags.
        ld_flags (List): clang link flags
        builtin_includes (List): Override the default list of builtin include dirs.
    """
    config_name = "_{}_config".format(name)
    _gbl_clang_cc_toolchain_config(
        name = config_name,
        cc_toolchain_name = name,
        target_cpu = target_cpu,
        target_system_triple = target_system_triple,
        cc_flags = cc_flags,
        ld_flags = ld_flags,
        builtin_includes = builtin_includes,
    )

    empty_filegroup = "_empty_{}".format(name)
    native.filegroup(name = empty_filegroup)
    empty_filegroup_target = ":{}".format(empty_filegroup)

    cc_toolchain(
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

def _prebuilt_binary_impl(ctx):
    """Generate a wrapper executable type target that simply symlinks to a given executable binary.

    This is for rules that only accept executable type target but not binary file directly.
    i.e. `rust_bindgen_toolchain`
    """
    out = ctx.actions.declare_file(ctx.label.name)
    ctx.actions.symlink(
        output = out,
        target_file = ctx.executable.bin,
    )
    return [DefaultInfo(files = depset([out]), executable = out)]

prebuilt_binary = rule(
    implementation = _prebuilt_binary_impl,
    executable = True,
    attrs = {
        "bin": attr.label(allow_single_file = True, executable = True, cfg = "exec"),
    },
)

# A transition rule that emits the `@gbl//toolchain:rust_no_sysroot_true` setting.
def _no_sysroot_transition_impl(_, __):
    return {"@gbl//toolchain:rust_no_sysroot": True}

_no_sysroot_transition = transition(
    implementation = _no_sysroot_transition_impl,
    inputs = [],
    outputs = ["@gbl//toolchain:rust_no_sysroot"],
)

# Creates a symlink wrapper to `file` in the given `ctx`.
# Returns the symlink file object.
def _create_symlink_wrapper(ctx, file):
    out = ctx.actions.declare_file("{}/{}".format(ctx.label.name, file.basename))
    ctx.actions.symlink(output = out, target_file = file)
    return out

# A rule implementation that simply forwards dependencies from attribute `deps` and generates
# symlinks to their output files.
def _forward_and_symlink(ctx):
    outs = []
    for file in ctx.files.deps:
        outs.append(_create_symlink_wrapper(ctx, file))
    return [DefaultInfo(files = depset(outs))]

# A rule for building rust targets with the `@gbl//toolchain:rust_no_sysroot_true` setting.
build_with_no_rust_sysroot = rule(
    implementation = _forward_and_symlink,
    cfg = _no_sysroot_transition,
    attrs = {
        # Mandatory attribute for rules with transition.
        "_allowlist_function_transition": attr.label(
            default = Label("@bazel_tools//tools/allowlists/function_transition_allowlist"),
        ),
        "deps": attr.label_list(allow_files = True, mandatory = True),
    },
)

# A transition rule that emits the "--platforms=<attr.platform>" option.
def _platform_transition_impl(settings, attr):
    mode = attr.mode if attr.mode != "" else settings["//command_line_option:compilation_mode"]
    return {
        "//command_line_option:platforms": attr.platform,
        "//command_line_option:compilation_mode": mode,
    }

_platform_transition = transition(
    implementation = _platform_transition_impl,
    inputs = ["//command_line_option:compilation_mode"],
    outputs = ["//command_line_option:platforms", "//command_line_option:compilation_mode"],
)

build_with_platform = rule(
    implementation = _forward_and_symlink,
    cfg = _platform_transition,
    attrs = {
        # Mandatory attribute for rules with transition.
        "_allowlist_function_transition": attr.label(
            default = Label("@bazel_tools//tools/allowlists/function_transition_allowlist"),
        ),
        "platform": attr.string(mandatory = True),
        "mode": attr.string(mandatory = False),
        "deps": attr.label_list(allow_files = True, mandatory = True),
    },
)

# Unconditionally transitions to the host dev platform.
def _dev_transition_impl(_settings, _attr):
    return {"//command_line_option:platforms": "@gbl//toolchain:host_x86_64_dev"}

_dev_transition = transition(
    inputs = [],
    outputs = ["//command_line_option:platforms"],
    implementation = _dev_transition_impl,
)

# Wrapper to build the dev version of a host test target.
# In our current setup, the default build is always the prod configuration
# so we need to wrap tests with this to also run the dev tests.
def _dev_test_impl(ctx):
    # Our rule implementation is required to create the executable it runs.
    # Since we're just wrapping a target that has already built the test under
    # the dev platform transition, we just symlink to it.
    file = ctx.files.target[0]
    return DefaultInfo(
        files = depset(ctx.files.target),
        executable = _create_symlink_wrapper(ctx, file),
        runfiles = ctx.attr.target[DefaultInfo].default_runfiles,
    )

dev_test = rule(
    cfg = _dev_transition,
    attrs = {
        "target": attr.label(),
    },
    implementation = _dev_test_impl,
    test = True,
)

# This rule creates symlink for a static library in both Linux/GNU and MSVC naming styles so that
# rust linker is able to find it when building for them.
#
# When flag "-Clink-arg=-l<libname>" is passed to rustc, for Linux/GNU target platforms, the linker
# looks for library named "lib<libname>.a", for MSVC target plaforms (i.e. UEFI), the linker looks
# for library named "<libname>.lib". When bazel builds a cc_library target, it always outputs the
# Linux/GNU naming style and therefore fails linking when building for UEFI targets.
def _link_static_cc_library_impl(ctx):
    # Put an underscore so that we don't need to deal with potential "lib" prefix from user
    # provided name.
    libname = "_{}".format(ctx.label.name)

    # Create symlink for both naming styles.
    out_msvc_style = ctx.actions.declare_file("{}.lib".format(libname))
    ctx.actions.symlink(output = out_msvc_style, target_file = ctx.files.cc_library[0])
    out_linux_style = ctx.actions.declare_file("lib{}.a".format(libname))
    ctx.actions.symlink(output = out_linux_style, target_file = ctx.files.cc_library[0])

    # Construct and return a `CcInfo` for this rule that includes the library to link, so that
    # other rust_library/cc_library can depend directly on this target.
    library_to_link = cc_common.create_library_to_link(
        actions = ctx.actions,
        # Either is fine, since both yield the same linker option by Bazel.
        static_library = out_linux_style,
    )
    linking_input = cc_common.create_linker_input(
        owner = ctx.label,
        libraries = depset([library_to_link]),
        # Make sure both symlinks are generated.
        additional_inputs = depset([out_msvc_style, out_linux_style]),
    )
    linking_context = cc_common.create_linking_context(linker_inputs = depset([linking_input]))
    return [CcInfo(linking_context = linking_context)]

link_static_cc_library = rule(
    implementation = _link_static_cc_library_impl,
    attrs = {
        "cc_library": attr.label(),  # The cc_library() target for the static library.
    },
)

# Implementation of the extract_pdb_file rule.
def _extract_pdb_file(ctx):
    output_groups = ctx.attr.target[OutputGroupInfo]

    # noop if target doesn't generate PDB file.
    out = output_groups.pdb_file if hasattr(output_groups, "pdb_file") else depset([])
    return DefaultInfo(files = out)

extract_pdb_file = rule(
    implementation = _extract_pdb_file,
    attrs = {
        # The target that generates pdb file
        "target": attr.label(
            mandatory = True,
            providers = [OutputGroupInfo],
        ),
    },
)

# Implementation of the rename_output rule.
def _rename_output(ctx):
    out = ctx.actions.declare_file("{}/{}".format(ctx.label.name, ctx.attr.out))
    ctx.actions.symlink(output = out, target_file = ctx.files.target[0])
    return DefaultInfo(files = depset([out]))

rename_output = rule(
    implementation = _rename_output,
    attrs = {
        "target": attr.label(
            mandatory = True,
            allow_single_file = True,
        ),
        "out": attr.string(mandatory = True),
    },
)

# Implementation of int_flag_to_c_def
def _int_flag_to_c_def_impl(ctx):
    value = ctx.attr.flag[BuildSettingInfo].value
    out = ctx.actions.declare_file(ctx.label.name + ".h")
    ctx.actions.write(out, """
#ifndef _{}_H
#define _{}_H

#define {} ({})
#endif
""".format(ctx.attr.macro, ctx.attr.macro, ctx.attr.macro, value))
    return [DefaultInfo(files = depset([out]))]

# Generates a header file with a C macro for the given flag value.
int_flag_to_c_def = rule(
    implementation = _int_flag_to_c_def_impl,
    attrs = {
        "flag": attr.label(mandatory = True),
        "macro": attr.string(mandatory = True),
    },
)

# A transition rule that emits the "@gbl//toolchain:enable_tracing" option.
def _tracing_transition_impl(_settings, _attr):
    return {"@gbl//toolchain:enable_tracing": True}

_tracing_transition = transition(
    implementation = _tracing_transition_impl,
    inputs = [],
    outputs = ["@gbl//toolchain:enable_tracing"],
)

build_with_tracing = rule(
    implementation = _forward_and_symlink,
    cfg = _tracing_transition,
    attrs = {
        # Mandatory attribute for rules with transition.
        "_allowlist_function_transition": attr.label(
            default = Label("@bazel_tools//tools/allowlists/function_transition_allowlist"),
        ),
        "deps": attr.label_list(allow_files = True, mandatory = True),
    },
)
