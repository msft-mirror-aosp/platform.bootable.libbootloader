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

"""Custom Clippy aspect for first-party GBL Rust crates.

`gbl_clippy_aspect` is an adapted version of upstream
`@rules_rust//rust:defs.bzl%rust_clippy_aspect`, which cannot be used as-is
because:
1. It unconditionally skips any target whose `workspace_root` starts with
   `"external"`. Both standalone (`uefi-gbl-mainline`) and kernel/Kleaf checkouts
   place the root `MODULE.bazel` at the repo checkout root (so `external/` and
   `prebuilts/` are within the workspace) and load `bootable/libbootloader/gbl`
   via `bazel_dep` + `local_path_override(module_name = "gbl", ...)`. As a result,
   Bazel assigns `@gbl//...` targets `workspace_root = "external/gbl+"`, which
   skips all `@gbl//...` targets.
2. It does not set `attr_aspects`, so it only runs on top-level targets that
   directly provide `CrateInfo` or `TestCrateInfo` and does not propagate
   through `test_suite`, `rust_test.crate`, `deps`, `data`, or platform-transition
   wrapper rules (`build_with_platform`, `dev_test`, `gbl_efi_dist`).

`gbl_clippy_aspect` propagates across the dependency graph and runs
`clippy-driver` on all first-party `@gbl` crates with checked-in crate roots.
"""

load("@rules_rust//rust:defs.bzl", "rust_common")

# buildifier: disable=bzl-visibility
load(
    "@rules_rust//rust/private:rustc.bzl",
    "collect_deps",
    "collect_inputs",
    "construct_arguments",
    "get_error_format",
)

# buildifier: disable=bzl-visibility
load(
    "@rules_rust//rust/private:utils.bzl",
    "determine_output_hash",
    "find_cc_toolchain",
    "find_toolchain",
    "is_exec_configuration",
)

_GBL_WORKSPACE_ROOT = Label("//:BUILD").workspace_root

_IGNORE_TAGS = [
    "no_clippy",
    "no_lint",
    "nolint",
    "noclippy",
]

def _has_ignore_tag(ctx):
    """Returns True if the target rule has a tag that opts out of Clippy.

    Args:
        ctx (ctx): The aspect's context object.

    Returns:
        bool: True if the target should be ignored by Clippy.
    """
    if hasattr(ctx.rule.attr, "tags"):
        for tag in ctx.rule.attr.tags:
            if tag.replace("-", "_").lower() in _IGNORE_TAGS:
                return True
    return False

def _get_clippy_ready_crate_info(target, ctx):
    """Checks if a target is a first-party `@gbl` crate and returns its `CrateInfo`.

    Args:
        target (Target): The target the aspect is running on.
        ctx (ctx): The aspect's context object.

    Returns:
        CrateInfo or None: The target's `CrateInfo` if Clippy should run on it,
        or `None` otherwise.
    """
    if target.label.workspace_root != _GBL_WORKSPACE_ROOT:
        return None

    if _has_ignore_tag(ctx):
        return None

    if rust_common.crate_info in target:
        crate_info = target[rust_common.crate_info]
    elif rust_common.test_crate_info in target:
        crate_info = target[rust_common.test_crate_info].crate
    else:
        return None

    # Skip crates whose root source file is generated (e.g. rust_bindgen wrappers)
    # or lives in an external third-party repository (e.g. @boringssl, @smoltcp).
    if not crate_info.root.is_source or crate_info.root.owner.workspace_root != _GBL_WORKSPACE_ROOT:
        return None

    return crate_info

def _dedup_rule_attr(rule_attr, crate_info):
    """Deduplicates `data` targets whose labels already appear in `compile_data_targets`.

    In an aspect with `attr_aspects = ["*"]`, `ctx.rule.attr.data` contains
    aspect-decorated `Target` objects, whereas `crate_info.compile_data_targets`
    contains undecorated `Target` objects from the rule evaluation. If a target
    lists the same label in both `data` and `compile_data`, `depset` will not
    deduplicate them and `ctx.expand_location` will fail with a duplicate label
    error.

    Args:
        rule_attr (struct): The target rule's `ctx.rule.attr` struct.
        crate_info (CrateInfo): The target crate's `CrateInfo` provider.

    Returns:
        struct: A copy of `rule_attr` with duplicate labels removed from `data`.
    """
    if not hasattr(rule_attr, "data"):
        return rule_attr
    compile_data_labels = {
        t.label: True
        for t in crate_info.compile_data_targets.to_list()
    }
    attrs = {name: getattr(rule_attr, name) for name in dir(rule_attr)}
    attrs["data"] = [t for t in rule_attr.data if t.label not in compile_data_labels]
    return struct(**attrs)

def _collect_transitive_clippy_outputs(ctx):
    """Collects `clippy_checks` output depsets from all target attributes of the rule.

    Args:
        ctx (ctx): The aspect's context object.

    Returns:
        list[depset]: Transitive Clippy output depsets from the rule's dependencies.
    """
    transitive = []
    if not hasattr(ctx, "rule"):
        return transitive

    for attr_name in dir(ctx.rule.attr):
        if attr_name.startswith("_"):
            continue
        attr = getattr(ctx.rule.attr, attr_name)
        if type(attr) == "list":
            for item in attr:
                if type(item) == "Target" and OutputGroupInfo in item and hasattr(item[OutputGroupInfo], "clippy_checks"):
                    transitive.append(item[OutputGroupInfo].clippy_checks)
        elif type(attr) == "Target" and OutputGroupInfo in attr and hasattr(attr[OutputGroupInfo], "clippy_checks"):
            transitive.append(attr[OutputGroupInfo].clippy_checks)

    return transitive

def _gbl_clippy_aspect_impl(target, ctx):
    """Aspect implementation that runs `clippy-driver` on first-party `@gbl` crates.

    Args:
        target (Target): The target the aspect is running on.
        ctx (ctx): The aspect's context object.

    Returns:
        list: Providers (`OutputGroupInfo`).
    """

    # Exit early if a target already provides a `clippy_checks` output group or
    # opts out via `tags = ["no_clippy"]`.
    if OutputGroupInfo in target and hasattr(target[OutputGroupInfo], "clippy_checks"):
        return []

    if _has_ignore_tag(ctx):
        return [OutputGroupInfo(clippy_checks = depset([]))]

    transitive = _collect_transitive_clippy_outputs(ctx)

    crate_info = _get_clippy_ready_crate_info(target, ctx)
    if not crate_info:
        return [OutputGroupInfo(clippy_checks = depset(transitive = transitive))]

    toolchain = find_toolchain(ctx)
    cc_toolchain, feature_configuration = find_cc_toolchain(ctx)

    dep_info, build_info, _ = collect_deps(
        deps = crate_info.deps,
        proc_macro_deps = crate_info.proc_macro_deps,
        aliases = crate_info.aliases,
    )

    # `construct_arguments` only applies `toolchain.extra_rustc_flags` to
    # non-exec targets (because `extra_exec_rustc_flags` is kept minimal so
    # `rules_rust`'s internal bootstrap crates can compile). Ensure first-party
    # `@gbl` exec targets (such as proc-macros and host tools) still receive
    # the toolchain lint flags during Clippy.
    clippy_flags = list(toolchain.extra_rustc_flags) if is_exec_configuration(ctx) else []

    compile_inputs, out_dir, build_env_files, build_flags_files, linkstamp_outs, ambiguous_libs = collect_inputs(
        ctx,
        ctx.rule.file,
        ctx.rule.files,
        depset([]),
        toolchain,
        cc_toolchain,
        feature_configuration,
        crate_info,
        dep_info,
        build_info,
        [],
    )

    args, env = construct_arguments(
        ctx = ctx,
        attr = _dedup_rule_attr(ctx.rule.attr, crate_info),
        file = ctx.file,
        toolchain = toolchain,
        tool_path = toolchain.clippy_driver.path,
        cc_toolchain = cc_toolchain,
        feature_configuration = feature_configuration,
        crate_info = crate_info,
        dep_info = dep_info,
        linkstamp_outs = linkstamp_outs,
        ambiguous_libs = ambiguous_libs,
        output_hash = determine_output_hash(crate_info.root, ctx.label),
        rust_flags = clippy_flags,
        out_dir = out_dir,
        build_env_files = build_env_files,
        build_flags_files = build_flags_files,
        emit = ["dep-info", "metadata"],
        skip_expanding_rustc_env = True,
        error_format = get_error_format(ctx.attr, "_error_format"),
    )

    if crate_info.is_test:
        args.rustc_flags.add("--test")

    clippy_out = ctx.actions.declare_file(ctx.label.name + ".clippy.ok", sibling = crate_info.output)
    args.process_wrapper_flags.add("--touch-file", clippy_out)

    env["CLIPPY_CONF_DIR"] = "${{pwd}}/{}".format(ctx.file._config.dirname)
    compile_inputs = depset([ctx.file._config], transitive = [compile_inputs])

    # buildifier: disable=pass-args-to-actions
    ctx.actions.run(
        executable = ctx.executable._process_wrapper,
        inputs = compile_inputs,
        outputs = [clippy_out],
        env = env,
        tools = [toolchain.clippy_driver],
        arguments = args.all,
        mnemonic = "Clippy",
        progress_message = "Clippy %{label}",
        toolchain = "@rules_rust//rust:toolchain_type",
    )

    return [OutputGroupInfo(clippy_checks = depset([clippy_out], transitive = transitive))]

gbl_clippy_aspect = aspect(
    fragments = ["cpp"],
    attr_aspects = ["*"],
    attrs = {
        "_config": attr.label(
            allow_single_file = True,
            default = Label("@rules_rust//rust/settings:clippy.toml"),
        ),
        "_error_format": attr.label(
            default = Label("@rules_rust//rust/settings:error_format"),
        ),
        "_extra_rustc_flag": attr.label(
            default = Label("@rules_rust//rust/settings:extra_rustc_flag"),
        ),
        "_per_crate_rustc_flag": attr.label(
            default = Label("@rules_rust//rust/settings:experimental_per_crate_rustc_flag"),
        ),
        "_process_wrapper": attr.label(
            default = Label("@rules_rust//util/process_wrapper"),
            executable = True,
            cfg = "exec",
        ),
    },
    toolchains = [
        str(Label("@rules_rust//rust:toolchain_type")),
        "@bazel_tools//tools/cpp:toolchain_type",
    ],
    implementation = _gbl_clippy_aspect_impl,
    doc = "Executes Clippy on first-party @gbl Rust targets and their @gbl dependencies.",
)
