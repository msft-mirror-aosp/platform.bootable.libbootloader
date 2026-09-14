# Copyright (C) 2025 The Android Open Source Project
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
Rules for creating local repositories by combining existing source directories
with custom BUILD files.
"""

load("@bazel_skylib//lib:paths.bzl", "paths")
load(":rust_crate_build_file.bzl", "rust_crate_build_file")

# Hack for missing original_name. original_name is available on 8.1 and above.
# https://github.com/bazelbuild/bazel/issues/24467
def _original_name(repo_ctx):
    if hasattr(repo_ctx, "original_name"):
        return repo_ctx.original_name
    idx = repo_ctx.attr.name.rfind("+")
    return repo_ctx.attr.name[idx + 1:]

def _symlink_tree(repo_ctx, source_root):
    """Symlinks each file in the given directory tree into the repo root.

    The purpose of this (as opposed to just symlinking the root directly) is to
    allow removing or modifying individual files in our generated repo without
    touching the source repo.

    Args:
        repo_ctx: `repository_rule` context for the repo we're creating.
        source_root: path to the source dir to replicate in this repo via links.
    """
    relative_dirs_to_read = ["."]

    # Bazel doesn't allow infinite loops, just use a high enough number to cover
    # any realistic tree. Each loop iteration handles one layer of a directory.
    for _ in range(10000):
        if not relative_dirs_to_read:
            break

        relative_dir = relative_dirs_to_read.pop()
        source_dir = source_root.get_child(relative_dir)

        for source_path in source_dir.readdir():
            relative_path = paths.join(relative_dir, source_path.basename)

            # Add directories to the stack to process on a future iteration,
            # create symlinks to files. `repo_ctx.symlink` will automatically
            # create any required parent directories.
            if source_path.is_dir:
                relative_dirs_to_read.append(relative_path)
            else:
                repo_ctx.symlink(source_path, relative_path)

    # Verify that our loop count was sufficient to process every directory.
    if relative_dirs_to_read:
        fail("{}: failed to symlink entire source tree", _original_name(repo_ctx))

def _gbl_new_local_repository_common_impl(repo_ctx, build_file, build_file_content):
    path = repo_ctx.workspace_root.get_child(repo_ctx.attr.path)
    if path.exists:
        # For simplicity, symlink the entire tree first and then explicitly
        # remove the symlinks the caller wants to exclude.
        _symlink_tree(repo_ctx, path)

        for path in getattr(repo_ctx.attr, "exclude_files", []):
            # Explicitly check that the deleted file existed; if it didn't then
            # the source repo might have significantly changed its structure and
            # the caller should re-examine the exclusion requests.
            if not repo_ctx.delete(path):
                fail("{}: excluded file {} does not exist", _original_name(repo_ctx), path)

    if hasattr(repo_ctx.attr, "exist_marker_path") and repo_ctx.attr.exist_marker_path != "":
        marker_build_file = """
load("@bazel_skylib//rules:common_settings.bzl", "bool_setting")

bool_setting(
    name = "exist",
    build_setting_default = {},
    visibility = ["//visibility:public"],
)

config_setting(
    name = "exists",
    flag_values = {{":exist": "True"}},
)

config_setting(
    name = "not_exists",
    flag_values = {{":exist": "False"}},
)
""".format(path.exists)
        repo_ctx.file("{}/BUILD".format(repo_ctx.attr.exist_marker_path), marker_build_file)

    # Symlink the provided build file or use the given build file content. Also
    # allow neither, in case the repo already contains a top-level BUILD file
    # that we can use as-is.
    if build_file and build_file_content:
        fail("{}: cannot specify both build_file and build_file_content", _original_name(repo_ctx))
    elif build_file:
        repo_ctx.file("BUILD", repo_ctx.read(repo_ctx.path(build_file)))
    elif build_file_content:
        repo_ctx.file("BUILD", build_file_content)

def _gbl_new_local_repository_impl(repo_ctx):
    _gbl_new_local_repository_common_impl(
        repo_ctx,
        repo_ctx.attr.build_file,
        repo_ctx.attr.build_file_content,
    )

gbl_new_local_repository = repository_rule(
    doc = """Assemble a new local repository with a custom top-level BUILD file

    Unlike "new_local_repository" from "@bazel_tools//tools/build_defs/repo:local.bzl",
    this supports excluding a set of files, which is commonly used when a repo already
    has Bazel build files but they don't work for our purposes and we need to define
    our own instead.
    """,
    implementation = _gbl_new_local_repository_impl,
    attrs = {
        "path": attr.string(
            mandatory = True,
            doc = "Path to the source repo, relative to the workspace root",
        ),
        "build_file": attr.label(doc = "Label of the build file to use"),
        "build_file_content": attr.string(doc = "Content of the build file to use"),
        "exclude_files": attr.string_list(doc = "List of files to exclude relative to root"),
        "exist_marker_path": attr.string(
            doc = "Optional path to create a marker BUILD file with `:exists` and `:not_exists` config settings indicating whether the source directory exists.",
            default = "",
        ),
    },
)

def _gbl_rust_crate_repository_impl(repo_ctx):
    _gbl_new_local_repository_common_impl(
        repo_ctx,
        None,
        rust_crate_build_file(
            _original_name(repo_ctx),
            rule = repo_ctx.attr.rule,
            crate_name = repo_ctx.attr.crate_name,
            deps = repo_ctx.attr.deps,
            proc_macro_deps = repo_ctx.attr.proc_macro_deps,
            features = repo_ctx.attr.crate_features,
            edition = repo_ctx.attr.edition,
            rustc_flags = repo_ctx.attr.rustc_flags,
            rustc_env = repo_ctx.attr.rustc_env,
            compile_data = repo_ctx.attr.compile_data,
            license_bsd_type = repo_ctx.attr.license_bsd_type,
            aliases = repo_ctx.attr.aliases,
        ),
    )

gbl_rust_crate_repository = repository_rule(
    doc = """Like gbl_new_local_repository but for crates.""",
    implementation = _gbl_rust_crate_repository_impl,
    attrs = {
        "path": attr.string(
            mandatory = True,
            doc = "Path to the source repo, relative to the workspace root",
        ),
        "rule": attr.string(
            doc = "Bazel Rust rule to build.",
            default = "rust_library",
        ),
        "crate_name": attr.string(doc = "name of the rust_library crate, same as name by default."),
        "deps": attr.string_list(doc = "The `deps` field."),
        "proc_macro_deps": attr.string_list(doc = "The `proc_macro_deps` field."),
        "edition": attr.string(doc = "Rust edition.", default = "2021"),
        "rustc_flags": attr.string_list(doc = "The `rustc_flags` field."),
        "rustc_env": attr.string_dict(doc = "The `rustc_env` field."),
        "compile_data": attr.string_list(doc = "The `compile_data` field."),
        "license_bsd_type": attr.string_list(doc = "The `bsd_type` field for generate_license."),
        "aliases": attr.string_dict(doc = "The `aliases` field."),
        "crate_features": attr.string_list(doc = "The `crate_features` field."),
    },
)
