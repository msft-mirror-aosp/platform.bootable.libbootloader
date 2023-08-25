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

# See
# http://bazelbuild.github.io/rules_rust/crate_universe.html
# for details on how Bazel handle Rust crate dependencies.

load("@rules_rust//crate_universe:defs.bzl", "crates_repository")

def _gbl_fetch_remote_rust_crate_impl(repo_ctx):
    """Implementation for _gbl_fetch_remote_rust_crate

    The rule downloads the crate archive from the given url and sets up
    necessary BUILD, Cargo.lock file.
    """

    # Download and extract the crate archive.
    repo_ctx.download_and_extract(
        output = ".",
        url = repo_ctx.attr.urls,
    )

    # Create a BUILD file with a rust_library() target that other
    # targets can depend on.
    repo_ctx.file("BUILD", """
load("@{}//:defs.bzl", "aliases", "all_crate_deps")
load("@rules_rust//rust:defs.bzl", "rust_library")

package(
    default_visibility = ["//visibility:public"],
)

rust_library(
    name = "{}",
    srcs = glob(["**/*.rs"]),
    aliases = aliases(),
    edition = "2021",
    proc_macro_deps = all_crate_deps(proc_macro = True),
    deps = all_crate_deps(normal = True),
)

""".format(repo_ctx.attr.crate_index, repo_ctx.attr.name))

    # If the crate doesn't come with a Cargo.lock, create one.
    # This is needed by crate_repository() for resolving the dependencies
    # this crate itself has.
    #
    # For newly created Cargo.lock, it'll be generated during build with
    # CARGO_BAZEL_REPIN=1
    cargo_lock_file = repo_ctx.path("Cargo.lock")
    if not cargo_lock_file.exists:
        repo_ctx.file("Cargo.lock", "")

_gbl_fetch_remote_rust_crate = repository_rule(
    implementation = _gbl_fetch_remote_rust_crate_impl,
    local = True,
    attrs = {
        "urls": attr.string_list(),
        "crate_index": attr.string(),
    },
)

def gbl_remote_rust_crate(
        name,
        urls):
    """Download a Rust crate from a remote source and generate bazel dependencies.

    Args:
        name (String): Name of the target.
        urls: (String/List of String): (List of) url(s) to the crate archive.
    """

    # The name for crates_repository(). It's bascially another repo Bazel assemble
    # for hosting the dpendencies and generated BUILD files for the target crate.
    crate_index = "{}_crate_index".format(name)

    # Downloads the crate and setup necessary files.
    _gbl_fetch_remote_rust_crate(
        name = name,
        urls = urls,
        crate_index = crate_index,
    )

    # crate_repository() analyzes the given Cargo.toml file (from the crate),
    # transitively downloads other needed dependencies and generates BUILD
    # files for all of them.
    crates_repository(
        name = crate_index,
        cargo_lockfile = "@{}//:Cargo.lock".format(name),
        generator = "@cargo_bazel_bootstrap//:cargo-bazel",
        manifests = ["@{}//:Cargo.toml".format(name)],
    )
