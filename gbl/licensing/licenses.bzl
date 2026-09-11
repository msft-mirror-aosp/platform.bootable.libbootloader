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

"""License utilities for GBL.

Android packages typically provide licensing information to the build system
via an Android.bp build file, but since we use Bazel instead we need a different
way to specify license information.

Importantly, we should avoid hardcoding per-package license information here,
as hardcoded licenses could get out-of-sync if a package uprev changes the
license information. These utilities instead examine the package files to
determine the correct licensing at build time.
"""

load(
    "@rules_license//rules:gather_licenses_info.bzl",
    "gather_licenses_info",
    "write_licenses_info",
)
load("@rules_license//rules:license.bzl", "license")
load("@rules_license//rules:providers.bzl", "LicenseInfo")

# Android 3P packages indicate licensing via empty marker files whose names
# reflect the license used. This map converts from the Android marker file to
# the corresponding Bazel license rule.
#
# This also serves as a list of all `license_kinds` that we accept. Make sure
# that any additions to this map meet our licensing guidelines.
LICENSE_MAP = {
    "MODULE_LICENSE_APACHE2": "@rules_license//licenses/spdx:Apache-2.0",
    "MODULE_LICENSE_BSD_2_CLAUSE": "@rules_license//licenses/spdx:BSD-2-Clause-FreeBSD",
    "MODULE_LICENSE_BSD_2_CLAUSE_FREEBSD": "@rules_license//licenses/spdx:BSD-2-Clause",
    "MODULE_LICENSE_BSD_3_CLAUSE": "@rules_license//licenses/spdx:BSD-3-Clause",
    "MODULE_LICENSE_BSD_LIKE": "@gbl//licensing:BSD-like",
    "MODULE_LICENSE_MIT": "@rules_license//licenses/spdx:MIT",
    "MODULE_LICENSE_MPL": "@rules_license//licenses/spdx:MPL-2.0",
    "MODULE_LICENSE_PERMISSIVE": "@rules_license//licenses/generic:permissive",
    "MODULE_LICENSE_ZERO_BSD": "@rules_license//licenses/spdx:0BSD",
    "MODULE_LICENSE_ZLIB": "@rules_license//licenses/spdx:Zlib",
}

# The known acceptable license kinds. Any target using a license kind other than
# this will cause the build to fail.
ACCEPTED_LICENSE_KINDS = LICENSE_MAP.values()

def generate_license(
        package_name,
        name = "license",
        license_text = "LICENSE",
        bsd_type = None):
    """Generates a license() rule by detecting MODULE_LICENSE_* files.

    Args:
        package_name (String): name of the package. In the final license output
            file, licenses will be reported by package rather than for each
            individual build target.
        name (String): name of the license rule to generate.
        license_text (String): name of the file containing the license text.
        bsd_type (optional String or List[String]): if the repo uses the generic
            MODULE_LICENSE_BSD marker, specify the exact Bazel license kind.
            Can either be a single string or a list of strings.
    """

    # Locate the license marker files and convert them to Bazel licenses.
    license_kinds = []
    marker_files = native.glob(["MODULE_LICENSE_*"])
    for marker in marker_files:
        # Ignore any unmapped license type - some packages may be
        # dual-licensed, in which case we elect to use the supported license.
        if marker in LICENSE_MAP:
            license_kinds.append(LICENSE_MAP[marker])
        elif marker == "MODULE_LICENSE_BSD":
            if bsd_type:
                # Some projects license under multiple different BSD licenses,
                # in which case this will be a list.
                if type(bsd_type) == "list":
                    license_kinds += bsd_type
                else:
                    license_kinds.append(bsd_type)

                # Mark the bsd_type as None to indicate it's been used.
                bsd_type = None
            else:
                fail("{}: Must specify `bsd_type` for MODULE_LICENSE_BSD".format(native.repo_name()))

    if not license_kinds:
        fail("{}: No known license kind found in markers: {}".format(native.repo_name(), marker_files))

    # If bsd_type is still valid here, it means the caller passed it but the
    # MODULE_LICENSE_BSD marker file doesn't exist - something may have changed
    # in the licensing, error out here to alert us to re-examine the call site.
    if bsd_type:
        fail("{}: `bsd_type` was provided but no MODULE_LICENSE_BSD file exists: {}".format(native.repo_name()))

    if not native.glob([license_text]):
        fail("{}: License file '{}' not found".format(native.repo_name(), license_text))

    license(
        name = name,
        license_kinds = license_kinds,
        license_text = license_text,
        visibility = ["//visibility:public"],
        package_name = package_name,
    )

LicenseCheckInfo = provider(
    "Accumulates the names of all dependencies with missing license information",
    fields = {
        "missing_licenses": "Depset of strings representing targets missing licenses",
    },
)

def _skip_license_check(target):
    """Returns True if this target can skip the licensing check.

    Some Bazel internal dependencies don't expose licenses in a way that we can
    use, but if they already use a notice-class license that we support we can
    skip them in the license check.

    This does make some assumptions about Bazel internals that could break in
    future versions, if this becomes common we might need to investigate
    alternatives.
    """
    label = target.label
    for repo_package_name in [
        # bazel is Apache 2, same as GBL.
        ("bazel_tools", "tools/cpp", "empty_lib"),
        ("bazel_tools", "tools/cpp", "link_extra_lib"),
        ("bazel_tools", "tools/cpp", "malloc"),
        # rules_cc+ is Apache 2, same as GBL.
        ("rules_cc+", "", "empty_lib"),
        ("rules_cc+", "", "link_extra_lib"),
        # rules_rust+ is Apache 2, same as GBL.
        ("rules_rust+", "ffi/rs", "empty_allocator_libraries"),
    ]:
        if (label.repo_name, label.package, label.name) == repo_package_name:
            return True
    return False

def check_license_kinds(info):
    """Checks that all license_kinds in the provided info are OK to use.

    Fails build if any invalid license kinds are found.

    Args:
        info (LicenseInfo): the license info to check.
    """
    if not info.license_kinds:
        fail("License '{}' doesn't provide any license_kinds".format(info.label))

    for license_kind_info in info.license_kinds:
        # Label canonicalization adds internal '+' characters to repos here,
        # strip them out so we can compare to generic labels.
        license_kind = license_kind_info.label.replace("+", "")
        if license_kind not in ACCEPTED_LICENSE_KINDS:
            fail("'{}' uses unsupported license kind '{}'".format(info.label, license_kind))

def _check_licenses_aspect_impl(target, ctx):
    missing = []
    transitive = []

    # If it's not a rule (e.g. source file), we skip checking it directly.
    #
    # Also skip a few targets we can't easily integrate into this check but we
    # know we meet licensing requirements for.
    if hasattr(ctx, "rule") and not _skip_license_check(target):
        # Skip filegroups as they are just groupings of files and don't need
        # licenses themselves.
        if ctx.rule.kind != "filegroup":
            # Accept either a target license or a package default license.
            applicable_licenses = getattr(ctx.rule.attr, "applicable_licenses", [])
            package_metadata = getattr(ctx.rule.attr, "package_metadata", [])

            has_license = False
            for dep in applicable_licenses + package_metadata:
                if LicenseInfo in dep:
                    # Check that all licenses are acceptable kinds. This
                    # function fails directly if it finds an invalid kind.
                    check_license_kinds(dep[LicenseInfo])
                    has_license = True
                    break

            if not has_license:
                missing.append(str(target.label))

        # Collect transitive info from all dependencies.
        for attr_name in dir(ctx.rule.attr):
            # Skip private attributes.
            if attr_name.startswith("_"):
                continue

            attr = getattr(ctx.rule.attr, attr_name)

            # Attr can be a list (e.g. `deps`) or a single label (`target`).
            if type(attr) == "list":
                for item in attr:
                    if type(item) == "Target" and LicenseCheckInfo in item:
                        transitive.append(item[LicenseCheckInfo].missing_licenses)
            elif type(attr) == "Target" and LicenseCheckInfo in attr:
                transitive.append(attr[LicenseCheckInfo].missing_licenses)

    return [LicenseCheckInfo(
        missing_licenses = depset(missing, transitive = transitive),
    )]

check_licenses_aspect = aspect(
    implementation = _check_licenses_aspect_impl,
    attr_aspects = ["*"],
    doc = "Aspect that collects targets with missing licenses.",
)

def _report_missing_licenses(deps):
    """Helper to check for and report missing licenses in dependencies."""
    all_missing_depsets = []
    for dep in deps:
        if LicenseCheckInfo in dep:
            all_missing_depsets.append(dep[LicenseCheckInfo].missing_licenses)

    all_missing = depset(transitive = all_missing_depsets).to_list()

    if all_missing:
        # Sort for deterministic output
        sorted_missing = sorted(all_missing)
        fail("The following targets are missing applicable_licenses:\n" + "\n".join(["  " + str(m) for m in sorted_missing]))

def _check_licenses_rule_impl(ctx):
    _report_missing_licenses(ctx.attr.deps)
    return [DefaultInfo()]

check_licenses = rule(
    implementation = _check_licenses_rule_impl,
    attrs = {
        "deps": attr.label_list(aspects = [check_licenses_aspect]),
    },
)

def _merged_license_impl(ctx):
    """Rule implementation to merge licenses into a single output file."""

    # Make sure every dependency has a known and valid license attached to it.
    # This has to be a custom Bazel function because `write_licenses_info()`
    # will just skip deps with missing licenses.
    _report_missing_licenses(ctx.attr.deps)

    # Intermediate JSON file to track license metadata.
    json_map = ctx.actions.declare_file(ctx.label.name + ".json")

    # `write_licenses_info()` does most of the heavy lifting here. We just
    # have to run the `gather_licenses_info` aspect on the deps (which we do
    # in the `merged_license` rule) and this function will:
    #   1. write a JSON containing all the license usage metadata
    #   2. return the set of license files
    license_files = write_licenses_info(ctx, ctx.attr.deps, json_map)

    # Run our custom formatter to generate our desired output format.
    ctx.actions.run(
        executable = ctx.executable._formatter,
        # The JSON map gives us metadata so we can map packages to their
        # license, and the license files give us the actual license texts.
        inputs = [json_map] + license_files,
        outputs = [ctx.outputs.out],
        arguments = [json_map.path, ctx.outputs.out.path],
        mnemonic = "MergeLicenses",
    )

    return [DefaultInfo(files = depset([ctx.outputs.out]))]

merged_license = rule(
    implementation = _merged_license_impl,
    doc = "Collects all licenses from dependencies and merges them into a single text file.",
    attrs = {
        "deps": attr.label_list(
            doc = "List of targets to collect licenses for.",
            aspects = [gather_licenses_info, check_licenses_aspect],
        ),
        "out": attr.output(
            doc = "The output filename.",
            mandatory = True,
        ),
        "_formatter": attr.label(
            default = Label("@gbl//licensing:license_formatter"),
            executable = True,
            cfg = "exec",
        ),
    },
)
