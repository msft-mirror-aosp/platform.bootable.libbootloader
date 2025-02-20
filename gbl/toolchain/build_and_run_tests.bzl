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
This file defines `build_and_run_tests` rule
"""

load("@rules_shell//shell:sh_test.bzl", "sh_test")

def _build_and_run_impl(ctx):
    # Executable file from the attribute.
    executable = ctx.executable.executable

    # Output log file.
    logfile = ctx.actions.declare_file("%s.txt" % ctx.attr.name)

    ctx.actions.run_shell(
        inputs = [executable] + ctx.files.data,
        outputs = [logfile],
        progress_message = "Running test %s" % executable.short_path,
        command = """\
        BIN="%s" && \
        OUT="%s" && \
        ($BIN > $OUT || \
        if [ $? == 0 ]; then
            true
        else
            echo "\n%s failed." && cat $OUT && false
        fi)
""" % (executable.path, logfile.path, executable.short_path),
    )

    return [DefaultInfo(files = depset([logfile]))]

build_and_run = rule(
    implementation = _build_and_run_impl,
    attrs = {
        "executable": attr.label(
            executable = True,
            cfg = "exec",
            allow_files = True,
            mandatory = True,
        ),
        "data": attr.label_list(
            allow_files = True,
            allow_empty = True,
        ),
    },
)

# TODO(b/382503065): This is a temporary workaround due to presubmit infra not blocking on test
# failures and only on build failures. Removed once the issue is solved.
def build_and_run_tests(name, tests, data):
    """Create an `sh_test` target that run a set of unittests during build time.

    Args:
        name (String): name of the rust_library target.
        tests (List of strings): List of test target.
        data (List of strings): Runtime data needed by the tests.
    """

    all_tests = []
    for idx, test in enumerate(tests):
        subtest_name = "{}_subtest_{}".format(name, idx)
        build_and_run(
            name = subtest_name,
            testonly = True,
            executable = test,
            data = data,
        )

        all_tests.append(":{}".format(subtest_name))

    sh_test(
        name = name,
        srcs = ["@gbl//tests:noop.sh"],
        data = all_tests,
    )
