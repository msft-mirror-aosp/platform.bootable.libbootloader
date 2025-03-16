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

load("@gbl//toolchain:build_and_run_tests.bzl", "build_and_run_tests")

test_suite(
    name = "tests",
    tests = [
        ":build_and_run_tests",
        # Doc tests does not work for `build_and_run_tests` because it accesses
        # `../rules_rust/util/process_wrapper` and its path can't be correctly provided as test
        # data.
        "@gbl//libstorage:libstorage_doc_test",
    ],
)

build_and_run_tests(
    name = "build_and_run_tests",
    # We need to re-specify the runtime data needed by tests.
    data = ["@gbl//libgbl/testdata"],
    tests = [
        "@gbl//:readme_test",
        "@gbl//efi:test",
        "@gbl//libabr:libabr_test",
        "@gbl//libasync:cyclic_executor_test",
        "@gbl//libasync:libasync_test",
        "@gbl//libbootimg:libbootimg_test",
        "@gbl//libbootparams:test",
        "@gbl//libc:libc_test",
        "@gbl//libdttable:libdttable_test",
        "@gbl//libefi:libefi_test",
        "@gbl//libefi:mocks_test",
        "@gbl//libefi_types:libefi_types_test",
        "@gbl//libelf:relocation_test",
        "@gbl//liberror:liberror_test",
        "@gbl//libfastboot:libfastboot_test",
        "@gbl//libfdt:libfdt_test",
        "@gbl//libgbl:libgbl_test",
        "@gbl//libmisc:libmisc_test",
        "@gbl//libsafemath:libsafemath_test",
        "@gbl//libstorage:libstorage_test",
        "@gbl//libutils:test",
        "@zbi//:zbi_test",
    ],
)
