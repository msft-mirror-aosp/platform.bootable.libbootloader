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

load("@bazel_skylib//lib:selects.bzl", "selects")
load("@gbl//toolchain:build_and_run_tests.bzl", "build_and_run_tests")

test_suite(
    name = "tests",
    tests = [
        ":build_and_run_tests",
        ":build_and_run_qemu_tests",
        # Doc tests does not work for `build_and_run_tests` because it accesses
        # `../rules_rust/util/process_wrapper` and its path can't be correctly provided as test
        # data.
        "@gbl//libefi_types:libefi_types_doc_test",
        "@gbl//libstorage:libstorage_doc_test",
        "@gbl//signtool:gblsigntool_test",
    ],
)

# Note: this rule does not work with `test_suite` targets, we must add each test
# individually.
build_and_run_tests(
    name = "build_and_run_tests",
    # We need to re-specify the runtime data needed by tests.
    data = ["@gbl//libgbl/testdata"],
    tests = [
        "@gbl//:readme_test",
        "@gbl//efi:test",
        "@gbl//efi:test_dev",
        "@gbl//libabr:libabr_test",
        "@gbl//libasync:cyclic_executor_test",
        "@gbl//libasync:libasync_test",
        "@gbl//libboot:libboot_test",
        "@gbl//libbootimg:libbootimg_test",
        "@gbl//libbootparams:test",
        "@gbl//libboringssl:crypto_test",
        "@gbl//libboringssl:sysdeps_test",
        "@gbl//libbuild_number:libbuild_number_test",
        "@gbl//libc:libc_c_test",
        "@gbl//libc:libc_test",
        "@gbl//libdttable:libdttable_test",
        "@gbl//libefi:efi_avb_test",
        "@gbl//libefi:libefi_test",
        "@gbl//libefi:libefi_test_dev",
        "@gbl//libefi:mocks_test",
        "@gbl//libefi_types:gbl_protocols_license_test",
        "@gbl//libefi_types:libefi_types_test",
        "@gbl//libelf:relocation_test",
        "@gbl//liberror:liberror_test",
        "@gbl//libfastboot:libfastboot_test",
        "@gbl//libfdt:libfdt_test",
        "@gbl//libfit:libfit_test",
        "@gbl//libgbl:libgbl_test",
        "@gbl//libgbl:libgbl_test_dev",
        "@gbl//libmisc:libmisc_test",
        "@gbl//libopendice:libopendice_test",
        "@gbl//libpvmfwconfig:libpvmfwconfig_test",
        "@gbl//libsafemath:libsafemath_test",
        "@gbl//libstorage:libstorage_test",
        "@gbl//libutils:test",
        "@gbl//libutils:testutils_test",
    ],
)

selects.config_setting_group(
    name = "qemu_test_dependencies_exist",
    match_all = [
        "@vmm//repo_exists:exists",
        "@mkbootimg//repo_exists:exists",
    ],
)

build_and_run_tests(
    name = "build_and_run_qemu_tests",
    # The vmm repo may not be added in all branches. Only enable the test when
    # it exists.
    # Put as data dependency so that this becomes a build-time test. The output produced
    # is the log file.
    # Put as a different test target so that it can be parallelized with other tests.
    data = select(
        {
            ":qemu_test_dependencies_exist": [
                "@gbl//tests/qemu:qemu_boot_memory_test",
                "@gbl//tests/qemu:qemu_dice_boot_test_ed25519",
                "@gbl//tests/qemu:qemu_dice_boot_test_mldsa65",
                "@gbl//tests/qemu:qemu_dice_boot_test_mldsa87",
                "@gbl//tests/qemu:qemu_dice_boot_test_p256",
                "@gbl//tests/qemu:qemu_dice_boot_test_p384",
                "@gbl//tests/qemu:qemu_fastboot_misc_test",
                "@gbl//tests/qemu:qemu_lldb_debugging_test",
                "@gbl//tests/qemu:qemu_trace_test",
            ],
            "//conditions:default": [],
        },
    ),
    tests = [],
)
