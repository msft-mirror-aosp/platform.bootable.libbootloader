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

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def android_external_rust_crate_archive(name, rev, build_file):
    crate_url = "https://android.googlesource.com/platform/external/rust/crates/" + \
                "{}/+archive/{}.tar.gz".format(name, rev)

    http_archive(
        name = name,
        url = crate_url,
        build_file = build_file,
    )

def android_external_rust_crates_repositories():
    """ Fetch necessary dependencies from android/external/rust/crates

    Note: To pull in a new crate, Add a new
    android_external_rust_crate_archive() rule below to fetch the crate and
    provide a BUILD file for it. Android.bp is a good reference for writing
    BUILD file as for most part it has an one-to-one mapping to a Bazel rule.
    If the target crate has additional dependencies, repeat for all of them
    until all needed crates are fetched.
    """
    android_external_rust_crate_archive(
        name = "byteorder",
        rev = "69440f2e49ba4d846f091a57c1826a268d04656e",
        build_file = "@gbl//android_external_rust_crates:BUILD.byteorder.bazel",
    )

    android_external_rust_crate_archive(
        name = "cfg-if",
        rev = "3a308fd77901411c7ed5161012cebeb2cf8dab1a",
        build_file = "@gbl//android_external_rust_crates:BUILD.cfg-if.bazel",
    )

    android_external_rust_crate_archive(
        name = "crc32fast",
        rev = "7225fa79b53d6a75f4dadcd974ca82c666044953",
        build_file = "@gbl//android_external_rust_crates:BUILD.crc32fast.bazel",
    )

    android_external_rust_crate_archive(
        name = "hex",
        rev = "1ddb3bec93394eeb62ee4f4187e8579b489c3d07",
        build_file = "@gbl//android_external_rust_crates:BUILD.hex.bazel",
    )

    android_external_rust_crate_archive(
        name = "proc-macro2",
        rev = "5c471c4a5c3e80c810dadb19c5996e420426c3bc",
        build_file = "@gbl//android_external_rust_crates:BUILD.proc-marco2.bazel",
    )

    android_external_rust_crate_archive(
        name = "proc-macro2",
        rev = "5c471c4a5c3e80c810dadb19c5996e420426c3bc",
        build_file = "@gbl//android_external_rust_crates:BUILD.proc-marco2.bazel",
    )

    android_external_rust_crate_archive(
        name = "quote",
        rev = "9791b3d2d985ed9aae113fc5112e9a607c6c5741",
        build_file = "@gbl//android_external_rust_crates:BUILD.quote.bazel",
    )

    android_external_rust_crate_archive(
        name = "syn",
        rev = "035a68a559d23e0f60aa2c274a4b4c6f7247bc3b",
        build_file = "@gbl//android_external_rust_crates:BUILD.syn.bazel",
    )

    android_external_rust_crate_archive(
        name = "unicode-ident",
        rev = "2d1f5f891da7f9645c864e54fa08a0aabc7ab65f",
        build_file = "@gbl//android_external_rust_crates:BUILD.unicode-ident.bazel",
    )

    android_external_rust_crate_archive(
        name = "zerocopy",
        rev = "38d9439810f66c9f287a7f1caee1f6e3cf076d38",
        build_file = "@gbl//android_external_rust_crates:BUILD.zerocopy.bazel",
    )

    android_external_rust_crate_archive(
        name = "zerocopy-derive",
        rev = "e987328e0df1334022cb8ada4233e672a2e4ea0e",
        build_file = "@gbl//android_external_rust_crates:BUILD.zerocopy-derive.bazel",
    )

    android_external_rust_crate_archive(
        name = "bitflags",
        rev = "4cb5dac10a9ca8a0c9b78ea24f0f23e7972576e2",
        build_file = "@gbl//android_external_rust_crates:BUILD.bitflags.bazel",
    )
