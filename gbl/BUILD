# Copyright (C) 2024 The Android Open Source Project
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

load(":readme.bzl", "readme_test")

readme_test(
    name = "readme_test",
    readme = "README.md",
    # Note: can't read files in subpackages, not sure how to add a dependency on all,
    # globbed, subpackages and all the rust_lib targets they contain.
    deps = [
        "@gbl//efi:main",
        "@gbl//libavb:sysdeps",
        "@gbl//libboot",
        "@gbl//libbootconfig",
        "@gbl//libbootimg",
        "@gbl//libc",
        "@gbl//libefi",
        "@gbl//libfastboot",
        "@gbl//libfdt",
        "@gbl//libgbl",
        "@gbl//libmisc",
        "@gbl//libsafemath",
        "@gbl//libstorage",
    ],
)
