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

# The rule builds the collection of sysroot libraries and assembles them into a single build
# output directory.
genrule(
    name = "rust_sysroot",
    srcs = [
        "@rust_prebuilts//:libcore",
        "@rust_prebuilts//:libcompiler_builtins",
        "@rust_prebuilts//:liballoc",
    ],
    outs = [
        "libcore.rlib",
        "libcompiler_builtins.rlib",
        "liballoc.rlib",
    ],
    # Copy each src[i] to outs[i]
    cmd = """
        IFS=" " read -a srcs <<< "$(SRCS)" && \
        IFS=" " read -a outs <<< "$(OUTS)" && \
        for index in $${!srcs[@]}; do cp $${srcs[$$index]} $${outs[$$index]}; done
""",
)
