#!/usr/bin/env python3
#
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
"""Generate test files for sparse image flash test"""

import os
import pathlib
import subprocess

SCRIPT_DIR = pathlib.Path(os.path.dirname(os.path.realpath(__file__)))

# Writes bytes to a file at a given offset.
def write_file(file, offset, data):
    file.seek(offset, 0)
    file.write(data)


if __name__ == '__main__':
    sz_kb = 1024
    out_file_raw = SCRIPT_DIR / "sparse_test_raw.bin"
    with open(out_file_raw, "wb") as f:
        # 4k filled with 0x78563412
        write_file(f, 0, b"\x12\x34\x56\x78" * 1024)
        # 8k file hole (will become dont-care with the "-s" option)
        # 12k raw data
        write_file(f, 12 * sz_kb, os.urandom(12 * sz_kb))
        # 8k filled with 0x78563412
        write_file(f, 24 * sz_kb, b"\x12\x34\x56\x78" * 1024 * 2)
        # 12k raw data
        write_file(f, 32 * sz_kb, os.urandom(12 * sz_kb))
        # 4k filled with 0x78563412
        write_file(f, 44 * sz_kb, b"\x12\x34\x56\x78" * 1024)
        # 8k filled with 0xEFCDAB90
        write_file(f, 48 * sz_kb, b"\x90\xab\xcd\xef" * 1024 * 2)

    subprocess.run(
        ["img2simg", "-s", out_file_raw, SCRIPT_DIR / "sparse_test.bin"])
    subprocess.run([
        "img2simg",
        "-s",
        out_file_raw,
        SCRIPT_DIR / "sparse_test_blk1024.bin",
        "1024",
    ])
