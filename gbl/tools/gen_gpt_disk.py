#!/usr/bin/env python3
#
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
"""Generate a GPT disk

Example:

The following command creates a 16mb disk file gpt.bin with two partitions:

  1) "boot_a" of size 4096KB, with data initialized from "file_a",
  2) "boot_b" of size 8192KB, with data initialized to zeroes.

    gen_gpt_disk.py ./gpt.bin 16M
        --partition "boot_a,4096K,<path to file_a>" \
        --partition "boot_b,8192K,"

All GUIDs will be non-deterministic for reproducibility.
"""

import argparse
import os
import pathlib
import shutil
import sys
import subprocess
import tempfile

GPT_BLOCK_SIZE = 512

# Some GPT libraries may expect a valid GUID here, these are just pre-generated
# valid GUIDs for reproducibility.
DISK_GUID = "b116114b-b6ae-4186-8231-b35104cb4c9e"
PARTITION_GUIDS = [
    "36bc51fd-c3d6-4109-a2ac-35bddd757e2a",
    "42aaac2e-37e3-43ba-9930-42dfa96e6334",
    "bdadfeca-879c-43e9-8f0d-8ef7da29b5e7",
    "8d5b90b2-0d65-476b-8691-94f74fcac271",
    "dafe682f-3f2b-4472-a1b8-a0f217701909",
    "7097fd78-f559-461e-bb9b-db176a8169d8",
    "c03dd176-117b-4e65-8205-37ebec007c1a",
    "6d9159db-9b9e-4906-8fa4-31f5ffaef50e",
    "4cdfda9f-23aa-4b27-9fea-24bb08238135",
    "2a0a3df9-e8ef-4627-b4ce-ef1e847924f4",
    "3c9b64f9-c659-4e5d-9d25-72028c46e6b8",
    "95f142f9-d1f3-41ad-96dc-b969ee8242a1",
    "5181811b-e836-4e66-bfe2-91aa86da515f",
    "f2dbad77-38ac-43de-b4c7-2f7432d2339e",
    "fc172d2c-f735-49a5-8be0-a475d0fc5be9",
    "5ad48195-8e26-4496-a7e2-669028db2dce",
    "f49a6965-8168-4c0c-8102-7b64a8176c25",
    "be495262-5d9b-4fcb-9240-d9e84b195abe",
    "c5ab3a8d-f898-420f-9039-a7445760fb0f",
    "bc79912b-44bf-4ed8-8320-796ba47714d1",
]


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("out", help="output file")
    parser.add_argument(
        "disk_size", type=str, help="disk size of the image. i.e. 64k, 1M etc"
    )
    parser.add_argument(
        "--partition",
        type=str,
        action="append",
        help="specifies a partition. Format should be"
        "--partition=<part name>,<size>,<file name>",
    )
    return parser.parse_args()


def parse_size_str(size_str: str) -> int:
    """Parse size string into integer, taking into account unit.

    Example:
        2M, 2m -> 2*1024*1024
        2K, 2k -> 2*1024
        512 -> 512
    """
    size_str = size_str.lower()
    if size_str.endswith("m"):
        return int(size_str[:-1]) * 1024 * 1024
    if size_str.endswith("k"):
        return int(size_str[:-1]) * 1024
    return int(size_str)


def _append(src_file: str, offset: int, size: int, dst_file: str):
    """Append a portion of a file to the end of another file

    Args:
        src_file: path to the source file
        offset: offset in the source file
        size: number of bytes to append
        dst_file: destination file

    Returns:
        number of bytes actually copied.
    """
    with open(src_file, "rb") as src_f:
        src_f.seek(offset, 0)
        data = src_f.read(size)
        if len(data) != size:
            raise ValueError(f"Want {size} bytes from {src_file}, but got {len(data)}.")
        with open(dst_file, "ab") as dst_f:
            dst_f.write(data)
    return size


def main() -> int:
    args = parse_args()
    with tempfile.TemporaryDirectory() as temp_dir:
        temp_disk = pathlib.Path(temp_dir) / "temp_disk"

        disk_size = parse_size_str(args.disk_size)
        temp_disk.write_bytes(disk_size * b"\x00")

        part_start = 34 * GPT_BLOCK_SIZE  # MBR + GPT header + entries
        partition_info = []
        sgdisk_command = [
            "sgdisk",
            str(temp_disk),
            "--clear",
            "--set-alignment",
            "1",
            "--disk-guid",
            DISK_GUID,
        ]

        for i, part in enumerate(args.partition, start=1):
            name, size, file = part.split(",")
            if not size:
                raise ValueError("Must provide a size")
            size = parse_size_str(size)

            sgdisk_command += [
                "--new",
                f"{i}:{part_start // GPT_BLOCK_SIZE}:{(part_start + size) // GPT_BLOCK_SIZE - 1}",
                "--partition-guid",
                f"{i}:{PARTITION_GUIDS[i]}",
                "--change-name",
                f"{i}:{name}",
            ]

            partition_info.append((name, part_start, size, file))
            part_start += size

        res = subprocess.run(sgdisk_command, check=True, text=True)

        # Create the final disk with partition content
        dest_file = pathlib.Path(args.out)
        dest_file.write_bytes(0 * b"\x00")
        append_offset = 0
        for name, start, size, file in partition_info:
            end = start + size
            # Fill gap
            append_offset += _append(
                str(temp_disk), append_offset, start - append_offset, args.out
            )

            # Copy over file
            if file:
                file_size = os.path.getsize(file)
                if file_size > size:
                    raise ValueError(f"{file} too large for {name}")
                append_offset += _append(file, 0, file_size, args.out)

            # If partition size greater than file size, copy the remaining
            # partition content from `temp_disk` (zeroes)
            append_offset += _append(
                str(temp_disk), append_offset, end - append_offset, args.out
            )

        # Copy the remaining disk from `temp_disk` (zeroes + back up header/entries)
        append_offset += _append(
            str(temp_disk), append_offset, disk_size - append_offset, args.out
        )

    return 0


if __name__ == "__main__":
    sys.exit(main())
