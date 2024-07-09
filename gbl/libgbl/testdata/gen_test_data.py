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
"""Generate test data files for libgbl tests"""

import os
import pathlib
import random
import shutil
import subprocess
import tempfile
from typing import List

SCRIPT_DIR = pathlib.Path(os.path.dirname(os.path.realpath(__file__)))
GPT_TOOL = pathlib.Path(SCRIPT_DIR.parents[1]) / "tools" / "gen_gpt_disk.py"
AVB_DIR = pathlib.Path(SCRIPT_DIR.parents[4]) / "external" / "avb"
AVB_TOOL = AVB_DIR / "avbtool.py"
AVB_TEST_DATA_DIR = AVB_DIR / "test" / "data"
SZ_KB = 1024

# RNG seed values. Keep the same seed value for a given file to ensure
# reproducibility as much as possible; this will prevent adding a bunch of
# unnecessary test binaries to the git history.
RNG_SEED_SPARSE_TEST_RAW = 1
RNG_SEED_ZIRCON = {"a": 2, "b": 3, "r": 4}


# A helper for writing bytes to a file at a given offset.
def write_file(file, offset, data):
    file.seek(offset, 0)
    file.write(data)


# Generates sparse image for flashing test
def gen_sparse_test_file():
    out_file_raw = SCRIPT_DIR / "sparse_test_raw.bin"
    random.seed(RNG_SEED_SPARSE_TEST_RAW)
    with open(out_file_raw, "wb") as f:
        # 4k filled with 0x78563412
        write_file(f, 0, b"\x12\x34\x56\x78" * 1024)
        # 8k file hole (will become dont-care with the "-s" option)
        # 12k raw data
        write_file(f, 12 * SZ_KB, random.randbytes(12 * SZ_KB))
        # 8k filled with 0x78563412
        write_file(f, 24 * SZ_KB, b"\x12\x34\x56\x78" * 1024 * 2)
        # 12k raw data
        write_file(f, 32 * SZ_KB, random.randbytes(12 * SZ_KB))
        # 4k filled with 0x78563412
        write_file(f, 44 * SZ_KB, b"\x12\x34\x56\x78" * 1024)
        # 8k filled with 0xEFCDAB90
        write_file(f, 48 * SZ_KB, b"\x90\xab\xcd\xef" * 1024 * 2)

    # For now this requires that img2simg exists on $PATH.
    # It can be built from an Android checkout via `m img2simg`; the resulting
    # binary will be at out/host/linux-x86/bin/img2simg.
    subprocess.run(["img2simg", "-s", out_file_raw, SCRIPT_DIR / "sparse_test.bin"])
    subprocess.run(
        [
            "img2simg",
            "-s",
            out_file_raw,
            SCRIPT_DIR / "sparse_test_blk1024.bin",
            "1024",
        ]
    )


# Generates GPT disk, kernel data for Zircon tests
def gen_zircon_gpt():
    gen_gpt_args = []
    for suffix in ["a", "b", "r"]:
        random.seed(RNG_SEED_ZIRCON[suffix])
        zircon = random.randbytes(16 * SZ_KB)
        out_file = SCRIPT_DIR / f"zircon_{suffix}.bin"
        out_file.write_bytes(zircon)
        gen_gpt_args.append(f"--partition=zircon_{suffix},16K,{str(out_file)}")

    subprocess.run(
        [GPT_TOOL, SCRIPT_DIR / "zircon_gpt.bin", "128K"] + gen_gpt_args, check=True
    )


# Generates test data for A/B slot Manager writeback test
def gen_writeback_test_bin():
    subprocess.run(
        [
            GPT_TOOL,
            SCRIPT_DIR / "writeback_test_disk.bin",
            "64K",
            "--partition=test_partition,4k,/dev/zero",
        ],
        check=True,
    )


def sha256_hash(path: pathlib.Path) -> bytes:
    """Returns the SHA256 hash of the given file."""
    hash_hex = (
        subprocess.run(
            ["sha256sum", path],
            check=True,
            capture_output=True,
            text=True,
        )
        .stdout.split()[0]  # output is "<hash> <filename>".
        .strip()
    )
    return bytes.fromhex(hash_hex)


def gen_vbmeta():
    """Creates the vbmeta keys and signs some images."""
    # Use the test vbmeta keys from libavb.
    for name in [
        "testkey_rsa4096.pem",
        "testkey_rsa4096_pub.pem",
        "testkey_cert_psk.pem",
        "cert_metadata.bin",
        "cert_permanent_attributes.bin",
    ]:
        shutil.copyfile(AVB_TEST_DATA_DIR / name, SCRIPT_DIR / name)

    # We need the permanent attribute SHA256 hash for libavb_cert callbacks.
    hash_bytes = sha256_hash(SCRIPT_DIR / "cert_permanent_attributes.bin")
    (SCRIPT_DIR / "cert_permanent_attributes.hash").write_bytes(hash_bytes)

    # Also create a corrupted version of the permanent attributes to test failure.
    # This is a little bit of a pain but we don't have an easy way to do a SHA256 in Rust
    # at the moment so we can't generate it on the fly.
    bad_attrs = bytearray((SCRIPT_DIR / "cert_permanent_attributes.bin").read_bytes())
    bad_attrs[4] ^= 0x01  # Bytes 0-3 = version, byte 4 starts the public key.
    (SCRIPT_DIR / "cert_permanent_attributes.bad.bin").write_bytes(bad_attrs)
    hash_bytes = sha256_hash(SCRIPT_DIR / "cert_permanent_attributes.bad.bin")
    (SCRIPT_DIR / "cert_permanent_attributes.bad.hash").write_bytes(hash_bytes)

    # Convert the public key to raw bytes for use in verification.
    subprocess.run(
        [
            AVB_TOOL,
            "extract_public_key",
            "--key",
            SCRIPT_DIR / "testkey_rsa4096_pub.pem",
            "--output",
            SCRIPT_DIR / "testkey_rsa4096_pub.bin",
        ],
        check=True,
    )

    with tempfile.TemporaryDirectory() as temp_dir:
        temp_dir = pathlib.Path(temp_dir)

        # Create the hash descriptor. We only need this temporarily until we add
        # it into the final vbmeta image.
        hash_descriptor_path = temp_dir / "hash_descriptor.bin"
        subprocess.run(
            [
                AVB_TOOL,
                "add_hash_footer",
                "--dynamic_partition_size",
                "--do_not_append_vbmeta_image",
                "--partition_name",
                "zircon_a",
                "--image",
                SCRIPT_DIR / "zircon_a.bin",
                "--output_vbmeta_image",
                hash_descriptor_path,
                "--salt",
                "2000",
            ],
            check=True,
        )

        # Create the final signed vbmeta including the hash descriptor.
        subprocess.run(
            [
                AVB_TOOL,
                "make_vbmeta_image",
                "--key",
                SCRIPT_DIR / "testkey_rsa4096.pem",
                "--algorithm",
                "SHA512_RSA4096",
                "--include_descriptors_from_image",
                hash_descriptor_path,
                "--output",
                SCRIPT_DIR / "zircon_a.vbmeta",
            ],
            check=True,
        )

        # Also create a vbmeta using the libavb_cert extension.
        subprocess.run(
            [
                AVB_TOOL,
                "make_vbmeta_image",
                "--key",
                SCRIPT_DIR / "testkey_cert_psk.pem",
                "--public_key_metadata",
                SCRIPT_DIR / "cert_metadata.bin",
                "--algorithm",
                "SHA512_RSA4096",
                "--include_descriptors_from_image",
                hash_descriptor_path,
                "--output",
                SCRIPT_DIR / "zircon_a.vbmeta.cert",
            ]
        )


if __name__ == "__main__":
    gen_writeback_test_bin()
    gen_sparse_test_file()
    gen_zircon_gpt()
    gen_vbmeta()