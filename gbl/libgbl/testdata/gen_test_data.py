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

import argparse
import os
import pathlib
import random
import shutil
import subprocess
import tempfile

SCRIPT_DIR = pathlib.Path(os.path.dirname(os.path.realpath(__file__)))
AOSP_ROOT = SCRIPT_DIR.parents[4]
GBL_ROOT = SCRIPT_DIR.parents[1]
GPT_TOOL = GBL_ROOT / "tools" / "gen_gpt_disk.py"
AVB_DIR = AOSP_ROOT / "external" / "avb"
AVB_TOOL = AVB_DIR / "avbtool.py"
MKBOOTIMG_TOOL = AOSP_ROOT / "tools" / "mkbootimg" / "mkbootimg.py"
AVB_TEST_DATA_DIR = AVB_DIR / "test" / "data"
DTC_TOOL = (
    AOSP_ROOT / "prebuilts" / "kernel-build-tools" / "linux-x86" / "bin" / "dtc"
)
MKDTBOIMG_TOOL = (
    AOSP_ROOT
    / "prebuilts"
    / "kernel-build-tools"
    / "linux-x86"
    / "bin"
    / "mkdtboimg"
)
SZ_KB = 1024

# RNG seed values. Keep the same seed value for a given file to ensure
# reproducibility as much as possible; this will prevent adding a bunch of
# unnecessary test binaries to the git history.
RNG_SEED_SPARSE_TEST_RAW = 1
RNG_SEED_ZIRCON = {"a": 2, "b": 3, "r": 4, "slotless": 5}
RNG_SEED_ANDROID = {"a": 6, "b": 7}

# AVB related constants.
PSK = AVB_TEST_DATA_DIR / "testkey_cert_psk.pem"
TEST_ROLLBACK_INDEX_LOCATION = 1
TEST_ROLLBACK_INDEX = 2


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
    subprocess.run(
        ["img2simg", "-s", out_file_raw, SCRIPT_DIR / "sparse_test.bin"]
    )
    subprocess.run(
        [
            "img2simg",
            "-s",
            out_file_raw,
            SCRIPT_DIR / "sparse_test_blk1024.bin",
            "1024",
        ]
    )


def gen_dtb(input_dts, output_dtb):
    subprocess.run(
        [DTC_TOOL, "-I", "dts", "-O", "dtb", "-o", output_dtb, input_dts],
        stderr=subprocess.STDOUT,
        check=True,
    )


def gen_android_test_dtb():
    out_dir = SCRIPT_DIR / "android"
    # Generates base test device tree.
    gen_dtb(out_dir / "device_tree.dts", out_dir / "device_tree.dtb")

    # Generates overlay
    gen_dtb(out_dir / "overlay_a.dts", out_dir / "overlay_a.dtb")
    gen_dtb(out_dir / "overlay_b.dts", out_dir / "overlay_b.dtb")

    subprocess.run(
        [
            MKDTBOIMG_TOOL,
            "create",
            out_dir / "dtbo_a.img",
            "--id=0x1",
            "--rev=0x0",
            out_dir / "overlay_a.dtb",
        ],
        stderr=subprocess.STDOUT,
        check=True,
    )
    subprocess.run(
        [
            MKDTBOIMG_TOOL,
            "create",
            out_dir / "dtbo_b.img",
            "--id=0x1",
            "--rev=0x0",
            out_dir / "overlay_b.dtb",
        ],
        stderr=subprocess.STDOUT,
        check=True,
    )


# Generate vbmeta data for a set of images.
def gen_android_test_vbmeta(partition_file_pairs, out_vbmeta):
    with tempfile.TemporaryDirectory() as temp_dir:
        desc_args = []
        temp_dir = pathlib.Path(temp_dir)
        for i, (part, image_file) in enumerate(partition_file_pairs):
            out = temp_dir / f"{i}.vbmeta_desc"
            desc_args += ["--include_descriptors_from_image", out]
            subprocess.run(
                [
                    AVB_TOOL,
                    "add_hash_footer",
                    "--image",
                    image_file,
                    "--partition_name",
                    part,
                    "--do_not_append_vbmeta_image",
                    "--output_vbmeta_image",
                    out,
                    "--salt",
                    "9f06406a750581266f21865d115e63b54db441bc0d614195c78c14451b5ecb8abb14d8cd88d816c4750545ef89cb348a3834815aac4fa359e8b02a740483d975",
                    "--partition_size",
                    "209715200",  # Randomly chosen large enough value.
                ],
                stderr=subprocess.STDOUT,
                check=True,
            )

        subprocess.run(
            [
                AVB_TOOL,
                "make_vbmeta_image",
                "--output",
                out_vbmeta,
                "--key",
                PSK,
                "--algorithm",
                "SHA512_RSA4096",
                "--rollback_index",
                f"{TEST_ROLLBACK_INDEX}",
                "--rollback_index_location",
                f"{TEST_ROLLBACK_INDEX_LOCATION}",
            ]
            + desc_args,
            stderr=subprocess.STDOUT,
            check=True,
        )

        # Generates digest file
        out_digest = out_vbmeta.with_suffix(".digest.txt")
        digest = subprocess.run(
            [
                AVB_TOOL,
                "calculate_vbmeta_digest",
                "--image",
                out_vbmeta,
                "--hash_algorithm",
                "sha512",
            ],
            check=True,
            text=True,
            capture_output=True,
        )
        out_digest.write_text(digest.stdout)


def gen_android_test_images():
    gen_android_test_dtb()

    with tempfile.TemporaryDirectory() as temp_dir:
        temp_dir = pathlib.Path(temp_dir)
        out_dir = SCRIPT_DIR / "android"
        out_dir.mkdir(parents=True, exist_ok=True)
        for slot in ["a", "b"]:
            random.seed(RNG_SEED_ANDROID[slot])
            kernel = out_dir / f"kernel_{slot}.img"
            kernel.write_bytes(random.randbytes(4 * SZ_KB))

            generic_ramdisk = out_dir / f"generic_ramdisk_{slot}.img"
            generic_ramdisk.write_bytes(random.randbytes(8 * SZ_KB))

            vendor_ramdisk = out_dir / f"vendor_ramdisk_{slot}.img"
            vendor_ramdisk.write_bytes(random.randbytes(12 * SZ_KB))

            vendor_bootconfig = temp_dir / f"vendor_bootconfig_{slot}.img"
            vendor_bootconfig.write_bytes(
                b"""\
androidboot.config_1=val_1
androidboot.config_2=val_2
"""
            )

            boot_cmdline = "cmd_key_1=cmd_val_1,cmd_key_2=cmd_val_2"
            vendor_cmdline = "cmd_vendor_key_1=cmd_vendor_val_1,cmd_vendor_key_2=cmd_vendor_val_2"

            # Generate v3, v4 boot image without ramdisk (usecase for init_boot)
            common = [
                MKBOOTIMG_TOOL,
                "--kernel",
                kernel,
                "--cmdline",
                boot_cmdline,
                "--dtb",
                out_dir / "device_tree.dtb",
            ]
            for i in [3, 4]:
                out = out_dir / f"boot_no_ramdisk_v{i}_{slot}.img"
                subprocess.run(
                    common + ["--header_version", f"{i}", "-o", out],
                    check=True,
                    stderr=subprocess.STDOUT,
                )

            # Generates v0 - v4 boot image that contains generic ramdisk.
            common += [
                "--ramdisk",
                generic_ramdisk,
            ]
            for i in range(0, 5):
                out = out_dir / f"boot_v{i}_{slot}.img"
                subprocess.run(
                    common + ["--header_version", f"{i}", "-o", out],
                    check=True,
                    stderr=subprocess.STDOUT,
                )

            # Generates init_boot
            subprocess.run(
                [
                    MKBOOTIMG_TOOL,
                    "-o",
                    out_dir / f"init_boot_{slot}.img",
                    "--ramdisk",
                    generic_ramdisk,
                    # init_boot uses fixed version 4.
                    "--header_version",
                    "4",
                ],
                check=True,
                stderr=subprocess.STDOUT,
            )

            # Generates vendor_boot images
            common = [
                MKBOOTIMG_TOOL,
                "--vendor_cmdline",
                vendor_cmdline,
                "--vendor_ramdisk",
                vendor_ramdisk,
                "--dtb",
                out_dir / "device_tree.dtb",
            ]
            # Generates vendor_boot v3 (no bootconfig)
            subprocess.run(
                common
                + [
                    "--vendor_boot",
                    out_dir / f"vendor_boot_v3_{slot}.img",
                    "--header_version",
                    "3",
                ],
                stderr=subprocess.STDOUT,
                check=True,
            )
            # Generates vendor_boot v4
            subprocess.run(
                common
                + [
                    "--vendor_boot",
                    out_dir / f"vendor_boot_v4_{slot}.img",
                    "--vendor_bootconfig",
                    vendor_bootconfig,
                    "--header_version",
                    "4",
                ],
                stderr=subprocess.STDOUT,
                check=True,
            )

            # Generates a vbmeta data for v0 - v2 setup
            for i in [0, 1, 2]:
                parts = [
                    (f"boot", out_dir / f"boot_v{i}_{slot}.img"),
                    ("dtbo", out_dir / f"dtbo_{slot}.img"),
                ]
                gen_android_test_vbmeta(
                    parts, out_dir / f"vbmeta_v{i}_{slot}.img"
                )

            # Generates different combinations of v3/v4 boot/vendor_boot/init_boot setup.
            for use_init_boot in [True, False]:
                for boot_ver in [3, 4]:
                    if use_init_boot:
                        boot = (
                            out_dir / f"boot_no_ramdisk_v{boot_ver}_{slot}.img"
                        )
                    else:
                        boot = out_dir / f"boot_v{boot_ver}_{slot}.img"

                    for vendor_ver in [3, 4]:
                        vendor_boot = (
                            out_dir / f"vendor_boot_v{vendor_ver}_{slot}.img"
                        )

                        parts = [
                            (f"boot", boot),
                            (f"vendor_boot", vendor_boot),
                            ("dtbo", out_dir / f"dtbo_{slot}.img"),
                        ]
                        prefix = f"vbmeta_v{boot_ver}_v{vendor_ver}"
                        if use_init_boot:
                            vbmeta_out = prefix + f"_init_boot_{slot}.img"
                            parts += [
                                (
                                    "init_boot",
                                    out_dir / f"init_boot_{slot}.img",
                                )
                            ]
                        else:
                            vbmeta_out = prefix + f"_{slot}.img"

                        gen_android_test_vbmeta(parts, out_dir / vbmeta_out)


def gen_zircon_test_images(zbi_tool):
    if not zbi_tool:
        print(
            "Warning: ZBI tool not provided. Skip regenerating zircon test"
            " images"
        )
        return

    ATX_METADATA = AVB_TEST_DATA_DIR / "cert_metadata.bin"

    with tempfile.TemporaryDirectory() as temp_dir:
        for slot in ["a", "b", "r", "slotless"]:
            temp_dir = pathlib.Path(temp_dir)
            random.seed(RNG_SEED_ZIRCON[slot])
            out_kernel_bin_file = temp_dir / f"zircon_{slot}.bin"
            # The first 16 bytes are two u64 integers representing `entry` and
            # `reserve_memory_size`.
            # Set `entry` value to 2048 and `reserve_memory_size` to 1024.
            kernel_bytes = int(2048).to_bytes(8, "little") + int(1024).to_bytes(
                8, "little"
            )
            kernel_bytes += random.randbytes(1 * SZ_KB - 16)
            out_kernel_bin_file.write_bytes(kernel_bytes)
            out_zbi_file = SCRIPT_DIR / f"zircon_{slot}.zbi"
            # Puts image in a zbi container.
            subprocess.run(
                [
                    zbi_tool,
                    "--output",
                    out_zbi_file,
                    "--type=KERNEL_X64",
                    out_kernel_bin_file,
                ]
            )

            # Generates vbmeta descriptor.
            vbmeta_desc = f"{temp_dir}/zircon_{slot}.vbmeta.desc"
            subprocess.run(
                [
                    AVB_TOOL,
                    "add_hash_footer",
                    "--image",
                    out_zbi_file,
                    "--partition_name",
                    "zircon",
                    "--do_not_append_vbmeta_image",
                    "--output_vbmeta_image",
                    vbmeta_desc,
                    "--partition_size",
                    "209715200",
                ]
            )
            # Generates two cmdline ZBI items to add as property descriptors to
            # vbmeta image for test.
            vbmeta_prop_args = []
            for i in range(2):
                prop_zbi_payload = f"{temp_dir}/prop_zbi_payload_{i}.bin"
                subprocess.run(
                    [
                        zbi_tool,
                        "--output",
                        prop_zbi_payload,
                        "--type=CMDLINE",
                        f"--entry=vb_prop_{i}=val",
                    ]
                )
                vbmeta_prop_args += [
                    "--prop_from_file",
                    f"zbi_vb_prop_{i}:{prop_zbi_payload}",
                ]
                # Also adds a property where the key name does not starts with
                # "zbi". The item should not be processed.
                vbmeta_prop_args += [
                    "--prop_from_file",
                    f"vb_prop_{i}:{prop_zbi_payload}",
                ]
            # Generates vbmeta image
            vbmeta_img = SCRIPT_DIR / f"vbmeta_{slot}.bin"
            subprocess.run(
                [
                    AVB_TOOL,
                    "make_vbmeta_image",
                    "--output",
                    vbmeta_img,
                    "--key",
                    PSK,
                    "--algorithm",
                    "SHA512_RSA4096",
                    "--public_key_metadata",
                    ATX_METADATA,
                    "--include_descriptors_from_image",
                    vbmeta_desc,
                    "--rollback_index",
                    f"{TEST_ROLLBACK_INDEX}",
                    "--rollback_index_location",
                    f"{TEST_ROLLBACK_INDEX_LOCATION}",
                ]
                + vbmeta_prop_args
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

    # Also creates a corrupted version of the permanent attributes to test failure.
    # This is a little bit of a pain but we don't have an easy way to do a SHA256 in Rust
    # at the moment so we can't generate it on the fly.
    bad_attrs = bytearray(
        (SCRIPT_DIR / "cert_permanent_attributes.bin").read_bytes()
    )
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
                SCRIPT_DIR / "zircon_a.zbi",
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

        # Also creates a vbmeta using the libavb_cert extension.
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


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )

    parser.add_argument(
        "--zbi_tool", default="", help="Path to the Fuchsia ZBI tool"
    )

    return parser.parse_args()


if __name__ == "__main__":
    args = _parse_args()
    gen_writeback_test_bin()
    gen_sparse_test_file()
    gen_zircon_test_images(args.zbi_tool)
    gen_vbmeta()
    gen_android_test_images()
