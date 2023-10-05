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

# See gbl/README.md for usage.

import argparse
import os
import pathlib
import shutil
import sys
import subprocess

# GBL bazel root.
GBL_DIR = pathlib.Path(__file__).resolve().parents[2]

ARCHS = ["x86_64", "x86_32", "aarch64", "riscv64"]


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--aosp_root", help="Path to Android root source")
    parser.add_argument("--bazel", help="Override path to bazel executable")
    parser.add_argument("--test", action="store_true", help="Run unittests")
    parser.add_argument(
        "--arch",
        help="Add a specific target architecture to build list",
        action='append',
        choices=ARCHS)
    parser.add_argument("out", help="Output directory")

    return parser.parse_args()


ARCH_TO_BAZEL_PLATFORM_CONFIG = {
    "x86_64": "gbl_uefi_x86_64",
    "x86_32": "gbl_uefi_x86_32",
    "aarch64": "gbl_uefi_aarch64",
    "riscv64": "gbl_elf_riscv64",
}

AOSP_GET_CLANG_VERSION_SCRIPT = pathlib.Path(
    "build") / "soong" / "scripts" / "get_clang_version.py"


def aosp_get_clang(aosp_root: pathlib.Path) -> str:
    return subprocess.run([AOSP_GET_CLANG_VERSION_SCRIPT],
                          check=True,
                          text=True,
                          capture_output=True,
                          cwd=str(aosp_root)).stdout.strip('\n')


def main() -> int:
    args = parse_args()

    if not args.aosp_root:
        args.aosp_root = os.environ.get("ANDROID_BUILD_TOP", None)

    if args.aosp_root:
        aosp_root = pathlib.Path(args.aosp_root).resolve()
        os.environ["GBL_LLVM_PREBUILTS"] = str(aosp_root / "prebuilts" /
                                               "clang" / "host" / "linux-x86" /
                                               aosp_get_clang(aosp_root))
        bazel = aosp_root / "prebuilts" / "bazel" / "linux-x86_64" / "bazel"

    if args.bazel:
        bazel = pathlib.Path(args.bazel).resolve()

    archs = args.arch if args.arch else ARCHS

    print(f"bazel = {bazel}")
    print(f"Target architectures: {archs}")

    out_dir = (pathlib.Path(args.out) / "gbl").resolve()
    os.makedirs(str(out_dir), exist_ok=True)

    if args.test:
        subprocess.run([bazel, "test", "@gbl//tests", "--verbose_failures"],
                       cwd=str(GBL_DIR),
                       check=True)

    out_paths = []
    for arch in archs:
        common_args = [
            f"--platforms=@gbl//toolchain:{ARCH_TO_BAZEL_PLATFORM_CONFIG[arch]}",
            f"--cpu={arch}",
            "--verbose_failures",
        ]

        # Build Rust sysroot
        # TODO(http://b/302569430): This can be skipped for platforms that will
        # get prebuilt sysroot upstream. It saves about 20 seconds build time
        # each.
        subprocess.run([
            bazel,
            "build",
            "@gbl//rust_sysroot",
        ] + common_args,
                       cwd=str(GBL_DIR),
                       check=True)

        os.environ["GBL_CUSTOM_RUST_SYSROOT"] =\
            str((GBL_DIR / "bazel-bin" / "rust_sysroot").resolve())

        subprocess.run([
            bazel,
            "build",
            "@gbl//efi:gbl_efi",
        ] + common_args,
                       cwd=str(GBL_DIR),
                       check=True)
        out_path = out_dir / f"gbl_{arch}.efi"
        # Delete old image first. Otherwise if the image doesn't have write permission,
        # copy fails.
        out_path.unlink(missing_ok=True)
        shutil.copy(GBL_DIR / "bazel-bin" / "efi" / "gbl.efi", out_path)
        out_paths.append(out_path)

    for path in out_paths:
        print(f"Image output at {path}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
