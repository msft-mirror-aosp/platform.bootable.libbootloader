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

# Super project root directory.
# Assumes that the project is checkout as "bootable/libbootloader/gbl"
SUPER_PROJECT_ROOT = pathlib.Path(__file__).resolve().parents[5]

ARCHS = ["x86_64", "x86_32", "aarch64", "riscv64"]

# Version used by Trusty and u-boot
DEFAULT_CLANG_VERSION = "clang-r475365b"
DEFAULT_LINUX_SYS_ROOT_VERSION = "x86_64-linux-glibc2.17-4.8"


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


AOSP_GET_CLANG_VERSION_SCRIPT = pathlib.Path(
    "build") / "soong" / "scripts" / "get_clang_version.py"


def aosp_get_clang() -> str:
    try:
        return subprocess.run([AOSP_GET_CLANG_VERSION_SCRIPT],
                              check=True,
                              text=True,
                              capture_output=True,
                              cwd=str(SUPER_PROJECT_ROOT)).stdout.strip('\n')
    except:
        return None


def get_clang_version() -> str:
    from_env = os.environ.get("GBL_CLANG_VERSION", None)
    if from_env:
        return f"clang-{from_env}"

    if aosp_get_clang():
        return aosp_get_clang()

    return DEFAULT_CLANG_VERSION


def run_bazel(bazel, out, args):
    """Wrapper for running bazel command"""
    command = [bazel, f"--output_user_root={out}"] + args
    subprocess.run(command, cwd=str(GBL_DIR), check=True)


def main() -> int:
    args = parse_args()
    if args.bazel:
        # Standalone build
        bazel = pathlib.Path(args.bazel).resolve()
    else:
        # Assume the project lives in a super project.
        print(f"Looking for super project at: {SUPER_PROJECT_ROOT}")

        llvm = str(SUPER_PROJECT_ROOT / "prebuilts" / "clang" / "host" /
                   "linux-x86" / get_clang_version())
        sysroot = str(SUPER_PROJECT_ROOT / "prebuilts" / "gcc" / "linux-x86" /
                      "host" / DEFAULT_LINUX_SYS_ROOT_VERSION)
        bazel = (SUPER_PROJECT_ROOT / "prebuilts" / "bazel" / "linux-x86_64" /
                 "bazel")

        if not os.path.isdir(str(llvm)):
            raise EnvironmentError(f"LLVM not found at {llvm}")

        if not os.path.isdir(str(sysroot)):
            raise EnvironmentError(f"Linux sysroot not found at {sysroot}")

        if not bazel.exists():
            raise EnvironmentError(f"Bazel binary not found {bazel}")

        os.environ["GBL_LLVM_PREBUILTS"] = str(llvm)
        os.environ["GBL_LINUX_SYSROOT"] = str(sysroot)
        print(f'LLVM: {os.environ["GBL_LLVM_PREBUILTS"]}')
        print(f'Linux Sysroot: {os.environ["GBL_LINUX_SYSROOT"]}')

    archs = args.arch if args.arch else ARCHS

    out_dir = (pathlib.Path(args.out) / "gbl").resolve()
    os.makedirs(str(out_dir), exist_ok=True)

    print(f"Output: {out_dir}")
    print(f"Target architectures: {archs}")

    if args.test:
        run_bazel(bazel, out_dir,
                  ["test", "@gbl//tests", "--verbose_failures"])

    out_paths = []
    for arch in archs:
        run_bazel(bazel, out_dir,
                  ["build", f"@gbl//efi:{arch}", "--verbose_failures"])
        out_path = out_dir / f"gbl_{arch}.efi"
        # Delete old image first. Otherwise if the image doesn't have write permission,
        # copy fails.
        out_path.unlink(missing_ok=True)
        shutil.copy(
            (GBL_DIR / "bazel-bin" / "efi" / f"gbl_{arch}.efi").resolve(),
            out_path)
        out_paths.append(out_path)

    for path in out_paths:
        print(f"Image output at {path}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
