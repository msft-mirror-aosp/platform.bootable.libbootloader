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
"""Script for fixing up rust-project.json"""

import argparse
import json
import logging
import os
import shutil
import tempfile

# To generate rust-project.json from bazel, run
# ./tools/bazel run @rules_rust//tools/rust_analyzer:gen_rust_project --norepository_disable_download -- --bazel ./tools/bazel --config=no_clippy @gbl//efi/...
# However, this yields incorrect source path.
# Your source file
# /usr/local/google/home/zhangkelvin/uefi-gbl-mainline/bootable/libbootloader/gbl/efi/src/main.rs
# would turn into
# /usr/local/google/home/uefi-gbl-mainline/out/bazel/output_user_root/e14d642d361d598c63507c64a56ecbc7/execroot/_main/external/gbl/efi/src/main.rs
# and this confuses the rust-analyzer. This script will resolve the right
# source path for you by checking if any of the parent path is a symlink,
# and resolve all symlinks to final destination.

ARCH_X86_64 = "x86_64"
ARCH_AARCH64 = "aarch64"
# CARGO_CFG_TARGET_ARCH does not recognize riscv64 yet. But we expect it to
# some time in the future.
ARCH_RISCV64 = "riscv64"

# Contains arch specific override of rust-project.json
ARCH_TARGET = {
    ARCH_X86_64: "x86_64-unknown-uefi",
    ARCH_AARCH64: "aarch64-unknown-uefi",
    ARCH_RISCV64: "riscv64-unknown-linux",  # RISCV uses ELF->UEI conversion.
}


def _parse_args() -> argparse.Namespace:
  parser = argparse.ArgumentParser(
      description=__doc__,
      formatter_class=argparse.RawDescriptionHelpFormatter,
  )

  parser.add_argument(
      "file",
      nargs="?",
      help="Path to rust-project.json",
      default="rust-project.json",
  )
  parser.add_argument(
      "--arch",
      choices=[ARCH_X86_64, ARCH_AARCH64, ARCH_RISCV64],
      default=ARCH_AARCH64,
      help="Target architecture",
  )

  parser.add_argument(
      "--exclude-tests",
      action="store_true",
  )

  return parser.parse_args()


def traverse(obj: dict, arch: str, exclude_tests: bool):
  if isinstance(obj, dict):
    for key, val in obj.items():
      if key == "root_module" or key == "CARGO_MANIFEST_DIR":
        obj[key] = os.path.realpath(val)
        continue
      elif key == "include_dirs" or key == "exclude_dirs":
        obj[key] = [os.path.realpath(d) for d in val]
        continue
      elif key == "cfg" and isinstance(val, list):
        obj[key] = [o for o in val if o != "test"] if exclude_tests else val
        continue
      elif key == "CARGO_CFG_TARGET_OS":
        obj[key] = "uefi"
      elif key == "CARGO_CFG_TARGET_ARCH":
        obj[key] = arch
      elif key == "target":
        obj[key] = ARCH_TARGET[arch]
      traverse(val, arch, exclude_tests)
  elif isinstance(obj, list):
    for item in obj:
      traverse(item, arch, exclude_tests)


def main():
  args = _parse_args()

  logging.basicConfig(level=logging.INFO)
  rust_project_json_path = os.path.abspath(args.file)
  logging.info("Starting updating %s", rust_project_json_path)
  with open(rust_project_json_path, "r") as fp:
    data = json.load(fp)
    traverse(data, args.arch, args.exclude_tests)

  with tempfile.NamedTemporaryFile("w+", delete=False) as fp:
    json.dump(data, fp.file, indent=True)
    tmp_path = fp.name
  shutil.move(tmp_path, rust_project_json_path)
  logging.info("Successfully updated %s", rust_project_json_path)


if __name__ == "__main__":
  main()
