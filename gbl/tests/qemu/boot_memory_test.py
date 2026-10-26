#!/usr/bin/env python3
#
# Copyright (C) 2026 The Android Open Source Project
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
"""QEMU boot memory test script"""

import logging
import os
import sys
from qemu_test_utils import (
    default_logging,
    process_and_check_trace,
    wait_for_kernel_exit,
    wait_for_log_pattern,
)


def main():
  default_logging()
  logging.info("Starting boot memory test...")

  console_log_path = os.environ.get("GBL_CONSOLE_LOG")
  assert console_log_path, "GBL_CONSOLE_LOG not set"

  # Wait for log messages indicating the partition buffer existence, i.e.:
  #
  # [2.3622] Found preloaded buffer for "boot"
  # [2.3711] Found designated load buffer for "vendor_boot"
  wait_for_log_pattern(
      console_log_path,
      [
          r'^\[\d+\.\d+\] Found preloaded buffer for "boot"',
          r'^\[\d+\.\d+\] Found designated load buffer for "vendor_boot"',
      ],
  )

  # Verify buffer allocation logs, i.e.:
  #
  # [1.2733] Allocated 0x100000 bytes for "kernel" buffer at 0x4c000000.
  # [1.2795] Allocated 0x100000 bytes for "ramdisk" buffer at 0x4bd23000.
  # [1.2845] Allocated 0x100000 bytes for "fdt" buffer at 0x4bc22018.
  alloc_matches = wait_for_log_pattern(
      console_log_path,
      [
          (
              r'^\[\d+\.\d+\] Allocated 0x100000 bytes for "kernel" buffer at'
              r" (0x[0-9a-fA-F]+)\.$"
          ),
          (
              r'^\[\d+\.\d+\] Allocated 0x100000 bytes for "ramdisk" buffer at'
              r" (0x[0-9a-fA-F]+)\.$"
          ),
          (
              r'^\[\d+\.\d+\] Allocated 0x100000 bytes for "fdt" buffer at'
              r" (0x[0-9a-fA-F]+)\.$"
          ),
      ],
  )
  kernel_addr = alloc_matches[0][0].group(1)
  ramdisk_addr = alloc_matches[0][1].group(1)
  fdt_addr = alloc_matches[0][2].group(1)

  # Verify HandleLoadedOs() and booting logs match allocated addresses, i.e.:
  #
  # [1.3490] handle_loaded_os: kernel @ 0x4c000000 (...), ramdisk @ 0x4bd23000 (...), fdt @ 0x4bc22018 (...)
  # [1.3496] Booting kernel @ 0x4c000000, ramdisk @ 0x4bd23000, fdt @ 0x4bc22018
  wait_for_log_pattern(
      console_log_path,
      [
          rf"^\[\d+\.\d+\] handle_loaded_os: kernel @ {kernel_addr}"
          r" \(0x[0-9a-fA-F]+\),"
          rf" ramdisk @ {ramdisk_addr} \(0x[0-9a-fA-F]+\),"
          rf" fdt @ {fdt_addr} \(0x[0-9a-fA-F]+\)$"
      ],
  )
  wait_for_log_pattern(
      console_log_path,
      [
          rf"^\[\d+\.\d+\] Booting kernel @ {kernel_addr}, ramdisk @"
          rf" {ramdisk_addr}, fdt @ {fdt_addr}$"
      ],
  )

  wait_for_kernel_exit(console_log_path)
  process_and_check_trace()

  logging.info("Dedicated boot memory test completed successfully.")


if __name__ == "__main__":
  main()
