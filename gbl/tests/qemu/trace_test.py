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
"""QEMU trace analysis test script

The script tests:

1. GBL trace collection and conversion to trace event format used by perfetto.
2. Enforce maximum stack usage in currently known critical path "fastboot boot".
3. HandleLoadedOs() invocation during "fastboot boot".
"""

import logging
import os
from qemu_test_utils import (
    VsockFastbootClient,
    default_logging,
    process_and_check_trace,
    wait_for_fastboot_ready,
    wait_for_kernel_exit,
    wait_for_log_pattern,
)


def main():
  default_logging()
  logging.info("Starting trace generation test...")

  console_log_path = os.environ.get("GBL_CONSOLE_LOG")
  assert console_log_path, "GBL_CONSOLE_LOG not set"

  # Wait for device to be ready before connecting to vsock. Otherwise
  # vhost-device-vsock may become out of sync if VsockFastbootClient
  # timeout first.
  wait_for_fastboot_ready(console_log_path)

  client = VsockFastbootClient(port=1)
  client.download("boot_a.img")
  client.run_command(b"boot", assert_ok=True)
  client.close()

  loaded_matches = wait_for_log_pattern(
      console_log_path,
      [
          r"^\[\d+\.\d+\] handle_loaded_os: kernel @ (0x[0-9a-fA-F]+)"
          r" \(0x[0-9a-fA-F]+\), ramdisk @ (0x[0-9a-fA-F]+)"
          r" \(0x[0-9a-fA-F]+\), fdt @ (0x[0-9a-fA-F]+) \(0x[0-9a-fA-F]+\)$"
      ],
  )
  kernel_addr, ramdisk_addr, fdt_addr = loaded_matches[0][0].groups()
  wait_for_log_pattern(
      console_log_path,
      [
          rf"^\[\d+\.\d+\] Booting kernel @ {kernel_addr}, ramdisk @"
          rf" {ramdisk_addr}, fdt @ {fdt_addr}$"
      ],
  )

  wait_for_kernel_exit(console_log_path)

  process_and_check_trace()

  logging.info("Trace test completed successfully.")


if __name__ == "__main__":
  main()
