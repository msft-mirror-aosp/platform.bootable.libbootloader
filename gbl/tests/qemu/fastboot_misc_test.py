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
"""QEMU fastboot reboot test script"""

import logging
import os
import sys
import time
from qemu_test_utils import (
    VsockFastbootClient,
    default_logging,
    wait_for_fastboot_ready,
    wait_for_kernel_exit,
    wait_for_log_pattern,
)


def main():
  default_logging()
  logging.info("Starting fastboot reboot test...")

  console_log_path = os.environ.get("GBL_CONSOLE_LOG")
  assert console_log_path, "GBL_CONSOLE_LOG not set"

  port = 1

  # Wait for device to be ready before connecting to vsock. Otherwise
  # vhost-device-vsock may become out of sync if VsockFastbootClient
  # timeout first.
  wait_for_fastboot_ready(console_log_path)

  client = VsockFastbootClient(port=port)

  client.run_command(b"oem gbl-integration-test-optional")
  wait_for_log_pattern(
      console_log_path,
      [r"^\[\d+\.\d+\] Test passed: test_gbl_fastboot_transport"],
  )
  wait_for_log_pattern(
      console_log_path,
      [r"^\[\d+\.\d+\] Test passed: test_hash2"],
  )
  client.run_command(b"oem gbl-integration-test-required")
  wait_for_log_pattern(
      console_log_path,
      [r"^\[\d+\.\d+\] Test passed: test_block_io"],
  )

  # Test readenv custom command
  test_name = os.environ.get("GBL_TEST_NAME")
  assert test_name, "GBL_TEST_NAME not set"
  reply, _ = client.run_command(
      f"oem readenv GBL_TEST_NAME".encode(), assert_ok=True
  )
  assert reply == f"OKAY{test_name}".encode()
  reply, _ = client.run_command(
      f"readenv:GBL_TEST_NAME".encode(), assert_ok=True
  )
  assert reply == f"OKAY{test_name}".encode()

  client.run_command(b"getvar:all", assert_ok=True)
  client.run_command(b"reboot-bootloader", assert_ok=True)
  client.close()

  wait_for_fastboot_ready(console_log_path, 2)

  client = VsockFastbootClient(port=port)
  client.run_command(b"reboot-recovery", assert_ok=True)

  # Poll the console log file for success pattern
  wait_for_log_pattern(
      console_log_path,
      [r"^\[\d+\.\d+\] Normal Mode: false$"],
  )
  wait_for_kernel_exit(console_log_path)


if __name__ == "__main__":
  main()
