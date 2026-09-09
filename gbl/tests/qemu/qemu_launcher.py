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
"""QEMU Test Launcher"""

import argparse
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time


def parse_args() -> argparse.Namespace:
  parser = argparse.ArgumentParser(
      description=__doc__,
      formatter_class=argparse.RawDescriptionHelpFormatter,
  )

  parser.add_argument("efi", help="Path to the GBL launcher EFI application")
  parser.add_argument("gbl", help="Path to the GBL binary")
  parser.add_argument("--bios", help="Path to the BIOS (UEFI firmware)")
  parser.add_argument("--qemu", help="Path to the QEMU binary")
  parser.add_argument(
      "--timeout", type=int, help="timeout in seconds", default=10
  )
  parser.add_argument("--log_output", help="Output path for serial log")
  parser.add_argument(
      "--artifacts_output", help="Output path for artifacts archive"
  )
  parser.add_argument(
      "--runfile",
      action="append",
      help=(
          "Comma-separated pair of <mapped_name>,<source_file_path> to "
          "symlink in the local working directory"
      ),
      default=[],
  )
  parser.add_argument(
      "--disk",
      action="append",
      help="Path to a disk image to attach as virtio-blk",
  )
  parser.add_argument(
      "--vhost_device_vsock", help="Path to the vhost device vsock binary"
  )
  parser.add_argument(
      "--test_script", help="Path to a user-provided Python script to execute"
  )
  parser.add_argument(
      "--test_name", help="Name of the test target", default="qemu_test"
  )
  parser.add_argument(
      "--gdb",
      action="store_true",
      help=(
          "If provided, QEMU will wait for a GDB connection on a Unix socket in"
          " the test directory and pause CPU at startup."
      ),
  )

  return parser.parse_args()


def wait_for_file(
    path: pathlib.Path, proc: subprocess.Popen = None, timeout: float = 5.0
):
  """Wait for a file (e.g. Unix domain socket) to exist on disk."""
  end_time = time.time() + timeout
  while time.time() < end_time:
    if path.exists():
      return
    if proc is not None and proc.poll() is not None:
      raise RuntimeError(
          f"Process exited with code {proc.returncode} while waiting for {path}"
      )
    time.sleep(0.01)
  raise TimeoutError(f"Timed out waiting for {path} to be created")


def launch_qemu(args):
  qemu = os.path.abspath(args.qemu)
  bios = os.path.abspath(args.bios)
  with tempfile.TemporaryDirectory() as test_dir:
    env = os.environ.copy()
    # Flushes any log immediately.
    env["PYTHONUNBUFFERED"] = "1"
    # The script will be run in a sandbox, so we need to set the temp dir.
    env["TMPDIR"] = test_dir
    env["TEMP"] = test_dir
    env["TMP"] = test_dir
    test_dir = pathlib.Path(test_dir)
    # Create a FAT filesystem image for the EFI System Partition (ESP)
    esp_part_dir = test_dir / "esp" / "EFI" / "BOOT"
    esp_part_dir.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(args.efi, esp_part_dir / "bootaa64.efi")
    # Make sure a log file always eixsts
    (test_dir / "console.log").write_text("")

    # Symlinks mandatory GBL to the current work directory.
    gbl_path = os.path.abspath(args.gbl)
    os.symlink(gbl_path, test_dir / "gbl.bin")

    # Symlinks all additional runfiles to the current work directory.
    for runfile_str in args.runfile:
      parts = runfile_str.split(",", 1)
      if len(parts) == 2:
        mapped_name, src_path = parts
      else:
        src_path = parts[0]
        mapped_name = os.path.basename(src_path)
      dest_path = test_dir / mapped_name
      dest_path.parent.mkdir(parents=True, exist_ok=True)
      os.symlink(os.path.abspath(src_path), dest_path)

    socket_path = test_dir / "vsock-guest.sock"
    uds_path = test_dir / "vsock-host.sock"

    # Shares the fastboot vsock socket path and log path to test script.
    env["FASTBOOT_OVER_VSOCK_UDS_PATH"] = str(uds_path)
    env["GBL_CONSOLE_LOG"] = str(test_dir / "console.log")
    env["GBL_TEST_NAME"] = args.test_name
    script_log_path = test_dir / "test_script.log"

    # Create artifacts directory and share it with the test script.
    outputs_dir = os.environ.get("TEST_UNDECLARED_OUTPUTS_DIR")
    if outputs_dir:
      artifacts_dir = pathlib.Path(outputs_dir)
    else:
      artifacts_dir = test_dir / "artifacts"
      artifacts_dir.mkdir(parents=True, exist_ok=True)
      env["TEST_UNDECLARED_OUTPUTS_DIR"] = str(artifacts_dir)
    env["TEST_ARTIFACTS_OUT"] = args.artifacts_output

    vhost_proc = None
    qemu_proc = None
    failed = False
    try:
      cmd_args = [qemu, "-nographic", "-cpu", "max"]
      cmd_args += [
          "-m",
          "256M",  # 256mb is minimum requirement by edk2
          "-object",
          "memory-backend-memfd,id=mem,size=256M,share=on",
      ]
      # Skips the 5 seconds delay spent waiting for user input in the boot menu
      cmd_args += ["-boot", "menu=on,splash-time=0"]
      # EDK2 firmware
      cmd_args += ["-bios", bios]
      # ESP partition
      cmd_args += ["-drive", "format=raw,file=fat:rw:esp"]
      # Add extra disks
      disks = args.disk or []
      for i, disk in enumerate(disks):
        # GBL needs read/write access to the disk image.
        # Bazel output artifacts are read-only, so create a copy of the disk
        # image.
        disk_path = test_dir / f"disk_{i}.img"
        shutil.copyfile(disk, disk_path)
        os.chmod(disk_path, 0o644)
        drive_id = f"hd{i}"
        cmd_args += [
            "-drive",
            f"file={disk_path},format=raw,if=none,id={drive_id}",
        ]
        cmd_args += ["-device", f"virtio-blk-device,drive={drive_id}"]

      con_in_sock_path = test_dir / "con_in.sock"
      # Re-direct all sources of serial log to a log file
      cmd_args += ["-serial", "chardev:console"]
      cmd_args += ["-monitor", "chardev:console"]
      cmd_args += ["-semihosting"]
      cmd_args += ["-semihosting-config", "chardev=console"]
      cmd_args += [
          "-chardev",
          f"socket,id=console,path={con_in_sock_path},server=on,wait=off,mux=on,logfile=console.log",
      ]
      # userspace vsock interface
      if args.vhost_device_vsock:
        cmd_args += [
            "-chardev",
            f"socket,id=char0,reconnect=0,path={socket_path}",
        ]
        cmd_args += ["-device", "vhost-user-vsock-pci,chardev=char0"]

      gdb_sock_path = test_dir / "gdb.sock"
      if args.gdb:
        env["GBL_GDB_SOCKET"] = str(gdb_sock_path)
        # Configure GDB server over Unix socket and pause CPU at startup (-S)
        cmd_args += [
            "-gdb",
            f"unix:{gdb_sock_path},server=on,wait=on",
            "-S",
        ]

      def start_vhost():
        proc = subprocess.Popen(
            [
                os.path.abspath(args.vhost_device_vsock),
                "--vm",
                f"guest-cid=3,socket={socket_path},uds-path={uds_path}",
            ],
            stderr=subprocess.STDOUT,
            cwd=test_dir,
            env=env,
        )
        wait_for_file(socket_path, proc)
        wait_for_file(uds_path, proc)
        return proc

      if args.vhost_device_vsock:
        vhost_proc = start_vhost()

      # Generate FDT with the full QEMU arguments.
      subprocess.run(
          cmd_args + ["-machine", "virt,dumpdtb=fdt.dtb,memory-backend=mem"],
          check=True,
          stderr=subprocess.STDOUT,
          cwd=test_dir,
          env=env,
      )

      # Restart vhost-device-vsock and clean up any sockets created during
      # dumpdtb so that the real QEMU run starts with a clean, ready socket set.
      if vhost_proc is not None:
        vhost_proc.terminate()
        vhost_proc.wait()
        vhost_proc = None
      for sock in (socket_path, uds_path, con_in_sock_path, gdb_sock_path):
        sock.unlink(missing_ok=True)
      if args.vhost_device_vsock:
        vhost_proc = start_vhost()

      qemu_end_time = time.time() + args.timeout
      # Launch QEMU
      qemu_proc = subprocess.Popen(
          cmd_args + ["-machine", "virt,memory-backend=mem"],
          stderr=subprocess.STDOUT,
          cwd=test_dir,
          env=env,
      )

      wait_for_file(con_in_sock_path, qemu_proc)
      if args.gdb:
        wait_for_file(gdb_sock_path, qemu_proc)

      # Run test script if provided
      #
      # Notes: The launching and management of qemu can also be driven by the
      # test script. This may allow the test script to be written like unittest.
      # For example, a test scripts may contain several python unittest and each
      # test launches its own instance of qemu.
      if args.test_script:
        with open(script_log_path, "w") as script_log:
          subprocess.run(
              [sys.executable, os.path.abspath(args.test_script)],
              timeout=args.timeout,
              check=True,
              stdout=script_log,
              stderr=subprocess.STDOUT,
              cwd=test_dir,
              env=env,
          )

      # Wait for QEMU to exit
      qemu_proc.wait(timeout=max(qemu_end_time - time.time(), 0))
      if qemu_proc.returncode != 0:
        raise subprocess.CalledProcessError(
            qemu_proc.returncode, qemu_proc.args
        )
    except Exception as e:
      failed = True
      print(f"QEMU error: {e}")
      raise
    finally:
      if vhost_proc is not None:
        vhost_proc.terminate()
        vhost_proc.wait()
      if qemu_proc is not None:
        qemu_proc.terminate()
        qemu_proc.wait()
      if args.log_output:
        with open(args.log_output, "w") as outfile:
          outfile.write(f"=== Test Name: {args.test_name} ===\n\n")
          outfile.write("=== Device Console Log ===\n")
          outfile.write((test_dir / "console.log").read_text())
          if script_log_path.exists():
            outfile.write("\n=== Host Test Script Log ===\n")
            outfile.write(script_log_path.read_text())
        if failed:
          print(f"\nQEMU Test Failed! Output log:\n")
          log_text = pathlib.Path(args.log_output).read_text()
          # Strip ANSI escape codes (like clear screen)
          clean_text = re.sub(r"\x1b\[[0-9;]*[mGHKJ]", "", log_text)
          print(clean_text)
      if args.artifacts_output:
        try:
          with tarfile.open(args.artifacts_output, "w") as tar:
            tar.add(artifacts_dir, arcname=".")
        except Exception as e:
          print(f"Failed to create artifacts archive: {e}")
          # Create an empty tar file if archiving failed, to satisfy Bazel outs
          with tarfile.open(args.artifacts_output, "w") as _:
            pass


if __name__ == "__main__":
  args = parse_args()
  launch_qemu(args)
  sys.exit(0)
