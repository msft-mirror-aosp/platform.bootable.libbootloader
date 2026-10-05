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

"""Macros for instantiating QEMU tests."""

load("@rules_python//python:defs.bzl", "py_test")

def qemu_test(
        name,
        gbl,
        disk,
        test_script = None,
        gbl_launcher = "@gbl//tests/qemu/gbl_launcher:gbl_launcher_aarch64",
        qemu = "@vmm//:qemu/x86_64-linux-gnu/bin/gbl-qemu-system-aarch64",
        bios = "@vmm//:qemu/x86_64-linux-gnu/usr/share/qemu/edk2-aarch64-code.fd",
        vhost_device_vsock = "@vhost_device_vsock",
        runfiles = [],
        timeout = None,
        env = {},
        gdb = False,
        **kwargs):
    """Instantiates a QEMU test target.

    Args:
        name: The name of the test target.
        gbl: Target label for the GBL binary.
        disk: Target label (or list of target labels) for disk images to attach.
        test_script: Target label for the test Python script.
        gbl_launcher: Target label for the GBL launcher application.
        qemu: Target label for the QEMU binary.
        bios: Target label for the BIOS/UEFI firmware.
        vhost_device_vsock: Target label for vhost_device_vsock. Can be None.
        runfiles: Optional list of labels or [label, mapped_name] lists to
             include as runfiles.
        timeout: Optional Starlark integer timeout in seconds.
        env: Optional Starlark dictionary mapping custom environment variable
             names to their values.
        gdb: Whether to enable GDB debugging. When true, QEMU will wait for
             GDB to connect before starting GBL.
        **kwargs: General rule arguments passed to the underlying py_test.
    """

    # Collect input files required by the test launcher.
    data = [
        gbl_launcher,
        gbl,
        qemu,
        bios,
    ]

    # Normalize disk targets into a list and add to inputs.
    disks = []
    if disk != None:
        if type(disk) == "string":
            disks = [disk]
        elif type(disk) == "list" or type(disk) == "tuple":
            disks = list(disk)
    data.extend(disks)

    # Gather executable host tool dependencies.
    if test_script != None:
        data.append(test_script)
    if vhost_device_vsock != None:
        data.append(vhost_device_vsock)

    # Assemble the base Python test launcher command arguments.
    args = [
        "$(rootpath " + gbl_launcher + ")",
        "$(rootpath " + gbl + ")",
        "--test_name=" + name,
        "--qemu=$(rootpath " + qemu + ")",
        "--bios=$(rootpath " + bios + ")",
    ]

    # Add runfiles targets to data and format command args
    for item in runfiles:
        if type(item) == "string":
            target = item
            data.append(target)
            args.append("--runfile=$(rootpath {})".format(target))
        elif type(item) == "list" or type(item) == "tuple":
            if len(item) != 2:
                fail(
                    "Each runfiles item must be a string label or a " +
                    "list/tuple of 2 strings: [label, mapped_name]",
                )
            target = item[0]
            dest = item[1]
            data.append(target)
            args.append("--runfile={},$(rootpath {})".format(dest, target))
        else:
            fail("runfiles items must be strings or lists/tuples of strings")

    # Append disks
    for d in disks:
        args.append("--disk=$(rootpath " + d + ")")

    # If userspace vsock is enabled, add vsock device.
    if vhost_device_vsock != None:
        args.append("--vhost_device_vsock=$(rootpath " + vhost_device_vsock + ")")

    # If userspace test script is enabled, add test script.
    if test_script != None:
        args.append("--test_script=$(rootpath " + test_script + ")")

    # If timeout is set, add timeout.
    if timeout != None:
        args.append("--timeout=" + str(timeout))

    # If GDB debugging is enabled, configure QEMU to wait for GDB.
    if gdb:
        args.append("--gdb")

    py_test(
        name = name,
        srcs = ["@gbl//tests/qemu:qemu_launcher.py"],
        main = "@gbl//tests/qemu:qemu_launcher.py",
        args = select({
            "@gbl//tests/qemu:test_dependencies_exist": args,
            "//conditions:default": [],
        }),
        data = select({
            "@gbl//tests/qemu:test_dependencies_exist": data,
            "//conditions:default": [],
        }),
        env = env,
        target_compatible_with = select({
            "@gbl//tests/qemu:test_dependencies_exist": [],
            "//conditions:default": ["@platforms//:incompatible"],
        }),
        **kwargs
    )
