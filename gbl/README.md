# Generic Bootloader Library

This directory hosts the Generic Bootloader Library project. A Bazel
workspace is setup for building the library as well as an EFI executable that
can be loaded directly from the firmware.

## Get source tree and build

To successfully get and build the tree your machine must have the following dependencies installed:

```
# repo to work with android repositories (https://source.android.com/docs/setup/reference/repo)
# bazel-bootstrap to build (https://bazel.build/)
sudo apt install repo bazel-bootstrap
```

The GBL project are intended to be built from the
[Android UEFI Manifest](https://android.googlesource.com/kernel/manifest/+/refs/heads/uefi-gbl-mainline/default.xml)
checkout:

```
repo init -u https://android.googlesource.com/kernel/manifest -b uefi-gbl-mainline
repo sync -j16
```

To build the EFI application:

```
./tools/bazel run //bootable/libbootloader:gbl_efi_dist --extra_toolchains=@gbl//toolchain:all
```

The above builds the EFI application for all of `x86_64`, `x86_32`, `aarch64`
and `riscv64` platforms.

To run the set of unit tests:

```
./tools/bazel test @gbl//tests --extra_toolchains=@gbl//toolchain:all
```

## IDE Setup

For rust development, we recommend use VSCode + rust-analyzer plugin.

rust-analyzer requires `rust-project.json` to work properly. Luckily, bazel has
support for generating `rust-project.json`:

```
# Currently ./tools/bazel must be in PATH for this target to build.
PATH=$PATH:~/android/uefi-gbl-mainline/tools/

./tools/bazel run @rules_rust//tools/rust_analyzer:gen_rust_project --norepository_disable_download @gbl//efi/...
```

`@gbl//efi/...` is the target to generate rust project for, here it means
"everything under @gbl//efi/ directory" . Omitting the target specifier would
result in analyzing "@/..." , which would most likely fail due to some obscure
reason. Should targets get moved around in the future, this path spec also need
to be updated.

After generating `rust-project.json`, you would notice that your IDE still
doesn't offer auto completion. This is because some source file paths pointing
to bazel-output dir, and you are most likely editing source files in
`bootable/libbootloader/gbl`. In addition, the generated rust-project.json sets
"cfg=test" for all targets, which causes certain dependency graph to resolve
incorrectly. To fix this, run

```
python3 bootable/libbootloader/gbl/rewrite_rust_project_path.py rust-project.json
```

And reload your IDE.

## Run the EFI application

### Boot Android on Cuttlefish

If you have a main AOSP checkout and is setup to run
[Cuttlefish](https://source.android.com/docs/setup/create/cuttlefish), you can
run the EFI image directly with:

```
cvd start --android_efi_loader=<path to the EFI image> ...
```

The above uses the same setting as a normal `cvd start` run, except that
instead of booting Android directly, the emulator first hands off to the EFI
application, which will take over booting android.

Note: For x86 platform, use the EFI image built for `x86_32`.

### Boot Fuchsia on Vim3

Booting Fuchsia on a Vim3 development board is supported. To run the
application:

1. Complete all
[bootstrap steps](https://fuchsia.dev/fuchsia-src/development/hardware/khadas-vim3?hl=en)
to setup Vim3 as a Fuchsia device.
2. Reboot the device into fastboot mode.
3. Run fastboot command:
```
fastboot stage <path to the EFI binary> && fastboot oem run-staged-efi
```

### Run on standalone QEMU

If you want to test the EFI image directly on QEMU with your custom
configurations:

1. Install EDK, QEMU and u-boot prebuilts

   ```
   sudo apt-get install qemu-system ovmf u-boot-qemu
   ```

1. Depending on the target architecture you want to run:

   For `x86_64`:
   ```
   mkdir -p /tmp/esp/EFI/BOOT && \
   cp <path to EFI image> /tmp/esp/EFI/BOOT/bootx64.efi && \
   qemu-system-x86_64 -nographic \
       -drive if=pflash,format=raw,readonly=on,file=/usr/share/OVMF/OVMF_CODE.fd \
       -drive format=raw,file=fat:rw:/tmp/esp
   ```

   For `aarch64`:
   ```
   mkdir -p /tmp/esp/EFI/BOOT && \
   cp <path to EFI image> /tmp/esp/EFI/BOOT/bootaa64.efi && \
   qemu-system-aarch64 -nographic -machine virt -m 1G -cpu cortex-a57 \
       -drive if=pflash,format=raw,readonly=on,file=/usr/share/AAVMF/AAVMF_CODE.fd \
       -drive format=raw,file=fat:rw:/tmp/esp
   ```

   For `riscv64`:
   ```
   mkdir -p /tmp/esp/EFI/BOOT && \
   cp <path to EFI image> /tmp/esp/EFI/BOOT/bootriscv64.efi && \
   qemu-system-riscv64 -nographic -machine virt -m 256M \
       -bios /usr/lib/u-boot/qemu-riscv64/u-boot.bin \
       -drive format=raw,file=fat:rw:/tmp/esp,id=blk0 \
       -device virtio-blk-device,drive=blk0
   ```

### Boot Fuchsia on emulator

1. Make sure Fuchsia target pass control to GBL.

   Set path to GBL binary here: [fuchsia/src/firmware/gigaboot/cpp/backends.gni : gigaboot_gbl_efi_app](https://cs.opensource.google/fuchsia/fuchsia/+/main:src/firmware/gigaboot/cpp/backends.gni;l=25?q=gigaboot_gbl_efi_app)

   E.g. in `fuchsia/src/firmware/gigaboot/cpp/backends.gni`:
   ```
   $ cat ./fuchsia/src/firmware/gigaboot/cpp/backends.gni
   ...
   declare_args() {
      ...
      gigaboot_gbl_efi_app = "<path to EFI image>/gbl_x86_64.efi"
   }
   ```

   Or in `fx set`:
   ```
   fx set core.x64 --args=gigaboot_gbl_efi_app='"<path to EFI image>/gbl_x86_64.efi"'
   ```

2. Build: (this has to be done every time if EFI app changes)

   `fx build`

3. Run emulator in UEFI mode with raw disk

   ```
   fx qemu -a x64 --uefi --disktype=nvme -D ./out/default/obj/build/images/disk.raw
   ```

## EFI Protocols

List of EFI protocols used by GBL and a brief description of each [here](./docs/efi_protocols.md).
