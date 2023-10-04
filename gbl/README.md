# Generic Bootloader Library

This directory hosts the Generic Bootloader Library project. A Bazel
workspace is setup for building the library as well as an EFI executable that
can be loaded directly from the firmware.

## Build

The library and the EFI application can be built using the
[build_gbl.py](tools/build/build_gbl.py) script. There are two ways of invoking
it:

### Build from AOSP

If this repo is checked out from a full
[AOSP](https://source.android.com/docs/setup/download/downloading) or
[Android Bootloader](https://source.android.com/docs/setup/create/cuttlefish-bootloader-dev#develop-bootloader)
super project, you can simply run

```.sh
python3 build_gbl.py <output directory>
```

The script will auto select the needed dependencies from the super project.
After build completes, the EFI image will be available in
`<output director>/gbl/`. By default, the script builds for all of `x86_64`,
`x86_32`, `aarch64` and `riscv64` architectures. If you only want to build for
a subset, append option `--arch <x86_64|x86_32|aarch64|riscv64>` one by one.

### Build without AOSP

If a full super project checkout is too heavy-weight, use the following options,
which only requires a Bazel binary.

```
python3 build_gbl.py \
    --bazel=<path to Bazel executable> \
    <output directory>
```

The above command will automatically download necessary toolchains from
Android prebuilts.

## Run on emulator

### Run on Cuttlefish

If you have a main AOSP checkout and is setup to run
[Cuttlefish](https://source.android.com/docs/setup/create/cuttlefish), you can
run the EFI image directly with it:

```
launch_cvd --android_efi_loader=<path to the EFI image> ...
```

The above uses the same setting as a normal `launch_cvd` run, except that
insted of booting Android directly, the emulator first hands off to your EFI
application.

Note: For x86 platform, use the EFI image built for `x86_32`.

### Run on standalone QEMU

If you simply want to test the EFI image as a standalone application on QEMU
directly:

1. Install EDK, QEMU and u-boot prebuilts

   ```
   sudo apt-get install qemu-system ovmf u-boot-qemu
   ```

1. Depending on the target achitecture you want to run:

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
