# Generic Bootloader Library

This directory hosts sources for the generic bootloader library. A Bazel
workspace is setup for building the library as well as a EFI executable that
can be loaded directly from the firmware. To build the efi executable, enter
directory `gbl` and follow the instructions below:

Set environment variable `GBL_LLVM_CLANG_PATH` to the path of the LLVM clang
binary. The build system is tested with upstream
[Android LLVM prebuilts](https://android.googlesource.com/platform/prebuilts/clang/host/linux-x86/).
It is recommended that users do the same. For example, if you have a local
Android source checkout, you can set it to:

```
export GBL_LLVM_CLANG_PATH=<android source>/prebuilts/clang/host/linux-x86/clang-r475365b/bin/clang
```

Note: the clang version number in `clang-r475365b` might be different.

(TODO(b/292250955): The longer term plan is to build from a higher level super
project that already checked out LLVM prebuilts, i.e. either Android source
checkout, u-boot-mainline, or a new dedicated repo. This way we can provide
script that auto select the prebuilt.)

If you want to run EFI applications on QEMU, run the following to install
EDK, QEMU, u-boot prebuilt:

```
sudo apt-get install qemu-system ovmf u-boot-qemu
```

(TODO(b/292250955): The longer term plan is to integrate the efi image into
the cuttlefish workflow.)

To build for different architectures:

1. Build for x86_64:

    ```
    CARGO_BAZEL_REPIN=1 \
    bazel build //efi:gbl_efi \
        --platforms=//toolchain:gbl_uefi_x86_64 \
        --cpu=x86_64
    ```

    Note: `CARGO_BAZEL_REPIN=1` is necessary because the build system downloads
    third party crates and need to re-generate necessary Cargo.lock/BUILD files
    during build. A possible alternative is to pre-generate these dependencies
    and files and hosts them in a dedicated repo, similar to the approach by
    [Fuchsia](https://cs.opensource.google/fuchsia/fuchsia/+/main:/third_party/rust_crates/Cargo.toml)
    and [Pigweed](https://pigweed.googlesource.com/third_party/rust_crates)

    To test on QEMU:

    ```
    mkdir -p /tmp/esp/EFI/BOOT
    cp bazel-bin/efi/gbl.efi /tmp/esp/EFI/BOOT/bootx64.efi
    qemu-system-x86_64 -nographic \
        -drive if=pflash,format=raw,readonly=on,file=/usr/share/OVMF/OVMF_CODE.fd \
        -drive format=raw,file=fat:rw:/tmp/esp
    ```

1. Build for x86_32(i386/i686):

    ```
    CARGO_BAZEL_REPIN=1 \
    bazel build //efi:gbl_efi \
        --platforms=//toolchain:gbl_uefi_x86_32 \
        --cpu=x86_32
    ```

1. Build for aarch64

    ```
    CARGO_BAZEL_REPIN=1 \
    bazel build //efi:gbl_efi \
        --platforms=//toolchain:gbl_uefi_aarch64 \
        --cpu=aarch64
    ```

    To test on QEMU:

    ```
    mkdir -p /tmp/esp/EFI/BOOT
    cp bazel-bin/efi/gbl.efi /tmp/esp/EFI/BOOT/bootaa64.efi
    qemu-system-aarch64 -nographic -machine virt -m 1G -cpu cortex-a57 \
        -drive if=pflash,format=raw,readonly=on,file=/usr/share/AAVMF/AAVMF_CODE.fd \
        -drive format=raw,file=fat:rw:/tmp/esp
    ```

1. Build for riscv64

    ```
    CARGO_BAZEL_REPIN=1 \
    bazel build //efi:gbl_efi \
        --platforms=//toolchain:gbl_elf_riscv64 \
        --cpu=riscv64
    ```

    To test on QEMU:

    ```
    mkdir -p /tmp/esp/EFI/BOOT
    cp bazel-bin/efi/gbl.efi /tmp/esp/EFI/BOOT/bootriscv64.efi
    qemu-system-riscv64 -nographic -machine virt -m 256M \
        -bios /usr/lib/u-boot/qemu-riscv64/u-boot.bin \
        -drive format=raw,file=fat:rw:/tmp/esp,id=blk0 \
        -device virtio-blk-device,drive=blk0
    ```