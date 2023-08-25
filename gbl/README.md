# Generic Bootloader Library

This directory hosts sources for the generic bootloader library. A Bazel
workspace is setup for building the library as well as a EFI executable that
can be loaded directly from the firmware. To build the efi executable, enter
directory `libgbl` and run the following:

1. Build for x86_64:

    ```
    bazel build //efi:gbl_efi \
        --platforms=//toolchain:gbl_uefi_x86_64 \
        --cpu=x86_64
    ```

    The above looks for system installed LLVM toolchain at `/usr/bin/clang++`
    by default. To use a different one, define environment variable
    `GBL_LLVM_CLANG_PATH=<path to clang++>` before running the command.

    TODO(b/292250955): Android has a
    [git repo](https://android.googlesource.com/platform/prebuilts/clang/host/linux-x86/)
    that hosts LLVM prebuilts. The next step is to investigate
    integrating these in a `repo init` checkout, where the LLVM prebuilts and this
    repo can be checkedout togehter. Then we can point bazel to the LLVM
    prebuilts for hermetic build, without depending on user system installed
    LLVM.

    To test on QEMU:

    ```
    mkdir -p /tmp/esp/EFI/BOOT
    cp bazel-bin/efi/gbl.efi /tmp/esp/EFI/BOOT/bootx64.efi
    qemu-system-x86_64 -nographic \
        -drive if=pflash,format=raw,readonly=on,file=/usr/share/OVMF/OVMF_CODE.fd \
        -drive format=raw,file=fat:rw:/tmp/esp
    ```

    (QEMU and OVMF prebuilts can be installed by
    "`sudo apt-get install qemu-system ovmf`")

     TODO(b/292250955): The longer term plan is to integrate the efi image into
     the cuttlefish workflow.

1. Build for x86_32(i386/i686):

    ```
    bazel build //efi:gbl_efi \
        --platforms=//toolchain:gbl_uefi_x86_32 \
        --cpu=x86_32
    ```

1. Build for aarch64

    ```
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