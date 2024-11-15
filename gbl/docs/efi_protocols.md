# GBL UEFI Protocols

This document lists every UEFI protocol that GBL may potentially use, and
describes the use case with any requirements.

## Upstream Protocols

These protocols are taken from an external source, typically the UEFI spec.

### BlockIoProtocol

* [`EFI_BLOCK_IO_PROTOCOL`](https://uefi.org/specs/UEFI/2.10/13_Protocols_Media_Access.html#efi-block-io-protocol)
* required

Used to read the GPT, load images from disk, and write data back to disk in
e.g. in fastboot.

This is required even if the Block I/O 2 Protocol is provided, as some use cases
might want to use this simpler API.

### BlockIo2Protocol

* [`EFI_BLOCK_IO2_PROTOCOL`](https://uefi.org/specs/UEFI/2.10/13_Protocols_Media_Access.html#block-i-o-2-protocol)
* optional: enables performance optimizations

If provided, GBL may use this protocol instead of the Block I/O Protocol as a
performance optimization; for example during fastboot flashing it may flash to
disk while concurrently receiving the next image over USB.

### DevicePathProtocol

* [`EFI_DEVICE_PATH_PROTOCOL`](https://uefi.org/specs/UEFI/2.10/10_Protocols_Device_Path_Protocol.html#efi-device-path-protocol)
* optional: enables logging the image path on GBL start

Used for logging the GBL image path to the console on load. This can be useful
as a "Hello world" proof-of-concept that GBL is running and can interact with
the UEFI protocols.

This logging requires all three of:
* Device Path Protocol
* Device Path to Text Protocol
* Loaded Image Protocol

### DevicePathToTextProtocol

* [`EFI_DEVICE_PATH_TO_TEXT_PROTOCOL`](https://uefi.org/specs/UEFI/2.10/10_Protocols_Device_Path_Protocol.html#device-path-to-text-protocol)
* optional: enables logging the image path on GBL start

Used for logging the GBL image path to the console on load. This can be useful
as a "Hello world" proof-of-concept that GBL is running and can interact with
the UEFI protocols.

This logging requires all three of:
* Device Path Protocol
* Device Path to Text Protocol
* Loaded Image Protocol

### LoadedImageProtocol

* [`EFI_LOADED_IMAGE_PROTOCOL`](https://uefi.org/specs/UEFI/2.10/09_Protocols_EFI_Loaded_Image.html#efi-loaded-image-protocol)
* optional: enables logging the image path on GBL start

Used for logging the GBL image path to the console on load. This can be useful
as a "Hello world" proof-of-concept that GBL is running and can interact with
the UEFI protocols.

This logging requires all three of:
* Device Path Protocol
* Device Path to Text Protocol
* Loaded Image Protocol

### Memory Allocation Services

* [Memory allocation services](https://uefi.org/specs/UEFI/2.10/07_Services_Boot_Services.html#memory-allocation-services)
* all required

Used by libavb for image verification.

Dynamic memory allocation can be minimized, but not completely eliminated, by
providing preallocated image buffers via the GBL Image Loading Protocol.

### RiscvBootProtocol

* [`RISCV_EFI_BOOT_PROTOCOL`](https://github.com/riscv-non-isa/riscv-uefi/blob/main/boot_protocol.adoc)
* required for RISC-V targets

Used to query the boot hart ID which is required to pass to the kernel.

### SimpleNetworkProtocol

* [`EFI_SIMPLE_NETWORK_PROTOCOL`](https://uefi.org/specs/UEFI/2.10/24_Network_Protocols_SNP_PXE_BIS.html#simple-network-protocol)
* optional: enables fastboot over TCP

Used to provide fastboot over TCP. This can be enabled by itself, or in
addition to fastboot over USB.

Currently if this protocol is available GBL will always start fastboot over TCP,
but in the future this functionality will be restricted to dev builds only.
Production devices should not expose fastboot over TCP.

GBL only uses the Simple Network Protocol, and will not use higher-level
protocols such as the TCP4/6 Protocols even if they are available.

### SimpleTextInputProtocol

* [`EFI_SIMPLE_TEXT_INPUT_PROTOCOL`](https://uefi.org/specs/UEFI/2.10/12_Protocols_Console_Support.html#simple-text-input-protocol)
* optional: enables the 'f' key to enter fastboot

This is currently used to look for the 'f' key on the serial line during boot,
which will trigger GBL to enter fastboot mode. If not provided, GBL will skip
this check.

We plan to remove this and instead use a more general protocol to allow devices
to specify their own custom fastboot triggers.

### SimpleTextOutputProtocol

* [`EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL`](https://uefi.org/specs/UEFI/2.10/12_Protocols_Console_Support.html#simple-text-output-protocol)
* required, but can be no-op

Used for logging and debugging. Implementations must provide this protocol, but
the functions may be no-ops.

## Community Protocols

Protocols defined by a community and used across the ecosystem, but not officially
part of the UEFI specification. None of these protocols are required.

### DtFixupProtocol

* original [proposal](https://github.com/U-Boot-EFI/EFI_DT_FIXUP_PROTOCOL)
* [upstream](https://github.com/u-boot/u-boot/blob/master/include/efi_dt_fixup.h)
* optional: allows FW to modify the final device tree

This protocol allows the firmware (FW) to inspect the final device tree and apply
necessary fixups.

GBL will validate the applied changes and prevent booting if any of the security
limitations (listed below) are violated. Any errors will be reported through the
UEFI log.

TODO (b/353272981): Add limitations

This protocol was proposed by U-Boot and is currently used by the Kernel UEFI stub.

## GBL Custom Protocols

These protocols are defined by GBL to provide specific functionality that is
not available elsewhere.

None of these custom protocols are required, with the intention that dev boards
that support a typical set of UEFI protocols should be able to use GBL without
any firmware modifications and still get some basic booting functionality.

However, without these protocols GBL will be missing key features such as
USB fastboot and verified boot, so production targets and more full-featured dev
boards will need to implement them.

### GblFastbootProtocol

* [`GBL_EFI_FASTBOOT_PROTOCOL`](./gbl_efi_fastboot_protocol.md)
* optional: enables custom fastboot functionality.

Used to provide an interface for
* Custom variables
* OEM commands
* Device lock/unlock controls
* Lock-contingent partition permission information
* User data erasure

### GblFastbootUsbProtocol

* [`GBL_EFI_FASTBOOT_USB_PROTOCOL`](./GBL_EFI_FASTBOOT_USB_PROTOCOL.md)
* optional: enables fastboot over USB

Used to provide fastboot over USB. This can be enabled by itself, or in
addition to fastboot over TCP.

### GblOsConfigurationProtocol

* [`GBL_EFI_OS_CONFIGURATION_PROTOCOL`](./gbl_os_configuration_protocol.md)
* optional: enables runtime fixups of OS data

Used for runtime fixups of data provided to the OS such as command line and
device tree. If not provided, the data in the OS images loaded from disk will
be used without modification.

### GblSlotProtocol

* TODO(b/359946695): link documentation
* optional: enables A/B slotted booting

Used to read and write A/B slot metadata. If not provided, GBL will
load from either the `_a` slot or a slotless boot partition.

All components that interact with A/B slot metadata must use the same format.
Typically these components are:

1. The UEFI firmware selecting which GBL slot to load
2. GBL selecting which OS slot to load
3. The OS update engine updating the metadata when a new version is downloaded

This protocol allows the device to implement its own A/B metadata format while
still allowing GBL to implement the boot flow logic.

### GblImageLoadingProtocol

* TODO(b/359946775): link documentation
* optional: enables loading images to predefined memory locations

Used to provide buffers to load the images for verification and boot process.

In addition this protocol provides a list of additional custom partitions to be
verified before booting, for boards that want to verify data in addition to the
standard boot partitions.

### GblAvbProtocol

* [`GBL_EFI_AVB_PROTOCOL`](./gbl_avb_protocol.md)
* Optional: enables AVB-related firmware callbacks.

This protocol delegates some of AVB-related logic to the firmware, including
tasks such as verifying public keys, handling verification results, and
managing the device’s secure state (e.g., ROT, lock state, rollback indexes,
etc.).
