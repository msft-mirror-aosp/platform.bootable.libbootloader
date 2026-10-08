# GBL UEFI Protocols

This document lists every UEFI protocol that GBL may potentially use, and
describes the use case with any requirements.

## Upstream Protocols

These protocols are taken from an external source, typically the UEFI spec.

### BlockIoProtocol

- [`EFI_BLOCK_IO_PROTOCOL`][efi_block_io_protocol]
- required

Used to read the GPT, load images from disk, and write data back to disk in e.g.
in fastboot.

This is required even if the Block I/O 2 Protocol is provided, as some use cases
might want to use this simpler API.

### BlockIo2Protocol

- [`EFI_BLOCK_IO2_PROTOCOL`][efi_block_io2_protocol]
- optional: enables performance optimizations.

If provided, GBL may use this protocol instead of the Block I/O Protocol as a
performance optimization; for example during fastboot flashing it may flash to
disk while concurrently receiving the next image over USB.

### EraseBlockProtocol

- [`EFI_ERASE_BLOCK_PROTOCOL`][efi_erase_block_protocol]
- optional: enables block IO specific erase.

If provided, GBL may use this protocol when erasing data on a block device
instead of writing zeroes.

### DevicePathProtocol

- [`EFI_DEVICE_PATH_PROTOCOL`][efi_device_path_protocol]
- optional: enables logging the image path on GBL start

Used for logging the GBL image path to the console on load. This can be useful
as a "Hello world" proof-of-concept that GBL is running and can interact with
the UEFI protocols.

This logging requires all three of:

- Device Path Protocol
- Device Path to Text Protocol
- Loaded Image Protocol

### DevicePathToTextProtocol

- [`EFI_DEVICE_PATH_TO_TEXT_PROTOCOL`][efi_device_path_to_text_protocol]
- optional: enables logging the image path on GBL start

Used for logging the GBL image path to the console on load. This can be useful
as a "Hello world" proof-of-concept that GBL is running and can interact with
the UEFI protocols.

This logging requires all three of:

- Device Path Protocol
- Device Path to Text Protocol
- Loaded Image Protocol

### LoadedImageProtocol

- [`EFI_LOADED_IMAGE_PROTOCOL`][efi_loaded_image_protocol]
- optional: enables logging the image path on GBL start

Used for logging the GBL image path to the console on load. This can be useful
as a "Hello world" proof-of-concept that GBL is running and can interact with
the UEFI protocols.

This logging requires all three of:

- Device Path Protocol
- Device Path to Text Protocol
- Loaded Image Protocol

### InitrdDevicePathProtocol

- [`LINUX_EFI_INITRD_MEDIA_GUID`][linux_efi_initrd_media_guid]
- optional: used by the Linux kernel efi boot stub to load the initrd

GBL installs the Initrd Device Path Protocol on the initrd device handle, so
the Linux kernel efi boot stub can identify it.

### LoadFile2Protocol

- [`EFI_LOAD_FILE2_PROTOCOL`][efi_load_file2_protocol]
- optional: used by the Linux kernel efi boot stub to load the initrd

GBL installs a Load File 2 Protocol on the Linux initrd device handle, and the
Linux kernel efi boot stub uses it to load the ramdisk.

### ServiceBindingProtocol

- [`EFI_SERVICE_BINDING_PROTOCOL`][efi_service_binding_protocol]
- optional: used to create bound handles for certain protocols.

The EFI_SERVICE_BINDING_PROTOCOL provides functionality to create and destroy
child handles with new protocols installed on them.

Note: the EFI_SERVICE_BINDING_PROTOCOL does not have its own GUID. Drivers for
protocols that are opened by service binding define GUIDs for a protocol that
has the same structural interface as the EFI_SERVICE_BINDING_PROTOCOL. Once the
corresponding EFI_SERVICE_BINDING_PROTOCOL has been opened, a call to
`CreateChild()` will generate a handle bound to the desired protocol.

### Hash2Protocol

- [`EFI_HASH2_PROTOCOL`][efi_hash2_protocol]
- optional: enables optimized, incremental cryptographic hash algorithms

Used as part of AVB signature checking. Implementations can use device specific
extensions to accelerate cryptographic hash functions. If not present GBL will
use hash implementations provided by BoringSSL.

Note: handles are bound to the EFI_HASH2_PROTOCOL via the
EFI_SERVICE_BINDING_PROTOCOL. See the documentation for EFI_HASH2_PROTOCOL and
EFI_SERVICE_BINDING_PROTOCOL for more information.

### Memory Allocation Services

- [Memory allocation services][efi_memory_allocation_services]
- required

Used by libavb for image verification.

Dynamic memory allocation can be minimized, but not completely eliminated, by
providing preallocated image buffers via the
[GBL Boot Memory Protocol](./gbl_efi_boot_memory_protocol.md).

### RiscvBootProtocol

- [`RISCV_EFI_BOOT_PROTOCOL`][riscv_efi_boot_protocol]
- required for RISC-V targets

Used to query the boot hart ID which is required to pass to the kernel.

### SimpleNetworkProtocol

- [`EFI_SIMPLE_NETWORK_PROTOCOL`][efi_simple_network_protocol]
- optional: enables fastboot over TCP

Used to provide fastboot over TCP. This can be enabled by itself, or in addition
to fastboot over USB.

Currently if this protocol is available GBL will always start fastboot over TCP,
but in the future this functionality will be restricted to dev builds only.
Production devices should not expose fastboot over TCP.

GBL only uses the Simple Network Protocol, and will not use higher-level
protocols such as the TCP4/6 Protocols even if they are available.

### SimpleTextInputProtocol

- [`EFI_SIMPLE_TEXT_INPUT_PROTOCOL`][efi_simple_text_input_protocol]
- optional: enables the 'f' key to enter fastboot

This is currently used to look for the 'f' key on the serial line during boot,
which will trigger GBL to enter fastboot mode. If not provided, GBL will skip
this check.

We plan to remove this and instead use a more general protocol to allow devices
to specify their own custom fastboot triggers.

### SimpleTextOutputProtocol

- [`EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL`][efi_simple_text_output_protocol]
- required, but can be no-op

Used for logging and debugging. Implementations must provide this protocol, but
the functions may be no-ops.

### TimestampProtocol

- [`EFI_TIMESTAMP_PROTOCOL`][efi_timestamp_protocol]
- optional: enables performance analysis.

### RandomNumberGeneratorProtocol

- [`EFI_RNG_PROTOCOL`][efi_rng_protocol]
- required: enables dynamic stack canary values and configures KASLR and
  bootloader entropy

GBL uses the EFI_RNG_PROTOCOL to set a new random value for the global stack
canary, and to propagate the `kaslr-seed` and `rng-seed` FDT properties to
initialize HLOS entropy.

For development builds, the RNG protocol is technically optional: if the
protocol is absent a random but static value will be used instead to initialize
the global stack canary value. The `kaslr-seed` and `rng-seed` FDT properties
will not be propagated.

## Community Protocols

Protocols defined by a community and used across the ecosystem, but not
officially part of the UEFI specification. None of these protocols are required.

### DtFixupProtocol

- original [proposal][dt_fixup_proposal]
- [u-boot][u_boot_dt_fixup]
- optional: allows FW to modify the final device tree

This protocol allows the firmware (FW) to inspect the final device tree and
apply necessary fixups.

Proposed to be used by FW to inspect and update device tree including Kernel
command line. GBL will validate the applied changes and prevent booting if any
of the security limitations (listed below) are violated. Error details will be
reported through the UEFI log.

TODO (b/353272981): Add limitations

## GBL Custom Protocols

These protocols are defined by GBL to provide specific functionality that is not
available elsewhere.

### Dev vs Prod

For GBL dev builds, none of these protocols are required. The goal is that dev
boards should be able to get at least rudimentary Android boot support with
an out-of-the-box UEFI implementation, no GBL customizations required. This
also allows more iterative development, bringing up GBL protocols one at a time
on a dev build.

GBL prod builds do require some GBL-specific protocols, but not all. Specific
protocol requirements are listed below, but the general guideline is that
security-critical protocols such as verified boot are required for prod, whereas
customization protocols such as the fastboot protocol are optional.

### GBL Custom Protocol Revisions

All GBL custom protocols have an unsigned 64 bit revision as their first field.
The semantics of the field are explained by the following macros:

```c
#define GBL_PROTOCOL_MAJOR_REV(x) (((x) >> 16 ) & 0xFFFF)
#define GBL_PROTOCOL_MINOR_REV(x) ((x) & 0xFFFF)

#define GBL_PROTOCOL_REVISION(major, minor) ((((major) & 0xFFFF) << 16) | ((minor) & 0xFFFF))
```

The minor revision is the 2 least significant bytes, and the major revision is
the second 2 least significant bytes.

Note: While the revision field is 64 bits wide, only the least significant 32
bits are used to define the major and minor version. The most significant 32
bits are reserved for future use.

Note: Major revisions of `0` indicate that the protocol is still in development
and backwards compatibility is not guaranteed.

Note: Once a protocol reaches major revision `1`, its specification is stable
and all subsequent revisions remain backwards compatible. A change that breaks
ABI compatibility requires a new GUID and a fresh revision sequence.

### GblFastbootProtocol

- [`GBL_EFI_FASTBOOT_PROTOCOL`](./gbl_efi_fastboot_protocol.md)
- optional: enables custom fastboot functionality.

Used to provide an interface for

- Custom variables
- OEM commands
- Device lock/unlock controls
- Lock-contingent partition permission information
- User data erasure

### GblFastbootTransportProtocol

- [`GBL_EFI_FASTBOOT_TRANSPORT_PROTOCOL`](./gbl_efi_fastboot_transport_protocol.md)
- optional: enables fastboot over platform defined channels such as USB.

This can be enabled by itself, or in addition to fastboot over TCP.

### GblOsConfigurationProtocol

- [`GBL_EFI_OS_CONFIGURATION_PROTOCOL`](./gbl_efi_os_configuration_protocol.md)
- optional: enables runtime fixups of OS data

Used for device tree and FIT configuration selection, bootconfig and kernel
command line fixups. If not provided, the data from boot partitions will be used
without FW-specific modifications.

### GblBootControlProtocol

- [`GBL_EFI_BOOT_CONTROL_PROTOCOL`](./gbl_efi_boot_control_protocol.md)
- required: enables A/B slotted booting and boot mode selection

Used to read and write A/B slot metadata.

All components that interact with A/B slot metadata must use the same format.
Typically these components are:

1. The UEFI firmware selecting which GBL slot to load
2. GBL selecting which OS slot to load
3. The OS update engine updating the metadata when a new version is downloaded

This protocol allows the device to implement its own A/B metadata format while
still allowing GBL to implement the boot flow logic.

### GblBootMemoryProtocol

- [`GBL_EFI_BOOT_MEMORY_PROTOCOL`](./gbl_efi_boot_memory_protocol.md)
- Optional: Provides reserved buffers for loading/preloaded partition image,
  assembling finalized kernel, ramdisk, fdt, pvmfw image and downloading in
  fastboot.

### GblAvbProtocol

- [`GBL_EFI_AVB_PROTOCOL`](./gbl_efi_avb_protocol.md)
- required for production devices: enables AVB-related firmware callbacks.

This protocol delegates some of AVB-related logic to the firmware, including
tasks such as verifying public keys, handling verification results, and managing
the device’s secure state (e.g., ROT, lock state, rollback indexes, etc.).

### GblAvfProtocol

- [`GBL_EFI_AVF_PROTOCOL`](./gbl_efi_avf_protocol.md)
- optional: enables AVF-related firmware callbacks.

This protocol delegates AVF-related logic to the firmware to ensure the
integrity of pVMs running under the Android Virtualization Framework.

### GblDebugProtocol

- [`GBL_EFI_DEBUG_PROTOCOL`](./gbl_efi_debug_protocol.md)
- optional: callbacks to facilitate debugging.

This protocol provides a callback for GBL to indicate that a fatal error has
occurred and gives the firmware an opportunity to save state internally before
GBL attempts to reset the system.

## GBL UEFI Variables

UEFI variables defined and used by GBL.

### Vendor GUID

| Name                       | Value                                                                            |
| :------------------------- | :------------------------------------------------------------------------------- |
| `EFI_GLOBAL_VARIABLE_GUID` | `{0x8be4df61, 0x93ca, 0x11d2, {0xaa, 0x0d, 0x00, 0xe0, 0x98, 0x03, 0x2b, 0x8c}}` |
| `GBL_EFI_VENDOR_GUID`      | `{0x5a6d92f3, 0xa2d0, 0x4083, {0x91, 0xa1, 0xa5, 0x0f, 0x6c, 0x3d, 0x98, 0x30}}` |

### gbl_debug

- Vendor GUID: `EFI_GLOBAL_VARIABLE_GUID`
- Feature flag: `gdb_debug` or `always-wait-gdb`

If this variable is defined, enable GDB debugger support.

### gbl_fw_api_level

- Vendor GUID: `GBL_EFI_VENDOR_GUID`
- Required

This variable must be set to the API level of the platform firmware, indicating
the API level of the vendor software. This should have the same value as the
[`ro.board.api_level`][android_vendor_api_level] system property in Android.
This variable must be read-only and readable from GBL.

GBL shall use this variable to decide the expected feature level and capability
of the firmware protocols. This variable can be updated when the platform
firmware is updated.

### gbl_os_boot_fuchsia

- Vendor GUID: `GBL_EFI_VENDOR_GUID`
- Feature flag: `fuchsia`

If this variable is defined, boot as Fuchsia OS.

[efi_block_io_protocol]:
  https://uefi.org/specs/UEFI/2.10/13_Protocols_Media_Access.html#efi-block-io-protocol
[efi_block_io2_protocol]:
  https://uefi.org/specs/UEFI/2.10/13_Protocols_Media_Access.html#block-i-o-2-protocol
[efi_erase_block_protocol]:
  https://uefi.org/specs/UEFI/2.10/13_Protocols_Media_Access.html#erase-block-protocol
[efi_device_path_protocol]:
  https://uefi.org/specs/UEFI/2.10/10_Protocols_Device_Path_Protocol.html#efi-device-path-protocol
[efi_device_path_to_text_protocol]:
  https://uefi.org/specs/UEFI/2.10/10_Protocols_Device_Path_Protocol.html#device-path-to-text-protocol
[efi_loaded_image_protocol]:
  https://uefi.org/specs/UEFI/2.10/09_Protocols_EFI_Loaded_Image.html#efi-loaded-image-protocol
[efi_service_binding_protocol]:
  https://uefi.org/specs/UEFI/2.11/11_Protocols_UEFI_Driver_Model.html#efi-service-binding-protocol
[efi_hash2_protocol]:
  https://uefi.org/specs/UEFI/2.11/37_Secure_Technologies.html#efi-hash2-protocol
[efi_memory_allocation_services]:
  https://uefi.org/specs/UEFI/2.10/07_Services_Boot_Services.html#memory-allocation-services
[riscv_efi_boot_protocol]:
  https://github.com/riscv-non-isa/riscv-uefi/blob/main/boot_protocol.adoc
[efi_simple_network_protocol]:
  https://uefi.org/specs/UEFI/2.10/24_Network_Protocols_SNP_PXE_BIS.html#simple-network-protocol
[efi_simple_text_input_protocol]:
  https://uefi.org/specs/UEFI/2.10/12_Protocols_Console_Support.html#simple-text-input-protocol
[efi_simple_text_output_protocol]:
  https://uefi.org/specs/UEFI/2.10/12_Protocols_Console_Support.html#simple-text-output-protocol
[efi_timestamp_protocol]:
  https://uefi.org/specs/UEFI/2.10/39_Micellaneous_Protocols.html?highlight=timestamp#efi-timestampprotocol-micellaneous-protocols
[efi_rng_protocol]:
  https://uefi.org/specs/UEFI/2.11/37_Secure_Technologies.html#random-number-generator-protocol
[dt_fixup_proposal]: https://github.com/U-Boot-EFI/EFI_DT_FIXUP_PROTOCOL
[u_boot_dt_fixup]:
  https://github.com/u-boot/u-boot/blob/master/include/efi_dt_fixup.h
[android_vendor_api_level]:
  https://source.android.com/docs/core/architecture/api-flags
[efi_load_file2_protocol]:
  https://uefi.org/specs/UEFI/2.11/13_Protocols_Media_Access.html#efi-load-file-2-protocol
[linux_efi_initrd_media_guid]:
  https://www.kernel.org/doc/html/v6.6/arch/x86/boot.html
