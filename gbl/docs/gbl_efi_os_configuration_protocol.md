# GBL EFI OS Configuration Protocol

|                |            |
| :------------- | :--------- |
| **Status**     | Stable     |
| **Created**    | 2024-07-17 |
| **Stabilized** | 2026-05-22 |

## GBL_EFI_OS_CONFIGURATION_PROTOCOL

### Summary

This protocol provides a mechanism for the EFI firmware to build and update OS
configuration data:

- device tree (select components with which to build the final one)
- bootconfig (append fixups)
- FIT configuration (select the configuration corresponding to the platform)

GBL will load and verify the data provided by boot partitions, and then call
these protocol functions to give the firmware a chance to construct and adjust
the data as needed for the particular device. Device tree fixups (including
kernel command line) are handled by the `EFI_DT_FIXUP` protocol.

If no runtime modifications are necessary, this protocol may be left
unimplemented, in which case GBL autoselection logic will be used. Refer to
[`SelectDeviceTrees()`][select_device_trees] description for more details.

### GUID

```c
// {dda0d135-aa5b-42ff-85ac-e3ad6efb4619}
#define GBL_EFI_OS_CONFIGURATION_PROTOCOL_GUID       \
  {                                                  \
    0xdda0d135, 0xaa5b, 0x42ff, {                    \
      0x85, 0xac, 0xe3, 0xad, 0x6e, 0xfb, 0x46, 0x19 \
    }                                                \
  }
```

### Revision Number

```c
#define GBL_EFI_OS_CONFIGURATION_PROTOCOL_REVISION GBL_PROTOCOL_REVISION(1, 0)
```

See [GBL Custom Protocol Revisions][custom_protocol_revisions] for details about
protocol revisions.

### Protocol Interface Structure

```c
typedef struct _GBL_EFI_OS_CONFIGURATION_PROTOCOL {
  UINT64                           Revision;
  GBL_EFI_FIXUP_BOOTCONFIG         FixupBootConfig;
  GBL_EFI_SELECT_DEVICE_TREES      SelectDeviceTrees;
  GBL_EFI_SELECT_FIT_CONFIGURATION SelectFitConfiguration;
} GBL_EFI_OS_CONFIGURATION_PROTOCOL;
```

### Parameters

#### Revision

The revision to which the `GBL_EFI_OS_CONFIGURATION_PROTOCOL` adheres. All
future revisions must be backwards compatible. If a future version is not
backwards compatible, a different GUID must be used.

#### FixupBootConfig

Applies bootconfig fixups. See [`FixupBootConfig()`][fixup_bootconfig] for more
information.

#### SelectDeviceTrees

Selects components such as base device tree and overlays to build the final
device tree. See [`SelectDeviceTrees()`][select_device_trees] for more
information.

#### SelectFitConfiguration

Selects the FIT configuration corresponding to the platform. See
[`SelectFitConfiguration()`][select_fit_configuration] for more information.

## GBL_EFI_OS_CONFIGURATION_PROTOCOL.FixupBootConfig()

### Summary

Allows the firmware to append device-specific parameters to the bootconfig built
by GBL.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI *GBL_EFI_FIXUP_BOOTCONFIG)(
  IN GBL_EFI_OS_CONFIGURATION_PROTOCOL *Self,
  IN UINTN                             BootConfigSize,
  IN CONST CHAR8                       *BootConfig,
  IN OUT UINTN                         *FixupBufferSize,
  OUT CHAR8                            *Fixup
  );
```

### Parameters

All parameters are valid only for the duration of the function call and must not
be retained by the protocol.

#### Self

A pointer to the `GBL_EFI_OS_CONFIGURATION_PROTOCOL` instance.

#### BootConfigSize

Specifies the size of the bootconfig provided by `BootConfig`.

#### BootConfig

A pointer to the bootconfig built by GBL so far. Guaranteed to contain
`BootConfigSize` bytes of bootconfig parameters, without the bootconfig trailer
or a null terminator.

#### FixupBufferSize

On input, points to the size of the provided `Fixup` buffer. The firmware is
free to provide fixup data up to this size.

On output, the firmware must update it according to the return code:

- `EFI_SUCCESS`: the size of the provided fixup data. GBL consumes exactly this
  number of bytes from `Fixup`.
- `EFI_BUFFER_TOO_SMALL`: the size required to fit the fixup data. GBL discards
  any data written to `Fixup` and either repeats the call with a larger buffer
  or fails to boot.
- Other: ignored by GBL.

#### Fixup

A pointer to a pre-allocated buffer of `FixupBufferSize` bytes to be filled by
the firmware with the bootconfig fixup.

### Description

This method allows the firmware to append device-specific parameters to the
[bootconfig][bootconfig] built by GBL.

GBL appends the fixup verbatim, without parsing or validating it, so every byte
becomes part of the final bootconfig. A trailing newline is added if missing.
The override operator `:=` may be used to re-define values provided by GBL.

The fixup must meet the following criteria:

1. Must consist of bootconfig parameters only, without the bootconfig trailer or
   a null terminator.
2. Must be derived from trusted data only and must not re-define verified boot
   parameters, since the OS trusts bootconfig as bootloader-provided data.

If no fixup is needed, `FixupBufferSize` can be set to `0` or `EFI_UNSUPPORTED`
can be returned - both have the same effect.

### Status Codes Returned

| Return Code             | Semantics                                                                               |
| :---------------------- | :-------------------------------------------------------------------------------------- |
| `EFI_SUCCESS`           | Fixup was successfully written.                                                         |
| `EFI_UNSUPPORTED`       | No fixup is provided; the bootconfig generated by GBL will be used as-is.               |
| `EFI_BUFFER_TOO_SMALL`  | `Fixup` buffer is too small; `FixupBufferSize` has been updated with the required size. |
| `EFI_INVALID_PARAMETER` | Unexpected input; GBL will refuse to boot.                                              |

## GBL_EFI_OS_CONFIGURATION_PROTOCOL.SelectDeviceTrees()

### Summary

Inspects device trees and overlays loaded by GBL to determine which ones to use.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI *GBL_EFI_SELECT_DEVICE_TREES)(
  IN GBL_EFI_OS_CONFIGURATION_PROTOCOL *Self,
  IN UINTN                             NumDeviceTrees,
  IN OUT GBL_EFI_VERIFIED_DEVICE_TREE  *DeviceTrees
  );
```

### Related Definitions

#### GBL_EFI_DEVICE_TREE_SOURCE

```c
enum {
  GBL_EFI_DEVICE_TREE_SOURCE_BOOT,
  GBL_EFI_DEVICE_TREE_SOURCE_VENDOR_BOOT,
  GBL_EFI_DEVICE_TREE_SOURCE_DTBO,
  GBL_EFI_DEVICE_TREE_SOURCE_DTB,
};

typedef UINT32 GBL_EFI_DEVICE_TREE_SOURCE;
```

#### GBL_EFI_DEVICE_TREE_TYPE

```c
enum {
  GBL_EFI_DEVICE_TREE_TYPE_DEVICE_TREE,
  GBL_EFI_DEVICE_TREE_TYPE_OVERLAY,
  GBL_EFI_DEVICE_TREE_TYPE_PVM_DA_OVERLAY,
};

typedef UINT32 GBL_EFI_DEVICE_TREE_TYPE;
```

#### GBL_EFI_DEVICE_TREE_METADATA

```c
typedef struct {
  GBL_EFI_DEVICE_TREE_SOURCE Source;
  GBL_EFI_DEVICE_TREE_TYPE   Type;
  UINT32                     Id;
  UINT32                     Rev;
  UINTN                      CustomSize;
  CONST UINT8                *Custom;
} GBL_EFI_DEVICE_TREE_METADATA;
```

##### Source

A `GBL_EFI_DEVICE_TREE_SOURCE` value identifying the origin partition of the
loaded device tree component.

##### Type

A `GBL_EFI_DEVICE_TREE_TYPE` value identifying the type of device tree
component.

##### Id

The ID value from the `dttable` `entry.id`. Zero when the component is loaded as
a raw image without a `dttable` structure.

##### Rev

The revision value from the `dttable` `entry.rev`. Zero when the component is
loaded as a raw image without a `dttable` structure.

##### CustomSize

Size, in bytes, of the `Custom` buffer. Zero when no custom metadata is
associated with the component.

##### Custom

Pointer to the buffer of `CustomSize` bytes with component metadata, or `NULL`
if no custom metadata is associated with the component.

#### GBL_EFI_VERIFIED_DEVICE_TREE

```c
typedef struct {
  GBL_EFI_DEVICE_TREE_METADATA Metadata;
  CONST VOID                   *DeviceTree;
  BOOLEAN                      Selected;
} GBL_EFI_VERIFIED_DEVICE_TREE;
```

##### Metadata

The metadata associated with this device tree component.

##### DeviceTree

Pointer to the device tree or overlay buffer. Guaranteed to be 8-byte aligned
and non-`NULL`.

##### Selected

Set to `TRUE` by the firmware if this component must be included in the final
device tree.

### Parameters

All parameters are valid only for the duration of the function call and must not
be retained by the protocol.

#### Self

A pointer to the `GBL_EFI_OS_CONFIGURATION_PROTOCOL` instance.

#### NumDeviceTrees

The number of device tree components in the provided `DeviceTrees` array.

#### DeviceTrees

Pointer to an array containing loaded device tree components along with
associated metadata to distinguish device tree component types
(`GBL_EFI_DEVICE_TREE_METADATA.Type`) and identify the source from which it's
loaded (`GBL_EFI_DEVICE_TREE_METADATA.Source`).

### Description

A single set of Android build artifacts may include multiple device tree
components distributed across Android boot partitions such as `boot`,
`vendor_boot`, `dtb`, `dtbo`, etc. It is common practice to leverage this
capability to support multiple SoCs using the same set of artifacts, with the
appropriate device tree selected dynamically at the bootloader stage.

To support this use case, GBL loads all available device tree components and
provides them to the firmware along with associated metadata, enabling selection
via this UEFI call.

Firmware can use the `GBL_EFI_DEVICE_TREE_METADATA.Type` metadata field to
distinguish between different types of device tree components:

1. Device trees (`DEVICE_TREE`) — Base device tree.
2. Device tree overlays (`OVERLAY`) — Overlays to be applied to a base device
   tree.
3. Device assignment overlays (`PVM_DA_OVERLAY`) — Overlays to be applied to
   pVMs managed by [AVF][avf]. Device assignment overlay is distinguished from
   the regular host overlay by 31st bit of `dttable` `entry.id`:

   ```c
   bool entry_is_vm = (entry.id >> 31) & 0x1;
   ```

   It also affects the exposed `GBL_EFI_DEVICE_TREE_METADATA.Id` value since
   it's a pure copy of corresponding `entry.id`.

The `GBL_EFI_DEVICE_TREE_METADATA.Source` field identifies the origin partition
of each loaded device tree component (`BOOT`, `VENDOR_BOOT`, `DTBO`, `DTB`).

Selection is performed by setting `GBL_EFI_VERIFIED_DEVICE_TREE.Selected` to
`TRUE` on the firmware side, following these rules:

1. Exactly one device tree must be selected. GBL will refuse to boot if none or
   multiple base device trees are selected.
2. Overlays are guaranteed to be provided in the same order as they appear in
   the `dtbo` partition and the selected ones are applied in that same order.
   Any number of overlays may be selected, including none.
3. At most one pVM device assignment overlay can be selected. If multiple such
   overlays are selected, GBL will refuse to boot.

`EFI_UNSUPPORTED` may be returned to indicate that firmware-specific selection
isn't required. GBL will use its default autoselection logic, which selects the
single provided base device tree without applying any overlays. GBL will fail to
boot if more than one base device tree is provided by the boot partitions. No
pVM device assignment overlays will be selected by the autoselection logic.

### Status Codes Returned

| Return Code             | Semantics                                                     |
| :---------------------- | :------------------------------------------------------------ |
| `EFI_SUCCESS`           | Base device tree, overlays, DA overlays have been selected.   |
| `EFI_UNSUPPORTED`       | No components have been selected; GBL will use autoselection. |
| `EFI_INVALID_PARAMETER` | Unexpected input; GBL will refuse to boot.                    |

## GBL_EFI_OS_CONFIGURATION_PROTOCOL.SelectFitConfiguration()

### Summary

Inspects FIT configurations and selects the configuration to be used for the
platform.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI *GBL_EFI_SELECT_FIT_CONFIGURATION)(
  IN GBL_EFI_OS_CONFIGURATION_PROTOCOL *Self,
  IN UINTN                             FitSize,
  IN CONST UINT8                       *Fit,
  IN UINTN                             MetadataSize,
  IN CONST UINT8                       *Metadata,
  OUT UINTN                            *SelectedConfigurationOffset
  );
```

### Parameters

All parameters are valid only for the duration of the function call and must not
be retained by the protocol.

#### Self

A pointer to the `GBL_EFI_OS_CONFIGURATION_PROTOCOL` instance.

#### FitSize

Size of the FIT FDT buffer.

#### Fit

Pointer to the FIT FDT loaded by GBL.

#### MetadataSize

Size of the metadata payload. The size is guaranteed to be `0` if `Metadata` is
NULL.

#### Metadata

Pointer to the first FIT image payload if the type is set to "metadata".

GBL requires the metadata payload to be referenced by the first sub-node inside
the `/images` node in FIT FDT. The sub-node for metadata must have type set to
"metadata".

If no such metadata node is found, this parameter will have a `NULL` value.

#### SelectedConfigurationOffset

Pointer to a value to be set by the firmware with the offset of the selected
configuration node within the `Fit` FDT.

### Description

A single FIT image can contain multiple configurations with various images -
kernel, DTB, ramdisk, etc. Each configuration can have a different set of images
corresponding to the platform on which images need to be loaded. Present GBL
implementation supports only device tree selection via FIT image.

The appropriate configuration can be dynamically selected by the firmware at
runtime based on the platform. Firmware can use the `Metadata` parameter to read
additional information required for comparing the configuration entries present
in the FIT image.

Exactly one FIT configuration must be selected. GBL will refuse to boot if no
configuration is selected. `EFI_UNSUPPORTED` may be returned to indicate that
firmware-specific selection isn't required. In this case, GBL will use
traditional device tree selection and ignore the FIT image entirely.

### Status Codes Returned

| Return Code             | Semantics                                             |
| :---------------------- | :---------------------------------------------------- |
| `EFI_SUCCESS`           | FIT configuration has been selected.                  |
| `EFI_UNSUPPORTED`       | No configuration selected; GBL will continue to boot. |
| `EFI_INVALID_PARAMETER` | Unexpected input; GBL will refuse to boot.            |

[fixup_bootconfig]: #gbl_efi_os_configuration_protocol_fixupbootconfig
[select_device_trees]: #gbl_efi_os_configuration_protocol_selectdevicetrees
[select_fit_configuration]:
  #gbl_efi_os_configuration_protocol_selectfitconfiguration
[custom_protocol_revisions]: efi_integration.md#gbl-custom-protocol-revisions
[avf]: https://source.android.com/docs/core/virtualization
[bootconfig]:
  https://source.android.com/docs/core/architecture/bootloader/implementing-bootconfig
