# GBL OS Configuration EFI Protocol

This document defines an EFI protocol for GBL which allows the device to
apply runtime fixups to data passed into the OS.

## GBL_EFI_OS_CONFIGURATION_PROTOCOL

### Summary

This protocol provides a mechanism for the EFI firmware to modify OS
configuration data:

* kernel commandline
* bootconfig
* devicetree

GBL will load and verify the base data from disk, and then call these protocol
functions to give the firmware a chance to adjust the data as needed for the
particular device.

If no runtime modifications are necessary, this protocol may be left
unimplemented.

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

Note: revision 0 means the protocol is not yet stable and may change in
backwards-incompatible ways.

```c
#define GBL_EFI_OS_CONFIGURATION_PROTOCOL_REVISION 0x00000000
```

### Protocol Interface Structure

```c
typedef struct GBL_EFI_OS_CONFIGURATION_PROTOCOL {
  UINT64                              Revision;
  GBL_FIXUP_ASCII_DATA                FixupKernelCommandline;
  GBL_FIXUP_ASCII_DATA                FixupBootconfig;
  GBL_FIXUP_DEVICETREE                FixupDevicetree;
  GBL_FIXUP_ZBI                       FixupZbi;
} GBL_EFI_OS_CONFIGURATION_PROTOCOL;
```

### Parameters

#### Revision
The revision to which the `GBL_EFI_OS_CONFIGURATION_PROTOCOL` adheres. All
future revisions must be backwards compatible. If a future version is not
backwards compatible, a different GUID must be used.

#### FixupKernelCommandline
Applies kernel commandline fixups. See
[`FixupKernelCommandline()`](#FixupKernelCommandline).

#### FixupBootconfig
Applies bootconfig fixups. See [`FixupBootconfig()`](#FixupBootconfig).

#### FixupDevicetree
Applies devicetree fixups. See [`FixupDevicetree()`](#FixupDevicetree).

#### FixupZbi
Applies ZBI fixups (Fuchsia kernels only). See [`FixupZbi()`](#FixupZbi).

## GBL_EFI_OS_CONFIGURATION_PROTOCOL.FixupKernelCommandline() {#FixupKernelCommandline}

### Summary

Applies runtime fixups to the kernel command line.

### Prototype

```c
typedef EFI_STATUS (EFIAPI *GBL_FIXUP_ASCII_DATA)(
  IN GBL_EFI_OS_CONFIGURATION_PROTOCOL     *This,
  IN OUT CHAR8                             *Data,
  IN OUT UINTN                             *BufferSize
);
```

### Parameters

#### This
A pointer to the `GBL_EFI_OS_CONFIGURATION_PROTOCOL` instance.

#### Data
A pointer to the ASCII nul-terminated data.

The protocol can modify this data directly, with the following restrictions:
* on return, the data must be valid ASCII encoding with nul termination
* the data and termination byte must never exceed the provided `BufferSize`
* no libavb arguments may be added, deleted, or modified (see Security below)

Ownership of this data is loaned only for the duration of the function call, and
must not be retained by the protocol after returning.

#### BufferSize
On function call, this contains the size of the command line buffer, which may
be larger than the current command line contents. The implementation is free to
grow the command line contents up to this size, including the termination byte.

If the buffer is not large enough to fit the fixups, the function should update
`BufferSize` with the required size and return `EFI_BUFFER_TOO_SMALL`; GBL will
then allocate a larger buffer and re-call this function with the original
un-modified command line.

`BufferSize` does not need to be updated on success, GBL will determine the
command line data size via the nul terminator.

### Description

GBL will call this function after loading and verifying the base kernel command
line, to give the device an opportunity to supply any runtime fixups.

Since the devicetree selection affects the base kernel command line, GBL will
call `FixupDevicetree` first before calling `FixupKernelCommandline`.

#### Security

To ensure the integrity of verified boot data, this protocol will not be
allowed to add, delete, or modify any command line parameters provided by
[libavb](https://source.android.com/docs/security/features/verifiedboot/avb).
If any of these parameters are modified, GBL will treat this as a failed boot
attempt:
* `androidboot.veritymode*`
* `androidboot.vbmeta*`
* `dm`
* `root`

Additionally, all data used to apply fixups to the command line must be trusted.
In particular, if the protocol loads any data from non-secure storage, it should
verify that data before use.

### Status Codes Returned

|||
| ----------- | ----------- |
| `EFI_SUCCESS` | Command line fixup completed. |
| `EFI_INVALID_PARAMETER` | A parameter is invalid. |
| `EFI_BUFFER_TOO_SMALL` | The buffer is too small; `BufferSize` has been updated with the required size. |
| `EFI_DEVICE_ERROR` | Internal error while updating the command line. |

## GBL_EFI_OS_CONFIGURATION_PROTOCOL.FixupBootconfig() {#FixupBootconfig}

TODO(b/353272981)

## GBL_EFI_OS_CONFIGURATION_PROTOCOL.FixupDevicetree() {#FixupDevicetree}

TODO(b/353272981)

## GBL_EFI_OS_CONFIGURATION_PROTOCOL.FixupZbi() {#FixupZbi}

TODO(b/353272981)
