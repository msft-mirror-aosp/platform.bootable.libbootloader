# GBL EFI Fastboot Protocol

This document describes the GBL Fastboot protocol. The protocol defines
interfaces that can be used by EFI applications to query and modify vendor-specific
information on a device that may be desired in the context of a fastboot environment.

|             |                    |
|:------------|-------------------:|
| **Status**  | *Work in progress* |
| **Created** |          2024-9-11 |

## `GBL_EFI_FASTBOOT_PROTOCOL`

### Summary

This protocol provides interfaces for platform-specific operations during Fastboot.
This can include support for vendor defined variables or variables whose query
requires cooperation with vendor firmware, OEM commands,

### GUID
```c
// {c67e48a0-5eb8-4127-be89-df2ed93d8a9a}
#define GBL_EFI_FASTBOOT_PROTOCOL_GUID               \
  {                                                  \
    0xc67e48a0, 0x5eb8, 0x4127, {                    \
      0xbe, 0x89, 0xdf, 0x2e, 0xd9, 0x3d, 0x8a, 0x9a \
    }                                                \
  }
```

### Revision Number

```c
#define GBL_EFI_FASTBOOT_PROTOCOL_REVISION 0x00000000
```

### Protocol Interface Structure

```c
#define GBL_EFI_FASTBOOT_SERIAL_NUMBER_MAX_LEN_UTF8 32

typedef struct _GBL_EFI_FASTBOOT_PROTOCOL {
  UINT32                                        Revision
  CHAR8                                         SerialNumber[GBL_EFI_FASTBOOT_SERIAL_NUMBER_MAX_LEN_UTF8];
  GBL_EFI_FASTBOOT_GET_VAR                      GetVar;
  GBL_EFI_FASTBOOT_START_VAR_ITERATOR           StartVarIterator;
  GBL_EFI_FASTBOOT_GET_NEXT_VAR_ARGS            GetNextVarArgs;
  GBL_EFI_FASTBOOT_RUN_OEM_FUNCTION             RunOemFunction;
  GBL_EFI_FASTBOOT_GET_POLICY                   GetPolicy;
  GBL_EFI_FASTBOOT_SET_LOCK                     SetLock;
  GBL_EFI_FASTBOOT_CLEAR_LOCK                   ClearLock;
  GBL_EFI_FASTBOOT_GET_PARTITION_PERMISSIONS    GetPartitionPermissions;
  GBL_EFI_FASTBOOT_WIPE_USER_DATA               WipeUserData;
} GBL_EFI_FASTBOOT_PROTOCOL;
```

### Parameters

**Revision**

The revision to which the `GBL_EFI_FASTBOOT_PROTOCOL` adheres.
All future revisions must be backwards compatible.
If a future version is not backwards compatible, a different GUID must be used.

**SerialNumber**

The device serial number expressed as a Null-terminated UTF-8 encoded string.
If the device serial number is 32 bytes long, the Null terminator must be excluded.
If the device serial number is longer than 32 bytes, it must be truncated.

**GetVar**

Gets the value for the given fastboot variable.
See [`GBL_EFI_FASTBOOT_PROTOCOL.GetVar()`](#gbl_efi_fastboot_protocolgetvar).

**StartVarIterator**

Creates an iterator at the beginning of all valid fastboot variables
tracked by the protocol driver.
See [`GBL_EFI_FASTBOOT_PROTOCOL.StartVarIterator()`](#gbl_efi_fastboot_protocolstartvariterator).

**GetNextVarArgs**

Gets the next variable and sub-arguments in the iterator.
See [`GBL_EFI_FASTBOOT_PROTOCOL.GetNextVarArgs()`](#gbl_efi_fastboot_protocolgetnextvarargs).

**RunOemFunction**

Runs an OEM-defined command on the device.
See [`GBL_EFI_FASTBOOT_PROTOCOL.RunOemFunction()`](#gbl_efi_fastboot_protocolrunoemfunction).

**GetPolicy**

Querys device policy including device lock state, whether the device firmware
supports a 'critical' lock, and whether the device is capable of booting from
an image loaded directly into RAM.
See [`GBL_EFI_FASTBOOT_PROTOCOL.GetPolicy()`](#gbl_efi_fastboot_protocolgetpolicy).

**SetLock**

Enables device locks according to the provided ORed lock definitions.
See [`GBL_EFI_FASTBOOT_PROTOCOL.SetLock()`](#gbl_efi_fastboot_protocolsetlock).

**ClearLock**

Removes devices locks according to the provided ORed lock definitions.
See [`GBL_EFI_FASTBOOT_PROTOCOL.ClearLock()`](#gbl_efi_fastboot_protocolclearlock).

**GetPartitionPermissions**

Queries permissions information about the provided partition.
See [`GBL_EFI_FASTBOOT_PROTOCOL.GetPartitionPermissions()`](#gbl_efi_fastboot_protocolgetpartitionpermissions).

**WipeUserData**

Erases all partitions containing user data.
See [`GBL_EFI_FASTBOOT_PROTOCOL.WipeUserData()`](#gbl_efi_fastboot_protocolwipeuserdata).

## `GBL_EFI_FASTBOOT_PROTOCOL.GetVar()`

### Summary

Gets the value for a fastboot variable.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_FASTBOOT_GET_VAR)(
    IN GBL_EFI_FASTBOOT_PROTOCOL*         This,
    IN GBL_EFI_FASTBOOT_ARG*              Args,
    IN UINTN                              NumArgs,
    OUT CHAR8*                            Buf,
    IN OUT UINTN*                         BufSize,
    OPTIONAL IN GBL_EFI_FASTBOOT_TOKEN    Hint,
);
```

### Related Definitions

```c
typedef struct _GBL_EFI_FASTBOOT_ARG {
    // Pointer to a Null-terminated, UTF-8 encoded string.
    const CHAR8* StrUtf8;
    // Length of StrUtf8 excluding the Null terminator.
    UINTN        Length;
} GBL_EFI_FASTBOOT_ARG;

typedef VOID* GBL_EFI_FASTBOOT_TOKEN;
```

### String Encoding

All strings provided to protocol methods, returned from protocol methods,
or defined as protocol fields are UTF-8 encoded and Null terminated.

Additionally, with the exception of `GBL_EFI_FASTBOOT_PROTOCOL.SerialNumber`,
all strings are either passed as pointer/length paired parameters or
are described by a `GBL_EFI_FASTBOOT_ARG`, which has pointer and length fields.
No length ever includes any Null-terminator characters.

The protocol requires both explicit length and Null-termination because GBL is
written in Rust. The Rust primitive `str` type is defined as a pointer and
length and is **NOT** Null-terminated.
Requiring protocol strings to provide an explicit length facilitates Rust
wrapping returned strings more easily.

Additionally, in-out length fields allow protocol methods to return
`EFI_BUFFER_TOO_SMALL` and provide the required buffer size to the caller
if necessary.

Null-terminators are required when passing strings to protocol methods because
Null-terminated strings are the standard in C, and protocol implementations
written in C must be supported.

### Parameters

*This*

A pointer to the [`GBL_EFI_FASTBOOT_PROTOCOL`](#protocol-interface-structure) instance.

*Args*

A pointer to an array of string fragments that describe a fastboot variable.
The caller splits an input string delimited with `:` to generate the fragments
and replaces the `:` characters with `\0`.

*NumArgs*

The number of elements in the *Args* array.

*Buf*

A pointer to the data buffer to store the value of the variable as a UTF-8
encoded string.

*BufSize*

On entry, the size in bytes of *Buf*.
On exit, the size in bytes of the UTF-8 encoded string describing the value,
excluding any Null-terminator.

*Hint*

If not `NULL` provides the driver with a user-opaque hint
in order to optimize variable lookup.
The only way to provide a valid hint is to use the tokens generated by
[`GBL_EFI_FASTBOOT_PROTOCOL.StartVarIterator()`](#gbl_efi_fastboot_protocolstartvariterator) and
[`GBL_EFI_FASTBOOT_PROTOCOL.GetNextVarArgs()`](#gbl_efi_fastboot_protocolgetnextvarargs).

### Description

`GetVar()` queries internal data structures and devices
to determine the value of the given variable.
Variables may have zero or more subfields with arbitrarily many variants per subfield.
These subfields are parsed by the caller and passed to `GetVar()`
as an array of UTF-8 encoded string slices.
The string slices are defined by a pointer and length structure,
and each string slice is also guaranteed to have a Null terminator.
See [Related Definitions](#related-definitions-1) for the definition of `GBL_EFI_FASTBOOT_ARG`.

The *Hint* parameter is an optional token generated
as part of iterating over the fastboot variables.
The method implementation can use a non-`NULL` *Hint*
to bypass a more expensive variable lookup.

An example client interaction:
```bash
# A variable with no subfields
$ fastboot getvar max-download-size
OKAY0x20000000

# A variable with two subfields
$ fastboot getvar block-device:0:total-blocks
OKAY0x800000000000
```

If *Hint* is `NULL`, invalid, or wrong, the lookup should proceed
as if the hint was not provided at all.

**Note:** even if the *Hint* parameter is *valid*,
i.e. it correctly points to a fastboot variable entry,
it may disagree with the variable description in *Args*.
The method implementation should check that the variable entry
described by *Hint* matches with *Args*.
If there is a discrepancy, *Args* should provide the authoritative lookup parameters
and *Hint* should be ignored.

### Status Codes Returned

| Return Code             | Semantics                                                                                                                                                                |
|:------------------------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `EFI_SUCCESS`           | The variable was found and its value successfully serialized.                                                                                                            |
| `EFI_INVALID_PARAMETER` | One of *This*, *Args*, *Buf*, or *BufSize* is `NULL` or improperly aligned.                                                                                              |
| `EFI_NOT_FOUND`         | The first element of *Args* does not contain a known variable.                                                                                                           |
| `EFI_UNSUPPORTED`       | The contents of *Args* do not contain a known variable with valid aruments. Any of the subarguments may be unknown, or too many or too few subarguments may be provided. |
| `EFI_BUFFER_TOO_SMALL`  | *Buf* is too small to store the serialized variable string. The value of *BufSize* is modified to contain the minimum necessary buffer size.                             |

## `GBL_EFI_FASTBOOT_PROTOCOL.StartVarIterator()`

### Summary

Creates an iterator at the beginning of the fastboot variables.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_FASTBOOT_START_VAR_ITERATOR)(
    IN GBL_EFI_FASTBOOT_PROTOCOL*  This,
    OUT GBL_EFI_FASTBOOT_TOKEN*    Token,
);
```

### Parameters

*This*

A pointer to the [`GBL_EFI_FASTBOOT_PROTOCOL`](#protocol-interface-structure) instance.

*Token*

On exit contains a caller-opaque token describing an iterator
at the beginning of the fastboot variables defined by the driver.

### Description
`StartVarIterator()` is used in conjunction with
[`GetNextVarArgs()`](#gbl_efi_fastboot_protocolgetnextvarargs) and
[`GetVar()`](#gbl_efi_fastboot_protocolgetvar) to
iterate over all variants of all driver defined fastboot variables and retrieve their values.
This faculty is used when a client requests the special `all` variable as in the following example.
The value of *Token* returned by `StartVarIterator()` **MUST** be a valid value for *Hint*
when passed to `GetVar()` along with the *Args* array returned by the first call to
`GetNextVarArgs()`.

Example client running `getvar all`:
```bash
$ fastboot getvar all
(bootloader) max-download-size: 0x20000000
(bootloader) version-bootloader: 1.0
(bootloader) max-fetch-size: 0xffffffffffffffff
(bootloader) partition-size:vbmeta:0: 0x8000000
(bootloader) partition-type:vbmeta:0: raw
(bootloader) partition-size:misc:0: 0x100000
(bootloader) partition-type:misc:0: raw
...
```

**Note:** `StartVarIterator()` **SHOULD** be idempotent,
i.e. the same token should be returned each time.
This makes comparing iterator values more stable,
which is helpful for detecting and exiting loops due to bugs.

**Note:** between the first call to `StartVarIterator()` and the final call to `GetNextVarArgs()`,
the iterator **MUST** remain valid.
The GBL is expected to invoke the following protocol methods during variable iteration;
these methods **MUST NOT** invalidate the iterator.

* `GBL_EFI_FASTBOOT_PROTOCOL.GetNextVarArgs()`
* `GBL_EFI_FASTBOOT_PROTOCOL.GetVar()`
* `GBL_EFI_FASTBOOT_USB_PROTOCOL.FastbootUsbReceive()`
* `GBL_EFI_FASTBOOT_USB_PROTOCOL.FastbootUsbSend()`
* `EFI_SIMPLE_NETWORK_PROTOCOL.Receive()`
* `EFI_SIMPLE_NETWORK_PROTOCOL.Transmit()`
* `EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL.OutputString()`

### Status Codes Returned

| Return Code             | Semantics                                                                          |
|:------------------------|:-----------------------------------------------------------------------------------|
| `EFI_SUCCESS`           | The value of *Token* has been updated to reference the starting iterator position. |
| `EFI_INVALID_PARAMETER` | One of *This* or *Token* is `NULL` or improperly aligned.                          |

## `GBL_EFI_FASTBOOT_PROTOCOL.GetNextVarArgs()`

### Summary

Gets the fastboot variable arguments at the current iterator position and advances the iterator.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_FASTBOOT_GET_NEXT_VAR_ARGS)(
    IN GBL_EFI_FASTBOOT_PROTOCOL*     This,
    OUT GBL_EFI_FASTBOOT_ARG*         Args,
    IN OUT UINTN*                     NumArgs,
    IN OUT GBL_EFI_FASTBOOT_TOKEN*    Token,
);
```

### Parameters

*This*

A pointer to the [`GBL_EFI_FASTBOOT_PROTOCOL`](#protocol-interface-structure) instance.

*Args*

A pointer to an uninitialized, caller-owned array of `GBL_EFI_FASTBOOT_ARG`.
On return defines the fastboot variable and subvariable variant
at the position indicated by the input value of *Token*.

*NumArgs*

On entry contains the maximum length of *Args*.
On exit contains the length of *Args* in elements defining the current variable.

*Token*

On entry contains the current iterator position.
On exit contains the next iterator position.

### Description

`GetNextVarArgs()` is used in conjunction with `GetVar()` and `StartVarIterator()`
to iterate over all fastboot variables and corresponding values provided by the protocol driver.
This functionality is used when handling the special `all` fastboot variable.

The position of the iterator is tracked by *Token*.
All values of *Token* are opaque handles used by the protocol driver.
Users **MUST NOT** assume that they are pointers, indices, references,
or have any user-accessible semantics of any kind.

When the iterator has reached the final fastboot variable entry,
the *next* call to `GetNextVarArgs()` **MUST** do **ALL** of the following:

* Return `EFI_SUCCESS`
* Set *NumArgs* to `0`
* Leave the value of *Token* unchanged

### Status Codes Returned

| Return Code             | Semantics                                                                                                                                        |
|:------------------------|:-------------------------------------------------------------------------------------------------------------------------------------------------|
| `EFI_SUCCESS`           | The call completed successfully.                                                                                                                 |
| `EFI_INVALID_PARAMETER` | One of *This*, *Args*, *NumArgs*, or *Token* is `NULL` or improperly aligned.                                                                    |
| `EFI_INVALID_PARAMETER` | The input value of *Token* is nonsensical.                                                                                                       |
| `EFI_BUFFER_TOO_SMALL`  | The entry value of *NumArgs* is too small to store the variable arguments. Its value is updated to contain the minimum necessary size of *Args*. |

## `GBL_EFI_FASTBOOT_PROTOCOL.RunOemFunction()`

### Summary

Runs a vendor defined function that requires firmware support.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_FASTBOOT_RUN_OEM_FUNCTION)(
    IN GBL_EFI_FASTBOOT_PROTOCOL* This,
    IN CHAR8*                     Command,
    IN UINTN                      CommandLen,
    OUT CHAR8*                    Buf,
    IN OUT UINTN*                 BufSize,
);
```

### Parameters

*This*

A pointer to the [`GBL_EFI_FASTBOOT_PROTOCOL`](#protocol-interface-structure) instance.

*Command*

The command to run as a Null-terminated UTF-8 encoded string.

*CommandLen*

The length of the command in bytes, excluding any Null-terminator.

*Buf*

A pointer to the data buffer to store any output the command generates
as a UTF-8 encoded, Null-terminated string.
On success, this output will be sent to the connected client as an INFO message.
On failure, this output will be sent to the connected client as a FAIL message.

**Note:** GBL is the only expected caller for any method of
`GBL_EFI_FASTBOOT_PROTOCOL`, including `RunOemFunction()`.
For a non-zero `BufSize`, GBL and all other callers are required to set the
first byte of `Buf` to `0`. GBL and all other callers are responsible for
parsing `Buf` until the first Null-terminator or for `Buf + BufSize` bytes,
whichever occurs first.

*BufSize*

On entry, the size in bytes of `Buf`.
On exit, the size in bytes of the UTF-8 encoded string describing the value,
excluding any Null-terminator.

### Description

`RunOemFunction()` runs a vendor defined Oem function.
These functions can take arbitrary arguments or subcommands;
the caller does no parsing or verification.
All parsing and verification is the responsibility of the method implementation.
Oem functions can display power or battery information, print or iterate over UEFI variables,
or conduct arbitrary other operations.

### Status Codes Returned

| Return Code             | Semantics                                                                                                                                                                       |
|:------------------------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `EFI_SUCCESS`           | The call completed successfully.                                                                                                                                                |
| `EFI_INVALID_PARAMETER` | One of *This*, *Command*, *CommandLen*, *Buf*, or *BufSize* is `NULL` or improperly aligned.                                                                                    |
| `EFI_BUFFER_TOO_SMALL`  | The provided buffer is too small to store the serialized representation of the command output. The value of `BufSize` is modified to contain the minimum necessary buffer size. |
| `EFI_UNSUPPORTED`       | The command is not supported or is nonsensical.                                                                                                                                 |
| `EFI_ACCESS_DENIED`     | The operation is not permitted in the current lock state.                                                                                                                       |

## `GBL_EFI_FASTBOOT_PROTOCOL.GetPolicy()`

### Summary

Gets the device policy pertaining to locking and booting directly from RAM.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_FASTBOOT_GET_POLICY)(
    IN GBL_EFI_FASTBOOT_PROTOCOL* This,
    OUT GBL_EFI_FASTBOOT_POLICY*  Policy,
);
```

### Related Definitions

```c
typedef struct _GBL_EFI_FASTBOOT_POLICY {
  // Indicates whether device can be unlocked.
  BOOL CanUnlock;
  // Device firmware supports 'critical' partition locking.
  BOOL HasCriticalLock;
  // Indicates whether device allows booting
  // from images loaded directly from RAM.
  BOOL CanRamBoot;
} GBL_EFI_FASTBOOT_POLICY;

```

### Parameters

*This*

A pointer to the [`GBL_EFI_FASTBOOT_PROTOCOL`](#protocol-interface-structure) instance.

*Policy*

On exit contains the device policy.
See [Related Definitions](#related-definitions-2) for the definition of `GBL_EFI_FASTBOOT_POLICY`.

### Description

Depending on various factors including whether the device
is a development target or end-user device,
certain operations may be prohibited.
In particular, loading an image directly into RAM and then booting it
is generally not permitted on anything except development hardware.
Developer workflows and CI/CD infrastructure need to be able to query
whether a device is able to be unlocked and whether RAM booting is permitted.

See [`SetLock()`](#gbl_efi_fastboot_protocolsetlock) and [`ClearLock()`](#gbl_efi_fastboot_protocolclearlock)
for methods that modify the device lock state. Querying lock state is handled by Android Verified Boot.

### Status Codes

| Return Code             | Semantics                                                  |
|:------------------------|:-----------------------------------------------------------|
| `EFI_SUCCESS`           | The device policy was successfuly retrieved.               |
| `EFI_INVALID_PARAMETER` | One of *This* or *Policy* is `NULL` or improperly aligned. |

## `GBL_EFI_FASTBOOT_PROTOCOL.SetLock()`

### Summary

Sets device partition locks.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_FASTBOOT_SET_LOCK)(
    IN GBL_EFI_FASTBOOT_PROTOCOL* This,
    IN UINT64                     LockState,
);
```

### Related Definitions

```c
typedef enum _GBL_EFI_FASTBOOT_LOCK_FLAGS {
  // All device partitions are locked.
  GBL_EFI_FASTBOOT_GBL_EFI_LOCKED = 0x1 << 0,
  // All 'critical' device partitions are locked.
  // The 'critical' lock is optional,
  // and which partitions are locked by the critical lock
  // is a vendor implementation detail.
  GBL_EFI_FASTBOOT_GBL_EFI_CRITICAL_LOCKED = 0x1 << 1,
} GBL_EFI_FASTBOOT_LOCK_FLAGS;

```

### Parameters

*This*

A pointer to the [`GBL_EFI_FASTBOOT_PROTOCOL`](#protocol-interface-structure) instance.

*LockState*

The ORed value of all device partition locks to enable.
When locked, partitions generally cannot be read, written, or erased via fastboot.
See [Related Definitions](#related-definitions-3) for valid lock flags.

### Description

Device lock state determines what operations can be performed on device partitions.
`SetLock()` enables the locks defined in *LockState*, some of which may already be set.
No locks are cleared by any call to `SetLock()`.

### Status Codes Returned

| Return Code             | Semantics                                          |
|:------------------------|:---------------------------------------------------|
| `EFI_SUCCESS`           | The call completed successfully.                   |
| `EFI_INVALID_PARAMETER` | *This* is `NULL` or improperly aligned.            |
| `EFI_INVALID_PARAMETER` | The lock flags in *LockState* are invalid.         |
| `EFI_ACCESS_DENIED`     | Device policy prohibited the change in lock state. |

## `GBL_EFI_FASTBOOT_PROTOCOL.ClearLock()`

### Summary

Clears device partition locks.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_FASTBOOT_CLEAR_LOCK)(
    IN GBL_EFI_FASTBOOT_PROTOCOL* This,
    IN UINT64                     LockState,
);
```

### Parameters

*This*

A pointer to the [`GBL_EFI_FASTBOOT_PROTOCOL`](#protocol-interface-structure) instance.

*LockState*

The ORed value of all device partition locks to disable.
See the [Related Definitions](#related-definitions-3) for `SetLock()` for valid lock flags.

### Description

Device lock state determines what operations can be performed on device partitions.
`ClearLock()` disables the locks defined in *LockState*, some of which may already be cleared.

### Status Codes Returned

| Return Code             | Semantics                                          |
|:------------------------|:---------------------------------------------------|
| `EFI_SUCCESS`           | The call completed successfully.                   |
| `EFI_INVALID_PARAMETER` | *This* is `NULL` or improperly aligned.            |
| `EFI_INVALID_PARAMETER` | The lock flags in *LockState* are invalid.         |
| `EFI_ACCESS_DENIED`     | Device policy prohibited the change in lock state. |

## `GBL_EFI_FASTBOOT_PROTOCOL.GetPartitionPermissions()`

### Summary

Gets access permission information about the given partition.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_FASTBOOT_GET_PARTITION_PERMISSIONS)(
    IN GBL_EFI_FASTBOOT_PROTOCOL* This,
    IN CHAR8*                     PartName,
    IN UINTN                      PartNameLen,
    OUT UINT64                    Permissions,
);
```

### Related Definitions

```c
typedef enum _GBL_EFI_FASTBOOT_PARTITION_PERMISSION_FLAGS {
  // Firmware can read the given partition and send its data to fastboot client.
  GBL_EFI_FASTBOOT_PARTITION_READ = 0x1 << 0,
  // Firmware can overwrite the given partition.
  GBL_EFI_FASTBOOT_PARTITION_WRITE = 0x1 << 1,
  // Firmware can erase the given partition.
  GBL_EFI_FASTBOOT_PARTITION_ERASE = 0x1 << 2,
} GBL_EFI_FASTBOOT_PARTITION_PERMISSION_FLAGS;

```

### Parameters

*This*

A pointer to the [`GBL_EFI_FASTBOOT_PROTOCOL`](#protocol-interface-structure) instance.

*PartName*

The name of the partition to query as a UTF-8 encoded, Null-terminated string.

*PartNameLen*

The length of *PartName* in bytes, excluding any Null-terminator.

*Permissions*

On exit contains the ORed flags detailing the current fastboot permissions for
the given partition.
See [Related Definitions](#related-definitions-4) for flag value semantics.

### Description

Depending on device lock state, Android Verified Boot policy, and other factors,
various partitions may have restricted permissions within a fastboot environment.
`GetPartitionPermissions()` retrieves the current permissions
for the requested partition.

By default, unless overridden by device policy, no operations are permitted on
any partition when the device is locked, and all operations are permitted
on all partitions when the device is unlocked.

### Status Codes

| Return Code             | Semantics                                                                          |
|:------------------------|:-----------------------------------------------------------------------------------|
| `EFI_SUCCESS`           | The partition permision information was successfully queried.                      |
| `EFI_INVALID_PARAMETER` | One of *This*, *PartName*, or *Permissions* is `NULL` or improperly aligned.       |
| `EFI_NOT_FOUND`         | There is no partition named *PartName*.                                            |
| `EFI_UNSUPPORTED`       | The device does not have a partition permission policy different from the default. |

## `GBL_EFI_FASTBOOT_PROTOCOL.WipeUserData()`

### Summary

Erases all partitions containing user data.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_FASTBOOT_WIPE_USER_DATA)(
    IN GBL_EFI_FASTBOOT_PROTOCOL* This,
);
```

### Parameters

*This*

A pointer to the [`GBL_EFI_FASTBOOT_PROTOCOL`](#protocol-interface-structure) instance.

### Description

Device user data is often stored on a dedicated partition
apart from kernel images or other system data.
This helps protect user data during system upgrades.
`WipeUserData()` erases all user data partitions.
This can be used to restore a device to its factory settings,
as part of a refurbishment process, or for testing purposes.

### Status Codes

| Return Code             | Semantics                                                 |
|:------------------------|:----------------------------------------------------------|
| `EFI_SUCCESS`           | User data was successfully wiped.                         |
| `EFI_INVALID_PARAMETER` | *This* is `NULL` or improperly aligned.                   |
| `EFI_ACCESS_DENIED`     | The operation is not permitted in the current lock state. |
| `EFI_DEVICE_ERROR`      | There was a block device or storage error.                |

