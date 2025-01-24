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
  GBL_EFI_FASTBOOT_GET_VAR_ALL                  GetVarAll;
  GBL_EFI_FASTBOOT_RUN_OEM_FUNCTION             RunOemFunction;
  GBL_EFI_FASTBOOT_GET_POLICY                   GetPolicy;
  GBL_EFI_FASTBOOT_SET_LOCK                     SetLock;
  GBL_EFI_FASTBOOT_CLEAR_LOCK                   ClearLock;
  GBL_EFI_FASTBOOT_GET_PARTITION_PERMISSIONS    GetPartitionPermissions;
  GBL_EFI_FASTBOOT_WIPE_USER_DATA               WipeUserData;
  GBL_EFI_FASTBOOT_SHOULD_STOP_IN_FASTBOOT      ShouldStopInFastboot;
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

**GetVarAll**

Iterates all combinations of arguments and values for all fastboot variables.
See [`GBL_EFI_FASTBOOT_PROTOCOL.GetVarAll()`](#gbl_efi_fastboot_protocolgetvarall).

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
    IN CONST CHAR8* CONST*                Args,
    IN UINTN                              NumArgs,
    OUT CHAR8*                            Buf,
    IN OUT UINTN*                         BufSize,
);
```

### Parameters

*This*

A pointer to the [`GBL_EFI_FASTBOOT_PROTOCOL`](#protocol-interface-structure)
instance.

*Args*

A pointer to an array of NULL-terminated strings that contains the name of the
variable followed by additional arguments.

*NumArgs*

The number of elements in the *Args* array.

*Buf*

A pointer to the data buffer to store the value of the variable as a UTF-8
encoded string.

*BufSize*

On entry, the size in bytes of *Buf*.
On exit, the size in bytes of the UTF-8 encoded string describing the value,
excluding any Null-terminator.

### Description

`GetVar()` queries internal data structures and drivers to determine the value
of the given variable. Variables may have zero or more additional arguments.
These arguments are parsed by the caller and passed to `GetVar()` as an array
of NULL-terminated UTF-8 encoded string.

An example client interaction:
```bash
# A variable with no argument.
$ fastboot getvar max-download-size
OKAY0x20000000

# A variable with two arguments.
$ fastboot getvar block-device:0:total-blocks
OKAY0x800000000000
```

### Status Codes Returned

| Return Code             | Semantics                                                                                                                                                                |
|:------------------------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `EFI_SUCCESS`           | The variable was found and its value successfully serialized.                                                                                                            |
| `EFI_INVALID_PARAMETER` | One of *This*, *Args*, *Buf*, or *BufSize* is `NULL`                                                                                                                     |
| `EFI_NOT_FOUND`         | The first element of *Args* does not contain a known variable.                                                                                                           |
| `EFI_UNSUPPORTED`       | The contents of *Args* do not contain a known variable with valid aruments. Any of the subarguments may be unknown, or too many or too few subarguments may be provided. |
| `EFI_BUFFER_TOO_SMALL`  | *Buf* is too small to store the serialized variable string. The value of *BufSize* is modified to contain the minimum necessary buffer size.                             |

## `GBL_EFI_FASTBOOT_PROTOCOL.GetVarAll()`

### Summary

Iterates all combinations of variables and values.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_FASTBOOT_GET_VAR_ALL)(
    IN GBL_EFI_FASTBOOT_PROTOCOL*         This,
    IN VOID*                              Context
    IN GBL_EFI_GET_VAR_ALL_CALLBACK       GetVarAllCallback,
);
```

### Parameters

*This*

A pointer to the [`GBL_EFI_FASTBOOT_PROTOCOL`](#protocol-interface-structure)
instance.

*Context*

A pointer to the context data for `GetVarAllCallback`.

*GetVarAllCallback*

A pointer to a function of type `GBL_EFI_GET_VAR_ALL_CALLBACK`. It receives as
parameter the `Context` pointer passed to this function, an array of
NULL-terminated UTF8 strings containing variable name and additional arguments,
the array length, and a NULL-terminated string representing the value.

### Related Definitions

```c
typedef
VOID (*GBL_EFI_GET_VAR_ALL_CALLBACK) (
    IN VOID*                              Context
    IN CONST CHAR8* CONST*                Args,
    IN UINTN                              NumArgs,
    IN CONST CHAR8*                       Value,
);
```
*Context*

The pointer to the context passed to `GetVarAll()`.

*Args*

A pointer to an array of NULL-terminated strings that contains the name of the
variable followed by additional arguments.

*NumArgs*

The number of elements in the *Args* array.

*Value*

A NULL-terminated string representing the value.

### Description

`GetVarAll()` iterates all combinations of arguments and values for all fastboot
variables. For each combination, the function invokes the caller provided
callback `GetVarAllCallback()` and passes the context, arguments and value.

### Status Codes Returned

| Return Code             | Semantics                                       |
|:------------------------|:------------------------------------------------|
| `EFI_SUCCESS`           | Operation is successful.                        |
| `EFI_INVALID_PARAMETER` | One of *This* or *GetVarAllCallback* is `NULL`. |

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

`RunOemFunction()` runs a vendor defined Oem function. These functions can take
arbitrary arguments or subcommands. The caller does no parsing or verification.
All parsing and verification is the responsibility of the method
implementation. Oem functions can display power or battery information, print
or iterate over UEFI variables, or conduct arbitrary other operations.

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

## `GBL_EFI_FASTBOOT_PROTOCOL.ShouldStopInFastboot()`

### Summary

Checks custom inputs to determine whether the device should stop in fastboot on boot.

### Prototype

```c
typedef
BOOL
(EFIAPI * GBL_EFI_FASTBOOT_SHOULD_STOP_IN_FASTBOOT)(
    IN GBL_EFI_FASTBOOT_PROTOCOL* This,
);
```

### Parameters

*This*

A pointer to the [`GBL_EFI_FASTBOOT_PROTOCOL`](#protocol-interface-structure) instance.

### Description

Devices often define custom mechanisms for determining whether to enter fastboot mode
on boot. A specific button press combination is common,
e.g. pressing 'volume down' for three seconds while booting.

`ShouldStopInFastboot()` returns whether the device should stop in fastboot mode
due to device input.

**Note:** `ShouldStopInFastboot()` should ONLY return `true` if the device specific
button press is active. In particular, if the device supports
[`GBL_EFI_AB_SLOT_PROTOCOL`](./gbl_efi_ab_slot_protocol.md),
`ShouldStopInFastboot()` should NOT check the information provided by
`GBL_EFI_AB_SLOT_PROTOCOL.GetBootReason()` or the underlying persistent boot reason.

Any errors should cause a return value of `false`.
