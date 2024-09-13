# GBL EFI AB Slot Protocol

This document describes the GBL AB Slot protocol.
The protocol defines interfaces that can be used by EFI applications
to query and manipulate boot slots.

| **Status**  | Work in progress |
|:------------|-----------------:|
| **Created** |        2024-9-17 |

## `GBL_EFI_AB_SLOT_PROTOCOL`

### Summary

This protocol provides interfaces for platform specific boot slot operations,
such as determining the number of slots and the current target slot,
changing the current target boot slot, marking boot attempts, and more.

### Boot Slot Coherency Warning

**Warning:** a boot slot may contain multiple artifacts, e.g. firmware images,
kernel images, RAM disks, partitions, and so forth. It is **NOT** guaranteed
that arbitrary artifacts from different slots interoperate correctly.
For example, the bootloader in slot A may pass command line arguments that are
invalid for the kernel in slot B. The **ONLY** safe way to boot a slot
different from the active boot slot is to

1. Change the slot by calling
[`SetActiveSlot()`](#gbl_efi_ab_slot_protocolsetactiveslot).
2. Reboot the device.
   1. Optionally enter fastboot mode.
3. Continue the boot process.

It is the EFI application's responsibility to track whether `SetActiveSlot()`
has been called and whether the current target slot and the active slot differ.

### GUID

```c
// {9a7a7db4-614b-4a08-3df9-006f49b0d80c}
#define GBL_EFI_AB_SLOT_PROTOCOL_GUID                \
  {                                                  \
    0x9a7a7db4, 0x614b, 0x4a08, {                    \
      0x3d, 0xf9, 0x00, 0x6f, 0x49, 0xb0, 0xd8, 0x0c \
    }                                                \
  }
```

### Protocol Version
```c
#define GBL_EFI_AB_SLOT_PROTOCOL_VERSION 0x00010000
```

### Protocol Interface Structure

```c
typedef struct GBL_EFI_AB_SLOT_PROTOCOL {
  // Currently must contain 0x00010000
  UINT32                              Version;
  GBL_EFI_AB_SLOT_LOAD_BOOT_DATA      LoadBootData;
  GBL_EFI_AB_SLOT_GET_SLOT_INFO       GetSlotInfo;
  GBL_EFI_AB_SLOT_GET_CURRENT_SLOT    GetCurrentSlot;
  GBL_EFI_AB_SLOT_SET_ACTIVE_SLOT     SetActiveSlot;
  GBL_EFI_AB_SLOT_SET_SLOT_UNBOOTABLE SetSlotUnbootable;
  GBL_EFI_AB_SLOT_MARK_BOOT_ATTEMPT   MarkBootAttempt;
  GBL_EFI_AB_SLOT_REINITIALIZE        Reinitialize;
  GBL_EFI_AB_SLOT_GET_BOOT_REASON     GetBootReason;
  GBL_EFI_AB_SLOT_SET_BOOT_REASON     SetBootReason;
  GBL_EFI_AB_SLOT_FLUSH               Flush;
} GBL_EFI_AB_SLOT_PROTOCOL;
```

### Parameters

**Version**

The revision to which the `GBL_EFI_AB_SLOT_PROTOCOL` adheres.
All future version must be backwards compatible.
If a future version is not backwards compatible, a different GUID must be used.

**LoadBootData**

Loads slot metadata from persistent storage. Other slot operations may call
this method internally.
See [`GBL_EFI_AB_SLOT_PROTOCOL.LoadBootData()`](#gbl_efi_ab_slot_protocolloadbootdata).

**GetSlotInfo**

Returns information about a slot by index.
See [`GBL_EFI_AB_SLOT_PROTOCOL.GetSlotInfo()`](#gbl_efi_ab_slot_protocolgetslotinfo).

**GetCurrentSlot**

Returns information about the current slot.
See [`GBL_EFI_AB_SLOT_PROTOCOL.GetCurrentSlot()`](#gbl_efi_ab_slot_protocolgetcurrentslot).

**SetActiveSlot**

Marks the specified slot as the active boot target.
See [`GBL_EFI_AB_SLOT_PROTOCOL.SetActiveSlot()`](#gbl_efi_ab_slot_protocolsetactiveslot).

**SetSlotUnbootable**

Marks the specified slot as unbootable.
See [`GBL_EFI_AB_SLOT_PROTOCOL.SetSlotUnbootable()`](#gbl_efi_ab_slot_protocolsetslotunbootable).

**MarkBootAttempt**

Marks the boot attempt and modifies tries remaining for the active slot.
See [`GBL_EFI_AB_SLOT_PROTOCOL.MarkBootAttempt()`](#gbl_efi_ab_slot_protocolmarkbootattempt).

**Reinitialize**

Resets slot metadata to a default, initial state.
See [`GBL_EFI_AB_SLOT_PROTOCOL.Reinitialize()`](#gbl_efi_ab_slot_protocolreinitialize).

**GetBootReason**

Gets the boot reason.
See [`GBL_EFI_AB_SLOT_PROTOCOL.GetBootReason()`](#gbl_efi_ab_slot_protocolgetbootreason).

**SetBootReason**

Sets the boot reason.
See [`GBL_EFI_AB_SLOT_PROTOCOL.SetBootReason()`](#gbl_efi_ab_slot_protocolsetbootreason).

**Flush**

Synchronizes slot metadata with persistent storage. May re-establish data
structure invariants, e.g. recalculate checksums.
See [`GBL_EFI_AB_SLOT_PROTOCOL.Flush()`](#gbl_efi_ab_slot_protocolflush).

## `GBL_EFI_AB_SLOT_PROTOCOL.LoadBootData()`

### Summary

Loads metadata about system boot slots.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_AB_SLOT_LOAD_BOOT_DATA)(
    IN GBL_EFI_AB_SLOT_PROTOCOL*     This,
    OUT GBL_EFI_SLOT_METADATA_BLOCK* Metadata,
);
```

### Related Definitions

```c
typedef struct _GBL_EFI_SLOT_METADATA_BLOCK {
  // Value of 1 if persistent metadata tracks slot unbootable reasons.
  UINT8 UnbootableMetadata;
  UINT8 MaxRetries;
  UINT8 SlotCount;
} GBL_EFI_SLOT_METADATA_BLOCK;
```

### Parameters

*This*

A pointer to the [`GBL_EFI_AB_SLOT_PROTOCOL`](#protcol-interface-structure)
instance.

*Metadata*

On return contains device-specific immutable information about the AB slot
implementation. See [`Related Definitions`](#related-definitions) for the layout
of the metadata structure and its fields.

### Description

In addition to information about individual slots, EFI applications need
overarching metadata about AB boot slot implementations.
In particular, implementations might not store persistent metadata detailing why
specific slots are not bootable (i.e. unbootable metadata). Developers may want
to know whether a device supports unbootable metadata to ease in debugging.

**Note:** calls to `LoadBootData()` are expected to be idempotent. The data
returned are not invalidated by any other operations.

### Status Codes Returned

| Return Code             | Semantics                                                                                                     |
|:------------------------|:--------------------------------------------------------------------------------------------------------------|
| `EFI_SUCCESS`           | Slot metadata was successfully read from persistent storage.                                                  |
| `EFI_INVALID_PARAMETER` | One of *This* or *Metadata* is `NULL` or improperly aligned.                                                  |
| `EFI_DEVICE_ERROR`      | There was an error while performing the read operation.                                                       |
| `EFI_VOLUME_CORRUPTED`  | The metadata loaded is invalid or corrupt. The caller should call `Reinitialize` before taking other actions. |

## `GBL_EFI_AB_SLOT_PROTOCOL.GetSlotInfo()`

### Summary

Queries info about a boot slot by index.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_AB_SLOT_GET_SLOT_INFO)(
    IN GBL_EFI_AB_SLOT_PROTOCOL* This,
    IN UINT8                     Idx,
    OUT GBL_EFI_SLOT_INFO*       Info,
)
```

### Related Definitions

```c
typedef enum _GBL_EFI_SLOT_UNBOOTABLE_REASON {
  UNKNOWN_REASON = 0,
  NO_MORE_TRIES,
  SYSTEM_UPDATE,
  USER_REQUESTED,
  VERIFICATION_FAILURE,
} GBL_EFI_SLOT_UNBOOTABLE_REASON;

typedef struct _GBL_EFI_SLOT_INFO {
    // One UTF-8 encoded single character
    UINT32 Suffix;
    // Any value other than those explicitly enumerated in
    // GBL_EFI_SLOT_UNBOOTABLE_REASON
    // will be interpreted as UNKNOWN_REASON.
    UINT32 UnbootableReason;
    UINT8  Priority;
    UINT8  Tries;
    // Value of 1 if slot has successfully booted
    UINT8  Successful;
    UINT8  MergeStatus;
} GBL_EFI_SLOT_INFO;
```

### Parameters

*This*

A pointer to the [`GBL_EFI_AB_SLOT_PROTOCOL`](#protcol-interface-structure)
instance.

*Idx*

The index of the slot to query.

*Info*

On exit contains the metadata for the specified slot.
See [Related Definitions](#related-definitions-1)
for the layout and fields of the metadata structure.

### Description

Developers and EFI applications may wish to query metadata of arbitrary boot
slots as part of debugging or logging.

### Status Codes Returned

| Return Code             | Semantics                                                                                                     |
|:------------------------|:--------------------------------------------------------------------------------------------------------------|
| `EFI_SUCCESS`           | The call completed successfully.                                                                              |
| `EFI_INVALID_PARAMETER` | One of *This* or *Info* is `NULL` or improperly aligned, or the value of *Idx* invalid.                       |
| `EFI_DEVICE_ERROR`      | There was an error reading metadata from persistent storage.                                                  |
| `EFI_VOLUME_CORRUPTED`  | The metadata loaded is invalid or corrupt. The caller should call `Reinitialize` before taking other actions. |

## `GBL_EFI_AB_SLOT_PROTOCOL.GetCurrentSlot()`

### Summary

Returns the slot information of the current slot.

### Definitions

The *current target* slot is defined as the highest priority bootable slot with
ties broken by inverse lexicographical ordering of slot suffixes. E.g. if slot A
and slot B are both bootable and have priority 15, slot A is the current slot.
The *active* slot is the slot that owns the running bootloader firmware.
Depending on whether `SetActiveSlot()` has been called, the current and active
slots may be the same or they may differ. See the
[Boot Slot Coherency Warning](#boot-slot-coherency-warning) for details.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_AB_SLOT_GET_CURRENT_SLOT)(
    IN GBL_EFI_AB_SLOT_PROTOCOL* This,
    OUT GBL_EFI_SLOT_INFO*       Info,
);
```

### Parameters

*This*

A pointer to the [`GBL_EFI_AB_SLOT_PROTOCOL`](#protcol-interface-structure)
instance.

*Info*

On exit contains the metadata for the current slot.
See the definition for [`GBL_EFI_SLOT_INFO`](#related-definitions-1)
for the structure definition.

### Description

This is identical to knowing the index of the current slot and calling
`GetSlotInfo()` with that index.

**Note:** the current slot is returned by value and not by index.
This simplifies interactions for the caller, who is usually more interested in
the suffix and associated metadata for a slot than its index.

### Status Codes Returned

| Return Code             | Semantics                                                                                                     |
|:------------------------|:--------------------------------------------------------------------------------------------------------------|
| `EFI_SUCCESS`           | The call completed successfully.                                                                              |
| `EFI_INVALID_PARAMETER` | One of *This* or *Info* is `NULL` or improperly aligned.                                                      |
| `EFI_DEVICE_ERROR`      | There was an error reading metadata from persistent storage.                                                  |
| `EFI_VOLUME_CORRUPTED`  | The metadata loaded is invalid or corrupt. The caller should call `Reinitialize` before taking other actions. |

## `GBL_EFI_AB_SLOT_PROTOCOL.SetActiveSlot()`

### Summary

Sets the active slot by index, reinitializes its tries remaining and priority,
and clears any unbootable reasons.
Sets the priority for all other slots to be lower than the new active slot's.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_AB_SLOT_SET_ACTIVE_SLOT)(
    IN GBL_EFI_AB_SLOT_PROTOCOL* This,
    IN UINT8                     Idx,
);
```

### Parameters

*This*

A pointer to the [`GBL_EFI_AB_SLOT_PROTOCOL`](#protcol-interface-structure)
instance.

*Idx*

The index of the new active slot.

### Description

Explicitly sets the target boot slot to the one defined by `Idx`.
This clears any unbootable reason metadata the slot may have, resets its tries
remaining to a device specific default, resets its priority to a device specific
default, sets the priority of all other slots to be lower than that of the
target, and clears the slot's *Successful* flag.
All these changes **MUST** be visible in subsequent calls to `GetSlotInfo()`.
Depending on device policy, e.g. lock state, changing the target boot slot
explicitly may be prohibited.

**Warning:** See the description for
[`GetCurrentSlot()`](#gbl_efi_ab_slot_protocolgetcurrentslot) for the
distinction between the *current target* boot slot and the *active* boot slot,
and see the [Boot Slot Coherency Warning](#boot-slot-coherency-warning) for
details about safely changing the *current target* slot.

### Status Codes Returned

| Return Code             | Semantics                                                                                                     |
|:------------------------|:--------------------------------------------------------------------------------------------------------------|
| `EFI_SUCCESS`           | The call completed successfully.                                                                              |
| `EFI_INVALID_PARAMETER` | One of *This* or *Info* is `NULL` or improperly aligned, or the value of *Idx* was invalid.                   |
| `EFI_DEVICE_ERROR`      | There was an error reading metadata from persistent storage.                                                  |
| `EFI_VOLUME_CORRUPTED`  | The metadata loaded is invalid or corrupt. The caller should call `Reinitialize` before taking other actions. |
| `EFI_ACCESS_DENIED`     | Device policy prohibited the boot slot target change.                                                         |

## `GBL_EFI_AB_SLOT_PROTOCOL.SetSlotUnbootable()`

### Summary

Marks a slot as unbootable for the provided reason.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_AB_SLOT_SET_SLOT_UNBOOTABLE)(
    IN GBL_EFI_AB_SLOT_PROTOCOL* This,
    IN UINT8                     Idx,
    IN UINT32                    UnbootableReason,
);
```

### Parameters

*This*

A pointer to the [`GBL_EFI_AB_SLOT_PROTOCOL`](#protcol-interface-structure)
instance.

*Idx*

The index of the slot to mark unbootable.

*UnbootableReason*

The reason the slot is being marked unable to be booted.
See the definition for [`GBL_EFI_SLOT_UNBOOTABLE_REASON`](#related-definitions-1)
for valid values of *UnbootableReason*.

**Note:** Unbootable reason codes are a best-effort debug and RMA helper.
The device's persistent metadata structures may not track unbootable reasons,
and other software that interacts with boot slots may not set unbootable reason
codes accurately.

### Description

Marks a slot as not a valid boot target.
The slot's *Priority*, *TriesRemaining*, and *Successful* fields are all set to
`0`.
Subsequent calls to `GetSlotInfo()` **MUST** reflect these changes to slot info.
If the slot was the current slot, the current boot target will have changed.
This change **MUST** be reflected in subsequent calls to `GetCurrentSlot()`.

If the protocol driver supports tracking slot unbootable reasons, then
subsequent calls to `GetSlotInfo()` **MUST** have the same *UnbootableReason* in
the info structure.

### Status Codes Returned

| Return Code             | Semantics                                                                                                             |
|:------------------------|:----------------------------------------------------------------------------------------------------------------------|
| `EFI_SUCCESS`           | The call completed successfully.                                                                                      |
| `EFI_INVALID_PARAMETER` | *This* is `NULL` or improperly aligned, the value of *Idx* is invalid, or the value of *UnbootableReason* is invalid. |
| `EFI_DEVICE_ERROR`      | There was an error reading metadata from persistent storage.                                                          |
| `EFI_VOLUME_CORRUPTED`  | The metadata loaded is invalid or corrupt. The caller should call `Reinitialize` before taking other actions.         |

## `GBL_EFI_AB_SLOT_PROTOCOL.MarkBootAttempt()`

### Summary

Marks a boot attempt on the current slot.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_AB_SLOT_MARK_BOOT_ATTEMPT)(
    IN GBL_EFI_AB_SLOT_PROTOCOL* This,
);
```
### Parameters

*This*

A pointer to the [`GBL_EFI_AB_SLOT_PROTOCOL`](#protcol-interface-structure)
instance.

### Description

Updates internal metadata for the current boot target slot.
If the current slot has registered a successful boot, its tries remaining field
is left unchanged.
If there are no slots with non-zero *Successful* or *Tries* fields, the call to
`MarkBootAttempt()` **MUST** return `EFI_ACCESS_DENIED`. The bootloader then
must decide on the next action to take.

Subsequent calls to `GetSlotInfo()` and `GetCurrentSlot()` **MUST** reflect
the decremented tries.

### Status Codes Returned

| Return Code             | Semantics                                                                                                     |
|:------------------------|:--------------------------------------------------------------------------------------------------------------|
| `EFI_SUCCESS`           | The call completed successfully.                                                                              |
| `EFI_INVALID_PARAMETER` | *This* is `NULL` or improperly aligned.                                                                       |
| `EFI_DEVICE_ERROR`      | There was an error reading metadata from persistent storage.                                                  |
| `EFI_VOLUME_CORRUPTED`  | The metadata loaded is invalid or corrupt. The caller should call `Reinitialize` before taking other actions. |
| `EFI_ACCESS_DENIED`     | The current slot has no more tries remaining.                                                                 |

## `GBL_EFI_AB_SLOT_PROTOCOL.Reinitialize()`

### Summary

Reinitializes all boot slot metadata to a known initial state.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_AB_SLOT_REINITIALIZE)(
    IN GBL_EFI_AB_SLOT_PROTOCOL* This,
);
```

### Parameters

*This*

A pointer to the [`GBL_EFI_AB_SLOT_PROTOCOL`](#protcol-interface-structure)
instance.

### Description

In particular, all slots should have the following fields cleared and set to
device-specific defaults:
* *Priority*
* *Tries*

and have the following fields set to `0`:
* *UnbootableReason*
* *MergeStatus*
* *Successful*

This may change the current target boot slot.
See the [Boot Slot Coherency Warning](#boot-slot-coherency-warning) for details.

### Status Codes Returned

| Return Code             | Semantics                                              |
|:------------------------|:-------------------------------------------------------|
| `EFI_SUCCESS`           | The call completed successfully.                       |
| `EFI_INVALID_PARAMETER` | *This* is `NULL` or improperly aligned.                |
| `EFI_ACCESS_DENIED`     | Device policy prohibited resetting boot slot metadata. |

## `GBL_EFI_AB_SLOT_PROTOCOL.GetBootReason()`

### Summary

Gets the current boot reason and subreason.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_AB_SLOT_GET_BOOT_REASON)(
    IN GBL_EFI_AB_SLOT_PROTOCOL* This,
    OUT UINT32*                  Reason,
    IN OUT UINTN*                SubreasonLength;
    OUT UINT8*                   Subreason;
);
```

### Related Definitions

```c
typedef enum _GBL_EFI_AB_SLOT_BOOT_REASON {
    EMPTY = 0,
    UNKNOWN = 1,
    WATCHDOG = 14,
    KERNEL_PANIC = 15,
    RECOVERY = 3,
    BOOTLOADER = 55,
    COLD = 56,
    HARD = 57,
    WARM = 58,
    SHUTDOWN = 59,
    REBOOT = 18,
} GBL_EFI_AB_SLOT_BOOT_REASON;
```

### Parameters

*This*

A pointer to the [`GBL_EFI_AB_SLOT_PROTOCOL`](#protcol-interface-structure)
instance.

*Reason*

On exit, the boot reason code. See [Related Definitions](#related-definitions-2)
for the list of valid codes.

*SubreasonLength*

On entry, the length of *Subreason* in bytes.
On exit, the length of the UTF-8 encoded string pointed to by *Subreason*,
ignoring any Null-terminator.

*Subreason*

On exit, the boot subreason as a UTF-8 encoded, Null-terminated string.

### Description

The boot reason is an Android mechanism for communicating between the running
system and the bootloader. For example, if the boot reason is 'recovery', the
bootloader should load the recovery RAM disk and command line. This information
is stored in a device specific location and format.

### Status Codes Returned

| Return Code             | Semantics                                                                                                                                                   |
|:------------------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `EFI_SUCCESS`           | The call completed successfully.                                                                                                                            |
| `EFI_INVALID_PARAMETER` | One of *This*, *Reason*, *SubreasonLength*, or *Subreason* is `NULL` or improperly aligned.                                                                 |
| `EFI_BUFFER_TOO_SMALL`  | *Subreason* is too small to store the serialized subreason string. The value of *SubreasonLength* is modified to contain the minimum necessary buffer size. |
| `EFI_VOLUME_CORRUPTED`  | The metadata loaded is invalid or corrupt. The caller should call `Reinitialize` before taking other actions.                                               |

## `GBL_EFI_AB_SLOT_PROTOCOL.SetBootReason()`

### Summary

Sets the current boot reason.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_AB_SLOT_SET_BOOT_REASON)(
    IN GBL_EFI_AB_SLOT_PROTOCOL* This,
    IN UINT32                    Reason,
    IN UINTN                     SubreasonLength,
    IN UINT8                     Subreason,
);
```

### Parameters

*This*

A pointer to the [`GBL_EFI_AB_SLOT_PROTOCOL`](#protcol-interface-structure)
instance.

*Reason*

The desired boot reason to set. See [here](#related-definitions-2) for the list
of valid boot reasons.

*SubreasonLength*

The length of the *Subreason* string.

*Subreason*

The desired boot subreason as a UTF-8 encoded, Null-terminated string.

### Description

Sets the Android boot reason and subreason.
This is usually used by the bootloader to clear the boot reason.
See [`GetBootReason()`](#gbl_efi_ab_slot_protocolgetbootreason) for more
information about boot reasons.

### Status Codes Returned

| Return Code             | Semantics                                                                               |
|:------------------------|:----------------------------------------------------------------------------------------|
| `EFI_SUCCESS`           | The call completed successfully.                                                        |
| `EFI_INVALID_PARAMETER` | One of *This*, *Reason*, or *Subreason* is `NULL` or improperly aligned.                |
| `EFI_INVALID_PARAMETER` | *Reason* is not a valid reason code or *Subreason* is not a valid UTF-8 encoded string. |
| `EFI_UNSUPPORTED`       | The platform does not support setting the boot reason.                                  |
| `EFI_BAD_BUFFER_SIZE`   | *Subreason* is too large  to be written to persistent storage.                          |

## `GBL_EFI_AB_SLOT_PROTOCOL.Flush()`

### Summary

Writes any slot metadata modifications to persistent storage.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_AB_SLOT_FLUSH)(
    IN GBL_EFI_AB_SLOT_PROTOCOL* This,
);
```

### Parameters

*This*

A pointer to the [`GBL_EFI_AB_SLOT_PROTOCOL`](#protcol-interface-structure)
instance.

### Description

Protocol driver implementations may store modifications to boot slot metadata in
memory before committing changes to storage in a single write operation.
Protocol consumers need a mechanism to instruct the driver that they are
finished operating on boot slots and that changes should be committed.
The implementation should conduct any necessary ancillary tasks, e.g.
recalculating checksums, before writing to storage.
This is an optimization for performance and flash lifetime; implementations are
free to write all modifications to storage as they occur and to define `Flash()`
as a no-op.

### Status Codes Returned

| Return Code        | Semantics                                                 |
|:-------------------|:----------------------------------------------------------|
| `EFI_SUCCESS`      | The call completed successfully.                          |
| `EFI_DEVICE_ERROR` | The device reported a write error during synchronization. |
