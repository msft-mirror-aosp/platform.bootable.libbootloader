# GBL AVB EFI Protocol

This protocol delegates some of AVB-related logic to the firmware, including
tasks such as verifying public keys, handling verification results, and
managing the device’s secure state (e.g., ROT, lock state, rollback indexes,
etc.).

## GBL_EFI_AVB_PROTOCOL

### GUID
```c
// {6bc66b9a-d5c9-4c02-9da9-50af198d912c}
#define GBL_EFI_AVB_PROTOCOL_UUID                    \
  {                                                  \
    0x6bc66b9a, 0xd5c9, 0x4c02, {                    \
      0x9d, 0xa9, 0x50, 0xaf, 0x19, 0x8d, 0x91, 0x2c \
    }                                                \
  }
```

### Revision Number

Note: revision 0 means the protocol is not yet stable and may change in
backwards-incompatible ways.

```c
#define GBL_EFI_AVB_PROTOCOL_REVISION 0x00010000
```

### Protocol Interface Structure

```c
typedef struct _GBL_EFI_AVB_PROTOCOL {
  UINT64 Revision;
  GBL_EFI_AVB_VALIDATE_VBMETA_PUBLIC_KEY ValidateVbmetaPublicKey;
  GBL_EFI_AVB_READ_IS_DEVICE_UNLOCKED ReadIsDeviceUnlocked;
  GBL_EFI_AVB_READ_ROLLBACK_INDEX ReadRollbackIndex;
  GBL_EFI_AVB_WRITE_ROLLBACK_INDEX WriteRollbackIndex;
  GBL_EFI_AVB_READ_PERSISTENT_VALUE ReadPersistentValue;
  GBL_EFI_AVB_WRITE_PERSISTENT_VALUE WritePersistentValue;
  GBL_EFI_AVB_HANDLE_VERIFICATION_RESULT HandleVerificationResult;
} GBL_EFI_AVB_PROTOCOL;
```

### Parameters

#### Revision
The revision to which the `GBL_EFI_AVB_PROTOCOL` adheres. All
future revisions must be backwards compatible. If a future version is not
backwards compatible, a different GUID must be used.

#### ValidateVbmetaPublicKey
Validate proper public key is used to sign HLOS artifacts.
[`ValidateVbmetaPublicKey()`](#ValidateVbmetaPublicKey).

#### ReadIsDeviceUnlocked
Gets whether the device is unlocked.
[`ReadIsDeviceUnlocked()`](#ReadIsDeviceUnlocked).

#### ReadRollbackIndex
Gets the rollback index corresponding to the location given by `index_location`.
[`ReadRollbackIndex()`](#ReadRollbackIndex).

#### WriteRollbackIndex
Sets the rollback index corresponding to the location given by `index_location` to `rollback_index`.
[`WriteRollbackIndex()`](#WriteRollbackIndex).

#### ReadPersistentValue
Gets the persistent value for the corresponding `name`.
[`ReadPersistentValue()`](#ReadPersistentValue).

#### WritePersistentValue
Sets or erases the persistent value for the corresponding `name`.
[`WritePersistentValue()`](#WritePersistentValue).

#### HandleVerificationResult
Handle AVB verification result (i.e update ROT, set device state, display UI
warnings/errors, handle anti-tampering, etc).
[`HandleVerificationResult()`](#HandleVerificationResult).

TODO(b/337846185): Cover more AVB functionality such as rollback indexes, open dice, etc.
TODO(b/337846185): Detailed (per-method) doc once protocol is finalized.

### Status Codes Returned

The following EFI error types are used to communicate result to GBL and libavb in particular:

|                                |                                                                                                                                                         |
| ------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `EFI_SUCCESS`                  | Requested operation was successful `libavb::AvbIOResult::AVB_IO_RESULT_OK`                                                                              |
| `EFI_STATUS_OUT_OF_RESOURCES`  | Unable to allocate memory `libavb::AvbIOResult::AVB_IO_RESULT_ERROR_OOM`                                                                                |
| `EFI_STATUS_DEVICE_ERROR`      | Underlying hardware (disk or other subsystem) encountered an I/O error `libavb::AvbIOResult::AVB_IO_RESULT_ERROR_IO`                                    |
| `EFI_STATUS_NOT_FOUND`         | Named persistent value does not exist `libavb::AvbIOResult::AVB_IO_RESULT_ERROR_NO_SUCH_VALUE`                                                          |
| `EFI_STATUS_END_OF_FILE`       | Range of bytes requested to be read or written is outside the range of the partition `libavb::AvbIOResult::AVB_IO_RESULT_ERROR_RANGE_OUTSIDE_PARTITION` |
| `EFI_STATUS_INVALID_PARAMETER` | Named persistent value size is not supported or does not match the expected size `libavb::AvbIOResult::AVB_IO_RESULT_ERROR_INVALID_VALUE_SIZE`          |
| `EFI_STATUS_BUFFER_TOO_SMALL`  | Buffer is too small for the requested operation `libavb::AvbIOResult::AVB_IO_RESULT_ERROR_INSUFFICIENT_SPACE`                                           |
| `EFI_STATUS_UNSUPPORTED`       | Operation isn't implemented / supported                                                                                                                 |
