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
  GBL_EFI_AVB_HANDLE_VERIFICATION_RESULT HandleVerificationResult,
} GBL_EFI_AVB_PROTOCOL;
```

### Parameters

#### Revision
The revision to which the `GBL_EFI_AVB_PROTOCOL` adheres. All
future revisions must be backwards compatible. If a future version is not
backwards compatible, a different GUID must be used.

#### HandleVerificationResult
Handle AVB verification result (i.e update ROT, set device state, display UI
warnings/errors, handle anti-tampering, etc).
[`HandleVerificationResult()`](#HandleVerificationResult).

TODO(b/337846185): Cover more AVB functionality such as verify keys, rollback
indexes, open dice, etc.
TODO(b/337846185): Detailed (per-method) doc once protocol is finalized.
