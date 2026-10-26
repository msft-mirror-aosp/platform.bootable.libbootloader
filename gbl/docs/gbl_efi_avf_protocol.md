# GBL EFI AVF Protocol

|                |            |
| :------------- | :--------- |
| **Status**     | Stable     |
| **Created**    | 2025-03-31 |
| **Stabilized** | 2026-05-22 |

## GBL_EFI_AVF_PROTOCOL

### Summary

While GBL is responsible for loading pvmfw and constructing the corresponding
configuration to share with the Android Virtualization Framework, it still
relies on the firmware through this protocol to get certain configurations.

The `GBL_EFI_AVF_PROTOCOL` is optional. When implemented, GBL loads pvmfw along
with related configuration, and refuses to boot if any error occurs. If the
protocol is not present, GBL ignores the `pvmfw` partition, and AVF will not be
available on such devices.

### GUID

```c
// {e7f1c4a6-0a52-4f61-bd98-9e60b559452a}
#define GBL_EFI_AVF_PROTOCOL_GUID                    \
  {                                                  \
    0xe7f1c4a6, 0x0a52, 0x4f61, {                    \
      0xbd, 0x98, 0x9e, 0x60, 0xb5, 0x59, 0x45, 0x2a \
    }                                                \
  }
```

### Revision Number

```c
#define GBL_EFI_AVF_PROTOCOL_REVISION GBL_PROTOCOL_REVISION(1, 0)
```

See [GBL Custom Protocol Revisions][custom_protocol_revisions] for details about
protocol revisions.

### Protocol Interface Structure

```c
typedef struct _GBL_EFI_AVF_PROTOCOL {
  UINT64                                   Revision;
  GBL_EFI_AVF_READ_VENDOR_DICE_HANDOVER    ReadVendorDiceHandover;
  GBL_EFI_AVF_READ_SECRETKEEPER_PUBLIC_KEY ReadSecretKeeperPublicKey;
} GBL_EFI_AVF_PROTOCOL;
```

### Parameters

#### Revision

The revision to which the `GBL_EFI_AVF_PROTOCOL` adheres. All future revisions
must be backwards compatible. If a future version is not backwards compatible, a
different GUID must be used.

#### ReadVendorDiceHandover

Retrieves the vendor DICE handover, covering GBL and earlier boot stages, to be
wrapped by GBL with pvmfw layer. See
[`ReadVendorDiceHandover()`][read_vendor_dice_handover] for more information.

#### ReadSecretKeeperPublicKey

Retrieves the Secret Keeper public key to be used in the VM reference DT built
by the GBL. See [`ReadSecretKeeperPublicKey()`][read_secret_keeper_public_key]
for more information.

## GBL_EFI_AVF_PROTOCOL.ReadVendorDiceHandover()

### Summary

Retrieves the vendor DICE handover, covering GBL and earlier boot stages, to be
wrapped by GBL with pvmfw layer.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI *GBL_EFI_AVF_READ_VENDOR_DICE_HANDOVER)(
  IN GBL_EFI_AVF_PROTOCOL *Self,
  IN OUT UINTN            *HandoverSize,
  OUT UINT8               *Handover
  );
```

### Parameters

#### Self

A pointer to the `GBL_EFI_AVF_PROTOCOL` instance.

#### HandoverSize

On function call, this points to the handover buffer size provided by
`Handover`. The implementation is free to provide vendor handover up to this
size.

If the buffer is not large enough to fit the handover, the function should
update `HandoverSize` with the required size and return `EFI_BUFFER_TOO_SMALL`;
GBL will then allocate a larger buffer and repeat the `ReadVendorDiceHandover`
call.

`HandoverSize` must be also updated on success to let GBL determine the provided
handover size.

#### Handover

Pointer to a pre-allocated buffer to store vendor DICE handover provided by FW.

### Description

The Android Virtualization Framework (AVF) leverages the DICE chain (see [Open
Profile for DICE][opendice]) to allow protected VMs (pVMs) to securely prove
their identity to both local and remote entities.

GBL constructs the resulting DICE chain handover by wrapping the vendor DICE
chain, obtained from the firmware via this UEFI call, with the `pvmfw` layer. To
ensure compliance with AVF security requirements, the provided vendor DICE
handover must meet the following criteria:

1. Must provide CDIs and Android DICE chain describing the previous boot steps
   following the [`AndroidDiceHandover`][dice_handover] format defined by the
   [Open Profile for DICE][opendice] reference implementation.
2. Must be rooted in the hardware-backed Unique Device Secret (UDS) on devices
   that fully implement DICE.
3. The FRS (factory reset secret), stored in tamper-evident storage and changed
   during every factory reset, must be used as a hidden input for one of the
   certificates describing a boot stage covered by the vendor DICE chain.
4. GBL must be the latest boot stage described in the vendor DICE chain. GBL EFI
   app code segment should be used as the "code input", and the signatures
   segment as the "authority input" for CDIs calculation.

The resulting DICE chain handover built by GBL is exposed to AVF through the
`/reserved-memory` HLOS device tree node `pkvm_guest_firmware`, marked as
`compatible="linux,pkvm-guest-firmware-memory"`, following the
[pvmfw][pvmfw_firmware_memory] specification.

GBL relies on the presence of this protocol to determine whether AVF is
supported or not. If present, GBL will run AVF-related setup (loading pVM
firmware and generating configuration data). In addition, GBL will add the
corresponding bootconfig parameters used by AVF -
`androidboot.hypervisor.protected_vm.supported`, and
`androidboot.hypervisor.vm.supported`.

The AVF protocol can be uninstalled at runtime if needed. In that case, GBL will
skip all the AVF-related work. To uninstall AVF protocol, use the
`UninstallProtocolInterface` function.

TODO(b/578052649): be less specific about AVF DICE requirements once protocol is
mainly adopted by the ecosystem.

### Status Codes Returned

| Return Code            | Semantics                                                                        |
| :--------------------- | :------------------------------------------------------------------------------- |
| `EFI_SUCCESS`          | Handover was successfully written.                                               |
| `EFI_BUFFER_TOO_SMALL` | The buffer is too small; `HandoverSize` has been updated with the required size. |
| Other                  | Error loading vendor DICE handover; GBL will refuse to boot                      |

## GBL_EFI_AVF_PROTOCOL.ReadSecretKeeperPublicKey()

### Summary

Retrieves the Secret Keeper public key to be used in the VM reference DT built
by GBL.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI *GBL_EFI_AVF_READ_SECRET_KEEPER_PUBLIC_KEY)(
  IN GBL_EFI_AVF_PROTOCOL *Self,
  IN OUT UINTN            *PublicKeySize,
  OUT UINT8               *PublicKey
  );
```

### Parameters

#### Self

A pointer to the `GBL_EFI_AVF_PROTOCOL` instance.

#### PublicKeySize

On function call, this points to the Secret Keeper public key buffer size
provided by `PublicKey`. The implementation is free to provide public key up to
this size.

If the buffer is not large enough to fit the public key, the function should
update `PublicKeySize` with the required size and return `EFI_BUFFER_TOO_SMALL`;
GBL will then allocate a larger buffer and repeat the
`ReadSecretKeeperPublicKey` call.

`PublicKeySize` must be also updated on success to let GBL determine the
provided public key size.

#### PublicKey

Pointer to a pre-allocated buffer to store Secret Keeper public key provided by
FW.

### Description

The Android Virtualization Framework (AVF) relies on reference DT provided as a
third entry of the PVMFW configuration to enable an additional verification of
the pVMs.

GBL is responsible for constructing the reference DT configuration following the
[pvmfw requirements][pvmfw_reference_dt] for Android bootloader. This UEFI
method is used by GBL to obtain the Secret Keeper public key from the FW.

### Status Codes Returned

| Return Code            | Semantics                                                                         |
| :--------------------- | :-------------------------------------------------------------------------------- |
| `EFI_SUCCESS`          | Secret Keeper public key was successfully written.                                |
| `EFI_BUFFER_TOO_SMALL` | The buffer is too small; `PublicKeySize` has been updated with the required size. |
| Other                  | Error loading Secret Keeper public key; GBL will refuse to boot                   |

[read_vendor_dice_handover]: #gbl_efi_avf_protocol_readvendordicehandover
[read_secret_keeper_public_key]: #gbl_efi_avf_protocol_readsecretkeeperpublickey
[custom_protocol_revisions]: efi_integration.md#gbl-custom-protocol-revisions
[dice_handover]:
  https://pigweed.googlesource.com/open-dice/+/42ae7760023/src/android.c#212
[opendice]:
  https://pigweed.googlesource.com/open-dice/+/refs/heads/main/docs/specification.md
[pvmfw_firmware_memory]:
  https://cs.android.com/android/platform/superproject/main/+/cf9c0b1007e87a58cb18a72d59ab488b72016c74:packages/modules/Virtualization/guest/pvmfw/README.md;l=71
[pvmfw_reference_dt]:
  https://cs.android.com/android/platform/superproject/main/+/cf9c0b1007e87a58cb18a72d59ab488b72016c74:packages/modules/Virtualization/guest/pvmfw/README.md;l=227
