# Partitions in GBL

This document describes how GBL defines and handles partitions on mass storage
devices.

## Definition of Partition

In GBL, all EFI devices that implement either the `EFI_BLOCK_IO_PROTOCOL` or
`EFI_BLOCK_IO2_PROTOCOL` protocols are considered storage devices that may
contain necessary data for GBL to access. For each of this device, GBL supports
two schemes of partition:

1. Entire raw storage as a partition.

   This scheme treats the entire storage device as a single partition. For
   storage devices intended to be used according to this scheme, the device
   need to provide an instance of device path that ends with the GBL
   "Vendor-Defined Media Device Path" defined as follows.

   | Mnemonic | Bytes Offset | Bytes Length | Description |
   | ----------- | ----------- | ----------- | ----------- |
   | Type | 0 | 1 | Type 4-Media Device Path. |
   | Sub-Type | 1 | 1 | Sub-Type 3 - Vendor. |
   | Length | 2 | 2 | Length of this structure in bytes. Length is 92 bytes. |
   | Vendor GUID | 4 | 16 | The `GBL_VENDOR_MEDIA_DEVICE_PATH_GUID` GUID defined below. |
   | Vendor Defined Data | 20 | 72 | Null-terminated ASCII partition name. |

   ```c
   // {a09773e3-0xf027-0x4f33-adb3-bd8dcf4b3854}
   #define GBL_VENDOR_MEDIA_DEVICE_PATH_GUID           \
     {                                                  \
       0xa09773e3, 0xf027, 0x4f33, {                    \
         0xad, 0xb3, 0xbd, 0x8d, 0xcf, 0x4b, 0x38, 0x54 \
       }                                                \
     }
   ```

   The partition will be identified using the null-terminated ASCII name from
   the device path in the context of booting and fastboot.


2. UEFI GUID Partition Table (GPT)

   For all other storage devices that doesn't have an instance of GBL
   vendor-defined media device path, GBL considers them to be using the GPT
   partition scheme defined in the UEFI spec. Each partition will be identified
   using its corresponding GPT partition name in the context of booting and
   fastboot.

GBL fastboot implementation introduces a special syntax
`<part>/<storage id>/<offset>/<size>` for specifying arbitrary subranges of a
partition on one of the potentially multiple storage devices. Thus the
partition name cannot contain character `'/'`. The name `gpt` is reserved for
flashing GPT partition table and thus should not be used as partition name.
See this [doc](./gbl_fastboot.md) for more details.
