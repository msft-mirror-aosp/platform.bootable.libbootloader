# GBL EFI Image Loading Protocol

This document describes the GBL Image Loading protocol. This optional protocol
defines interfaces that can be used by EFI applications to specify implement
customised buffer location in memory. And additional images for verification.

|||
| :--- | :--- |
| **Status** | Work in progress |
| **Created** | 2024-12-11 |


## GBL_EFI_IMAGE_LOADING_PROTOCOL

### Summary

This protocol allows firmware to provide platform reserved memory spaces to
applications for a specific usage or feature, or alternatively, specify the
amount of memory the application should allocate dynamically for it.

It also provides interface to communicate additional images to be verified by
GBL.

### GUID

```c
// {db84b4fa-53bd-4436-98a7-4e0271428ba8}
#define GBL_EFI_IMAGE_LOADING_PROTOCOL_GUID          \
  {                                                  \
    0xdb84b4fa, 0x53bd, 0x4436, {                    \
      0x98, 0xa7, 0x4e, 0x02, 0x71, 0x42, 0x8b, 0xa8 \
    }                                                \
  }
```

### Revision Number

```c
#define GBL_EFI_IMAGE_PROTOCOL_PROTOCOL_REVISION 0x00010000
```

### Protocol Interface Structure

```c
typedef struct _GBL_EFI_IMAGE_LOADING_PROTOCOL {
  UINT64                        Revision;
  GBL_EFI_GET_IMAGE_BUFFER      GetBuffer;
  GBL_EFI_GET_VERIFY_PARTITIONS GetVerifyPartitions;
} GBL_EFI_IMAGE_LOADING_PROTOCOL;
```

### Parameters

**Revision** \
The revision to which the GBL_EFI_IMAGE_BUFFER_PROTOCOL adheres. All future
revisions must be backwards compatible. If a future version is not backwards
compatible, a different GUID must be used.

**GetBuffer** \
Query custom buffer for the image. See
[`GBL_EFI_IMAGE_LOADING_PROTOCOL.GetBuffer()`](#gbl_efi_image_loading_protocolgetbuffer).

**GetVerifyPartitions** \
Query for list of partitions to be verified by GBL. See
[`GBL_EFI_IMAGE_LOADING_PROTOCOL.GetVerifyPartitions()`](#gbl_efi_image_loading_protocolgetverifypartitions).


## GBL_EFI_IMAGE_LOADING_PROTOCOL.GetBuffer()

### Summary

`GetBuffer()` is used by GBL to get buffers for loading different images into
RAM.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI *GBL_EFI_GET_IMAGE_BUFFER) (
  IN GBL_EFI_IMAGE_LOADING_PROTOCOL *This,
  IN GBL_EFI_IMAGE_INFO             *ImageInfo,
  OUT GBL_EFI_IMAGE_BUFFER          *Buffer,
)
```

### Parameters

**This** \
A pointer to the
[`GBL_EFI_IMAGE_LOADING_PROTOCOL`](#gbl_efi_image_loading_protocol) instance.

**ImageInfo** \
Information for the requested buffer. See
[`GBL_EFI_IMAGE_INFO`](#gbl_efi_image_info) for details.

**Buffer** \
Output pointer for `GBL_EFI_IMAGE_BUFFER`. See
[`GBL_EFI_IMAGE_BUFFER`](#gbl_efi_image_buffer) for details.

### Description

The interface is for the firmware to provide platform reserved memory spaces
to, or instruct caller to allocate specific amount of memory for the usage
context described in `GBL_EFI_IMAGE_INFO.StrUtf16`. The usage context is
application specific and may represent usages such as buffers for loading
specific partitions, sharing data with secure world, and downloading in
fastboot etc.

If platform has a reserved memory space for the usage context,
`GBL_EFI_IMAGE_BUFFER.Memory` and `GBL_EFI_IMAGE_BUFFER.SizeBytes` should be
set to the address and size of the memory. Ownership of the provided memory
must be passed exclusively to GBL, and must not be retained for any other
purpose by firmware.

If the caller should allocate memory dynamically by itself for the usage
context, `GBL_EFI_IMAGE_BUFFER.Memory` should be set to NULL and
`GBL_EFI_IMAGE_BUFFER.SizeBytes` should be set to the amount of memory caller
should allocate.

Caller may pass a suggested size via `GBL_EFI_IMAGE_INFO.SizeBytes` based on
its run time knowledge. Implementation should eventually determine the size.

### Status Codes Returned

|||
| --- | --- |
| EFI_SUCCESS | Buffer provided successfully |
| EFI_OUT_OF_RESOURCES | Failed to allocate buffers due to lack of free memory |

### Related Definitions

#### GBL_EFI_IMAGE_BUFFER

```c
typedef
struct GBL_EFI_IMAGE_BUFFER {
  VOID  *Memory;
  UINTN SizeBytes;
} GBL_EFI_IMAGE_BUFFER;
```

**Memory** \
Start address of the reserved buffer or NULL if caller should allocate.

**SizeBytes** \
Size of the reserved buffer or amount of memory caller should allocate.

## GBL_EFI_IMAGE_LOADING_PROTOCOL.GetVerifyPartitions()

### Summary

Query for list of partitions to be verified by GBL.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI *GBL_EFI_GET_VERIFY_PARTITIONS) (
  IN GBL_EFI_IMAGE_LOADING_PROTOCOL *This,
  IN OUT UINTN                      *NumberOfPartitions,
  IN OUT GBL_EFI_PARTITION_NAME     *Partitions,
);
```

### Parameters

**This** \
A pointer to the
[`GBL_EFI_IMAGE_LOADING_PROTOCOL`](#gbl_efi_image_loading_protocol) instance.

**NumberOfPartitions** \
Number of elements in `Partitions[]`. Should be updated to
number of partitions returned. If there are no partitions to be verified,
`NumberOfPartitions` should be set to 0.

**Partitions** \
Array of partitions' names that should be verified. Should be update on return.
And contain `NumberOfPartitions` valid elements.

### Description

This function is used to override list of partitions to be verified by GBL.

If this function is not implemented or returns `EFI_UNSUPPORTED` GBL will verify
default list of partitions.

[`GBL_EFI_PARTITION_NAME`](#gbl_efi_partition_name) is struct representing
partition name. Partition name is UCS-2 string of at most
`PARTITION_NAME_LEN_U16` elements with terminating `NULL` element.

### Status Codes Returned

|||
| --- | --- |
| EFI_SUCCESS | Successfully provided additional partitions to verify |
| EFI_INVALID_PARAMETER | If `Partitions[]` is `NULL`, where `NumberOfPartitions != 0` |

### Related Definitions

#### GBL_EFI_PARTITION_NAME

```c
const size_t PARTITION_NAME_LEN_U16 = 36;

typedef
struct GBL_EFI_PARTITION_NAME {
  CHAR16 StrUtf16[PARTITION_NAME_LEN_U16];
} GBL_EFI_PARTITION_NAME;
```

**StrUtf16** \
UCS-2 C-String. This string contains partition name, that identifies what
partition to use for additional validation. The string is at most
`PARTITION_NAME_LEN_U16` of char16_t elements. E.g. `u"boot"`, `u"fdt"`

#### GBL_EFI_IMAGE_INFO

```c
const size_t PARTITION_NAME_LEN_U16 = 36;

typedef
struct GBL_EFI_IMAGE_INFO {
  CHAR16 ImageType[PARTITION_NAME_LEN_U16];
  UINTN  SizeBytes;
} GBL_EFI_IMAGE_INFO;
```

**ImageType** \
UCS-2 C-String. This string describes the usage context for the buffer being
queried. It should be at most `PARTITION_NAME_LEN_U16` of char16_t elements
including terminating `u'\0'`. E.g. `u"dtb"`

Below are usage strings reserved by GBL.

```c
//******************************************************
// GBL reserved image types
//******************************************************
// Buffer for loading, verifying and fixing up OS images.
#define GBL_IMAGE_TYPE_OS_LOAD L"os_load"
// Buffer for use as fastboot download buffer.
#define GBL_IMAGE_TYPE_FASTBOOT L"fastboot"
```

**SizeBytes** \
Size of the buffer or allocation suggested by the caller.
