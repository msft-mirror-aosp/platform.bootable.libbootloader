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

This protocol allows boards that want a specific RAM location for images to
communicate this to GBL. Default dynamic allocation is used if a specific
location is not provided. It also provides interface to communicate additional
images to be verified by GBL.

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
Image information for the requested buffer. See
[`GBL_EFI_IMAGE_INFO`](#gbl_efi_image_info) for details.

**Buffer** \
Buffer that can be used to load image data. Must be at least
`ImageInfo.SizeBytes`. See [`GBL_EFI_IMAGE_BUFFER`](#gbl_efi_image_buffer) for
details.

### Description

`GetBuffer()` is expected to be called multiple times by GBL to get buffers for
loading different images into RAM.

Implementation can provide custom buffers only for desired images. If there is
no buffer to provide, address (`GblEfiImageBuffer.Memory.`) should be set to
NULL.

Provided buffers must not overlap. GBL will verify if the same buffer was
already returned before proceeding further.

Ownership of the provided memory must be passed exclusively to GBL, and must not
be retained for any other purpose by firmware.

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
Start address of the buffer

**SizeBytes** \
Size of the buffer in bytes. This value can be bigger than requested
size in order to facilitate additional requirements. E.g. partition containing
boot arguments will require appending in place. Or kernel partition might
require scratch pad space after the image.

In case no buffer is provided `GBL_EFI_BUFFER.Memory` should be set to `NULL`.
Then GBL will allocate memory for this image using available allocator.

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
UCS-2 C-String. This string contains partition name(s), that identifies what
buffer to provide. The type string is at most `PARTITION_NAME_LEN_U16` of
char16_t elements including terminating `u'\0'`. E.g. `u"dtb"`

**SizeBytes** \
Requested size for the buffer in bytes