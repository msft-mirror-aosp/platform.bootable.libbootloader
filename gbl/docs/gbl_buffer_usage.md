# Buffer Usage in GBL

This doc discusses how GBL (EFI bootloader) gets and uses buffers for various
functionalities.

## OS Load Buffer

GBL needs a sufficiently large and contiguous buffer for loading, fixing up and
assembling various OS images such as boot, init_boot, vendor_boot, dtb, dtbo,
misc etc. This buffer can either be from EFI memory allocation or memory space
reserved by the platform. At run time, GBL performs the following for
requesting an OS load buffer.

1. Via
[GBL_EFI_IMAGE_LOADING_PROTOCOL.GetBuffer()](./GBL_EFI_IMAGE_LOADING_PROTOCOL.md#gbl_efi_image_loading_protocolgetbuffer)

   If [GBL_EFI_IMAGE_LOADING_PROTOCOL](./GBL_EFI_IMAGE_LOADING_PROTOCOL.md) is
   implemented, GBL will make a call to
   `GBL_EFI_IMAGE_LOADING_PROTOCOL.GetBuffer()` with input image type set to
   [GBL_IMAGE_TYPE_OS_LOAD](./GBL_EFI_IMAGE_LOADING_PROTOCOL.md#related-definitions-1)
   and input size set to 0 (size determined by vendor). Vendor returns the size
   and address of the reserved memory if available or instructs GBL to
   allocates a specific amount of memory via EFI memory allocation.

2. Via EFI Memory Allocation

   If [GBL_EFI_IMAGE_LOADING_PROTOCOL](./GBL_EFI_IMAGE_LOADING_PROTOCOL.md) is
   not implemented GBL allocates a 256MB size buffer via EFI memory allocation.

## Fastboot Download Buffer

When booting to fastboot mode, GBL requires a buffer for download. The buffer
is requested following the same process as the case of
[OS Load Buffer](#os-load-buffer):

1. Via
[GBL_EFI_IMAGE_LOADING_PROTOCOL.GetBuffer()](./GBL_EFI_IMAGE_LOADING_PROTOCOL.md#gbl_efi_image_loading_protocolgetbuffer)

   If [GBL_EFI_IMAGE_LOADING_PROTOCOL](./GBL_EFI_IMAGE_LOADING_PROTOCOL.md) is
   implemented, GBL will make a call to
   `GBL_EFI_IMAGE_LOADING_PROTOCOL.GetBuffer()` with input image type set to
   [GBL_IMAGE_TYPE_FASTBOOT](./GBL_EFI_IMAGE_LOADING_PROTOCOL.md#related-definitions-1)
   and input size set to 0 (size determined by vendor). Vendor returns the size
   and address of the reserved memory if available or instructs GBL to
   allocates a specific amount of memory via EFI memory allocation.

2. Via EFI Memory Allocation

   If [GBL_EFI_IMAGE_LOADING_PROTOCOL](./GBL_EFI_IMAGE_LOADING_PROTOCOL.md) is
   not implemented GBL allocates a 512MB size buffer via EFI memory allocation.

## AARCH64 Kernel Decopmression

GBL can detect and handle compressed kernel for aarch64. However, current
implementation requires allocating a separate piece of memory for storing
decompressed kernel temporarily. This buffer is allocated via EFI memory
allocation.

## AVB

The AVB (Android Verified Boot) implementation in GBL requires allocating
additional memory for constructing commandline argument strings and loading
vbmeta images from disk and any other vendor required partitions for
verification. The memory is allocated via EFI memory allocation.
