# Fastboot in GBL

This document describes Fastboot in the [GBL UEFI bootloader](../efi/BUILD).

## Transport

The GBL UEFI bootloader supports both Fastboot over TCP and USB. To enable
Fastboot over TCP, the UEFI loader needs to implement the
`EFI_SIMPLE_NETWORK_PROTOCOL` protocol. To enable Fastboot over USB, the
[GBL_EFI_FASTBOOT_USB_PROTOCOL](./GBL_EFI_FASTBOOT_USB_PROTOCOL.md) protocol is needed.
GBL automatically establishes the corresponding transport channel if the needed
protocol is available.

## Definition of Partition

Certain fastboot commands such as `fastboot flash`, `fastboot fetch` and
`fastboot getvar partition-size` require to specify a partition. GBL Fastboot
assumes that the platform may have multiple storage devices that may or may not
use GPT partitions. Therefore, in the context of GBL Fastboot, the notion
"partition" is defined to represent both GPT partitions or raw storage of any
sub window and on any storage device. Specifically, the following semantics are
introduced for specifying a partition:

* GPT partitions
  ```sh
  <part>[:<block_id>]
  <part>:[<block_id>][:<offset>]
  <part>:[<block_id>]:[<offset>][:<size>]
  ```
  This specifies range `[offset, offset+size)` in GPT partition `part` on the
  block device with ID `block id`. `block_id`, `offset` and `size` must be a
  64bit integer hex string. If `block id` is not given, GBL will check and only
  accept it if the GPT partition is unique among all devices. `offset` defaults
  to 0 if not given. `size` defaults to the rest of the GPT partition after
  `offset` if not given. The list of GPT partitions, block devices and IDs are
  listed by `fastboot getvar all`

  Examples:
  * `fastboot flash boot_a` -- Checks that `boot_a` is a unique GPT partition
  among all storage devices and flashes in the entire range of the partition.
  * `fastboot flash boot_a:0x0` or `boot_a:0` -- Flashes in the entire range of
  GPT partition "boot_a" on block device 0.
  * `fastboot flash boot_a:0:200` -- Flashes only in range `[512, end)` of GPT
  partition "boot_a" on block device 0.
  * `fastboot flash boot_a:0:200:200` -- Flashes only in range `[512, 1024)` of
  GPT partition "boot_a" on block device 0.
  * `fastboot flash boot_a:::` -- Same as `"boot_a"`.

* Raw storage
  ```
  :<block_id>
  :<block_id>[:<offset>]
  :<block_id>:[<offset>][:<size>]
  ```
  This is similar to the case of GPT partitions except that `part` is an empty
  string and `block_id` is mandatory. It specifies range `[offset, offset+size)`
  of the raw data on the block device with ID `block_id`. `offset` defaults to
  0 if not given. `size` defaults to the rest of the storage after `offset` if
  not given.

## Non-blocking `fastboot flash`.

If the UEFI firmware supports `EFI_BLOCK_IO2_PROTOCOL` for the block devices,
GBL Fastboot provides an option to make `fastboot flash` non-blocking.
Specifically, after the image is downloaded, GBL Fastboot will launch a
separate task in the background for writing the image to the device, while
itself will continue to listen for the next Fastboot command from the host,
including a new `fastboot flash` command. This provides some paralellism
between downloading and flashing when the host is flashing multiple images.
Example:

```
fastboot oem gbl-enable-async-block-io
fastboot flash boot_a <image>
fastboot flash boot_b <image>
fastboot flash vendor_boot_a <image>
...
fastboot oem gbl-sync-blocks
fastboot oem gbl-disable-async-block-io
```

If a block device is busy processing a previous flash when a new image is
downloaded and ready to be flashed, it will be blocked until the previous flash
is completed. Different block devices are independent to each other.

Because IO is now non-blocking, the return status of a `fastboot flash` does
necessarily represents the status of the IO. If a block device encounters
errors while processing a non-blocking IO, all subsequent flash requests will
be rejected and the host should reboot the device.
`fastboot oem gbl-sync-blocks` can be used to wait until all currently pending
flash are completed. The command returns error if any block encounters errors.
