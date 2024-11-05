# Fastboot in GBL

This document describes Fastboot in the [GBL UEFI bootloader](../efi/BUILD).

## Transport

The GBL UEFI bootloader supports both Fastboot over TCP and USB. To enable
Fastboot over TCP, the UEFI loader needs to implement the
`EFI_SIMPLE_NETWORK_PROTOCOL` protocol. To enable Fastboot over USB, the
[GBL_EFI_FASTBOOT_USB_PROTOCOL](./GBL_EFI_FASTBOOT_USB_PROTOCOL.md) protocol is
needed. GBL automatically establishes the corresponding transport channel if
the needed protocol is available.

## The Partition Argument

Fastboot commands such as `fastboot flash`, `fastboot fetch` and
`fastboot getvar partition-size` operate on partitions and requires a partition
name argument. See this [doc](./partitions.md) for how GBL defines and handles
partitions on storage devices. GBL fastboot additionaly supports accessing sub
ranges of partitions and disambiguating betweeen same name partitions on
multiple storage devices (i.e. in the presence of external or removable boot
storage). The following summarizes the supported syntaxes for partition name
argument in fastboot.

* Partition
  ```sh
  <part>[/<storage_id>]
  <part>/[<storage_id>][/<offset>]
  <part>/[<storage_id>]/[<offset>][/<size>]
  ```

  This specifies range `[offset, offset+size)` in partition `part` on the
  storage device with ID `storage_id`. `storage_id` is a hex string and
  represents a unique integer ID assigned to each storage device detected
  by GBL. The integer ID is for disambiguation purpose in case multiple storage
  devices have same name partitions.  If `storage_id` is not given, GBL will
  check if a default storage ID is set via
  `fastboot oem gbl-set-default-block <storage_id>` and use the default ID if
  set. If the default ID is not set, GBL will check that `part` can match to a
  unique parition. Otherwise, it will be rejected. The default ID can be unset
  via `fastboot oem gbl-unset-default-block`. `offset` and `size` must be a
  64bit integer hex string. `offset` defaults to 0 if not given. `size`
  defaults to the rest of the partition after `offset` if not given.

  Examples:
  * `fastboot flash boot_a` -- If there is only one storage or a default
    storage ID is set via `fastboot oem gbl-set-default-block <default ID>`,
    flashes in the entire range of the storage. If not, checks that `boot_a`
    can match to a unique partition among all storage devices and flashes to
    it.
  * `fastboot flash boot_a/0x0` or `boot_a/0` -- Flashes in the entire range of
    partition "boot_a" on storage device 0.
  * `fastboot flash boot_a/0/200` -- Flashes only in range `[512, end)` of
    partition "boot_a" on storage device 0.
  * `fastboot flash boot_a/0/200/200` -- Flashes only in range `[512, 1024)` of
    partition "boot_a" on storage device 0.
  * `fastboot flash boot_a///` -- Same as `"fastboot flash boot_a"`.
  * `fastboot flash boot_a//200/200` -- Same as `"fastboot flash boot_a///"`,
    except that it only flashes in range `[512, 1024)`

* Raw storage devices by ID
  ```
  /[<storage_id>]
  /[<storage_id>][/<offset>]
  /[<storage_id>][/<offset>][/<size>]
  ```

  This is similar to the case of partition except that `part` is an empty
  string. It specifies range`[offset, offset+size)` of the raw data on the
  storage device with ID `storage_id`.  If `storage_id` is not given, GBL will
  check if a default storage ID is set via
  `fastboot oem gbl-set-default-block <storage_id>` and use the default ID if
  set. Otherwise it is rejected. `offset` defaults to 0 if not given. `size`
  defaults to the rest of the block after `offset` if not given. This semantic
  applies to all storage devcies that can detected by GBL, whether or not it is
  a raw storage partition or GPT device.

  Examples:
  * `fastboot flash /` -- If there is only one storage or a default storage ID
    is set via `fastboot oem gbl-set-default-block <default ID>`, flashes in
    the entire range of the storage.
  * `fastboot flash /0x0` or `/0` -- Flashes in the entire range of storage
    device 0.
  * `fastboot flash /0/200` -- Flashes only in range `[512, end)` of storage
    device 0.
  * `fastboot flash /0/200/200` -- Flashes only in range `[512, 1024)` of
    storage device 0.
  * `fastboot flash ///` -- Same as `"fastboot flash /"`.
  * `fastboot flash //200/200` -- Same as `"fastboot flash ///"`, except that
    it only flashes in range `[512, 1024)`

Note: AOSP fastboot client tool introduces a special flash command syntax
`fastboot flash vendor_boot_a:<part_size>` for performing vendor ramdisk
repacking and flashing. This however, does not work with GBL's `'/'` syntax
discussed above, i.e. `fastboot flash vendor_boot_a/0:<part_size>` will not
trigger the repack and flash flow for the vendor_boot_a partition on storage 0
as might be expected. Instead, in this case, user should run
`fastboot oem gbl-set-default-block 0` to set the default block to 0 first and
then use `fastboot flash vendor_boot_a:<part size>` normally.

### Updating GPT Partition Table

GBL also supports the following syntaxes for updating GPT partition table on a
storage device:

```
fastboot flash gpt <path to MBR+primary GPT blob file>
fastboot flash gpt/<storage_id> <path to MBR+primary GPT blob file>
fastboot flash gpt/[<storage_id>][/resize] <path to MBR+primary GPT blob file>
```

User must provide an image file that contains a MBR block and the primary GPT
header and entries. The above command will verify the given GPT and update it
to the specified storage device. If the `resize` option is given, GBL will
adjust the `last usable block` field in the GPT header and the ending block of
the last partition entry to cover the rest of the storage. This is useful for
sharing one single GPT blob file for different devices with varying size of
storage.

Examples:
  * `fastboot flash gpt` -- If there is only one storage or a default storage
    ID is set via `fastboot oem gbl-set-default-block <default ID>`, updates
    the GPT of that storage.
  * `fastboot flash gpt//resize` -- Same as `fastboot flash gpt` but also
    performs resizing.
  * `fastboot flash gpt/0` -- Update GPT to storage device 0.
  * `fastboot flash gpt/0/resize` -- Same as `fastboot flash gpt/0` but also
    performs resizing.


## Non-blocking `fastboot flash`.

If the UEFI firmware supports `EFI_BLOCK_IO2_PROTOCOL` for the storage devices,
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

If a storage device is busy processing a previous flash when a new image is
downloaded and ready to be flashed, it will be blocked until the previous flash
is completed. Different storage devices are independent to each other.

Because IO is now non-blocking, the return status of a `fastboot flash` does
not necessarily represents the status of the IO. If a storage device encounters
errors while processing a non-blocking IO, all subsequent flash requests will
be rejected and the host should reboot the device.
`fastboot oem gbl-sync-blocks` can be used to wait until all currently pending
flash are completed. The command returns error if any previous or current flash
encounters errors.
