# GBL EFI Fastboot USB Protocol

This document describes the GBL Fastboot USB protocol. The protocol defines
interfaces that can be used by EFI applications to implement Fastboot over USB.

|||
| ----------- | ----------- |
| **Status** | Work in progress |
| **Created** | 2024-3-21 |


## GBL_EFI_FASTBOOT_USB_PROTOCOL

### Summary

This protocol provides interfaces for platform-specific AVB operations, such as
reading/writing antirollback indices, persistant values, and performing AVB
public key validation etc. It also defines interfaces that abstract platform
USB controller for interfacing with the Android Fastboot tooling. These include
starting/stopping a Fastboot USB interface and sending/receiving USB packets.

### GUID

```c
// {6281a893-ac23-4ca7-b281-340ef8168955}
#define GBL_EFI_FASTBOOT_USB_PROTOCOL_GUID           \
  {                                                  \
    0x6281a893, 0xac23, 0x4ca7, {                    \
      0xb2, 0x81, 0x34, 0x0e, 0xf8, 0x16, 0x89, 0x55 \
    }                                                \
  }
```

### Revision Number

```c
#define GBL_EFI_FASTBOOT_USB_PROTOCOL_REVISION 0x00000000
```

### Protocol Interface Structure

```c
typedef struct _GBL_EFI_FASTBOOT_USB_PROTOCOL {
  UINT64                                              Revision;
  GBL_EFI_FASTBOOT_USB_FASTBOOT_USB_INTERFACE_START   FastbootUsbInterfaceStart;
  GBL_EFI_FASTBOOT_USB_FASTBOOT_USB_INTERFACE_STOP    FastbootUsbInterfaceStop;
  GBL_EFI_FASTBOOT_USB_FASTBOOT_USB_RECEIVE           FastbootUsbReceive;
  GBL_EFI_FASTBOOT_USB_FASTBOOT_USB_SEND              FastbootUsbSend;
  EFI_EVENT                                           WaitForSendCompletion;
} GBL_EFI_FASTBOOT_USB_PROTOCOL;
```

### Parameters

**Revision**  
The revision to which the GBL_EFI_FASTBOOT_USB_PROTOCOL adheres. All future
revisions must be backwards compatible. If a future version is not backwards
compatible, a different GUID must be used.

**FastbootUsbInterfaceStart**  
Starts a USB interface for Fastboot traffic. See
[`GBL_EFI_FASTBOOT_USB_PROTOCOL.FastbootUsbInterfaceStart()`](#gbl_efi_fastboot_usb_protocolfastbootusbinterfacestart).

**FastbootUsbInterfaceStop**  
Stops the USB interface started by `FastbootUsbInterfaceStart()`. See
[`GBL_EFI_FASTBOOT_USB_PROTOCOL.FastbootUsbInterfaceStop()`](#gbl_efi_fastboot_usb_protocolfastbootusbinterfacestop).

**FastbootUsbReceive**  
Polls and receives the next USB packet if available. See
[`GBL_EFI_FASTBOOT_USB_PROTOCOL.FastbootUsbReceive()`](#gbl_efi_fastboot_usb_protocolfastbootusbreceive).

**FastbootUsbSend**  
Sends a USB packet. See
[`GBL_EFI_FASTBOOT_USB_PROTOCOL.FastbootUsbSend()`](#gbl_efi_fastboot_usb_protocolfastbootusbsend).

**WaitForSendCompletion**  
Event used with `EFI_BOOT_SERVICES.WaitForEvent()` to wait for the previous
packet sent by `FastbootUsbSend()` to complete.


## GBL_EFI_FASTBOOT_USB_PROTOCOL.FastbootUsbInterfaceStart()

### Summary

Starts a USB interface for Fastboot.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_FASTBOOT_USB_FASTBOOT_USB_INTERFACE_START)(
  IN GBL_EFI_FASTBOOT_USB_PROTOCOL  *This,
  OUT UINTN                         *MaxPacketSize,
  );
```

### Parameters

*This*  
A pointer to the [`GBL_EFI_FASTBOOT_USB_PROTOCOL`](#gbl_efi_fastboot_usb_protocol)
instance.

*MaxPacketSize*  
On exit, set to the maximum packet size in bytes allowed by the USB interface.

### Description

`FastbootUsbInterfaceStart()` shoud start and expose a device mode USB inteface
that can be used by `FastbootUsbReceive()` and `FastbootUsbSend()` to exchange
USB packets. In order for the interface to be compatible with the Android
Fastboot tool, the interface setup should meet the following requirement:

* The USB interface should contain two bulk endpoints (in, out).
* Max packet size must be 64 bytes for full-speed, 512 bytes for high-speed and
1024 bytes for Super Speed USB.
* The class, subclass and protocol code in the USB interface descriptor should be
set to the values specified by the upstream Fastboot USB protocol:
  * Interface class: 0xff (Vendor specific)
  * Interface subclass: 0x42 (ADB)
  * Interface protocol: 0x03 (Fastboot)
* The USB device descriptor should provide a valid serial number string
descriptor.

**Note**: EFI_USBFN_IO_PROTOCOL is not used because: 1) it lacks support for
specifying serial number and USB3.0 at the time this protocol is drafted. 2)
Other than the requirement above, the rest of USB configuration required by
EFI_USBFN_IO_PROTOCOL is not concerned by the Fastboot USB protocol. The
abstracted interfaces allow EFI Fastboot applications to avoid having to know
how to configure a full USB.

**Note**: This protocol is not applicable to platforms that only operate in USB
host mode. However, platforms that support xHCI debug capability (DbC) can
present as a USB device and thus communicate with a host. Future revision of
this protocol and Android Fastboot tool may support this usecase.

### Status Codes Returned

|||
| ----------- | ----------- |
| EFI_SUCCESS | USB interface is started successfully. |
| EFI_INVALID_PARAMETER | A parameter is invalid. |
| EFI_ALREADY_STARTED | USB interface is already started. |
| EFI_NO_RESPONSE | USB is not connected |
| EFI_UNSUPPORTED | USB is not supported by the platform |
| EFI_DEVICE_ERROR | The physical device reported an error. |

## GBL_EFI_FASTBOOT_USB_PROTOCOL.FastbootUsbInterfaceStop()

### Summary

Stops the USB interface started by `FastbootUsbInterfaceStart()`.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_FASTBOOT_USB_FASTBOOT_USB_INTERFACE_STOP)(
  IN GBL_EFI_FASTBOOT_USB_PROTOCOL  *This
  );
```

### Parameters

*This*  
A pointer to the [`GBL_EFI_FASTBOOT_USB_PROTOCOL`](#gbl_efi_fastboot_usb_protocol)
instance.

### Description

`FastbootUsbInterfaceStop()` should abort any pending transfer and remove the
USB interface started by `FastbootUsbInterfaceStart()` from the USB descriptors.
Upon successful return, the device should no longer be visible as a Fastboot
device from the host.

### Status Codes Returned

|||
| ----------- | ----------- |
| EFI_SUCCESS | USB interface is stopped successfully.|
| EFI_INVALID_PARAMETER | A parameter is invalid.|
| EFI_NOT_STARTED | The USB interface is not started.|
| EFI_DEVICE_ERROR | The physical device reported an error.|

## GBL_EFI_FASTBOOT_USB_PROTOCOL.FastbootUsbReceive()

### Summary

Receives a USB packet from the interface started by
`FastbootUsbInterfaceStart()`.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_FASTBOOT_USB_FASTBOOT_USB_RECEIVE)(
  IN GBL_EFI_FASTBOOT_USB_PROTOCOL  *This,
  IN OUT UINTN                      *BufferSize,
  OUT VOID                          *Buffer,
  );
```

### Parameters

*This*  
A pointer to the [`GBL_EFI_FASTBOOT_USB_PROTOCOL`](#gbl_efi_fastboot_usb_protocol)
instance.

*BufferSize*  
On entry, the size in bytes of `Buffer`. On exit, the size in bytes of the
packet that was received.

*Buffer*  
A pointer to the data buffer to receive the USB packet.

### Description

`FastbootUsbReceive()` should poll and, if available, receive the next USB
packet from the Fastboot USB interface into the provided buffer.

### Status Codes Returned

|||
| ----------- | ----------- |
| EFI_SUCCESS | A new USB packet is received successfully. |
| EFI_INVALID_PARAMETER | A parameter is invalid.|
| EFI_NOT_STARTED | The USB interface is not started.|
| EFI_NOT_READY | No packet has been received from the interface.|
| EFI_BUFFER_TOO_SMALL | Buffer is too small for the next packet. `BufferSize` should be updated to the required size in this case. |
| EFI_DEVICE_ERROR | The physical device reported an error.|

## GBL_EFI_FASTBOOT_USB_PROTOCOL.FastbootUsbSend()

### Summary

Sends a USB packet from the USB interface started by
`FastbootUsbInterfaceStart()`.

### Prototype

```c
typedef
EFI_STATUS
(EFIAPI * GBL_EFI_FASTBOOT_USB_FASTBOOT_USB_SEND)(
  IN GBL_EFI_FASTBOOT_USB_PROTOCOL  *This,
  IN OUT UINTN                      *BufferSize,
  IN CONST VOID                     *Buffer,
  );
```

### Parameters

*This*  
A pointer to the [`GBL_EFI_FASTBOOT_USB_PROTOCOL`](#gbl_efi_fastboot_usb_protocol)
instance.

*BufferSize*  
On entry, the size in bytes of `Buffer` to be sent. If the size is greater than
the maximum packet size of the USB interface, it should be set to the maximum
packet size and EFI_BAD_BUFFER_SIZE should be returned.

*Buffer*  
A pointer to the data buffer to be sent.

### Description

`FastbootUsbSend()` should copy the provided packet into an internal Tx buffer
owned by the protocol driver and initiate the send. The interface is
non-blocking and should return immediately. It should not accept any new packet
if the previous one hasn't complete.

### Status Codes Returned

|||
| ----------- | ----------- |
| EFI_SUCCESS | The USB packet is sent successfully. |
| EFI_INVALID_PARAMETER | A parameter is invalid.|
| EFI_NOT_STARTED | The USB interface is not started.|
| EFI_NOT_READY | The previous packet is still pending. |
| EFI_BAD_BUFFER_SIZE | `BufferSize` is greater than the maximum packet size of the USB interface. `BufferSize` should be updated to the maximum packet size in this case. |
| EFI_DEVICE_ERROR | The physical device reported an error.|
