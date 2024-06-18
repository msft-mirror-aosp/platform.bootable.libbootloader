The EFI application of GBL requires certain EFI protocols in order to boot,
and can require other protocols for certain targets or to enable optional features.

### Required Protocols

#### BlockIoProtocol

The BlockIo protocol is required for loading system images from disk.
If a target supports Fastboot mode, it is also used for writing images to disk.

#### SimpleTextOutputProtocol

The SimpleTextOutput protocol is used for logging
and the text-based interface of Fastboot.
On systems where there is no output functionality,
this can be implemented as a series of no-op functions.

### Conditionally Required Protocols

#### RiscvBootProtocol

Determines the boot hart ID which is then passed to the kernel.
Only required for RISC-V targets.

### Optional Protocols

#### AndroidBootProtocol

This is a custom protocol intended to provide
specific functionality needed to boot Android.
A full description is available [here](./EFI_ANDROID_BOOT_PROTOCOL.md).

#### DevicePathProtocol

The DevicePath protocol is a variable length binary structure
made of variable length Device Path nodes.
A handle representing a hardware resource is mapped
to the protocol and provides specific data about that resource.

If all three of DevicePath protocol, DevicePathToText protocol,
and LoadedImage protocol are present, the GBL image path is logged
to the console on load.

This is a useful proof of concept for development to demonstrate
that GBL is running and can interact with the UEFI environment.

#### DevicePathToTextProtocol

The DevicePathToText protocol converts device paths and nodes to text.

#### LoadedImageProtocol

The LoadedImage protocol can be used on the handle of an image to provide
information about the image, including its device handle and device path.

#### SimpleNetworkProtocol

If present, the SimpleNetwork protocol is used to provide Fastboot over TCP.
No other EFI protocols are required: GBL wraps SimpleNetwork to provide TCP.

Note: for security reasons, Fastboot over TCP is only available in dev builds.

#### SimpleTextInputProtocol

TODO: remove this protocol

#### GblSlotProtocol

If present, the system is expected to boot Android. This protocol abstracts over
implementation details in the system AB metadata and provides a common interface
for GBL.
