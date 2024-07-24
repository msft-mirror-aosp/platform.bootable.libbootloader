/*
 * Copyright (C) 2024 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */

// This is a custom protocol introduced by GBL.
// See gbl/docs/GBL_EFI_FASTBOOT_USB_PROTOCOL.md for details.

#ifndef __GBL_EFI_FASTBOOT_USB_H__
#define __GBL_EFI_FASTBOOT_USB_H__

#include "types.h"

typedef struct GblEfiFastbootUsbProtocol {
  uint64_t revision;
  EfiStatus (*fastboot_usb_interface_start)(struct GblEfiFastbootUsbProtocol* self,
                                            size_t* max_packet_size);
  EfiStatus (*fastboot_usb_interface_stop)(struct GblEfiFastbootUsbProtocol* self);
  EfiStatus (*fastboot_usb_receive)(struct GblEfiFastbootUsbProtocol* self,
                                    size_t* buffer_size, void* buffer);
  EfiStatus (*fastboot_usb_send)(struct GblEfiFastbootUsbProtocol* self,
                                 size_t* buffer_size, const void* buffer);
  EfiEvent wait_for_send_completion;
} GblEfiFastbootUsbProtocol;

#endif  //__GBL_EFI_FASTBOOT_USB_H__
