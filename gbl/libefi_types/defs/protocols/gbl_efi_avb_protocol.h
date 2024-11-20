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
 */

// This is a custom protocol introduced by GBL.
// See gbl/docs/gbl_efi_avb_protocol.md for details.

#ifndef __GBL_AVB_PROTOCOL_H__
#define __GBL_AVB_PROTOCOL_H__

#include "types.h"

// Os boot state color.
//
// https://source.android.com/docs/security/features/verifiedboot/boot-flow#communicating-verified-boot-state-to-users
typedef enum GBL_EFI_AVB_BOOT_STATE_COLOR {
  GREEN,
  YELLOW,
  ORANGE,
  RED_EIO,
  RED,
} GblEfiAvbBootStateColor;

typedef struct {
  // GblEfiAvbBootStateColor
  uint32_t color;

  // TODO(b/337846185): Add result vbmeta digest.

  // Pointers to zero terminated os versions and security_patches for different
  // boot components. NULL is provided in case value isn't presented in the boot
  // artifacts or fatal AVB failure.
  // https://source.android.com/docs/core/architecture/bootloader/version-info-avb
  const char8_t* boot_version;
  const char8_t* boot_security_patch;
  const char8_t* system_version;
  const char8_t* system_security_patch;
  const char8_t* vendor_version;
  const char8_t* vendor_security_patch;
} GblEfiAvbVerificationResult;

typedef struct GblEfiAvbProtocol {
  uint64_t revision;

  EfiStatus (*handle_verification_result)(
      struct GblEfiAvbProtocol* self,
      const GblEfiAvbVerificationResult* result);

} GblEfiAvbProtocol;

#endif  //__GBL_AVB_PROTOCOL_H__