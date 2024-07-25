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
// See gbl/docs/gbl_efi_os_configuration_protocol.md for details.

#ifndef __GBL_OS_CONFIGURATION_PROTOCOL_H__
#define __GBL_OS_CONFIGURATION_PROTOCOL_H__

#include "types.h"

typedef struct GblEfiOsConfigurationProtocol {
  uint64_t revision;
  EfiStatus (*fixup_kernel_commandline)(
      struct GblEfiOsConfigurationProtocol* self, char8_t* data,
      size_t* buffer_size);
  // TODO(b/353272981): remaining fields.
} GblEfiOsConfigurationProtocol;

#endif  //__GBL_OS_CONFIGURATION_PROTOCOL_H__
