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

#ifndef __GBL_EFI_COMMON_H__
#define __GBL_EFI_COMMON_H__

#include <types.h>

#define GBL_EFI_VENDOR_GUID                                     \
  EfiGuid {                                                     \
    .data1=0x5a6d92f3,                                          \
      .data2=0xa2d0,                                            \
      .data3=0x4083,                                            \
      .data4=[0x91, 0xa1, 0xa5, 0x0f, 0x6c, 0x3d, 0x98, 0x30]   \
  }
#define GBL_EFI_OS_BOOT_TARGET_VARNAME "gbl_os_boot_fuchsia"

#endif  /* __GBL_EFI_COMMON_H__ */
