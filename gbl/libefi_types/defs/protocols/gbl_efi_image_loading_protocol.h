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

#ifndef __GBL_EFI_IMAGE_LOADING_PROTOCOL_H__
#define __GBL_EFI_IMAGE_LOADING_PROTOCOL_H__

#include <stddef.h>

#include "types.h"

const uint64_t GBL_EFI_IMAGE_LOADING_PROTOCOL_REVISION = 0x00010000;

const size_t PARTITION_NAME_LEN_U16 = 36;

typedef struct GblEfiImageInfo {
  char16_t ImageType[PARTITION_NAME_LEN_U16];
  size_t SizeBytes;
} GblEfiImageInfo;

typedef struct GblEfiImageBuffer {
  void* Memory;
  size_t SizeBytes;
} GblEfiImageBuffer;

typedef struct GblEfiPartitionName {
  char16_t StrUtf16[PARTITION_NAME_LEN_U16];
} GblEfiPartitionName;

typedef struct GblEfiImageLoadingProtocol {
  uint64_t revision;
  EfiStatus (*get_buffer)(struct GblEfiImageLoadingProtocol* self,
                          const GblEfiImageInfo* ImageInfo,
                          GblEfiImageBuffer* Buffer);
  EfiStatus (*get_verify_partitions)(struct GblEfiImageLoadingProtocol* self,
                                     size_t* NumberOfPartitions,
                                     GblEfiPartitionName* Partitions);
} GblEfiImageLoadingProtocol;

#endif  //__GBL_EFI_IMAGE_LOADING_PROTOCOL_H__
