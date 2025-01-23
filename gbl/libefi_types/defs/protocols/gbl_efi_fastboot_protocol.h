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
// See gbl/docs/GBL_EFI_FASTBOOT_PROTOCOL.md for details.

#ifndef __GBL_EFI_FASTBOOT_PROTOCOL_H__
#define __GBL_EFI_FASTBOOT_PROTOCOL_H__

#include "types.h"

#define GBL_EFI_FASTBOOT_SERIAL_NUMBER_MAX_LEN_UTF8 32

typedef struct GblEfiFastbootPolicy {
  // Indicates whether device can be unlocked
  bool can_unlock;
  // Device firmware supports 'critical' partition locking
  bool has_critical_lock;
  // Indicates whether device allows booting from image loaded directly from
  // RAM.
  bool can_ram_boot;
} GblEfiFastbootPolicy;

// Callback function pointer passed to GblEfiFastbootProtocol.get_var_all.
//
// context: Caller specific context.
// args: An array of NULL-terminated strings that contains the variable name
//       followed by additional arguments if any.
// val: A NULL-terminated string representing the value.
typedef void (*GetVarAllCallback)(void* context, const char* const* args,
                                  size_t num_args, const char* val);

typedef enum GBL_EFI_FASTBOOT_PARTITION_PERMISSION_FLAGS {
  // Firmware can read the given partition and send its data to fastboot client.
  GBL_EFI_FASTBOOT_PARTITION_READ = 0x1 << 0,
  // Firmware can overwrite the given partition.
  GBL_EFI_FASTBOOT_PARTITION_WRITE = 0x1 << 1,
  // Firmware can erase the given partition.
  GBL_EFI_FASTBOOT_PARTITION_ERASE = 0x1 << 2,
} GblEfiFastbootPartitionPermissionFlags;

typedef enum GBL_EFI_FASTBOOT_LOCK_FLAGS {
  // All device partitions are locked.
  GBL_EFI_FASTBOOT_GBL_EFI_LOCKED = 0x1 << 0,
  // All 'critical' device partitions are locked.
  GBL_EFI_FASTBOOT_GBL_EFI_CRITICAL_LOCKED = 0x1 << 1,
} GblEfiFastbootLockFlags;

typedef struct GblEfiFastbootProtocol {
  // Revision of the protocol supported.
  uint32_t version;
  // Null-terminated UTF-8 encoded string
  char8_t serial_number[GBL_EFI_FASTBOOT_SERIAL_NUMBER_MAX_LEN_UTF8];

  // Fastboot variable methods
  EfiStatus (*get_var)(struct GblEfiFastbootProtocol* self,
                       const char* const* args, size_t num_args, uint8_t* out,
                       size_t* out_size);
  EfiStatus (*get_var_all)(struct GblEfiFastbootProtocol* self, void* ctx,
                           GetVarAllCallback cb);

  // Fastboot oem function methods
  EfiStatus (*run_oem_function)(struct GblEfiFastbootProtocol* this,
                                const char8_t* command, size_t command_len,
                                char8_t* buf, size_t* bufsize);

  // Device lock methods
  EfiStatus (*get_policy)(struct GblEfiFastbootProtocol* this,
                          GblEfiFastbootPolicy* policy);
  EfiStatus (*set_lock)(struct GblEfiFastbootProtocol* this,
                        uint64_t lock_state);
  EfiStatus (*clear_lock)(struct GblEfiFastbootProtocol* this,
                          uint64_t lock_state);

  // Misc methods
  EfiStatus (*get_partition_permissions)(struct GblEfiFastbootProtocol* this,
                                         const char8_t* part_name,
                                         size_t part_name_len,
                                         uint64_t* permissions);
  EfiStatus (*wipe_user_data)(struct GblEfiFastbootProtocol* this);
  bool (*should_stop_in_fastboot)(struct GblEfiFastbootProtocol* this);
} GblEfiFastbootProtocol;

#endif  // __GBL_EFI_FASTBOOT_PROTOCOL_H__
