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

#ifndef __AB_SLOT_PROTOCOL_H__
#define __AB_SLOT_PROTOCOL_H__

#include "system_table.h"
#include "types.h"

typedef enum EFI_UNBOOTABLE_REASON {
  UNKNOWN_REASON = 0,
  NO_MORE_TRIES,
  SYSTEM_UPDATE,
  USER_REQUESTED,
  VERIFICATION_FAILURE,
} EfiUnbootableReason;

typedef enum EFI_BOOT_REASON {
  EMPTY_EFI_BOOT_REASON = 0,
  UNKNOWN_EFI_BOOT_REASON = 1,
  WATCHDOG = 14,
  KERNEL_PANIC = 15,
  RECOVERY = 3,
  BOOTLOADER = 55,
  COLD = 56,
  HARD = 57,
  WARM = 58,
  SHUTDOWN,
  REBOOT = 18,
} EfiBootReason;

typedef struct EfiGblSlotInfo {
  // One UTF-8 encoded single character
  uint32_t suffix;
  // Any value other than those explicitly enumerated in EFI_UNBOOTABLE_REASON
  // will be interpreted as UNKNOWN_REASON.
  uint32_t unbootable_reason;
  uint8_t priority;
  uint8_t tries;
  // Value of 1 if slot has successfully booted.
  uint8_t successful;
  uint8_t merge_status;
} EfiGblSlotInfo;

typedef struct EfiGblSlotMetadataBlock {
  // Value of 1 if persistent metadata tracks slot unbootable reasons.
  uint8_t unbootable_metadata;
  uint8_t max_retries;
  uint8_t slot_count;
} EfiGblSlotMetadataBlock;

typedef struct EfiGblSlotProtocol {
  // Currently must contain 0x00010000
  uint32_t version;
  // Slot metadata query methods
  EfiStatus (*load_boot_data)(struct EfiGblSlotProtocol*,
                              EfiGblSlotMetadataBlock* /* out param*/);
  EfiStatus (*get_slot_info)(struct EfiGblSlotProtocol*, uint8_t,
                             EfiGblSlotInfo* /* out param */);
  EfiStatus (*get_current_slot)(struct EfiGblSlotProtocol*,
                                EfiGblSlotInfo* /* out param */);
  // Slot metadata manipulation methods
  EfiStatus (*set_active_slot)(struct EfiGblSlotProtocol*, uint8_t);
  EfiStatus (*set_slot_unbootable)(struct EfiGblSlotProtocol*, uint8_t,
                                   uint32_t);
  EfiStatus (*mark_boot_attempt)(struct EfiGblSlotProtocol*);
  EfiStatus (*reinitialize)(struct EfiGblSlotProtocol*);
  // Miscellaneous methods
  EfiStatus (*get_boot_reason)(struct EfiGblSlotProtocol*,
                               uint32_t* /* out param */,
                               size_t* /* in-out param */,
                               uint8_t* /* out param*/);
  EfiStatus (*set_boot_reason)(struct EfiGblSlotProtocol*, uint32_t, size_t,
                               const uint8_t*);
  EfiStatus (*flush)(struct EfiGblSlotProtocol*);
} EfiGblSlotProtocol;

#endif
