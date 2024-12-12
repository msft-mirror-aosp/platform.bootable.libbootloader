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

#ifndef __GBL_EFI_AB_SLOT_PROTOCOL_H__
#define __GBL_EFI_AB_SLOT_PROTOCOL_H__

#include "system_table.h"
#include "types.h"

typedef enum GBL_EFI_SLOT_MERGE_STATUS {
  GBL_EFI_SLOT_MERGE_STATUS_NONE = 0,
  GBL_EFI_SLOT_MERGE_STATUS_UNKNOWN,
  GBL_EFI_SLOT_MERGE_STATUS_SNAPSHOTTED,
  GBL_EFI_SLOT_MERGE_STATUS_MERGING,
  GBL_EFI_SLOT_MERGE_STATUS_CANCELLED,
} GblEfiSlotMergeStatus;

typedef enum GBL_EFI_UNBOOTABLE_REASON {
  GBL_EFI_UNKNOWN_REASON = 0,
  GBL_EFI_NO_MORE_TRIES,
  GBL_EFI_SYSTEM_UPDATE,
  GBL_EFI_USER_REQUESTED,
  GBL_EFI_VERIFICATION_FAILURE,
} GblEfiUnbootableReason;

// We are currently following
// https://cs.android.com/android/platform/superproject/main/+/main:system/core/bootstat/bootstat.cpp;l=229
// for boot reason code.
//
// But we may want to revisit this since GBL mostly just cares normal,
// bootloader, fastbootd, recovery mode.
typedef enum GBL_EFI_BOOT_REASON {
  EMPTY_BOOT_REASON = 0,
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
  FASTBOOTD = 196,
} GblEfiBootReason;

typedef struct {
  // One UTF-8 encoded single character
  uint32_t suffix;
  // Any value other than those explicitly enumerated in EFI_UNBOOTABLE_REASON
  // will be interpreted as UNKNOWN_REASON.
  uint32_t unbootable_reason;
  uint8_t priority;
  uint8_t tries;
  // Value of 1 if slot has successfully booted.
  uint8_t successful;
} GblEfiSlotInfo;

typedef struct {
  // Value of 1 if persistent metadata tracks slot unbootable reasons.
  uint8_t unbootable_metadata;
  uint8_t max_retries;
  uint8_t slot_count;
  // See GblEFiSlotMergeStatus for enum values.
  uint8_t merge_status;
} GblEfiSlotMetadataBlock;

typedef struct GblEfiABSlotProtocol {
  // Currently must contain 0x00010000
  uint32_t version;
  // Slot metadata query methods
  EfiStatus (*load_boot_data)(struct GblEfiABSlotProtocol*,
                              GblEfiSlotMetadataBlock* /* out param*/);
  EfiStatus (*get_slot_info)(struct GblEfiABSlotProtocol*, uint8_t,
                             GblEfiSlotInfo* /* out param */);
  EfiStatus (*get_current_slot)(struct GblEfiABSlotProtocol*,
                                GblEfiSlotInfo* /* out param */);
  EfiStatus (*get_next_slot)(struct GblEfiABSlotProtocol*, bool,
                             GblEfiSlotInfo* /* out param */);
  // Slot metadata manipulation methods
  EfiStatus (*set_active_slot)(struct GblEfiABSlotProtocol*, uint8_t);
  EfiStatus (*set_slot_unbootable)(struct GblEfiABSlotProtocol*, uint8_t,
                                   uint32_t);
  EfiStatus (*reinitialize)(struct GblEfiABSlotProtocol*);
  // Miscellaneous methods
  EfiStatus (*get_boot_reason)(struct GblEfiABSlotProtocol*,
                               uint32_t* /* out param */,
                               size_t* /* in-out param */,
                               uint8_t* /* out param*/);
  EfiStatus (*set_boot_reason)(struct GblEfiABSlotProtocol*, uint32_t, size_t,
                               const uint8_t*);
  EfiStatus (*flush)(struct GblEfiABSlotProtocol*);
} GblEfiABSlotProtocol;

#endif  // __GBL_EFI_AB_SLOT_PROTOCOL_H__
