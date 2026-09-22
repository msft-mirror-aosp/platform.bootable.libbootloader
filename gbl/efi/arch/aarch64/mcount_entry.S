/*
 * Copyright (C) 2026 The Android Open Source Project
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


.global mcount_return_override
.global mcount


/* -----------------------------------------------------
 * void mcount(size_t return_address)
 *
 * Inserted by compiler at function entry. Receives the return address of the
 * caller function.
 * -----------------------------------------------------
 */
mcount:
    bti c
    sub sp, sp, #0x20
    stp x29, x30, [sp]
    mov x29, sp
    add x0, sp, #0x20
    bl mcount_func_entry
    ldp x29, x30, [sp]
    add sp, sp, #0x20
    ret

#define CALLER_SAVE_REG_SIZE #(20 * 8)

/* -----------------------------------------------------
 * Set by mcount() to override caller's return address to capture function exit event.
 * -----------------------------------------------------
 */
mcount_return_override:
    bti jc
    /* We are in the context of caller's parent. Since we don't know which
    caller-saved registers it uses, just save all of them. */
    sub sp, sp, CALLER_SAVE_REG_SIZE
    stp x0, x1, [sp]
    stp x2, x3, [sp, #0x10]
    stp x4, x5, [sp, #0x20]
    stp x6, x7, [sp, #0x30]
    stp x8, x9, [sp, #0x40]
    stp x10, x11, [sp, #0x50]
    stp x12, x13, [sp, #0x60]
    stp x14, x15, [sp, #0x70]
    stp x16, x17, [sp, #0x80]
    stp x18, x0, [sp, #0x90]
    add x0, sp, CALLER_SAVE_REG_SIZE
    bl mcount_func_exit
    mov x30, x0
    ldp x0, x1, [sp]
    ldp x2, x3, [sp, #0x10]
    ldp x4, x5, [sp, #0x20]
    ldp x6, x7, [sp, #0x30]
    ldp x8, x9, [sp, #0x40]
    ldp x10, x11, [sp, #0x50]
    ldp x12, x13, [sp, #0x60]
    ldp x14, x15, [sp, #0x70]
    ldp x16, x17, [sp, #0x80]
    ldp x18, x0, [sp, #0x90]
    add sp, sp, CALLER_SAVE_REG_SIZE
    ret
