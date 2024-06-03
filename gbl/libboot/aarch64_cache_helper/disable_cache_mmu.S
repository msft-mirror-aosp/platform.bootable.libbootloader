/*
 * Copyright (C) 2023 The Android Open Source Project
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

 #include <arch.h>

.global disable_cache_mmu_and_jump

/* ---------------------------------------------------------------
 * Disable cache, MMU and jump to the given address with arguments
 *
 * x0 - x3: Arguments for the target jump address.
 * x4: The jump address.
 * ---------------------------------------------------------------
 */
disable_cache_mmu_and_jump:
    // Query current EL
    mrs     x5, CurrentEL
    cmp     x5, #(1 << 3)
    beq     asm_disable_cache_mmu_el2

    /*
     * Invalidate instruction cache before disabling it.
     */
    ic  iallu
    isb

asm_disable_cache_mmu_el1:
    mrs x5, sctlr_el1
    bic x5, x5, #SCTLR_M_BIT
    bic x5, x5, #SCTLR_C_BIT
    bic x5, x5, #SCTLR_I_BIT
    msr sctlr_el1, x5
    b asm_finish

asm_disable_cache_mmu_el2:
    mrs x5, sctlr_el2
    bic x5, x5, #SCTLR_M_BIT
    bic x5, x5, #SCTLR_C_BIT
    bic x5, x5, #SCTLR_I_BIT
    msr sctlr_el2, x5

asm_finish:
    ic  iallu
    isb
    /*
     * Invalidate TLB.
     */
    tlbi vmalle1

    br x4
    /*
     * Prevent speculative execution.
     */
    dsb nsh
    isb
