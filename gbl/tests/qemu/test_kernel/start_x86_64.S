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

.section .text.start, "ax", @progbits
.global _start
.hidden _start

// Minimal Linux x86_64 bzImage setup header (1 boot sector + 1 setup sector = 0x400 bytes).
// `boot_linux_bzimage` copies bytes after the setup sectors (`offset >= 0x400`) to `0x100000`
// (`LOAD_ADDR_HIGH`) and jumps to `0x100200` (`LOAD_ADDR_HIGH + 0x200`), which corresponds to
// offset `0x600` (`_start64`) below, with `%rsi` pointing to `struct boot_params`.
_start:
    .org 0x1f1
    .byte 1               // setup_sects = 1 (kernel_off = (1 + 1) * 512 = 0x400)
    .org 0x1fe
    .word 0xaa55          // boot_flag
    .org 0x200
    jmp real_mode_end
    .org 0x202
    .ascii "HdrS"         // header magic
    .org 0x206
    .word 0x020f          // version >= 0x0206
    .org 0x211
    .byte 0x01            // loadflags: LOADED_HIGH (1 << 0)
    .org 0x236
    .word 0x0002          // xloadflags: XLF_KERNEL_64 (1 << 1)
real_mode_end:
    .org 0x400
    // Start of protected-mode kernel image loaded at 0x100000.
    .org 0x600
_start64:
    endbr64
    // Align stack to 16 bytes and preserve %rsi (pointer to boot_params).
    andq $-16, %rsp
    pushq %rsi
    pushq %rsi

    // ApplyRelocation(program_base, dynamic_section)
    leaq _start(%rip), %rdi
    leaq _DYNAMIC(%rip), %rsi
    call ApplyRelocation
    testb %al, %al
    jz spin

    // Restore boot_params pointer into %rdi (first argument to kernel_main).
    popq %rsi
    popq %rdi
    call kernel_main

spin:
    jmp spin
