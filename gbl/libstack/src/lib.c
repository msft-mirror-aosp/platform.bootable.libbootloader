// Copyright 2025, The Android Open Source Project
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <limits.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <uefi/efi.h>

/*
 * When adding stack protector calls to functions, LLVM doesn't treat the
 * stack canary checker/handler as special and will blithely add canary checks
 * to __security_check_cookie and __stack_chk_fail. This causes infinite
 * recursion. The workaround used here is to define the special variables and
 * functions in C because the UEFI C toolchains are not configured to add stack
 * canaries. The infinite recursion problem also prevents calling any functions
 * written in rust, which includes the rust wrappers around UEFI Simple Text
 * Output Protocol and Reset System.
 *
 * Note: the stack canary semantics are slightly different between PE/COFF and
 * ELF. None of this is properly documented anywhere; it is the result of
 * reading the LLVM stack protector code and running experiments.
 *
 * PE/COFF inserts a call to __security_check_cookie right before returning
 * from a function, and it is the responsibility of __security_check_cookie to
 * both check for an overwritten canary and to handle any failures.
 *
 * ELF inserts canary checking assembly into the end of the basic block and
 * calls __stack_chk_fail on failure, which is only responsible for resetting
 * the system.
 *
 * As of 2025-04-16, RISC-V is the only platform that uses ELF objects for UEFI.
 * This is a hack to work around lack of official support in the PE/COFF
 * executable format.
 */

static EfiSystemTable* system_table = NULL;

__attribute__((no_stack_protector, no_instrument_function)) static void
libstack_debug_print(uint16_t* str) {
  if (system_table && system_table->con_out &&
      system_table->con_out->output_string) {
    system_table->con_out->output_string(system_table->con_out, str);
  }
}

__attribute__((no_stack_protector, no_instrument_function)) static void
libstack_system_reset(void) {
  if (system_table && system_table->runtime_services &&
      system_table->runtime_services->reset_system) {
    system_table->runtime_services->reset_system(
        EFI_RESET_TYPE_COLD, EFI_STATUS_ACCESS_DENIED, 0, NULL);
    libstack_debug_print(u"Failed to reset system\n");
  }
  for (;;) {
  }
}

// The stack canary and canary check function for PE/COFF
// (i.e. "real" UEFI apps).
size_t __security_cookie = 0;
__attribute__((no_stack_protector, no_instrument_function, noinline)) void
__security_check_cookie(size_t cookie) {
  if (cookie != __security_cookie) {
    libstack_debug_print(u"Stack check failure\n");
    libstack_system_reset();
  }
}

// The stack canary and canary failure handler for ELF objects.
size_t __stack_chk_guard = 0;
__attribute__((no_stack_protector, no_instrument_function, noinline)) void
__stack_chk_fail(void) {
  libstack_debug_print(u"Stack check failure\n");
  libstack_system_reset();
}

// Trap handler for trap-mode UBSan.
__attribute__((no_stack_protector, no_instrument_function, noinline)) void
gbl_ubsan_trap(void) {
  libstack_debug_print(u"Undefined behavior trap\n");
  libstack_system_reset();
}

__attribute__((no_stack_protector, no_instrument_function, noinline)) void
initialize_canary(EfiSystemTable* systab, size_t canary) {
  if (!system_table) {
    system_table = systab;
    __security_cookie = canary;
    __stack_chk_guard = canary;
  } else {
    libstack_debug_print(
        u"WARNING: attempting to set libstack system table more than once.\n");
  }
}
