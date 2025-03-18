/*
 * Copyright (C) 2025 The Android Open Source Project
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

#ifndef __GBL_PRINT_H__
#define __GBL_PRINT_H__

#include <stdarg.h>

#ifdef __cplusplus
extern "C" {
#endif

// GBL-speicifc function to expose print implementation to 3d party C code.
// Implementation: libc/src/print.c
void gbl_printf(const char* fmt, va_list args);

// Printing back-end functions to be used by `gbl_printf`.
// Implementation: libc/src/print.rs
void gbl_print_string(const char* s);

#ifdef __cplusplus
}
#endif

#endif
