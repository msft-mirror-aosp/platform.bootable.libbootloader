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
 */

#include <gbl/print.h>
#include <libavb/avb_sysdeps.h>
#include <stdarg.h>

void avb_printf(const char* fmt, ...) {
  va_list args;
  va_start(args, fmt);
  gbl_printf(fmt, args);
  va_end(args);
}

void avb_printv(const char* message, ...) {
  va_list args;
  va_start(args, message);
  gbl_printf(message, args);
  va_end(args);
}
