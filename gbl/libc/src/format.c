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

// Minimal format string implementation used by GBL to provide printing
// functionality to third-party C code. Currently used by:
//
//   1. `external/libufdt` via `dto_print()`
//   2. `external/avb/libavb` via `avb_printf()`
//
// Because this implementation is used by a limited set of consumers, it
// provides a simplified format parser that meets the current requirements. The
// integrator must ensure it remains sufficient for any new use cases.
//
// Current functionality is based on the format string specification:
// (https://cplusplus.com/reference/cstdio/printf/)
//
//   %[flags][width][precision][length modifier][conversion specifier]
//
//   - flags: not supported (skipped by `skip_flags`)
//   - width: not supported (skipped by `skip_width`)
//   - precision: not supported (skipped by `skip_precision`)
//   - length modifier: all are supported (l, ll, h, hh, z, etc.)
//   - conversion specifier:
//       * signed numeric values (i, d)
//       * unsigned numeric values (u, o, x)
//       * characters (c)
//       * nul-terminated strings (s)
//     Others are not supported (undefined behaviour).
//
// TODO(b/394149272): Support floating pointers formatting.
//
// The maximum supported output length is 2048 bytes (see `PRINT_BUFFER_SIZE`).
// Any additional content is silently truncated.

#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "gbl/print.h"

// Maximum amount of characters can be printed at once. The rest of symbols
// are getting silently cut.
#define PRINT_BUFFER_SIZE 2048

#define NUMBER_ALPHABET "0123456789abcdef"

#define BASE_DEC 10U
#define BASE_OCT 8U
#define BASE_HEX 16U

#define FLAGS_LONG (1U << 0U)
#define FLAGS_LONG_LONG (1U << 1U)
#define FLAGS_CHAR (1U << 2U)
#define FLAGS_SHORT (1U << 3U)

#define ULL_MAX_DIGITS 20

// Formats unsigned `value` in base `base` into `buffer`.
//
// Returns number of characters written to the result buffer.
static size_t format_number_unsigned(unsigned long long value, char *buffer,
                                     size_t buffer_len, unsigned int base) {
  if (buffer_len == 0) return 0;

  if (value == 0) {
    buffer[0] = '0';
    return 1;
  }

  char tmp[ULL_MAX_DIGITS];
  int tmp_pos = 0;

  // Convert number to reversed string
  while (value > 0) {
    tmp[tmp_pos++] = NUMBER_ALPHABET[value % base];
    value /= base;
  }

  // Copy reversed number to buffer
  size_t used = 0;
  for (int i = tmp_pos - 1; i >= 0 && used < buffer_len; i--) {
    buffer[used++] = tmp[i];
  }

  return used;
}

// Formats signed `value` in base `base` into `buffer`.
//
// Returns number of characters written to the result buffer.
static size_t format_number_signed(long long value, char *buffer,
                                   size_t buffer_len, unsigned int base) {
  size_t used = 0;
  unsigned long long abs = 0;

  if (value < 0) {
    if (used < buffer_len) {
      buffer[used++] = '-';
    }
    abs = value == LLONG_MIN ? (unsigned long long)(-(value + 1)) + 1 : -value;
  } else {
    abs = value;
  }

  return used +
         format_number_unsigned(abs, buffer + used, buffer_len - used, base);
}

// Formats nul-terminated string `s` into `buffer`.
//
// Returns number of characters written to the result buffer.
static size_t format_string(const char *s, char *buffer, size_t buffer_len) {
  size_t used = 0;
  while (*s && used < buffer_len) {
    buffer[used++] = *s++;
  }
  return used;
}

// Formats a single character `c` into `buffer`.
//
// Returns number of characters written to the result buffer.
static size_t format_character(char c, char *buffer, size_t buffer_len) {
  size_t used = 0;
  if (buffer_len) {
    buffer[used++] = c;
  }
  return used;
}

// Noop implementation of the number format used in both width and precision
// segments to represent the number. Can be asterisk symbol or dec number.
//
// Returns number of processed symbols in the format string.
static size_t skip_format_number(const char *fmt) {
  if (*fmt == '*') return 1;

  size_t used = 0;
  while (*fmt >= '0' && *fmt <= '9') {
    fmt++;
    used++;
  }
  return used;
}

// Width segment isn't supported by this implementation. It's getting parsed,
// but ignored.
//
// Returns number of processed symbols in the format string.
static size_t skip_width(const char *fmt) { return skip_format_number(fmt); }

// Precision segment isn't supported by this implementation. It's getting
// parsed, but ignored.
//
// Returns number of processed symbols in the format string.
static size_t skip_precision(const char *fmt) {
  if (*fmt == '.') {
    return 1 + skip_format_number(fmt + 1);
  }
  return 0;
}

// Format flags aren't supported by this implementation. They are getting
// parsed, but ignored. Skipped symbols: '-', '+', ' ', '#', '0'.
//
// Returns number of processed symbols in the format string.
static size_t skip_flags(const char *fmt) {
  size_t used = 0;
  while (strchr("-+ #0", *fmt) != NULL) {
    fmt++;
    used++;
  }
  return used;
}

// Parse length modifiers flags.
//
// Returns number of processed symbols in the format string.
static size_t parse_length_modifiers(const char *fmt, unsigned int *out_flags) {
  size_t used = 0;
  switch (*fmt) {
    case 'l':
      *out_flags = FLAGS_LONG;
      used++;
      fmt++;
      if (*fmt == 'l') {
        *out_flags = FLAGS_LONG_LONG;
        used++;
      }
      break;
    case 'h':
      *out_flags = FLAGS_SHORT;
      used++;
      fmt++;
      if (*fmt == 'h') {
        *out_flags = FLAGS_CHAR;
        used++;
      }
      break;
    case 'z':
      *out_flags =
          sizeof(size_t) == sizeof(long) ? FLAGS_LONG : FLAGS_LONG_LONG;
      used++;
      break;
    case 'j':
      *out_flags |=
          sizeof(intmax_t) == sizeof(long) ? FLAGS_LONG : FLAGS_LONG_LONG;
      used++;
      break;
    case 't':
      *out_flags |=
          sizeof(ptrdiff_t) == sizeof(long) ? FLAGS_LONG : FLAGS_LONG_LONG;
      used++;
      break;
  }
  return used;
}

// Appends an error message into `buffer` to handle unsupported format string
// symbol error.
//
// Returns number of processed symbols in the error message.
static size_t append_cannot_handle_error(char *buffer, size_t buffer_len,
                                         char current) {
  size_t used = 0;
  used += format_string(
      "GBL print implementation cannot handle format string at symbol: ",
      buffer, buffer_len);
  used += format_character(current, buffer + used, buffer_len - used);
  return used;
}

// Format `fmt` into `buffer` using provided `args`.
//
// Only `buffer_len` bytes will be formatted. The rest of `fmt` string and
// provided `args` will be ignored.
static void gbl_printf_buffer(const char *fmt, va_list args, char *buffer,
                              size_t buffer_len) {
  // Ensure can nul terminate.
  const size_t buffer_available = buffer_len - 1;

  size_t i = 0;
  while (*fmt && i < buffer_available) {
    if (*fmt == '%') {
      // %% case
      if (*(fmt + 1) == '%') {
        // Skip one % to print another.
        fmt++;
      } else {
        unsigned int base = BASE_DEC;
        unsigned int flags = 0;
        fmt++;

        fmt += skip_flags(fmt);
        fmt += skip_width(fmt);
        fmt += skip_precision(fmt);
        fmt += parse_length_modifiers(fmt, &flags);

        switch (*fmt) {
          case 's':
            i += format_string(va_arg(args, char *), buffer + i,
                               buffer_available - i);
            fmt++;
            continue;
          case 'o':
          case 'x':
          case 'u':
            switch (*fmt) {
              case 'o':
                base = BASE_OCT;
                break;
              case 'x':
                base = BASE_HEX;
                break;
            }
            if (flags & FLAGS_LONG_LONG) {
              i += format_number_unsigned(va_arg(args, unsigned long long),
                                          buffer + i, buffer_available - i,
                                          base);
            } else if (flags & FLAGS_LONG) {
              i += format_number_unsigned(va_arg(args, unsigned long),
                                          buffer + i, buffer_available - i,
                                          base);
            } else {
              i +=
                  format_number_unsigned(va_arg(args, unsigned int), buffer + i,
                                         buffer_available - i, base);
            }
            fmt++;
            continue;
          case 'd':
          case 'i':
            if (flags & FLAGS_LONG_LONG) {
              i += format_number_signed(va_arg(args, long long), buffer + i,
                                        buffer_available - i, base);
            } else if (flags & FLAGS_LONG) {
              i += format_number_signed(va_arg(args, long), buffer + i,
                                        buffer_available - i, base);
            } else {
              i += format_number_signed(va_arg(args, int), buffer + i,
                                        buffer_available - i, base);
            }
            fmt++;
            continue;
          case 'c':
            i += format_character(va_arg(args, int), buffer + i,
                                  buffer_available - i);
            fmt++;
            break;
          default:
            i += append_cannot_handle_error(buffer + i, buffer_available - i,
                                            *fmt);
            goto out;
        }
      }
    }
    buffer[i++] = *fmt++;
  }

out:
  buffer[i] = 0;
}

// Generic output format implementation to be exposed to 3d party C code.
void gbl_printf(const char *fmt, va_list args) {
  char output_buffer[PRINT_BUFFER_SIZE];
  gbl_printf_buffer(fmt, args, output_buffer, sizeof(output_buffer));
  gbl_print_string(output_buffer);
}
