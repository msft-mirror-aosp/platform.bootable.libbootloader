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

#include <gtest/gtest.h>

#include "gbl/print.h"

// Must be the same value as `PRINT_BUFFER_SIZE` from format.c
#define MOCK_PRINT_BUFFER_SIZE 2048
static char print_buffer[MOCK_PRINT_BUFFER_SIZE];

void gbl_print_string(const char* s) {
  strncpy(print_buffer, s, MOCK_PRINT_BUFFER_SIZE);
}

void test_gbl_printf(const char* fmt, ...) {
  va_list args;
  va_start(args, fmt);
  gbl_printf(fmt, args);
  va_end(args);
}

TEST(PrintfTest, FormatString) {
  test_gbl_printf("before %s after", "text");
  ASSERT_STREQ("before text after", print_buffer);
}

TEST(PrintfTest, FormatInt) {
  test_gbl_printf("before %d after", 100);
  ASSERT_STREQ("before 100 after", print_buffer);
}

TEST(PrintfTest, FormatChar) {
  test_gbl_printf("char value: %c", 'a');
  ASSERT_STREQ("char value: a", print_buffer);
}

TEST(PrintfTest, FormatCharAsciiCode) {
  test_gbl_printf("char value: %hhd", 'a');
  ASSERT_STREQ("char value: 97", print_buffer);
}

TEST(PrintfTest, FormatUnsigned) {
  test_gbl_printf("Unsigned value: %u", 123456789U);
  ASSERT_STREQ("Unsigned value: 123456789", print_buffer);
}

TEST(PrintfTest, FormatOctal) {
  test_gbl_printf("Octal value: %o", 0777);
  ASSERT_STREQ("Octal value: 777", print_buffer);
}

TEST(PrintfTest, FormatHex) {
  test_gbl_printf("Hex value: %x", 0xabcdef);
  ASSERT_STREQ("Hex value: abcdef", print_buffer);
}

TEST(PrintfTest, FormatEmptyString) {
  test_gbl_printf("String: '%s'", "");
  ASSERT_STREQ("String: ''", print_buffer);
}

TEST(PrintfTest, FormatMultiple) {
  test_gbl_printf("Values: %d %u %x %s", -42, 42U, 0x42, "forty-two");
  ASSERT_STREQ("Values: -42 42 42 forty-two", print_buffer);
}

TEST(PrintfTest, FormatLongLong) {
  long long val = 1234567890123LL;
  test_gbl_printf("Long long: %lld", val);
  ASSERT_STREQ("Long long: 1234567890123", print_buffer);
}

TEST(PrintfTest, FormatLLongMin) {
  long long val = LLONG_MIN;
  char expected[64];
  snprintf(expected, sizeof(expected), "LLONG_MIN: %lld", val);
  test_gbl_printf("LLONG_MIN: %lld", val);
  ASSERT_STREQ(expected, print_buffer);
}

TEST(PrintfTest, FormatULLongMax) {
  unsigned long long val = ULLONG_MAX;
  char expected[64];
  snprintf(expected, sizeof(expected), "ULLONG_MAX: %llu", val);
  test_gbl_printf("ULLONG_MAX: %llu", val);
  ASSERT_STREQ(expected, print_buffer);
}

TEST(PrintfTest, FormatUnknownSpecifierErrorAppended) {
  test_gbl_printf("Unknown specifier: %q");
  ASSERT_STREQ(
      "Unknown specifier: GBL print implementation cannot handle format string "
      "at symbol: q",
      print_buffer);
}

TEST(PrintfTest, FormatPercent) {
  test_gbl_printf("percent: %%");
  ASSERT_STREQ("percent: %", print_buffer);
}

TEST(PrintfTest, FormatIntNegative) {
  test_gbl_printf("before %d after", -100);
  ASSERT_STREQ("before -100 after", print_buffer);
}

TEST(PrintfTest, SkipWidthZeroFlag) {
  test_gbl_printf("before %08d after", 42);
  ASSERT_STREQ("before 42 after", print_buffer);
}

TEST(PrintfTest, SkipPrecisionInt) {
  test_gbl_printf("before %.5d after", 2025);
  ASSERT_STREQ("before 2025 after", print_buffer);
}

TEST(PrintfTest, SkipComplexFlagsInt) {
  test_gbl_printf("before %-015.6d after", -999);
  ASSERT_STREQ("before -999 after", print_buffer);
}

TEST(PrintfTest, SkipDynamicWidth) {
  test_gbl_printf("before %*d after", 77);
  ASSERT_STREQ("before 77 after", print_buffer);
}

TEST(PrintfTest, SkipDynamicPrecision) {
  test_gbl_printf("before %.*d after", 123);
  ASSERT_STREQ("before 123 after", print_buffer);
}

TEST(PrintfTest, SkipFlagsString) {
  test_gbl_printf("before %-+#5.8s after", "TestMe!");
  ASSERT_STREQ("before TestMe! after", print_buffer);
}

TEST(PrintfTest, SkipPlusFlag) {
  test_gbl_printf("before %+d after", 100);
  ASSERT_STREQ("before 100 after", print_buffer);
}

TEST(PrintfTest, SkipSpaceFlag) {
  test_gbl_printf("before % d after", 500);
  ASSERT_STREQ("before 500 after", print_buffer);
}

TEST(PrintfTest, LongStringIsTruncated) {
  char long_string[MOCK_PRINT_BUFFER_SIZE + 100];
  memset(long_string, 'A', sizeof(long_string) - 1);
  long_string[sizeof(long_string) - 1] = '\0';

  test_gbl_printf("%s", long_string);

  ASSERT_EQ(strlen(print_buffer), MOCK_PRINT_BUFFER_SIZE - 1);
  for (int i = 0; i < MOCK_PRINT_BUFFER_SIZE - 1; ++i) {
    ASSERT_EQ(print_buffer[i], 'A') << "Expected character 'A' at index " << i
                                    << ", but got '" << print_buffer[i] << "'";
  }
}

TEST(PrintfTest, MultipleMessages) {
  test_gbl_printf("First message: %s", "first");
  ASSERT_STREQ("First message: first", print_buffer);
  test_gbl_printf("Second message: %s", "second");
  ASSERT_STREQ("Second message: second", print_buffer);
}
