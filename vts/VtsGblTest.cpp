/**
 * Copyright (C) 2025 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <android-base/file.h>
#include <android-base/parseint.h>
#include <android-base/properties.h>
#include <android-base/strings.h>
#include <gmock/gmock.h>
#include <gtest/gtest.h>

class VtsGblTest : public testing::Test {};

TEST_F(VtsGblTest, TestRunningProp) {
  // TODO: Check assumptions. feature flag or API level?
  const int32_t gbl_version =
      android::base::GetIntProperty("ro.boot.gbl.version", -1);
  const std::string build_number =
      android::base::GetProperty("ro.boot.gbl.build_number", "");

  if (gbl_version == -1) {
    GTEST_SKIP() << "Device not booted with GBL";
  }

  GTEST_LOG_(INFO) << "GBL version: " << gbl_version;
  GTEST_LOG_(INFO) << "GBL build_number: " << build_number;

  if (android::base::StartsWith(build_number, "eng.")) {
    GTEST_LOG_(WARNING) << "GBL is a local eng build";
  }
  ASSERT_THAT(build_number, testing::MatchesRegex("P?[0-9]+"))
      << "Invalid build ID";
  if (build_number[0] == 'P') {
    GTEST_LOG_(INFO) << "GBL appears to be a presubmit build";
  } else {
    uint64_t build_incremental = 0;
    EXPECT_TRUE(android::base::ParseUint(build_number, &build_incremental))
        << "Failed to parse build id";
    // TODO: Update this number after build script is updated to embed build id
    // in artifact
    // EXPECT_GE(build_incremental, 12345678)
    //     << "GBL build number should be at least ...";
  }
}
