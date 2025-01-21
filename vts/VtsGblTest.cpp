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
#include <gmock/gmock.h>
#include <gtest/gtest.h>

class VtsGblTest : public testing::Test {};

TEST_F(VtsGblTest, TestRunningProp) {
  // TODO: Check assumptions. feature flag or API level?
  const std::string build_id =
      android::base::GetProperty("ro.boot.gbl.build_number", "");
  if (build_id.empty()) {
    GTEST_SKIP() << "Device does not appear to be running on GBL";
  }
  EXPECT_THAT(build_id, testing::MatchesRegex("P?[0-9]+"))
      << "Invalid build ID";
  if (build_id[0] == 'P') {
    GTEST_LOG_(INFO) << "GBL appears to be a presubmit build";
  } else {
    uint64_t build_number = 0;
    EXPECT_TRUE(android::base::ParseUint(build_id, &build_number))
        << "Failed to parse build id";
    // TODO: Update this number after build script is updated to embed build id
    // in artifact
    // EXPECT_GE(build_number, 12345678)
    //     << "GBL build number should be at least ...";
  }
}
