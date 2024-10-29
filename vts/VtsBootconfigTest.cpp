/**
 * Copyright (C) 2021 The Android Open Source Project
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

#include "gtest/gtest.h"
#include <android-base/file.h>
#include <android-base/properties.h>
#include "bpf/BpfUtils.h"

class VtsBootconfigTest : public testing::Test {};

TEST_F(VtsBootconfigTest, ProcCmdlineAndroidbootTest) {
  // This was supported in Android S with kernel version 5.10+, but really only
  // required by Android T because Android still needs to support
  // Android S devices that launched with 4.19 for as long as it supports
  // Android S.
  int first_api_level = android::base::GetIntProperty(
        "ro.board.first_api_level",
        android::base::GetIntProperty("ro.vendor.api_level", 1000000));
  if (first_api_level < __ANDROID_API_T__) {
    GTEST_SKIP() << "Bootconfig requirements do not apply";
  }

  std::string cmdline;
  ASSERT_TRUE(android::base::ReadFileToString("/proc/cmdline", &cmdline));
  EXPECT_TRUE(cmdline.size() > 0);
  EXPECT_EQ(cmdline.find("androidboot"), cmdline.npos)
    << "\"androidboot\" parameters are not allowed in the kernel cmdline for "
    << "devices using kernel version 5.10 or greater with Android S and beyond. "
    << "These parameters are to be placed in bootconfig."
    << "\n/proc/cmdline contents:\n" << cmdline;
}
