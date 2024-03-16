#! /usr/bin/env bash
# Copyright (C) 2024  Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

set -e

readonly SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"

PARTITION_NAME="test_partition"
PARTITION_SIZE="4k"

python3 ${SCRIPT_DIR}/../../tools/gen_gpt_disk.py ${SCRIPT_DIR}/writeback_test_disk.bin 64K \
        --partition "${PARTITION_NAME},${PARTITION_SIZE},/dev/zero"
