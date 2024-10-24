#!/bin/bash
#
# Copyright (C) 2024 The Android Open Source Project
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

readonly SCRIPT_DIR=`cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd`
readonly DATA_DIR="${SCRIPT_DIR}/data/"
readonly TMP_DIR=`mktemp -d`

dtc -I dts -O dtb -o ${TMP_DIR}/a.dtb ${SCRIPT_DIR}/a.dts
dtc -I dts -O dtb -o ${TMP_DIR}/b.dtb ${SCRIPT_DIR}/b.dts

echo "corrupted dttable" > ${DATA_DIR}/corrupted_dttable.img

# mkdtboimg is built by cd aosp/system/libufdt/utils && mm
mkdtboimg create ${DATA_DIR}/dttable.img \
        --id=0x2 --rev=0x0 ${TMP_DIR}/b.dtb \
        --id=0x1 --rev=0x0 ${TMP_DIR}/a.dtb
