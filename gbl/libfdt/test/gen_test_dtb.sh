#!/bin/bash
#
# Copyright (C) 2023 The Android Open Source Project
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
readonly DATA_DIR="${SCRIPT_DIR}/data/"

dtc -@ -I dts -O dtb -o ${DATA_DIR}/base.dtb ${SCRIPT_DIR}/base.dts

dtc -@ -I dts -O dtb -o ${DATA_DIR}/overlay_by_path.dtbo ${SCRIPT_DIR}/overlay_by_path.dts
dtc -@ -I dts -O dtb -o ${DATA_DIR}/overlay_2_by_path.dtbo ${SCRIPT_DIR}/overlay_2_by_path.dts

dtc -@ -I dts -O dtb -o ${DATA_DIR}/overlay_by_reference.dtbo ${SCRIPT_DIR}/overlay_by_reference.dts
dtc -@ -I dts -O dtb -o ${DATA_DIR}/overlay_2_by_reference.dtbo ${SCRIPT_DIR}/overlay_2_by_reference.dts

dtc -@ -I dts -O dtb -o ${DATA_DIR}/overlay_wrong_path.dtbo ${SCRIPT_DIR}/overlay_wrong_path.dts
