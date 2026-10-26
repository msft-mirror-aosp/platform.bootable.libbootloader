#!/bin/bash -e
# Copyright (C) 2024 The Android Open Source Project
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Use host readlink: the hermetic prebuilts cannot be located until WORKSPACE_DIR is known.
MYPATH=$(readlink -f "$0")
BAZEL_PY="${MYPATH%/*}/bazel.py"
WORKSPACE_DIR=${MYPATH%/bootable/libbootloader/gbl/*}

cd "$WORKSPACE_DIR"
exec "$WORKSPACE_DIR"/prebuilts/build-tools/path/linux-x86/python3 "$BAZEL_PY" "$@"
