#!/bin/bash
#
# Copyright (C) 2025 The Android Open Source Project
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

# The script builds debug x86_64 GBL, lanuches QEMU and runs rust-gdb for debugging.

set -e

readonly SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
readonly REPO_ROOT=$(readlink -f "${SCRIPT_DIR}/../../../..")

if [[ -z $1 ]] || [[ $1 == "x64" ]]; then
    # Default to x86_64
    BAZEL_TARGET="@gbl//efi:x86_64_debug_dev"
    BAZEL_OUT_BASE="${REPO_ROOT}/out_x86_64_debug_dev"
    EFI_BIN_NAME="bootx64.efi"
    QEMU_BIN="qemu-system-x86_64"
    OVMF="/usr/share/OVMF/OVMF_CODE_4M.fd"
    EXTRA_QEMU_OPTIONS=""
    EXTRA_GDB_INIT_CMD=""
    # Uses any version of rust-gdb that can be found from the prebuilts.
    GDB=$(find ${REPO_ROOT}/prebuilts/rust-toolchain/linux-musl-x86/ -name rust-gdb -print -quit)
    if [[ ! (-x "${GDB}" &&  -e "${GDB}") ]]; then
        echo "Cannot find any rust-gdb from ${REPO_ROOT}/prebuilts/rust-toolchain/linux-musl-x86/"
        exit 1;
    fi
elif [[ $1 == "aarch64" ]]; then
    BAZEL_TARGET="@gbl//efi:aarch64_debug_dev"
    BAZEL_OUT_BASE="${REPO_ROOT}/out_aarch64_debug_dev"
    EFI_BIN_NAME="bootaa64.efi"
    QEMU_BIN="qemu-system-aarch64"
    OVMF="/usr/share/AAVMF/AAVMF_CODE.fd"
    EXTRA_QEMU_OPTIONS="-machine virt -cpu cortex-a57"
    EXTRA_GDB_INIT_CMD="set arch aarch64"
    GDB="gdb-multiarch"
    if [[ -z $(which "${GDB}") ]]; then
        echo "${GDB} not installed."
        echo "Please run 'sudo apt-get install ${GDB}'"
        exit 1
    fi
else
    echo "Unknown architecture option."
    exit 1
fi

pushd "${REPO_ROOT}" > /dev/null

# Builds debug GBL binary.
#
# We need to build the debug binary in a separate output directory because:
#
#   1. We need to build with the "--sandbox_debug" option to prevent Bazel from deleting the .dwo
#      files (there isn't a way to tell bazel they are needed). But we don't want this option when
#      building the normal dist targets.
#   2. Building in a dedicated output directory makes it easier to collect .dwo files since we can
#      just grab all of them.
echo ""
echo "--------------------------------------"
echo "Building ${BAZEL_TARGET}..."
echo ""
"${REPO_ROOT}/tools/bazel" "--output_base=${BAZEL_OUT_BASE}" build "${BAZEL_TARGET}" \
    --verbose_failures \
    --sandbox_debug \
    --@gbl//toolchain:always_wait_gdb \
    --symlink_prefix=/
# Copies the EFI binary to the top level output directory so that it's easier to access.
BAZEL_OUT_BIN=$("${REPO_ROOT}/tools/bazel" cquery "${BAZEL_TARGET}" --output files 2>/dev/null)
BAZEL_OUT_BIN=$(readlink -f "${BAZEL_OUT_BASE}/execroot/_main/${BAZEL_OUT_BIN}")
GBL_DBG_BIN="${BAZEL_OUT_BASE}/gbl.efi"
cp "${BAZEL_OUT_BIN}" "${GBL_DBG_BIN}"

# Packs all .dwo files into a .dwp file.
#
# Bazel build is multithreaded and each thread has its own sandbox directory. This causes the .dwo
# files to scatter among many directories, which makes adding search path difficult. To workaround
# the issue, we simply package all .dwo files into a .dwp and pass it to gdb.
echo ""
echo "--------------------------------------"
echo "Collecting DWO files and generating DWARF package..."
echo ""
# .dwo files are considered unneeded artifacts by bazel and will be deleted in the next bazel
# invoke. Specifically, each time "bazel build" is invoked. it'll delete all artifacts it thinks
# are unneeded first. Therefore, unless we are doing a full rebuild, the new build output will only
# contains .dwo files corresponding to the sources that have changed which are actually built by
# bazel. Because of this, each time after build, we need to copy out any .dwo files generated and
# replace existing ones so that we always have the full up-to-date symbol set.
DWO_OUT="${BAZEL_OUT_BASE}/dwo"
mkdir -p "${DWO_OUT}"
# Because we only build a single debug binary in the output directory, we can just grab all the
# .dwo files.
find "${BAZEL_OUT_BASE}" -name *.dwo -not -path "${DWO_OUT}*" -exec mv -f {} "${DWO_OUT}"/ \; \
    2>/dev/null || true # Ignore empty result or permission denied errors.
# Packs all .dwo files into .dwp.
# Uses any version of llvm-dwp from the prebuilts.
LLVM_DWP=$(find ${REPO_ROOT}/prebuilts/clang/host/linux-x86/ -name llvm-dwp -print -quit)
if [[ ! (-x "${LLVM_DWP}" &&  -e "${LLVM_DWP}") ]]; then
    echo "Cannot find any llvm-dwp from ${REPO_ROOT}/prebuilts/clang/host/linux-x86/"
    exit 1;
fi
# The .dwp file must be placed alongside the debug binary and have the same file name plus
# extension ".dwp".
"${LLVM_DWP}" -o "${GBL_DBG_BIN}.dwp" $(ls "${DWO_OUT}"/*.dwo)

# Creates a GDB script to connect to QEMU, set source search path and load symbol.
DEBUG_PORT="1337"
GDB_INIT_CMD="${BAZEL_OUT_BASE}/gdb_init_cmd"
cat << EOF > "${GDB_INIT_CMD}"
${EXTRA_GDB_INIT_CMD}
echo Connecting to QEMU\n
target remote localhost:${DEBUG_PORT}

# Adds source search path
directory ${BAZEL_OUT_BASE}/execroot/_main/

echo Loading debug symbols and starting EFI app...\n
source ${SCRIPT_DIR}/load_gbl_debug_bin.py
load_gbl_debug_bin "${GBL_DBG_BIN}"
EOF

# Checks host QEMU dependencies.
if [[ -z $(which "${QEMU_BIN}") ]]; then
    echo "${QEMU_BIN} not installed."
    echo "Please run 'sudo apt-get install qemu-system ovmf'"
    exit 1
elif [[ ! -f "${OVMF}" ]]; then
    echo "Cannot find ${OVMF}."
    echo "Please run 'sudo apt-get install qemu-system ovmf'"
    exit 1
fi

# Assembles EFI boot partition to be used by QEMU.
EFI_OUTPUT_DIR="${BAZEL_OUT_BASE}/esp/EFI/BOOT"
mkdir -p "${EFI_OUTPUT_DIR}"
cp "${GBL_DBG_BIN}" "${EFI_OUTPUT_DIR}/${EFI_BIN_NAME}"

# Assembles QEMU commandline.
QEMU_CMD="${QEMU_BIN} -nographic -m 1G -smp 4"
QEMU_CMD+=" -drive if=pflash,format=raw,readonly=on,file=""${OVMF}"
QEMU_CMD+=" -drive format=raw,file=fat:rw:""${EFI_OUTPUT_DIR}""/../.."
QEMU_CMD+=" -drive format=raw,file=${SCRIPT_DIR}/gpt_with_misc.bin"
QEMU_CMD+=" -gdb tcp::${DEBUG_PORT} -S"
QEMU_CMD+=" ${EXTRA_QEMU_OPTIONS}"

echo "Starting rust-gdb in a new terminal..."
# Wait 2 seconds for QEMU to start first. Otherwise connect may hang if started too fast.
(sleep 2 && gnome-terminal -- bash -c "${GDB} --command=${GDB_INIT_CMD}")&

echo ""
echo "Starting QEMU..."
$QEMU_CMD

wait

popd > /dev/null
