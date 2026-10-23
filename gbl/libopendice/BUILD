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

load("@gbl_llvm_prebuilts//:info.bzl", "LLVM_PREBUILTS_C_INCLUDE")
load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")
load("@rules_rust_bindgen//:defs.bzl", "rust_bindgen")

package(
    default_applicable_licenses = ["@gbl//licensing:gbl_license"],
    default_visibility = ["//visibility:public"],
)

exports_files(glob(["**/*"]))

rust_library(
    name = "libopendice",
    srcs = glob(["src/**/*.rs"]),
    crate_name = "opendice",
    edition = "2021",
    deps = [
        ":opendice_android_bindgen",
        ":opendice_cbor_bindgen",
        "@ciborium_ll",
        "@open_dice//:libopen_dice_android_baremetal_multialg_static",
        "@open_dice//:libopen_dice_cbor_baremetal_multialg_static",
        "@zeroize",
    ] + select({
        "@gbl//toolchain:gbl_rust_aarch64": [
            "@gbl//libboot/aarch64_cache_helper:aarch64_cache_helper_staticlib",
        ],
        "//conditions:default": [],
    }),
)

rust_test(
    name = "libopendice_test",
    crate = ":libopendice",
)

rust_bindgen(
    name = "libopen_dice_cbor_bindgen_nostd",
    # Flags should match Soong definition
    bindgen_flags = [
        "--use-core",
        "--raw-line=#![no_std]",
        "--raw-line=#![allow(missing_docs)]",
        "--raw-line=#![allow(non_camel_case_types)]",
        "--raw-line=#![allow(non_snake_case)]",
        "--raw-line=#![allow(non_upper_case_globals)]",
        "--ctypes-prefix=core::ffi",
        "--rustified-enum=DiceConfigType",
        "--rustified-enum=DiceMode",
        "--rustified-enum=DiceResult",
        "--rustified-enum=DicePrincipal",
        "--rustified-enum=DiceKeyAlgorithm",
        "--allowlist-function=DiceDeriveCdiPrivateKeySeed",
        "--allowlist-function=DiceDeriveCdiCertificateId",
        "--allowlist-function=DiceMainFlow",
        "--allowlist-function=DiceHash",
        "--allowlist-function=DiceKdf",
        "--allowlist-function=DiceKeypairFromSeed",
        "--allowlist-function=DiceSign",
        "--allowlist-function=DiceCoseSignAndEncodeSign1",
        "--allowlist-function=DiceVerify",
        "--allowlist-function=DiceGenerateCertificate",
        "--allowlist-type=DiceContext",
        "--allowlist-var=DICE_CDI_SIZE",
        "--allowlist-var=DICE_HASH_SIZE",
        "--allowlist-var=DICE_HIDDEN_SIZE",
        "--allowlist-var=DICE_INLINE_CONFIG_SIZE",
        "--allowlist-var=DICE_PRIVATE_KEY_SEED_SIZE",
        "--allowlist-var=DICE_ID_SIZE",
        "--allowlist-var=DICE_PRIVATE_KEY_BUFFER_SIZE",
        "--allowlist-var=kCoseAlg.*",
        "--allowlist-var=kCoseKey.*",
    ],
    cc_lib = "@open_dice//:libopen_dice_android_baremetal_multialg",
    clang_flags = select({
        "//conditions:default": ["-m64"],
    }) + [
        "-I{}".format(LLVM_PREBUILTS_C_INCLUDE),
        "-nostdinc",
    ],
    header = "bindgen/dice/dice.h",
)

rust_library(
    name = "opendice_cbor_bindgen",
    srcs = [":libopen_dice_cbor_bindgen_nostd"],
)

rust_bindgen(
    name = "libopen_dice_android_bindgen_nostd",
    # Flags should match Soong definition
    bindgen_flags = [
        "--use-core",
        "--raw-line=#![no_std]",
        "--raw-line=#![allow(missing_docs)]",
        "--raw-line=#![allow(non_camel_case_types)]",
        "--raw-line=#![allow(non_snake_case)]",
        "--raw-line=#![allow(non_upper_case_globals)]",
        "--ctypes-prefix=core::ffi",
        "--allowlist-function=DiceAndroidFormatConfigDescriptor",
        "--allowlist-function=DiceAndroidHandoverMainFlow",
        "--allowlist-function=DiceAndroidHandoverParse",
        "--allowlist-var=DICE_ANDROID_CONFIG_.*",
        "--blocklist-type=DiceInputValues_",
        "--blocklist-type=DiceInputValues",
        "--raw-line=pub use opendice_cbor_bindgen::DiceInputValues;",
        "--blocklist-type=DiceResult",
        "--raw-line=pub use opendice_cbor_bindgen::DiceResult;",
    ],
    cc_lib = "@open_dice//:libopen_dice_android_baremetal_multialg",
    clang_flags = select({
        "//conditions:default": ["-m64"],
    }) + [
        "-I{}".format(LLVM_PREBUILTS_C_INCLUDE),
        "-nostdinc",
    ],
    header = "bindgen/dice/dice.h",
)

rust_library(
    name = "opendice_android_bindgen",
    srcs = [":libopen_dice_android_bindgen_nostd"],
    deps = [":opendice_cbor_bindgen"],
)
