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

load("@bazel_skylib//lib:selects.bzl", "selects")
load("@bazel_skylib//rules:common_settings.bzl", "bool_flag", "bool_setting", "int_flag")
load("@gbl_config//:variables.bzl", "ENABLE_CROSS_LANG_LTO")
load(
    "@gbl_llvm_prebuilts//:info.bzl",
    "GBL_CPP_CONFIG_INC",
    "GBL_EFI_SYSROOT",
    "LINUX_SYSROOT_INCLUDES",
    "LINUX_SYSROOT_LIB_DIR",
    "LINUX_X86_MUSL_CPP_CONFIG",
    "LLVM_PREBUILTS_CPP_INCLUDE",
    "LLVM_PREBUILTS_C_INCLUDE",
    "gbl_llvm_tool_path",
)
load(
    "@rules_rust//rust:toolchain.bzl",
    "rust_stdlib_filegroup",
    "rust_toolchain",
    "rustfmt_toolchain",
)
load("@rules_rust_bindgen//:defs.bzl", "rust_bindgen_toolchain")
load(
    ":gbl_toolchain.bzl",
    "build_with_no_rust_sysroot",
    "gbl_clang_cc_toolchain",
    "prebuilt_binary",
)

package(
    default_applicable_licenses = ["@gbl//licensing:gbl_license"],
    default_visibility = ["//visibility:public"],
)

# The following constraint/settings will be used in our newly defined
# toolchains, so that they only get selected by bazel when we configure
# to build GBL.
constraint_setting(name = "firmware_image_type")

constraint_value(
    name = "uefi",
    constraint_setting = ":firmware_image_type",
)

constraint_value(
    name = "uefi_debug",
    constraint_setting = ":firmware_image_type",
)

constraint_value(
    name = "elf",
    constraint_setting = ":firmware_image_type",
)

# This constraint specifies whether we're building for a dev or prod board.
constraint_setting(
    name = "board_class",
    # Default to prod for now; eventually we may want to update all call sites
    # and force the caller to explicitly declare which variant to build.
    default_constraint_value = ":prod",
)

constraint_value(
    name = "dev",
    constraint_setting = ":board_class",
)

constraint_value(
    name = "prod",
    constraint_setting = ":board_class",
)

# Specifies whether we're booting Linux with the EFI boot stub.
constraint_setting(name = "linux_jump_mode")

constraint_value(
    name = "efi_boot_stub",
    constraint_setting = ":linux_jump_mode",
)

# Rustc flags to add based on the dev/prod board class.
# This is intended to be used inside a `select()` statement.
rustc_dev_prod_flags_select = {
    # Enable the "gbl_dev" feature for all dev targets.
    # Enable the "fuchsia" feature for all dev targets.
    ":dev": [
        "--cfg=feature=\"gbl_dev\"",
        "--cfg=feature=\"fuchsia\"",
    ],
    # Prod is the absence of the dev feature.
    # Rust features should be additive; in this case we consider prod to be
    # the default featureset, and adding "dev" on top enables additional
    # dev-only functionality e.g. extra logging, fastboot over TCP, etc.
    ":prod": [],
}

host_x86_64_constraint_values = [
    "@platforms//os:linux",
    "@platforms//cpu:x86_64",
]

uefi_x86_64_constraint_values = [
    ":uefi",
    "@platforms//os:none",
    "@platforms//cpu:x86_64",
]

uefi_x86_64_debug_constraint_values = [
    ":uefi_debug",
    "@platforms//os:none",
    "@platforms//cpu:x86_64",
]

uefi_aarch64_constraint_values = [
    ":uefi",
    "@platforms//os:none",
    "@platforms//cpu:aarch64",
]

uefi_aarch64_debug_constraint_values = [
    ":uefi_debug",
    "@platforms//os:none",
    "@platforms//cpu:aarch64",
]

elf_riscv64_constraint_values = [
    ":elf",
    "@platforms//os:none",
    "@platforms//cpu:riscv64",
]

config_setting(
    name = "gbl_rust_host_x86_64",
    constraint_values = host_x86_64_constraint_values,
)

config_setting(
    name = "gbl_rust_uefi_x86_64",
    constraint_values = uefi_x86_64_constraint_values,
)

config_setting(
    name = "gbl_rust_uefi_x86_64_debug",
    constraint_values = uefi_x86_64_debug_constraint_values,
)

config_setting(
    name = "gbl_rust_uefi_aarch64",
    constraint_values = uefi_aarch64_constraint_values,
)

config_setting(
    name = "gbl_rust_uefi_aarch64_debug",
    constraint_values = uefi_aarch64_debug_constraint_values,
)

config_setting(
    name = "gbl_rust_elf_riscv64",
    constraint_values = elf_riscv64_constraint_values,
)

elf_aarch64_constraint_values = [
    ":elf",
    "@platforms//os:none",
    "@platforms//cpu:aarch64",
]

config_setting(
    name = "gbl_rust_elf_aarch64",
    constraint_values = elf_aarch64_constraint_values,
)

selects.config_setting_group(
    name = "gbl_rust_aarch64",
    match_any = [
        ":gbl_rust_uefi_aarch64",
        ":gbl_rust_uefi_aarch64_debug",
        ":gbl_rust_elf_aarch64",
    ],
)

platform(
    name = "host_x86_64_dev",
    constraint_values = host_x86_64_constraint_values + [":dev"],
)

platform(
    name = "host_x86_64_prod",
    constraint_values = host_x86_64_constraint_values + [":prod"],
)

platform(
    name = "gbl_uefi_x86_64_dev",
    constraint_values = uefi_x86_64_constraint_values + [":dev"],
)

platform(
    name = "gbl_uefi_x86_64_prod",
    constraint_values = uefi_x86_64_constraint_values + [":prod"],
)

platform(
    name = "gbl_uefi_x86_64_debug_dev",
    constraint_values = uefi_x86_64_debug_constraint_values + [":dev"],
)

platform(
    name = "gbl_uefi_x86_64_debug_prod",
    constraint_values = uefi_x86_64_debug_constraint_values + [":prod"],
)

platform(
    name = "gbl_uefi_aarch64_dev",
    constraint_values = uefi_aarch64_constraint_values + [":dev"],
)

platform(
    name = "gbl_uefi_aarch64_prod",
    constraint_values = uefi_aarch64_constraint_values + [":prod"],
)

platform(
    name = "gbl_uefi_aarch64_debug_dev",
    constraint_values = uefi_aarch64_debug_constraint_values + [":dev"],
)

platform(
    name = "gbl_uefi_aarch64_debug_prod",
    constraint_values = uefi_aarch64_debug_constraint_values + [":prod"],
)

platform(
    name = "gbl_elf_riscv64_dev",
    constraint_values = elf_riscv64_constraint_values + [":dev"],
)

platform(
    name = "gbl_elf_riscv64_prod",
    constraint_values = elf_riscv64_constraint_values + [":prod"],
)

platform(
    name = "gbl_elf_aarch64_dev",
    constraint_values = elf_aarch64_constraint_values + [":dev"],
)

platform(
    name = "gbl_elf_aarch64_prod",
    constraint_values = elf_aarch64_constraint_values + [":prod"],
)

platform(
    name = "gbl_uefi_x86_64_dev_bootstub",
    constraint_values = uefi_x86_64_constraint_values + [
        ":dev",
        ":efi_boot_stub",
    ],
)

platform(
    name = "gbl_uefi_aarch64_dev_bootstub",
    constraint_values = uefi_aarch64_constraint_values + [
        ":dev",
        ":efi_boot_stub",
    ],
)

bool_setting(
    name = "rust_no_sysroot",
    build_setting_default = False,
    visibility = ["//visibility:public"],
)

config_setting(
    name = "rust_no_sysroot_true",
    flag_values = {":rust_no_sysroot": "True"},
)

# For the end-to-end GDB example, we are using prebuilt UEFI firmware which doesn't have our custom
# `gbl_debug` EFI variables. Thus for the example, we use a build flag to force enable waiting for
# gdb connection.
bool_flag(
    name = "always_wait_gdb",
    build_setting_default = False,
    help = "Whether to enable always waiting for gdb connection",
)

config_setting(
    name = "always_wait_gdb_enabled",
    flag_values = {
        ":always_wait_gdb": "True",
    },
)

bool_flag(
    name = "pause_boot_in_fastboot",
    build_setting_default = False,
    help = "Whether to enable always waiting for gdb connection",
)

config_setting(
    name = "pause_boot_in_fastboot_true",
    flag_values = {
        ":pause_boot_in_fastboot": "True",
    },
)

bool_flag(
    name = "enable_tracing",
    build_setting_default = False,
    help = "Whether to enable gbl-tracing",
)

config_setting(
    name = "tracing_enabled",
    flag_values = {
        ":enable_tracing": "True",
    },
)

int_flag(
    name = "trace_buffer_size_mb",
    build_setting_default = 64,
    help = "Size of trace buffer.",
)

builtin_includes_common = [
    LLVM_PREBUILTS_CPP_INCLUDE,  # C++ headers must come first.
    LLVM_PREBUILTS_C_INCLUDE,
]

cc_flags_common = [
    "-fno-common",
    "-fno-exceptions",
    "-fno-rtti",
    "-femit-dwarf-unwind=always",
    "-ffunction-sections",
    "-fdata-sections",
    # Enable optimization otherwise software AVB hash will be too slow.
    "-O3",
    # The llvm version we use errors out for every goto statement that bypasses variable
    # initialization. The problematic sources are all C. There's an upstream fix that disables
    # this warning for non-C++ sources. (https://github.com/llvm/llvm-project/pull/138507)
    "-Wno-microsoft-goto",
    # Newer Clang versions (e.g. r596125) mark certain intrinsic headers as
    # `constexpr`, but their implementations contain builtins that are not
    # valid constant expressions when evaluated in a constant expression
    # context. This leads to -Winvalid-constexpr errors when building targets
    # (such as BoringSSL) that include these headers. Disable it.
    "-Wno-invalid-constexpr",
]

# Linux host LLVM toolchain.
# The toolchain is mainly used for building/linking host tools, i.e. bindgen pre-processing
gbl_clang_cc_toolchain(
    name = "x86_64-unknown-linux-gnu",
    # Host LLVM toolchain has additional C++ stdlib.
    builtin_includes = [LINUX_X86_MUSL_CPP_CONFIG] + builtin_includes_common + [LINUX_SYSROOT_INCLUDES],
    cc_flags = cc_flags_common + [
        "-D_LIBCPP_PROVIDES_DEFAULT_RUNE_TABLE",
    ],
    ld_flags = [
        "-stdlib=libc++",
        "-static-libstdc++",
    ],
    target_cpu = "x86_64",
    target_system_triple = "x86_64-unknown-linux-gnu",
)

toolchain(
    name = "x86_64-unknown-linux-gnu_toolchain",
    exec_compatible_with = ["@platforms//os:linux"],
    target_compatible_with = [
        "@platforms//os:linux",
        "@platforms//cpu:x86_64",
    ],
    toolchain = ":x86_64-unknown-linux-gnu",
    toolchain_type = "@bazel_tools//tools/cpp:toolchain_type",
)

# The following defines LLVM C++ toolchains for UEFI/ELF targets. They are mostly used for the
# final step of linking Rust executables, but may also be used for compiling mixed C/C++ code.

uefi_c_lto_flags = [
    "-flto=thin",
] if ENABLE_CROSS_LANG_LTO else []

cc_flags_uefi_common = cc_flags_common + [
    "-D_LIBCPP_HAS_NO_THREADS",
    "-D_LIBCPP_HAS_NO_WIDE_CHARACTERS",
    "-D_LIBCPP_NO_VCRUNTIME",
    "-ffreestanding",
    # This prevents clang C++ header from defining _LIBCPP_MSVCRT which requires MSVC runtime.
    "-U_MSC_VER",
    "-fstack-protector-all",
    # Always stores frame pointers.
    "-fno-omit-frame-pointer",
    # Supports unwind table. (On arm, this makes sure x29 is stored on stack first).
    "-funwind-tables",
] + uefi_c_lto_flags

uefi_ld_flags_common = [
    "-z,noexecstack",
    "-z,now",
    "--as-needed",
]

builtin_includes_uefi_common = [GBL_CPP_CONFIG_INC] + builtin_includes_common + [GBL_EFI_SYSROOT]

x86_64_uefi_cc_flags = cc_flags_uefi_common + [
    # Adding this prevents the compiler from generating mmx, sse instructions such as
    # "movsd (%esp),%xmm0" which likely isn't enabled during the bootloader stage and causes
    # crash as a result.
    "-mgeneral-regs-only",
    # libavb and boringssl uses more than 4K of stack space. This prevents the compiler
    # from inserting _chkstk().
    "-mno-stack-arg-probe",
    # Enable shadow stack
    "-mshstk",
    "-fcf-protection=full",
]

# x86_64 UEFI targets
gbl_clang_cc_toolchain(
    name = "x86_64_uefi_clang_cc_toolchain",
    builtin_includes = builtin_includes_uefi_common,
    cc_flags = x86_64_uefi_cc_flags,
    ld_flags = uefi_ld_flags_common,
    target_cpu = "x86_64",
    target_system_triple = "x86_64-unknown-windows-msvc",
)

toolchain(
    name = "x86_64_uefi_clang",
    exec_compatible_with = ["@platforms//os:linux"],
    target_compatible_with = uefi_x86_64_constraint_values,
    toolchain = ":x86_64_uefi_clang_cc_toolchain",
    toolchain_type = "@bazel_tools//tools/cpp:toolchain_type",
)

# x86_64 UEFI DEBUG targets

x86_64_uefi_debug_cc_flags = x86_64_uefi_cc_flags

x86_64_uefi_debug_cc_flags.remove("-O3")

gbl_clang_cc_toolchain(
    name = "x86_64_uefi_debug_clang_cc_toolchain",
    builtin_includes = builtin_includes_uefi_common,
    cc_flags = x86_64_uefi_debug_cc_flags,
    ld_flags = uefi_ld_flags_common,
    target_cpu = "x86_64",
    target_system_triple = "x86_64-unknown-windows",
)

toolchain(
    name = "x86_64_uefi_debug_clang",
    exec_compatible_with = ["@platforms//os:linux"],
    target_compatible_with = uefi_x86_64_debug_constraint_values,
    toolchain = ":x86_64_uefi_debug_clang_cc_toolchain",
    toolchain_type = "@bazel_tools//tools/cpp:toolchain_type",
)

# aarch64 UEFI targets
gbl_clang_cc_toolchain(
    name = "aarch64_uefi_clang_cc_toolchain",
    builtin_includes = builtin_includes_uefi_common,
    cc_flags = cc_flags_uefi_common + [
        "-mbranch-protection=standard",
        "-march=armv8-a",
    ] + select({
        "//conditions:default": [],
        ":tracing_enabled": ["-pg"],  # mcount instrumentation
    }),
    ld_flags = uefi_ld_flags_common + select({
        "//conditions:default": [],
        # Switch to a dedicate main entry that sets up tracing.
        ":tracing_enabled": ["/entry:efi_main_tracing"],
    }),
    target_cpu = "aarch64",
    target_system_triple = "aarch64-windows-msvc",
)

toolchain(
    name = "aarch64_uefi_clang",
    exec_compatible_with = ["@platforms//os:linux"],
    target_compatible_with = uefi_aarch64_constraint_values,
    toolchain = ":aarch64_uefi_clang_cc_toolchain",
    toolchain_type = "@bazel_tools//tools/cpp:toolchain_type",
)

# aarch64 UEFI DEBUG targets

aarch64_uefi_debug_cc_flags = cc_flags_uefi_common + [
    "-mbranch-protection=standard",
    "-O0",
]

aarch64_uefi_debug_cc_flags.remove("-O3")

gbl_clang_cc_toolchain(
    name = "aarch64_uefi_debug_clang_cc_toolchain",
    builtin_includes = builtin_includes_uefi_common,
    cc_flags = aarch64_uefi_debug_cc_flags,
    ld_flags = uefi_ld_flags_common,
    target_cpu = "aarch64",
    target_system_triple = "aarch64-unknown-windows",
)

toolchain(
    name = "aarch64_uefi_debug_clang",
    exec_compatible_with = ["@platforms//os:linux"],
    target_compatible_with = uefi_aarch64_debug_constraint_values,
    toolchain = ":aarch64_uefi_debug_clang_cc_toolchain",
    toolchain_type = "@bazel_tools//tools/cpp:toolchain_type",
)

# riscv64 ELF targets
gbl_clang_cc_toolchain(
    name = "riscv64_elf_clang_cc_toolchain",
    builtin_includes = builtin_includes_uefi_common,
    cc_flags = cc_flags_uefi_common + [
        "-fpie",
        # Macros required by floating APIs in C++ headers.
        # This is typically provided by target platform sysroot, which we don't have for our EFI
        # environment. But since floating point is not used, we simply define placeholder codes.
        "-DFP_NAN=0",
        "-DFP_INFINITE=1",
        "-DFP_ZERO=2",
        "-DFP_SUBNORMAL=3",
        "-DFP_NORMAL=4",
        # The default setting 'all' causes problems on RISC-V
        "-fstack-protector-strong",
    ],
    ld_flags = uefi_ld_flags_common,
    target_cpu = "riscv64",
    target_system_triple = "riscv64-unknown-linux",
)

toolchain(
    name = "riscv64_elf_clang",
    exec_compatible_with = ["@platforms//os:linux"],
    target_compatible_with = elf_riscv64_constraint_values,
    toolchain = ":riscv64_elf_clang_cc_toolchain",
    toolchain_type = "@bazel_tools//tools/cpp:toolchain_type",
)

gbl_clang_cc_toolchain(
    name = "aarch64_elf_clang_cc_toolchain",
    builtin_includes = builtin_includes_uefi_common,
    cc_flags = cc_flags_uefi_common + [
        "-fpie",
        "-march=armv8-a",
    ],
    target_cpu = "aarch64",
    target_system_triple = "aarch64-none-elf",
)

toolchain(
    name = "aarch64_elf_clang",
    exec_compatible_with = ["@platforms//os:linux"],
    target_compatible_with = elf_aarch64_constraint_values,
    toolchain = ":aarch64_elf_clang_cc_toolchain",
    toolchain_type = "@bazel_tools//tools/cpp:toolchain_type",
)

# Rust toolchains

# An empty rust std file group used as placeholder when building rust sysroot.
rust_stdlib_filegroup(
    name = "rust_stdlib_empty",
    srcs = [],
)

# A rule for building sysroot from source.
build_with_no_rust_sysroot(
    name = "rust_sysroot_source_build",
    deps = [
        "@rust_prebuilts//:liballoc",
        "@rust_prebuilts//:libcompiler_builtins",
        "@rust_prebuilts//:libcore",
    ],
)

rust_stdlib_filegroup(
    name = "rust_std_source_build",
    srcs = [":rust_sysroot_source_build"],
)

common_lint_opts = [
    "-A",
    "deprecated",
    # external/rust/crates/spin doesn't pass this lint check and there is not a way to make an
    # exemption. Disable it until upstream is fixed or we figure out a workaround.
    #"-D",
    #"unsafe_op_in_unsafe_fn",
    "-D",
    "warnings",
    "-D",
    "clippy::undocumented_unsafe_blocks",
    "-D",
    "clippy::too-many-arguments",
]

# Linux x86_64 Host toolchain
rust_toolchain(
    name = "x86_64_unknown_linux_gnu",
    allocator_library = None,
    binary_ext = "",
    default_edition = "2021",
    dylib_ext = ".so",
    exec_triple = "x86_64-unknown-linux-musl",
    extra_rustc_flags = select(rustc_dev_prod_flags_select) + [
        # Allow multiple definitions so that custom C implementations in @gbl//libc (such as
        # strtoul) can override matching symbols in musl's static libc.a without linker collision.
        "-C",
        "link-arg=-Wl,--allow-multiple-definition",
    ],
    extra_rustc_flags_for_crate_types = {
        # The x86_64-unknown-linux-musl target defaults to static CRT (+crt-static). For proc-macros
        # (dynamically loaded .so plugins), static CRT linking embeds an uninitialized musl allocator
        # into the shared object, causing SIGSEGV when dlopened by rustc. Force dynamic linking against
        # the musl sysroot libc_musl.so for proc-macros only, while leaving host binaries statically linked.
        "proc-macro": [
            "-C",
            "target-feature=-crt-static",
            "-C",
            "link-self-contained=no",
            "-C",
            "link-arg=-L" + LINUX_SYSROOT_LIB_DIR,
            "-C",
            "link-arg=-Wl,-rpath," + LINUX_SYSROOT_LIB_DIR,
        ],
    },
    global_allocator_library = None,
    rust_doc = "@rust_prebuilts//:bin/rustdoc",
    rust_std = "@rust_prebuilts//:stdlib_x86_64-unknown-linux-musl",
    rustc = "@rust_prebuilts//:bin/rustc",
    staticlib_ext = ".a",
    stdlib_linkflags = [],
    target_triple = "x86_64-unknown-linux-musl",
)

toolchain(
    name = "x86_64_unknown_linux_gnu_toolchain",
    exec_compatible_with = ["@platforms//os:linux"],
    target_settings = [":gbl_rust_host_x86_64"],
    toolchain = ":x86_64_unknown_linux_gnu",
    toolchain_type = "@rules_rust//rust:toolchain",
)

# Common flags for all Rust UEFI toolchains.
# Note this disables the default sysroot, so the rule must explicitly set `rust_std`.
uefi_rustc_flags = [
    # The linker options generated by rustc assumes `lld` as the linker. For windows platforms,
    # the lld args style is different than that of clang++, i.e. for library search path, lld
    # uses "/L<path>" while clang++ uses "-L<path>". Thus we need to use lld directly instead
    # of `clang++`.
    "--codegen=linker={}".format(gbl_llvm_tool_path("lld")),
    # Disable default sysroot. We'll pass sysroot explicitly via the `rust_std` field.
    "--sysroot",
    "/dev/null",
    # The bootloader does not persist for long and does not directly
    # do any heavy computation.
    # Trade some performance for additional security checks.
    "-C",
    "overflow-checks=true",
    # Stack protector must be one of {none,all}
    # Note: because the UEFI toolchain does not link against a libc
    # we need to define the required symbols manually.
    # All required functions must be implemented in C to prevent
    # infinite recursion.
    "-Z",
    "stack-protector=all",
    # `rustc` requires `-Zunstable-options` to use custom target specifications
    # since Rust 1.95.0 (https://github.com/rust-lang/rust/pull/151534).
    "-Z",
    "unstable-options",
    # Always stores frame pointers.
    "-C",
    "force-frame-pointers=yes",
    # Support unwind tables. (On arm, this make sures x29 is stored on stack first).
    "-C",
    "force-unwind-tables=yes",
    # Generate debug information. For MSVC targets, this only affects the size of the PDB file.
    "-g",
] + ([
    # Enable linker-plugin LTO for cross-language inlining
    "-C",
    "linker-plugin-lto",
] if ENABLE_CROSS_LANG_LTO else [])

config_setting(
    name = "compilation_mode_dbg",
    values = {"compilation_mode": "dbg"},
)

rustc_opt_flags = ["-C"] + select({
    ":compilation_mode_dbg": ["opt-level=0"],
    "//conditions:default": ["opt-level=3"],  # Default to enable optimization
})

wait_gdb_switch = select({
    ":always_wait_gdb_enabled": [
        "--cfg",
        "feature=\"always-wait-gdb\"",
    ],
    "//conditions:default": [],
})

pause_boot_in_fastboot_switch = select({
    ":pause_boot_in_fastboot_true": [
        "--cfg",
        "feature=\"pause-boot-in-fastboot\"",
    ],
    "//conditions:default": [],
})

efi_boot_stub_switch = select({
    ":efi_boot_stub": [
        "--cfg",
        "feature=\"efi_boot_stub\"",
    ],
    "//conditions:default": [],
})

rustc_common_flags = common_lint_opts + uefi_rustc_flags + select(rustc_dev_prod_flags_select) + \
                     wait_gdb_switch + pause_boot_in_fastboot_switch + efi_boot_stub_switch

# x86_64 UEFI toolchain
rust_toolchain(
    name = "x86_64-unknown-uefi",
    allocator_library = None,
    binary_ext = ".efi",
    default_edition = "2021",
    dylib_ext = ".so",
    exec_triple = "x86_64-unknown-linux-musl",
    extra_rustc_flags = [
        "-Z",
        "cf-protection=full",
    ] + rustc_common_flags + rustc_opt_flags,
    global_allocator_library = None,
    rust_doc = "@rust_prebuilts//:bin/rustdoc",
    rust_std = select({
        ":rust_no_sysroot_true": ":rust_stdlib_empty",
        "//conditions:default": ":rust_std_source_build",
    }),
    rustc = "@rust_prebuilts//:bin/rustc",
    staticlib_ext = ".a",
    stdlib_linkflags = [],
    # rules_rust only outputs pdb file when stripping is disabled.
    # Debug info is in PDB file. There appears to be no change on file size.
    strip_level = {
        "dbg": "none",
        "fastbuild": "none",
        "opt": "none",
    },
    target_triple = "x86_64-unknown-uefi",
)

toolchain(
    name = "x86_64-unknown-uefi_toolchain",
    exec_compatible_with = ["@platforms//os:linux"],
    target_settings = [":gbl_rust_uefi_x86_64"],
    toolchain = ":x86_64-unknown-uefi",
    toolchain_type = "@rules_rust//rust:toolchain",
)

msvc_rustc_debug_common = [
    "--cfg",
    "feature=\"gdb_debug\"",
    # This also generates symbols in the EFI app binary (in addition to DWARF files) and makes
    # it easier to read its disassembly.
    "-C",
    "link-args=/debug:dwarf",
]

# x64 debug target
rust_toolchain(
    name = "x86_64-unknown-uefi-debug",
    allocator_library = None,
    binary_ext = "",
    default_edition = "2021",
    dylib_ext = ".so",
    exec_triple = "x86_64-unknown-linux-musl",
    extra_rustc_flags = [
        "-Z",
        "cf-protection=full",
    ] + rustc_common_flags + msvc_rustc_debug_common,
    global_allocator_library = None,
    rust_doc = "@rust_prebuilts//:bin/rustdoc",
    # Need to use our own built sysroot because we are using a custom spec below.
    rust_std = select({
        ":rust_no_sysroot_true": ":rust_stdlib_empty",
        "//conditions:default": ":rust_std_source_build",
    }),
    rustc = "@rust_prebuilts//:bin/rustc",
    staticlib_ext = ".a",
    stdlib_linkflags = [],
    # The custom spec is based on builtin target "x86_64-unknown-uefi" but with the following
    # changes for enabling debug symbols:
    #
    #   1. "debuginfo-kind" changed from "pdb" to "dwarf".
    #   2. "split-debuginfo" and "supported-split-debuginfo" changed from "packed" to "unpacked".
    #
    # Notes: 1 and 2 should be possible using commandline argument as well. Investigate reusing
    # existing toolchain definition.
    #
    # The original spec can be obtained by:
    #
    #   rustc +nightly -Z unstable-options --print target-spec-json \
    #     --target x86_64-unknown-uefi
    target_json = """
                {
                    "abi-return-struct-as-int": true,
                    "allows-weak-linkage": false,
                    "arch": "x86_64",
                    "archive-format": "coff",
                    "binary-format": "coff",
                    "cpu": "x86-64",
                    "crt-objects-fallback": "false",
                    "data-layout": "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128",
                    "debuginfo-kind": "dwarf",
                    "disable-redzone": true,
                    "dll-tls-export": false,
                    "emit-debug-gdb-scripts": false,
                    "entry-abi": "win64",
                    "entry-name": "efi_main",
                    "exe-suffix": ".efi",
                    "features": "-mmx,-sse,+soft-float",
                    "is-like-msvc": true,
                    "is-like-windows": true,
                    "linker": "rust-lld",
                    "linker-flavor": "msvc-lld",
                    "linker-is-gnu": false,
                    "lld-flavor": "link",
                    "llvm-target": "x86_64-unknown-windows",
                    "max-atomic-width": 64,
                    "metadata": {
                        "description": "64-bit UEFI",
                        "host_tools": false,
                        "std": null,
                        "tier": 2
                    },
                    "os": "uefi",
                    "panic-strategy": "abort",
                    "plt-by-default": false,
                    "pre-link-args": {
                        "msvc": [
                        "/NOLOGO",
                        "/entry:efi_main",
                        "/subsystem:efi_application"
                        ],
                        "msvc-lld": [
                        "/NOLOGO",
                        "/entry:efi_main",
                        "/subsystem:efi_application"
                        ]
                    },
                    "rustc-abi": "x86-softfloat",
                    "singlethread": true,
                    "split-debuginfo": "unpacked",
                    "stack-probes": {
                        "kind": "call"
                    },
                    "supported-split-debuginfo": [
                        "unpacked"
                    ],
                    "target-pointer-width": 64
                }
""",
)

toolchain(
    name = "x86_64-unknown-uefi-debug_toolchain",
    exec_compatible_with = ["@platforms//os:linux"],
    target_settings = ["@gbl//toolchain:gbl_rust_uefi_x86_64_debug"],
    toolchain = ":x86_64-unknown-uefi-debug",
    toolchain_type = "@rules_rust//rust:toolchain",
)

# aarch64 UEFI toolchain
rust_toolchain(
    name = "aarch64-unknown-uefi",
    allocator_library = None,
    binary_ext = ".efi",
    default_edition = "2021",
    dylib_ext = ".so",
    exec_triple = "x86_64-unknown-linux-musl",
    extra_rustc_flags = [
        "-Z",
        "branch-protection=bti,pac-ret,leaf",
    ] + rustc_common_flags + rustc_opt_flags + select({
        ":tracing_enabled": [
            "-Z",
            "instrument-mcount",
            "--cfg=feature=\"gbl_tracing\"",
            # Expansion of macro sometimes causes incorrect line information in debugging.
            "-C",
            "collapse-macro-debuginfo=yes",
        ],
        "//conditions:default": [],
    }),
    global_allocator_library = None,
    rust_doc = "@rust_prebuilts//:bin/rustdoc",
    rust_std = select({
        ":rust_no_sysroot_true": ":rust_stdlib_empty",
        "//conditions:default": ":rust_std_source_build",
    }),
    rustc = "@rust_prebuilts//:bin/rustc",
    staticlib_ext = ".a",
    stdlib_linkflags = [],
    # rules_rust only outputs pdb file when stripping is disabled.
    # Debug info is in PDB file. There appears to be no change on file size.
    strip_level = {
        "dbg": "none",
        "fastbuild": "none",
        "opt": "none",
    },
    target_triple = "aarch64-unknown-uefi",
)

toolchain(
    name = "aarch64-unknown-uefi_toolchain",
    exec_compatible_with = ["@platforms//os:linux"],
    target_settings = [":gbl_rust_uefi_aarch64"],
    toolchain = ":aarch64-unknown-uefi",
    toolchain_type = "@rules_rust//rust:toolchain",
)

# aarch64 debug target
rust_toolchain(
    name = "aarch64-unknown-uefi-debug",
    allocator_library = None,
    binary_ext = "",
    default_edition = "2021",
    dylib_ext = ".so",
    exec_triple = "aarch64-unknown-linux-gnu",
    extra_rustc_flags = rustc_common_flags + msvc_rustc_debug_common,
    global_allocator_library = None,
    rust_doc = "@rust_prebuilts//:bin/rustdoc",
    # Need to use our own built sysroot because we are using a custom spec below.
    rust_std = select({
        ":rust_no_sysroot_true": ":rust_stdlib_empty",
        "//conditions:default": ":rust_std_source_build",
    }),
    rustc = "@rust_prebuilts//:bin/rustc",
    staticlib_ext = ".a",
    stdlib_linkflags = [],
    # The custom spec is based on builtin target "aarch64-unknown-uefi" but with the following
    # changes for enabling debug symbols:
    #
    #   1. "debuginfo-kind" changed from "pdb" to "dwarf".
    #   2. "split-debuginfo" and "supported-split-debuginfo" changed from "packed" to "unpacked".
    #
    # Notes: 1 and 2 should be possible using commandline argument as well. Investigate reusing
    # existing toolchain definition.
    #
    # The original spec can be obtained by:
    #
    #   rustc +nightly -Z unstable-options --print target-spec-json \
    #     --target aarch64-unknown-uefi
    target_json = """
                {
                    "abi-return-struct-as-int": true,
                    "allows-weak-linkage": false,
                    "arch": "aarch64",
                    "archive-format": "coff",
                    "binary-format": "coff",
                    "crt-objects-fallback": "false",
                    "data-layout": "e-m:w-p270:32:32-p271:32:32-p272:64:64-p:64:64-i32:32-i64:64-i128:128-n32:64-S128-Fn32",
                    "debuginfo-kind": "dwarf",
                    "disable-redzone": true,
                    "dll-tls-export": false,
                    "emit-debug-gdb-scripts": false,
                    "entry-name": "efi_main",
                    "exe-suffix": ".efi",
                    "features": "+v8a",
                    "is-like-msvc": true,
                    "is-like-windows": true,
                    "linker": "rust-lld",
                    "linker-flavor": "msvc-lld",
                    "linker-is-gnu": false,
                    "lld-flavor": "link",
                    "llvm-target": "aarch64-unknown-windows",
                    "max-atomic-width": 128,
                    "metadata": {
                        "description": "ARM64 UEFI",
                        "host_tools": false,
                        "std": null,
                        "tier": 2
                    },
                    "os": "uefi",
                    "panic-strategy": "abort",
                    "pre-link-args": {
                        "msvc": [
                        "/NOLOGO",
                        "/entry:efi_main",
                        "/subsystem:efi_application",
                        "/machine:arm64"
                        ],
                        "msvc-lld": [
                        "/NOLOGO",
                        "/entry:efi_main",
                        "/subsystem:efi_application",
                        "/machine:arm64"
                        ]
                    },
                    "singlethread": true,
                    "split-debuginfo": "unpacked",
                    "stack-probes": {
                        "kind": "call"
                    },
                    "supported-split-debuginfo": [
                        "unpacked"
                    ],
                    "target-pointer-width": 64
                }
""",
)

toolchain(
    name = "aarch64-unknown-uefi-debug_toolchain",
    exec_compatible_with = ["@platforms//os:linux"],
    target_settings = ["@gbl//toolchain:gbl_rust_uefi_aarch64_debug"],
    toolchain = ":aarch64-unknown-uefi-debug",
    toolchain_type = "@rules_rust//rust:toolchain",
)

# riscv64 PIE ELF toolchain
rust_toolchain(
    name = "riscv64gc-unknown-none-pie_elf",
    allocator_library = None,
    binary_ext = "",
    default_edition = "2021",
    dylib_ext = ".so",
    exec_triple = "x86_64-unknown-linux-musl",
    extra_rustc_flags = rustc_common_flags + rustc_opt_flags,
    global_allocator_library = None,
    rust_doc = "@rust_prebuilts//:bin/rustdoc",
    # Need to use our own built sysroot because we are using a custom spec below.
    rust_std = select({
        ":rust_no_sysroot_true": ":rust_stdlib_empty",
        "//conditions:default": ":rust_std_source_build",
    }),
    rustc = "@rust_prebuilts//:bin/rustc",
    staticlib_ext = ".a",
    stdlib_linkflags = [],
    # The custom spec is based on builtin target "riscv64gc-unknown-none-elf" but with the
    # following changes for enabling PIE:
    #
    #   1. "relocation-model" config entry changed from "static" to "pic".
    #   2. Added "position-independent-executables": true.
    #   3. Added "os": "none" config. Otherwise bazel uses the wrong library naming convention
    #      during linking.
    #
    # The original spec can be obtained by:
    #
    #   rustc +nightly -Z unstable-options --print target-spec-json \
    #     --target riscv64gc-unknown-none-elf
    target_json = """
                {
                    "arch": "riscv64",
                    "code-model": "medium",
                    "cpu": "generic-rv64",
                    "crt-objects-fallback": "false",
                    "data-layout": "e-m:e-p:64:64-i64:64-i128:128-n32:64-S128",
                    "eh-frame-header": false,
                    "emit-debug-gdb-scripts": false,
                    "features": "+m,+a,+f,+d,+c,+zicsr,+zifencei",
                    "linker": "rust-lld",
                    "linker-flavor": "gnu-lld",
                    "llvm-abiname": "lp64d",
                    "llvm-target": "riscv64",
                    "max-atomic-width": 64,
                    "os": "none",
                    "metadata": {
                        "description": "Bare RISC-V (RV64IMAFDC ISA)",
                        "host_tools": false,
                        "std": false,
                        "tier": 2
                    },
                    "panic-strategy": "abort",
                    "relocation-model": "pic",
                    "position-independent-executables": true,
                    "supported-sanitizers": [
                        "shadow-call-stack",
                        "kernel-address"
                    ],
                    "target-pointer-width": 64
                }
""",
)

toolchain(
    name = "riscv64gc-unknown-none-pie_elf_toolchain",
    exec_compatible_with = ["@platforms//os:linux"],
    target_settings = ["@gbl//toolchain:gbl_rust_elf_riscv64"],
    toolchain = ":riscv64gc-unknown-none-pie_elf",
    toolchain_type = "@rules_rust//rust:toolchain",
)

rust_toolchain(
    name = "aarch64-unknown-none",
    allocator_library = None,
    binary_ext = "",
    default_edition = "2021",
    dylib_ext = ".so",
    exec_triple = "x86_64-unknown-linux-musl",
    extra_rustc_flags = rustc_common_flags + rustc_opt_flags + [
        "-C",
        "relocation-model=pic",
        "-C",
        "link-arg=-pie",
    ],
    global_allocator_library = None,
    rust_doc = "@rust_prebuilts//:bin/rustdoc",
    rust_std = select({
        ":rust_no_sysroot_true": ":rust_stdlib_empty",
        "//conditions:default": ":rust_std_source_build",
    }),
    rustc = "@rust_prebuilts//:bin/rustc",
    staticlib_ext = ".a",
    stdlib_linkflags = [],
    target_triple = "aarch64-unknown-none",
)

toolchain(
    name = "aarch64-unknown-none_toolchain",
    exec_compatible_with = ["@platforms//os:linux"],
    target_settings = ["@gbl//toolchain:gbl_rust_elf_aarch64"],
    toolchain = ":aarch64-unknown-none",
    toolchain_type = "@rules_rust//rust:toolchain",
)

# rustfmt toolchain
rustfmt_toolchain(
    name = "rustfmt",
    rustfmt = "@rust_prebuilts//:bin/rustfmt",
)

toolchain(
    name = "rustfmt_toolchain",
    exec_compatible_with = ["@platforms//os:linux"],
    toolchain = ":rustfmt",
    toolchain_type = "@rules_rust//rust/rustfmt:toolchain_type",
)

# Rust bindgen toolchain

prebuilt_binary(
    name = "bindgen_prebuilt",
    bin = "@bindgen//:bindgen",
)

rust_bindgen_toolchain(
    name = "bindgen_toolchain_impl",
    bindgen = ":bindgen_prebuilt",
    clang = "@gbl_llvm_prebuilts//:clang-bin",
    libclang = "@gbl_llvm_prebuilts//:libclang",
    libstdcxx = "@gbl_llvm_prebuilts//:libc++",
)

toolchain(
    name = "bindgen_toolchain",
    toolchain = "bindgen_toolchain_impl",
    toolchain_type = "@rules_rust_bindgen//:toolchain_type",
)
