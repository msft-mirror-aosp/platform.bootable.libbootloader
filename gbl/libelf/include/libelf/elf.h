/*
 * Copyright (C) 2026 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef __ELF_H__
#define __ELF_H__

// ELF definitions based on standard
// https://gabi.xinuos.com/elf/

// 1.2. Data Representation

// Table 1.2 64-Bit Data Types
typedef uint64_t Elf64_Addr;
typedef uint64_t Elf64_Off;
typedef uint16_t Elf64_Half;
typedef uint32_t Elf64_Word;
typedef int32_t Elf64_Sword;
typedef uint64_t Elf64_Xword;
typedef int64_t Elf64_Sxword;

// Listing 2.1 ELF Header
#define EI_NIDENT 16
typedef struct {
  unsigned char e_ident[EI_NIDENT];
  Elf64_Half e_type;
  Elf64_Half e_machine;
  Elf64_Word e_version;
  Elf64_Addr e_entry;
  Elf64_Off e_phoff;
  Elf64_Off e_shoff;
  Elf64_Word e_flags;
  Elf64_Half e_ehsize;
  Elf64_Half e_phentsize;
  Elf64_Half e_phnum;
  Elf64_Half e_shentsize;
  Elf64_Half e_shnum;
  Elf64_Half e_shstrndx;
} Elf64_Ehdr;

// 5. Symbol Table Entry
typedef struct {
  Elf64_Word st_name;
  unsigned char st_info;
  unsigned char st_other;
  Elf64_Half st_shndx;
  Elf64_Addr st_value;
  Elf64_Xword st_size;
} Elf64_Sym;

// 6.1. Relocation Entry

// Listing 6.1 Relocation Entries
typedef struct {
  Elf64_Addr r_offset;
  Elf64_Xword r_info;
} Elf64_Rel;

typedef struct {
  Elf64_Addr r_offset;
  Elf64_Xword r_info;
  Elf64_Sxword r_addend;
} Elf64_Rela;

// 7.1. Program Header Entry
// Listing 7.1 Program Header
typedef struct {
  Elf64_Word p_type;
  Elf64_Word p_flags;
  Elf64_Off p_offset;
  Elf64_Addr p_vaddr;
  Elf64_Addr p_paddr;
  Elf64_Xword p_filesz;
  Elf64_Xword p_memsz;
  Elf64_Xword p_align;
} Elf64_Phdr;

// 7.2 Segment Types, p_type
#define PT_NULL 0
#define PT_LOAD 1
#define PT_DYNAMIC 2
#define PT_INTERP 3
#define PT_NOTE 4
#define PT_SHLIB 5
#define PT_PHDR 6
#define PT_TLS 7
#define PT_LOOS 0x60000000
#define PT_HIOS 0x6fffffff
#define PT_LOPROC 0x70000000
#define PT_HIPROC 0x7fffffff

// 8 Dynamic Linking

// 8.3 Dynamic Section

// Listing 8.1 Dynamic Structure
typedef struct {
  Elf64_Sxword d_tag;
  union {
    Elf64_Xword d_val;
    Elf64_Addr d_ptr;
  } d_un;
} Elf64_Dyn;

// Table 8.1 Dynamic Array Tags, d_tag
#define DT_NULL 0              // ignored
#define DT_NEEDED 1            // d_val
#define DT_PLTRELSZ 2          // d_val
#define DT_PLTGOT 3            // d_ptr
#define DT_HASH 4              // d_ptr
#define DT_STRTAB 5            // d_ptr
#define DT_SYMTAB 6            // d_ptr
#define DT_RELA 7              // d_ptr
#define DT_RELASZ 8            // d_val
#define DT_RELAENT 9           // d_val
#define DT_STRSZ 10            // d_val
#define DT_SYMENT 11           // d_val
#define DT_INIT 12             // d_ptr
#define DT_FINI 13             // d_ptr
#define DT_SONAME 14           // d_val
#define DT_RPATH 15            // d_val
#define DT_SYMBOLIC 16         // ignored
#define DT_REL 17              // d_ptr
#define DT_RELSZ 18            // d_val
#define DT_RELENT 19           // d_val
#define DT_PLTREL 20           // d_val
#define DT_DEBUG 21            // d_ptr
#define DT_TEXTREL 22          // ignored
#define DT_JMPREL 23           // d_ptr
#define DT_BIND_NOW 24         // ignored
#define DT_INIT_ARRAY 25       // d_ptr
#define DT_FINI_ARRAY 26       // d_ptr
#define DT_INIT_ARRAYSZ 27     // d_val
#define DT_FINI_ARRAYSZ 28     // d_val
#define DT_RUNPATH 29          // d_val
#define DT_FLAGS 30            // d_val
#define DT_ENCODING 32         // unspecified
#define DT_PREINIT_ARRAY 32    // d_ptr
#define DT_PREINIT_ARRAYSZ 33  // d_val
#define DT_SYMTAB_SHNDX 34     // d_ptr
#define DT_RELRSZ 35           // d_val
#define DT_RELR 36             // d_ptr
#define DT_RELRENT 37          // d_val
#define DT_SYMTABSZ 39         // d_val
#define DT_LOOS 0x6000000D     // unspecified
#define DT_HIOS 0x6ffff000     // unspecified
#define DT_LOPROC 0x70000000   // unspecified
#define DT_HIPROC 0x7fffffff   // unspecified

// RISCV specific definitions
// From https://lists.riscv.org/g/tech-psabi/attachment/61/0/riscv-abi.pdf

// This is part of enum from Table 9. Relocation types.
#define R_RISCV_RELATIVE 3
#define R_X86_64_RELATIVE 8
#define R_AARCH64_RELATIVE 1027

#endif  // __ELF_H__
