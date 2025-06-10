#pragma once

// =============================================================================
// Overview:
// ---------
//
// This module is very primitive right now. It can only emit an executable
// file. It cannot emit shared or relocatable objects. It also cannot emit
// position independent executables (PIE) since those on linux are just
// shared objects.
//
// Since we already use RIP-relative addressing, all we need to do to fully
// support PIE's is to have support for shared objects. For that we have to
// add support for stuff like relocatable objects, GOT and PLT structures...
//
// We need to ensure the generated elf file adheres to the small position
// independent code model. So all adressing is RIP-relative (already done),
// and the maximum distance between a symbol and the end of an instruction
// is limited to (2^31 − 2^24 − 1) or 0x7effffff (not done). More info in
// the System V ABI spec.
//
// Note that we will have to mangle the names of nested functions when
// outputing actual elf computed symbols.
// =============================================================================
#include "base/mem.h"
#include "base/array.h"
#include "base/string.h"

istruct (ElfHeader) {
    U8  e_ident[16];
    U16 e_type;
    U16 e_machine;
    U32 e_version;
    U64 e_entry;
    U64 e_phoff;
    U64 e_shoff;
    U32 e_flags;
    U16 e_ehsize;
    U16 e_phentsize;
    U16 e_phnum;
    U16 e_shentsize;
    U16 e_shnum;
    U16 e_shstrndx;
};

istruct (ElfSection) {
    U32 sh_name;
    U32 sh_type;
    U64 sh_flags;
    U64 sh_addr;
    U64 sh_offset;
    U64 sh_size;
    U32 sh_link;
    U32 sh_info;
    U64 sh_addralign;
    U64 sh_entsize;

    AString astr;
    U32 start_padding;
};

istruct (ElfSegment) {
    U32 p_type;
    U32 p_flags;
    U64 p_offset;
    U64 p_vaddr;
    U64 p_paddr;
    U64 p_filesz;
    U64 p_memsz;
    U64 p_align;
};

istruct (ElfSymbol) {
    Void *id;
    ElfSection *section;
    U32 section_offset;
};

istruct (ElfRelocation) {
    Bool is_relative;
    Void *id;
    ElfSection *section;
    U32 section_offset;
    U32 size;
    U32 address_offset;
};

istruct (Elf) {
    Mem *mem;

    U64 file_pos;
    U64 virt_pos;

    Array(ElfSymbol) symbols;
    Array(ElfRelocation) relocations;

    ElfSegment text_segment;
    ElfSegment data_segment;

    ElfSection undef_section;
    ElfSection text_section;
    ElfSection data_section;
    ElfSection shstrtab_section;
};

Elf  elf_new        (Mem *);
Void elf_emit_exe   (Elf *, String exe_file_path);
Void elf_add_symbol (Elf *, Void *tag, ElfSection *, U32 offset);
Void elf_add_reloc  (Elf *, Bool is_relative, Void *tag, ElfSection *, U32 section_offset, U32 size, U32 address_offset);
