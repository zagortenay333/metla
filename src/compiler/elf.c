#if 1
#include "compiler/elf.h"
#include "os/fs.h"

#define NUMBER_OF_PROGRAM_HEADERS  2
#define NUMBER_OF_SECTION_HEADERS  4

#define SIZEOF_HEADER         64
#define SIZEOF_PROGRAM_HEADER 56
#define SIZEOF_SECTION_HEADER 64

#define VIRT_START_ADDRESS 0x400000
#define PAGE_SIZE          0x200000
#define SECTION_ALIGNMENT  16

#define SHF_WRITE     0x1
#define SHF_ALLOC     0x2
#define SHF_EXECINSTR 0x4

#define SHT_NULL     0 // Section header table entry unused
#define SHT_PROGBITS 1 // Program data
#define SHT_SYMTAB   2 // Symbol table
#define SHT_STRTAB   3 // String table
#define SHT_RELA     4 // Relocation entries with addends
#define SHT_HASH     5 // Symbol hash table
#define SHT_DYNAMIC  6 // Dynamic linking information
#define SHT_NOTE     7 // Notes
#define SHT_NOBITS   8 // Program space with no data (bss)
#define SHT_REL      9 // Relocation entries, no addends

Elf elf_new (Mem *mem) {
    Elf elf = {};

    elf.mem = mem;
    array_init(&elf.symbols, mem);
    array_init(&elf.relocations, mem);

    elf.text_segment.p_type  = 1; // PT_LOAD
    elf.text_segment.p_flags = 0x1|0x4; // read-exec
    elf.text_segment.p_align = PAGE_SIZE;

    elf.data_segment.p_type  = 1; // PT_LOAD
    elf.data_segment.p_flags = 0x2|0x4; // read-write
    elf.data_segment.p_align = PAGE_SIZE;

    Auto section_names = astr_new(mem);

    astr_push_cstr_nul(&section_names, ""); // Name of undef section.

    elf.text_section.sh_name          = section_names.count;
    astr_push_cstr_nul(&section_names, ".text");
    elf.text_section.sh_type          = SHT_PROGBITS;
    elf.text_section.sh_flags         = SHF_ALLOC | SHF_EXECINSTR;
    elf.text_section.sh_addralign     = SECTION_ALIGNMENT;
    elf.text_section.astr             = astr_new(mem);

    elf.data_section.sh_name          = section_names.count;
    astr_push_cstr_nul(&section_names, ".data");
    elf.data_section.sh_type          = SHT_PROGBITS;
    elf.data_section.sh_flags         = SHF_ALLOC | SHF_WRITE;
    elf.data_section.sh_addralign     = SECTION_ALIGNMENT;
    elf.data_section.astr             = astr_new(mem);

    elf.shstrtab_section.sh_name      = section_names.count;
    astr_push_cstr_nul(&section_names, ".shstrtab");
    elf.shstrtab_section.sh_type      = SHT_STRTAB;
    elf.shstrtab_section.sh_addralign = SECTION_ALIGNMENT;
    elf.shstrtab_section.astr         = section_names;

    return elf;
}

Void elf_add_symbol (Elf *elf, Void *id, ElfSection *section, U32 section_offset) {
    array_push(&elf->symbols, ((ElfSymbol) {
        .id             = id,
        .section        = section,
        .section_offset = section_offset,
    }));
}

Void elf_add_reloc (Elf *elf, Bool is_relative, Void *id, ElfSection *section, U32 section_offset, U32 size, U32 address_offset) {
    array_push(&elf->relocations, ((ElfRelocation) {
        .is_relative    = is_relative,
        .id             = id,
        .section        = section,
        .section_offset = section_offset,
        .size           = size,
        .address_offset = address_offset,
    }));
}

static Void patch_exe (Elf *elf, String exe) {
    array_iter (reloc, &elf->relocations, *) {
        array_iter (symbol, &elf->symbols, *) {
            if (symbol->id != reloc->id) continue;

            if (reloc->is_relative) {
                I32 off1 = (I32)(reloc->section->sh_addr + reloc->section_offset);
                I32 off2 = (I32)(symbol->section->sh_addr + symbol->section_offset);
                I32 val  = off2 - off1 + (I32)reloc->address_offset;
                U8 *ptr  = (U8*)&exe.data[reloc->section->sh_offset + reloc->section_offset - 4];
                ptr[0]   = (U8)(val >> 0);
                ptr[1]   = (U8)(val >> 8);
                ptr[2]   = (U8)(val >> 16);
                ptr[3]   = (U8)(val >> 24);
            } else {
                U64 val = (U64)(symbol->section->sh_addr + symbol->section_offset + reloc->address_offset);
                U8 *ptr = (U8*)&exe.data[reloc->section->sh_offset + reloc->section_offset - 8];
                ptr[0]  = (U8)(val >> 0);
                ptr[1]  = (U8)(val >> 8);
                ptr[2]  = (U8)(val >> 16);
                ptr[3]  = (U8)(val >> 24);
                ptr[4]  = (U8)(val >> 32);
                ptr[5]  = (U8)(val >> 40);
                ptr[6]  = (U8)(val >> 48);
                ptr[7]  = (U8)(val >> 56);


            }

            break;
        }
    }
}

static Void serialize_header (AString *astr, ElfHeader *header) {
    astr_push_str(astr, (String){ .data=(Char*)header->e_ident, .count=16 });
    astr_push_u16(astr, header->e_type);
    astr_push_u16(astr, header->e_machine);
    astr_push_u32(astr, header->e_version);
    astr_push_u64(astr, header->e_entry);
    astr_push_u64(astr, header->e_phoff);
    astr_push_u64(astr, header->e_shoff);
    astr_push_u32(astr, header->e_flags);
    astr_push_u16(astr, header->e_ehsize);
    astr_push_u16(astr, header->e_phentsize);
    astr_push_u16(astr, header->e_phnum);
    astr_push_u16(astr, header->e_shentsize);
    astr_push_u16(astr, header->e_shnum);
    astr_push_u16(astr, header->e_shstrndx);
}

static Void serialize_program_header (AString *astr, ElfSegment *segment) {
    astr_push_u32(astr, segment->p_type);
    astr_push_u32(astr, segment->p_flags);
    astr_push_u64(astr, segment->p_offset);
    astr_push_u64(astr, segment->p_vaddr);
    astr_push_u64(astr, segment->p_paddr);
    astr_push_u64(astr, segment->p_filesz);
    astr_push_u64(astr, segment->p_memsz);
    astr_push_u64(astr, segment->p_align);
}

static Void serialize_section_header (AString *astr, ElfSection *section) {
    astr_push_u32(astr, section->sh_name);
    astr_push_u32(astr, section->sh_type);
    astr_push_u64(astr, section->sh_flags);
    astr_push_u64(astr, section->sh_addr);
    astr_push_u64(astr, section->sh_offset);
    astr_push_u64(astr, section->sh_size);
    astr_push_u32(astr, section->sh_link);
    astr_push_u32(astr, section->sh_info);
    astr_push_u64(astr, section->sh_addralign);
    astr_push_u64(astr, section->sh_entsize);
}

#define advance_pos(elf, n) ((elf)->file_pos += (n), (elf)->virt_pos += (n))

static Void compute_section_size (Elf *elf, ElfSection *section) {
    section->start_padding = padding_to_align(elf->file_pos, SECTION_ALIGNMENT);
    advance_pos(elf, section->start_padding);

    section->sh_addr   = (section->sh_flags & SHF_ALLOC) ? elf->virt_pos : 0;
    section->sh_offset = elf->file_pos;
    section->sh_size   = section->astr.count;

    advance_pos(elf, section->sh_size);
}

Void elf_emit_exe (Elf *elf, String exe_file_path) {
    elf->file_pos = 0;
    elf->virt_pos = VIRT_START_ADDRESS;

    { // Compute size of text segment and it's sections:
        elf->text_segment.p_vaddr  = elf->virt_pos;
        elf->text_segment.p_paddr  = elf->virt_pos;
        elf->text_segment.p_offset = elf->file_pos;

        advance_pos(elf, SIZEOF_HEADER + NUMBER_OF_PROGRAM_HEADERS*SIZEOF_PROGRAM_HEADER);

        compute_section_size(elf, &elf->text_section);

        elf->text_segment.p_filesz = elf->file_pos;
        elf->text_segment.p_memsz  = elf->file_pos;
    }

    { // Compute size of data segment and it's sections:
        elf->virt_pos += padding_to_align(elf->virt_pos, PAGE_SIZE);
        elf->virt_pos += elf->file_pos;

        elf->data_segment.p_vaddr  = elf->virt_pos;
        elf->data_segment.p_paddr  = elf->virt_pos;
        elf->data_segment.p_offset = elf->file_pos;

        compute_section_size(elf, &elf->data_section);

        elf->data_segment.p_filesz = elf->virt_pos - elf->data_segment.p_vaddr;
        elf->data_segment.p_memsz  = elf->data_segment.p_filesz;
    }

    compute_section_size(elf, &elf->shstrtab_section);

    { // Emit executable:
        Auto astr = astr_new(elf->mem);

        serialize_header(&astr, &(ElfHeader) {
            .e_ident = {
                0x7f, // [EI_MAG0]
                'E',  // [EI_MAG1]
                'L',  // [EI_MAG2]
                'F',  // [EI_MAG3]
                2,    // [EI_CLASS] = ELFCLASS64
                1,    // [EI_DATA] = ELFDATA2LSB
                1,    // [EI_VERSION] = EV_CURRENT
                0,    // [EI_OSABI] = ELFOSABI_NONE (same as ELFOSABI_SYSV)
                0,    // [EI_ABIVERSION]
                0,    // padding
                0,    // padding
                0,    // padding
                0,    // padding
                0,    // padding
                0,    // padding
                0,    // padding
            },
            .e_type      = 2, // ET_EXEC (executable file)
            .e_machine   = 0x3e, // EM_X86_64 (AMD x86_64)
            .e_version   = 1, // EV_CURRENT
            .e_entry     = elf->text_section.sh_addr,
            .e_phoff     = SIZEOF_HEADER,
            .e_shoff     = elf->file_pos,
            .e_flags     = 0,
            .e_ehsize    = SIZEOF_HEADER,
            .e_phentsize = SIZEOF_PROGRAM_HEADER,
            .e_phnum     = NUMBER_OF_PROGRAM_HEADERS,
            .e_shentsize = SIZEOF_SECTION_HEADER,
            .e_shnum     = NUMBER_OF_SECTION_HEADERS,
            .e_shstrndx  = NUMBER_OF_SECTION_HEADERS - 1,
        });

        serialize_program_header(&astr, &elf->text_segment);
        serialize_program_header(&astr, &elf->data_segment);

        astr_push_bytes(&astr, 0, elf->text_section.start_padding);
        astr_push_str(&astr, astr_to_str(&elf->text_section.astr));

        astr_push_bytes(&astr, 0, elf->data_section.start_padding);
        astr_push_str(&astr, astr_to_str(&elf->data_section.astr));

        astr_push_bytes(&astr, 0, elf->shstrtab_section.start_padding);
        astr_push_str(&astr, astr_to_str(&elf->shstrtab_section.astr));

        serialize_section_header(&astr, &elf->undef_section);
        serialize_section_header(&astr, &elf->text_section);
        serialize_section_header(&astr, &elf->data_section);
        serialize_section_header(&astr, &elf->shstrtab_section);

        Auto exe = astr_to_str(&astr);
        patch_exe(elf, exe);
        fs_write_entire_file(exe_file_path, exe);
        fs_make_file_executable(exe_file_path);
    }
}
#endif
