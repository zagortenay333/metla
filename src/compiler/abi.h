#pragma once

#include "base/mem.h"
#include "base/string.h"

istruct (Ast);
istruct (Abi);
istruct (Sem);
istruct (Type);
istruct (TypeFn);

#define ABI_REG_MEM UINT32_MAX // Means value is in memory.

typedef U32 AbiReg;

istruct (AbiObj) {
    U8 align; // In bytes.
    U32 size; // In bytes.
};

istruct (AbiFn) {
    Abi *abi;
    AbiReg output;
    Type *output_type;
    Array(AbiReg) inputs;
    Array(Type*) input_types;
};

istruct (Abi) {
    Sem *sem;

    U8 pointer_size;
    U8 register_size;
    U8 stack_frame_align;
    U8 stack_arg_min_size;
    U8 stack_arg_min_align;

    U32 any_id_offset;
    U32 any_value_offset;
    U32 any_value_size;
    U32 slice_data_offset;
    U32 slice_count_offset;

    U32    (*get_offset)    (Abi *, Ast *field);
    Bool   (*can_be_in_reg) (Abi *, Type *);
    AbiObj (*get_obj_abi)   (Abi *, Type *);
    AbiFn *(*get_fn_abi)    (Abi *, Mem *, TypeFn *);
};

#define abi_offset(abi, field)       (abi->get_offset(abi, field))
#define abi_can_be_in_reg(abi, type) (abi->can_be_in_reg(abi, type))
#define abi_of_obj(abi, type)        (abi->get_obj_abi(abi, type))
#define abi_of_fn(abi, mem, type)    (abi->get_fn_abi(abi, mem, type))
