#pragma once

#include "base/map.h"
#include "base/mem.h"
#include "base/string.h"
#include "compiler/abi.h"

istruct (Ast);
istruct (Type);
istruct (AstFn);
istruct (Interns);
istruct (SemProgram);

#define VM_INPUT_REGISTER_COUNT 16

iunion (Value) {
    U64 u64;
    U32 u32;
    U16 u16;
    U8  u8;
    I64 i64;
    I32 i32;
    I16 i16;
    I8  i8;
    F64 f64;
    F32 f32;
    Ast *ast;
    Void *ptr;
    AstFn *fn;
    IString *str;
};

array_typedef(Value, Value);

istruct (Vm);

Vm   *vm_new              (Interns *, Mem *, SemProgram *, Abi *);
Value vm_run              (Vm *);
Void  vm_test             (String main_file_path);
Abi  *vm_abi_new          (Mem *, Sem *);

Value vm_value_add        (Type *, Value, Value);
Value vm_value_bitand     (Type *, Value, Value);
Value vm_value_bitcast    (Type *to, Type *from, Value);
Value vm_value_bitnot     (Type *, Value);
Value vm_value_bitor      (Type *, Value, Value);
Value vm_value_bitxor     (Type *, Value, Value);
Value vm_value_box        (Type *, U64);
Value vm_value_cast       (Type *to, Type *from, Value);
Value vm_value_div        (Type *, Value, Value);
Value vm_value_equal      (Type *, Value, Value);
Value vm_value_greater    (Type *, Value, Value);
Value vm_value_greater_eq (Type *, Value, Value);
Value vm_value_less       (Type *, Value, Value);
Value vm_value_less_eq    (Type *, Value, Value);
Void  vm_value_log        (AString *, Type *, Value);
Value vm_value_lshift     (Type *, Value, Value);
Bool  vm_value_match      (Type *, Value, Value);
Value vm_value_mod        (Type *, Value, Value);
Value vm_value_mul        (Type *, Value, Value);
Value vm_value_negate     (Type *, Value);
Value vm_value_not        (Type *, Value);
Value vm_value_not_eq     (Type *, Value, Value);
Value vm_value_rshift     (Type *, Value, Value);
Value vm_value_sub        (Type *, Value, Value);
I64   vm_value_to_i64     (Type *, Value);
U64   vm_value_to_u64     (Type *, Value);
