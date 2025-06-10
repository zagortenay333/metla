#include "compiler/vm.h"
#include "compiler/sem.h"
#include "compiler/interns.h"
#include "compiler/sir.h"
#include "compiler/sir_reg.h"
#include "compiler/sir_frame.h"
#include "compiler/elf.h"

#define box(VAL) typematch((VAL),\
    Bool: (Value){ .u8  = (VAL) },\
    I8:   (Value){ .i8  = (VAL) },\
    I16:  (Value){ .i16 = (VAL) },\
    I32:  (Value){ .i32 = (VAL) },\
    I64:  (Value){ .i64 = (VAL) },\
    U8:   (Value){ .u8  = (VAL) },\
    U16:  (Value){ .u16 = (VAL) },\
    U32:  (Value){ .u32 = (VAL) },\
    U64:  (Value){ .u64 = (VAL) },\
    F32:  (Value){ .f32 = (VAL) },\
    F64:  (Value){ .f64 = (VAL) }\
)

#define op_box(F, V)          box(cast(Type(r.F), (V)))
#define op_cast(F, V, T)      box(cast(T, (V.F)))
#define op_bitcast(F, V, T)   box(*cast(T*, &(V.F)))
#define op_bitnot(F, V)       box(cast(Type(V.F), (~V.F)))
#define op_negate(F, V)       box(cast(Type(V.F), (-V.F)))
#define op_add(F, V1, V2)     box(cast(Type(V1.F), (V1.F + V2.F)))
#define op_bitand(F, V1, V2)  box(cast(Type(V1.F), (V1.F & V2.F)))
#define op_bitor(F, V1, V2)   box(cast(Type(V1.F), (V1.F | V2.F)))
#define op_bitxor(F, V1, V2)  box(cast(Type(V1.F), (V1.F ^ V2.F)))
#define op_div(F, V1, V2)     box(cast(Type(V1.F), (V1.F / V2.F)))
#define op_mod(F, V1, V2)     box(cast(Type(V1.F), (V1.F % V2.F)))
#define op_mul(F, V1, V2)     box(cast(Type(V1.F), (V1.F * V2.F)))
#define op_lshift(F, V1, V2)  box(cast(Type(V1.F), (V1.F << V2.F)))
#define op_rshift(F, V1, V2)  box(cast(Type(V1.F), (V1.F >> V2.F)))
#define op_sub(F, V1, V2)     box(cast(Type(V1.F), (V1.F - V2.F)))
#define op_equal(F, V1, V2)   box(cast(U8, (V1.F == V2.F)))
#define op_less(F, V1, V2)    box(cast(U8, (V1.F < V2.F)))
#define op_less_eq(F, V1, V2) box(cast(U8, (V1.F <= V2.F)))

#define f(OP, T, ...) ({\
    Value r;\
    assert_dbg(T->tag == TYPE_FLOAT);\
    U8 w = cast(TypeFloat*, T)->bitwidth;\
    if      (w == 32) r = OP(f32, __VA_ARGS__);\
    else if (w == 64) r = OP(f64, __VA_ARGS__);\
    else              badpath;\
    r;\
})

#define i(OP, T, ...) ({\
    def1(t, T);\
    if (t->tag == TYPE_ENUM) t = cast(TypeEnum*, t)->raw;\
    assert_dbg(t->tag == TYPE_INT);\
    Value r;\
    U8 w = cast(TypeInt*, t)->bitwidth;\
    U8 s = cast(TypeInt*, t)->is_signed;\
    if (s) {\
        if      (w == 8)  r = OP(i8, __VA_ARGS__);\
        else if (w == 16) r = OP(i16, __VA_ARGS__);\
        else if (w == 32) r = OP(i32, __VA_ARGS__);\
        else if (w == 64) r = OP(i64, __VA_ARGS__);\
        else              badpath;\
    } else {\
        if      (w == 8)  r = OP(u8, __VA_ARGS__);\
        else if (w == 16) r = OP(u16, __VA_ARGS__);\
        else if (w == 32) r = OP(u32, __VA_ARGS__);\
        else if (w == 64) r = OP(u64, __VA_ARGS__);\
        else              badpath;\
    }\
    r;\
})

#define fib(OP, T, ...) ({\
    Value r;\
    switch (T->tag) {\
    case TYPE_BOOL:  r = OP(u8, __VA_ARGS__); break;\
    case TYPE_FLOAT: r = f(OP, T, __VA_ARGS__); break;\
    case TYPE_ENUM:  r = i(OP, T, __VA_ARGS__); break;\
    default:         r = i(OP, T, __VA_ARGS__); break;\
    }\
    r;\
})

#define fi(OP, T, ...) ({\
    (T->tag == TYPE_INT) ? i(OP, T, __VA_ARGS__) : f(OP, T, __VA_ARGS__);\
})

Void vm_value_log (AString *astr, Type *t, Value v) {
    switch (t->tag) {
    case TYPE_ENUM:
        t = cast(TypeEnum*, t)->raw;
        through;
    case TYPE_INT: {
        U8 w = cast(TypeInt*, t)->bitwidth;
        U8 s = cast(TypeInt*, t)->is_signed;
        if (s) {
            if      (w == 8)  astr_push_fmt(astr, "%i", v.i8);
            else if (w == 16) astr_push_fmt(astr, "%i", v.i16);
            else if (w == 32) astr_push_fmt(astr, "%i", v.i32);
            else if (w == 64) astr_push_fmt(astr, "%li", v.i64);
            else badpath;
        } else {
            if      (w == 8)  astr_push_fmt(astr, "%u", v.u8);
            else if (w == 16) astr_push_fmt(astr, "%u", v.u16);
            else if (w == 32) astr_push_fmt(astr, "%u", v.u32);
            else if (w == 64) astr_push_fmt(astr, "%lu", v.u64);
            else badpath;
        }
    } break;
    case TYPE_FLOAT: {
        U8 w = cast(TypeFloat*, t)->bitwidth;
        if      (w == 32) astr_push_fmt(astr, "%.9f", v.f32);
        else if (w == 64) astr_push_fmt(astr, "%.17f", v.f64);
        else badpath;
    } break;
    case TYPE_BOOL:
        astr_push_cstr(astr, v.u8 ? "true" : "false");
        break;
    default: break;
    }
}

Value vm_value_cast (Type *to, Type *from, Value v) {
    switch (to->tag) {
    case TYPE_BOOL:
        return fib(op_cast, from, v, U8);
    case TYPE_INT: {
        U8 w = cast(TypeInt*, to)->bitwidth;
        U8 s = cast(TypeInt*, to)->is_signed;
        if (s) {
            if (w == 8)  return fib(op_cast, from, v, I8);
            if (w == 16) return fib(op_cast, from, v, I16);
            if (w == 32) return fib(op_cast, from, v, I32);
            if (w == 64) return fib(op_cast, from, v, I64);
        } else {
            if (w == 8)  return fib(op_cast, from, v, U8);
            if (w == 16) return fib(op_cast, from, v, U16);
            if (w == 32) return fib(op_cast, from, v, U32);
            if (w == 64) return fib(op_cast, from, v, U64);
        }
        badpath;
    }
    case TYPE_FLOAT: {
        U8 w = cast(TypeFloat*, to)->bitwidth;
        if (w == 32) return fib(op_cast, from, v, F32);
        if (w == 64) return fib(op_cast, from, v, F64);
        badpath;
    }
    default: badpath;
    }
}

Value vm_value_bitcast (Type *to, Type *from, Value v) {
    switch (to->tag) {
    case TYPE_BOOL:
        return fib(op_bitcast, from, v, U8);
    case TYPE_INT: {
        U8 w = cast(TypeInt*, to)->bitwidth;
        U8 s = cast(TypeInt*, to)->is_signed;
        if (s) {
            if (w == 8)  return fib(op_bitcast, from, v, I8);
            if (w == 16) return fib(op_bitcast, from, v, I16);
            if (w == 32) return fib(op_bitcast, from, v, I32);
            if (w == 64) return fib(op_bitcast, from, v, I64);
        } else {
            if (w == 8)  return fib(op_bitcast, from, v, U8);
            if (w == 16) return fib(op_bitcast, from, v, U16);
            if (w == 32) return fib(op_bitcast, from, v, U32);
            if (w == 64) return fib(op_bitcast, from, v, U64);
        }
        badpath;
    }
    case TYPE_FLOAT: {
        U8 w = cast(TypeFloat*, to)->bitwidth;
        if (w == 32) return fib(op_bitcast, from, v, F32);
        if (w == 64) return fib(op_bitcast, from, v, F64);
        badpath;
    }
    default: badpath;
    }
}

Value vm_value_add        (Type *t, Value v1, Value v2) { return fib(op_add, t, v1, v2); }
Value vm_value_bitand     (Type *t, Value v1, Value v2) { return i(op_bitand, t, v1, v2); }
Value vm_value_bitnot     (Type *t, Value v)            { return i(op_bitnot, t, v); }
Value vm_value_bitor      (Type *t, Value v1, Value v2) { return i(op_bitor, t, v1, v2); }
Value vm_value_bitxor     (Type *t, Value v1, Value v2) { return i(op_bitxor, t, v1, v2); }
Value vm_value_box        (Type *t, U64 v)              { return i(op_box, t, v); }
Value vm_value_div        (Type *t, Value v1, Value v2) { return fi(op_div, t,  v1, v2); }
Value vm_value_equal      (Type *t, Value v1, Value v2) { return (t->flags & TYPE_IS_PRIMITIVE) ? fib(op_equal, t, v1, v2) : (Value){}; }
Value vm_value_greater    (Type *t, Value v1, Value v2) { return vm_value_less(t, v2, v1); }
Value vm_value_greater_eq (Type *t, Value v1, Value v2) { return vm_value_less_eq(t, v2, v1);  }
Value vm_value_less       (Type *t, Value v1, Value v2) { return fib(op_less, t, v1, v2); }
Value vm_value_less_eq    (Type *t, Value v1, Value v2) { return fib(op_less_eq, t, v1, v2); }
Value vm_value_lshift     (Type *t, Value v1, Value v2) { return i(op_lshift, t, v1, v2); }
Bool  vm_value_match      (Type *t, Value v1, Value v2) { return vm_value_equal(t, v1, v2).u8; }
Value vm_value_mod        (Type *t, Value v1, Value v2) { return i(op_mod, t, v1, v2); }
Value vm_value_mul        (Type *t, Value v1, Value v2) { return fi(op_mul, t, v1, v2); }
Value vm_value_negate     (Type *t, Value v)            { return fi(op_negate, t, v); }
Value vm_value_not        (Type *t, Value v)            { assert_dbg(t->tag == TYPE_BOOL); v.u8 = !v.u8; return v; }
Value vm_value_not_eq     (Type *t, Value v1, Value v2) { Value v = vm_value_equal(t, v1, v2); v.u8 = !v.u8; return v; }
Value vm_value_rshift     (Type *t, Value v1, Value v2) { return i(op_rshift, t, v1, v2); }
Value vm_value_sub        (Type *t, Value v1, Value v2) { return fi(op_sub, t, v1, v2); }
I64   vm_value_to_i64     (Type *t, Value val)          { return fib(op_cast, t, val, I64).i64; }
U64   vm_value_to_u64     (Type *t, Value val)          { return fib(op_cast, t, val, U64).u64; }
