#pragma once

// =============================================================================
// Overview:
// ---------
//
// This module is responsible for semantic analysis.
// It attaches info onto AST nodes by either:
//
//     1. Setting one of the AST_SEM_FLAGS.
//     2. Setting Ast fields that start with 'sem_': sem_edge, sem_type, ...
//     3. Using the AstId as key into external data structures.
//
// Thus after copying a node, one can reset any semantic info
// by unsetting the AST_SEM_FLAGS, setting the sem_* fields to
// 0 and ensuring that the copy has a unique AstId.
// =============================================================================
#include "base/mem.h"
#include "base/map.h"
#include "base/array.h"
#include "base/string.h"
#include "compiler/vm.h"
#include "compiler/ast.h"
#include "compiler/abi.h"

istruct (Interns);

// X(TypeTag, typedef, TypeFlags)
#define EACH_TYPE(X)\
    X(TYPE_ARRAY, TypeArray, TYPE_IS_STRUCTURAL)\
    X(TYPE_BOOL, TypeBool, TYPE_IS_PRIMITIVE | TYPE_CAN_BE_IN_REG)\
    X(TYPE_ENUM, TypeEnum, TYPE_IS_PRIMITIVE | TYPE_CAN_BE_IN_REG)\
    X(TYPE_FLOAT, TypeFloat, TYPE_IS_STRUCTURAL | TYPE_IS_PRIMITIVE | TYPE_CAN_BE_IN_REG)\
    X(TYPE_FN, TypeFn, TYPE_IS_STRUCTURAL | TYPE_CAN_BE_IN_REG)\
    X(TYPE_INT, TypeInt, TYPE_IS_STRUCTURAL | TYPE_IS_PRIMITIVE | TYPE_CAN_BE_IN_REG)\
    X(TYPE_MISC, TypeMisc, TYPE_IS_SPECIAL)\
    X(TYPE_POINTER, TypePointer, TYPE_IS_STRUCTURAL | TYPE_CAN_BE_IN_REG)\
    X(TYPE_STRUCT, TypeStruct, 0)\
    X(TYPE_TUPLE, TypeTuple, TYPE_IS_STRUCTURAL)\
    X(TYPE_VAR, TypeVar, TYPE_IS_SPECIAL)\
    X(TYPE_VOID, TypeVoid, TYPE_IS_SPECIAL)

// X(name, is_signed, bits)
#define EACH_BUILTIN_INT_TYPE(X)\
    X(I8,  1, 8)\
    X(I16, 1, 16)\
    X(I32, 1, 32)\
    X(I64, 1, 64)\
    X(U8,  0, 8)\
    X(U16, 0, 16)\
    X(U32, 0, 32)\
    X(U64, 0, 64)

// X(name, tag)
#define EACH_BUILTIN_TYPE(X)\
    X(Bool, TYPE_BOOL)\
    X(F32,  TYPE_FLOAT)\
    X(F64,  TYPE_FLOAT)\
    X(I8,   TYPE_INT)\
    X(I16,  TYPE_INT)\
    X(I32,  TYPE_INT)\
    X(I64,  TYPE_INT)\
    X(U8,   TYPE_INT)\
    X(U16,  TYPE_INT)\
    X(U32,  TYPE_INT)\
    X(U64,  TYPE_INT)\
    X(Void, TYPE_VOID)

// X(lowercase, type)
#define EACH_SPECIAL_TYPE(X)\
    X(any, Any)\
    X(caller_info, CallerInfo)\
    X(slice, Slice)\
    X(string, String)\
    X(type_id, TypeId)

fenum (TypeFlags, U16) {
    TYPE_CAN_BE_IN_REG    = flag(0),
    TYPE_IS_CONST_POINTER = flag(1),
    TYPE_IS_DISTINCT      = flag(2),
    TYPE_IS_PRIMITIVE     = flag(3),
    TYPE_IS_SPECIAL       = flag(4),
    TYPE_IS_STRUCTURAL    = flag(5),
    TYPE_IS_TVAR_FN       = flag(6),
    TYPE_IS_UNTYPED_LIT   = flag(7),
    TYPE_VISITED          = flag(8),
};

ienum (TypeTag, U8) {
    #define X(TAG, ...) TAG,
        EACH_TYPE(X)
    #undef X
};

typedef U64 TypeId;
istruct (TypeSize) { U8 align; U64 size; };

istruct (Type)        { TypeTag tag; TypeFlags flags; TypeId id; };
istruct (TypeArray)   { Type type; U64 length; Ast *node; Type *element; };
istruct (TypeBool)    { Type type; };
istruct (TypeEnum)    { Type type; AstEnum *node; Type *raw; };
istruct (TypeFloat)   { Type type; U8 bitwidth; };
istruct (TypeFn)      { Type type; AstBaseFn *node; };
istruct (TypeInt)     { Type type; U8 bitwidth; Bool is_signed; };
istruct (TypeMisc)    { Type type; Ast *node; };
istruct (TypePointer) { Type type; Ast *node; Type *pointee; };
istruct (TypeStruct)  { Type type; AstStruct *node; };
istruct (TypeTuple)   { Type type; AstTuple *node; };
istruct (TypeVar)     { Type type; Ast *node; };
istruct (TypeVoid)    { Type type; };

array_typedef(Type*, Type);

istruct (CoreTypes) {
    Type *type_void_ptr;

    #define X(T, ...) Type *type_##T;
        EACH_SPECIAL_TYPE(X)
    #undef X

    #define X(T, ...) Type *type_##T;
        EACH_BUILTIN_TYPE(X)
    #undef X
};

istruct (Sem);

// Use this to iterate over the children of an AST node that
// contains generated code via if:ct, embed or similar. This
// way you don't have to write recursive code.
istruct (SemIterLevel) {
    U64 idx;
    ArrayAst *nodes;
};

istruct (SemIter) {
    Sem *sem;
    Ast *node; // Current node or 0 if done.
    U64 abs_idx; // Absolute index of the child.
    Array(SemIterLevel) stack;
};

istruct (SemProgram) {
    Sem *sem;
    AstFn *entry;
    ArrayAstFn *fns;
    ArrayType *types;
    ArrayAstVarDef *globals;
};

istruct (Scope) {
    Scope *parent;
    Map(IString*, Ast*) map;
    Array(U64) namegens; // Private.

    // If Scope.parent = 0, it's the autoimport scope which is
    // the parent of all file scopes. Entries in this scope are
    // auto inserted by the compiler and cannot be shadowed.
    //
    // If (owner->tag == AST_CODE_GEN), it's a scope that contains
    // generated code. The Scope.map is empty with all it's entries
    // instead added to the nearest enclosing non-codegen scope. If
    // this node has the AST_ENDS_WITH_BLOCK flag, it means that the
    // generated code is not inside the special codegen file.
    Ast *owner;
};

#define sem_get_type(SEM, NODE) ((NODE)->sem_type)

Sem          *sem_new                (Interns *, Mem *);
SemProgram    sem_check              (Sem *, String, Abi *);
Value         sem_get_const          (Sem *, Ast *);
SemIter      *sem_iter_new           (Mem *, Sem *, ArrayAst *);
Bool          sem_iter_next          (SemIter *);
Bool          sem_type_has_pointers  (Sem *, Type *);
Type         *sem_alloc_type_pointer (Sem *, Mem *, Type *pointee);
CoreTypes    *sem_get_core_types     (Sem *);
AstAttribute *sem_get_attribute      (Sem *, Ast *, IString *);
SliceAst      sem_get_arg_instances  (Sem *, Ast *);
Void          sem_print_node         (Sem *, AString *, Ast *);
Void          sem_print_node_out     (Sem *, Ast *);
TypeSize      sem_get_type_size      (Sem *, Type *);
