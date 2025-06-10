#pragma once

#include "base/mem.h"
#include "base/log.h"
#include "base/core.h"
#include "base/string.h"

istruct (Type);
istruct (Scope);
istruct (Interns);

// X(AstBaseTag, type)
//
// These types do not represent AST nodes but rather common
// initial sequences among them. Note that you cannot have
// more than 64 different bases since we must be able to
// express them as flags that can be bitwise ored to indicate
// that a node has multiple bases. See AstBaseTag definition.
#define EACH_AST_BASE(X)\
    X(AST, Ast)\
    X(AST_BASE_FN, AstBaseFn)\
    X(AST_BASE_UNARY, AstBaseUnary)\
    X(AST_BASE_BINARY, AstBaseBinary)

// X(AstTag, type, bases, flags)
#define EACH_AST_NODE(X)\
    X(AST_ADD, AstAdd, AST_BASE_BINARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_ADDRESS_OF, AstAddressOf, AST_BASE_UNARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_ALIGNOF, AstAlignof, AST_BASE_UNARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_ARG_POLY_CODE, AstArgPolyCode, 0, 0)\
    X(AST_ARG_POLY_TYPE, AstArgPolyType, 0, AST_IS_TYPE | AST_HAS_POLY_ARGS)\
    X(AST_ARG_POLY_VALUE, AstArgPolyValue, 0, AST_HAS_POLY_ARGS)\
    X(AST_ARRAY_LITERAL, AstArrayLiteral, 0, AST_CREATES_TYPE | AST_CAN_EVAL_WITHOUT_VM | AST_IS_LITERAL)\
    X(AST_ARRAY_TYPE, AstArrayType, 0, AST_IS_TYPE | AST_CAN_EVAL_WITHOUT_VM | AST_CREATES_TYPE)\
    X(AST_ASSIGN, AstAssign, AST_BASE_BINARY, 0)\
    X(AST_ATTRIBUTE, AstAttribute, 0, 0)\
    X(AST_BITWISE_AND, AstBitwiseAnd, AST_BASE_BINARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_BITWISE_NOT, AstBitwiseNot, AST_BASE_UNARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_BITWISE_OR, AstBitwiseOr, AST_BASE_BINARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_BITWISE_XOR, AstBitwiseXor, AST_BASE_BINARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_BLOCK, AstBlock, 0, AST_CREATES_SCOPE)\
    X(AST_BOOL_LITERAL, AstBoolLiteral, 0, AST_IS_LITERAL | AST_CAN_EVAL_WITHOUT_VM | AST_EVALED)\
    X(AST_BREAK, AstBreak, 0, 0)\
    X(AST_CALL, AstCall, 0, 0)\
    X(AST_CALLER_INFO, AstCallerInfo, 0, AST_EVALED)\
    X(AST_CALL_DEFAULT_ARG, AstCallDefaultArg, 0, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_CALL_MACRO, AstCallMacro, 0, 0)\
    X(AST_CALL_MACRO_ARG, AstCallMacroArg, 0, AST_EVALED | AST_IS_LITERAL | AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_CALL_MACRO_BARG, AstCallMacroBArg, 0, 0)\
    X(AST_CALL_NAMED_ARG, AstCallNamedArg, 0, 0)\
    X(AST_CAST, AstCast, 0, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_CODE_GEN, AstCodeGen, 0, AST_CREATES_SCOPE | AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_CONTINUE, AstContinue, 0, 0)\
    X(AST_CT_ASSERT, AstCtAssert, AST_BASE_UNARY, 0)\
    X(AST_DEFER, AstDefer, 0, 0)\
    X(AST_DEREF, AstDeref, AST_BASE_UNARY, AST_IS_LVALUE | AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_DIV, AstDiv, AST_BASE_BINARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_DOT, AstDot, 0, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_DUMMY, AstDummy, 0, 0)\
    X(AST_EMBED, AstEmbed, 0, AST_IS_BINDGEN | AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_ENUM, AstEnum, 0, AST_IS_TYPE | AST_CAN_EVAL_WITHOUT_VM | AST_CREATES_TYPE | AST_CREATES_SCOPE)\
    X(AST_ENUM_FIELD, AstEnumField, 0, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_ENUM_LITERAL, AstEnumLiteral, 0, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_EQUAL, AstEqual, AST_BASE_BINARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_EVAL, AstEval, 0, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_F64_LITERAL, AstF64Literal, 0, AST_IS_LITERAL | AST_CAN_EVAL_WITHOUT_VM | AST_EVALED)\
    X(AST_FILE, AstFile, 0, AST_CREATES_SCOPE)\
    X(AST_FN, AstFn, AST_BASE_FN, AST_IS_READ_ONLY | AST_CREATES_TYPE | AST_CREATES_SCOPE | AST_IS_LITERAL | AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_FN_LINUX, AstFnLinux, AST_BASE_FN, AST_IS_READ_ONLY | AST_CREATES_TYPE | AST_CREATES_SCOPE)\
    X(AST_FN_POLY, AstFnPoly, AST_BASE_FN, AST_IS_READ_ONLY | AST_CREATES_SCOPE | AST_IS_POLYMORPH | AST_CAN_EVAL)\
    X(AST_FN_TYPE, AstFnType, AST_BASE_FN, AST_IS_READ_ONLY | AST_IS_TYPE | AST_CREATES_TYPE)\
    X(AST_GREATER, AstGreater, AST_BASE_BINARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_GREATER_EQUAL, AstGreaterEqual, AST_BASE_BINARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_I64_LITERAL, AstI64Literal, 0, AST_IS_LITERAL | AST_CAN_EVAL_WITHOUT_VM | AST_EVALED)\
    X(AST_IDENT, AstIdent, 0, AST_IS_LVALUE | AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_IF, AstIf, 0, 0)\
    X(AST_IF_CT, AstIfCt, 0, AST_IS_BINDGEN)\
    X(AST_IMPORT, AstImport, 0, AST_CAN_EVAL_WITHOUT_VM | AST_IS_BINDGEN)\
    X(AST_IMPORT_CONFIG, AstImportConfig, 0, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_INDEX, AstIndex, 0, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_INTERFACE, AstInterface, 0, 0)\
    X(AST_LESS, AstLess, AST_BASE_BINARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_LESS_EQUAL, AstLessEqual, AST_BASE_BINARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_LOGICAL_AND, AstLogicalAnd, AST_BASE_BINARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_LOGICAL_OR, AstLogicalOr, AST_BASE_BINARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_MOD, AstMod, AST_BASE_BINARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_MUL, AstMul, AST_BASE_BINARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_NEGATE, AstNegate, AST_BASE_UNARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_NIL, AstNil, 0, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_NOT, AstNot, AST_BASE_UNARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_NOT_EQUAL, AstNotEqual, AST_BASE_BINARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_PAIR, AstPair, AST_BASE_BINARY, 0)\
    X(AST_RAW, AstRaw, AST_BASE_UNARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_RETURN, AstReturn, 0, 0)\
    X(AST_SCOPE_MOD, AstScopeMod, 0, 0)\
    X(AST_SELF, AstSelf, 0, 0)\
    X(AST_SHIFT_LEFT, AstShiftLeft, AST_BASE_BINARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_SHIFT_RIGHT, AstShiftRight, AST_BASE_BINARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_SIZEOF, AstSizeof, AST_BASE_UNARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_STRING_LITERAL, AstStringLiteral, 0, AST_IS_LITERAL | AST_EVALED | AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_STRUCT, AstStruct, 0, AST_IS_TYPE | AST_CAN_EVAL_WITHOUT_VM | AST_CREATES_TYPE | AST_CREATES_SCOPE)\
    X(AST_STRUCT_LITERAL, AstStructLiteral, 0, AST_CAN_EVAL_WITHOUT_VM | AST_IS_LITERAL)\
    X(AST_STRUCT_LIT_INIT, AstStructLitInit, 0, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_STRUCT_POLY, AstStructPoly, 0, AST_CREATES_SCOPE | AST_IS_POLYMORPH | AST_CAN_EVAL)\
    X(AST_SUB, AstSub, AST_BASE_BINARY, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_TUPLE, AstTuple, 0, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_TUPLE_FIELD, AstTupleField, 0, AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_TYPEOF, AstTypeof, AST_BASE_UNARY, AST_IS_TYPE)\
    X(AST_TYPE_ALIAS, AstTypeAlias, 0, AST_IS_TYPE | AST_CAN_EVAL | AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_TYPE_CONSTRAINT, AstTypeConstraint, 0, 0)\
    X(AST_TYPE_DISTINCT, AstTypeDistinct, 0, AST_IS_TYPE | AST_CAN_EVAL | AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_TYPE_ID, AstTypeId, 0, 0)\
    X(AST_U64_LITERAL, AstU64Literal, 0, AST_IS_LITERAL | AST_CAN_EVAL_WITHOUT_VM | AST_EVALED)\
    X(AST_VAR_DEF, AstVarDef, 0, AST_IS_LVALUE | AST_CAN_EVAL_WITHOUT_VM)\
    X(AST_WHILE, AstWhile, 0, AST_CREATES_SCOPE)

// X(AstTag, type)
//
// These are nodes that are known to introduce names
// to scopes before any code generators have run.
// They must have an "IString *name" field.
#define EACH_STATIC_NAME_GENERATOR(X)\
    X(AST_ENUM, AstEnum)\
    X(AST_ENUM_FIELD, AstEnumField)\
    X(AST_FN, AstFn)\
    X(AST_FN_LINUX, AstFnLinux)\
    X(AST_FN_POLY, AstFnPoly)\
    X(AST_STRUCT, AstStruct)\
    X(AST_STRUCT_POLY, AstStructPoly)\
    X(AST_VAR_DEF, AstVarDef)\
    X(AST_ARG_POLY_CODE, AstArgPolyCode)\
    X(AST_ARG_POLY_TYPE, AstArgPolyType)\
    X(AST_ARG_POLY_VALUE, AstArgPolyValue)\
    X(AST_TUPLE_FIELD, AstTupleField)\
    X(AST_TYPE_ALIAS, AstTypeAlias)\
    X(AST_TYPE_CONSTRAINT, AstTypeConstraint)\
    X(AST_TYPE_DISTINCT, AstTypeDistinct)

// X(AstTag, type, description)
//
// Selectors are nodes that have a connection to another node
// established during semantic analysis rather than parsing.
// For example, identifiers are connected to the definitions
// they refer to. Each of these will have a "sem_edge" field.
#define EACH_AST_SELECTOR(X)\
    X(AST_BREAK, AstBreak, "Target is always an AstWhile.")\
    X(AST_CALL, AstCall, "If it is a direct call, target is the called fn.")\
    X(AST_CALL_MACRO, AstCallMacro, "Target is always the macro instance.")\
    X(AST_CONTINUE, AstContinue, "Target is always an AstWhile.")\
    X(AST_DEFER, AstDefer, "Target is always the corresponding Scope.owner.")\
    X(AST_DOT, AstDot, "Always has a target.")\
    X(AST_EMBED, AstEmbed, "Target is always an AstCodeGen.")\
    X(AST_ENUM_LITERAL, AstEnumLiteral, "Target is an AstEnumField.")\
    X(AST_FN_POLY, AstFnPoly, "The target is the fn instance if the poly fn was assigned like a value.")\
    X(AST_IDENT, AstIdent, "Always has a target.")\
    X(AST_INDEX, AstIndex, "If indexing into a tuple, target is the tuple field.")\
    X(AST_IMPORT_CONFIG, AstImportConfig, "Has target if AstImportConfig.init == 0.")\
    X(AST_RETURN, AstReturn, "Target is always a function or macro.")\
    X(AST_SELF, AstSelf, "Target is always the nearest enclosing function.")\
    X(AST_STRUCT_LIT_INIT, AstStructLitInit, "Target is always a struct field Ast.")

typedef U64 AstId; // 0 means no id.

fenum (AstFlags, U64) {
    AST_ADDED_TO_CHECK_LIST     = flag(0),
    AST_ADDRESS_TAKEN           = flag(1),
    AST_BACKTICKED              = flag(2),
    AST_CAN_EVAL                = flag(3),
    AST_CAN_EVAL_WITHOUT_VM     = flag(4),
    AST_CHECKED                 = flag(5),
    AST_CREATES_SCOPE           = flag(6),
    AST_CREATES_TYPE            = flag(7),
    AST_ENDS_WITH_BLOCK         = flag(8),
    AST_EVALED                  = flag(9),
    AST_HAS_POLY_ARGS           = flag(10),
    AST_IN_POLY_ARG_POSITION    = flag(11),
    AST_IN_STANDALONE_POSITION  = flag(12),
    AST_IS_BINDGEN              = flag(13),
    AST_IS_FN_ARG               = flag(14),
    AST_IS_FN_ARG_PASSED_BY_MEM = flag(15),
    AST_IS_GLOBAL               = flag(16),
    AST_IS_LITERAL              = flag(17),
    AST_IS_LVALUE               = flag(18),
    AST_IS_MACRO                = flag(19),
    AST_IS_MACRO_INSTANCE       = flag(20),
    AST_IS_POLYMORPH            = flag(21),
    AST_IS_POLYMORPH_INSTANCE   = flag(22),
    AST_IS_PRIVATE              = flag(23),
    AST_IS_READ_ONLY            = flag(24),
    AST_IS_SEALED_SCOPE         = flag(25),
    AST_IS_TYPE                 = flag(26),
    AST_IS_UNION                = flag(27),
    AST_MUST_EVAL               = flag(28),
    AST_VISITED                 = flag(29),
    AST_WAITING_FOR_SCOPE_SEAL  = flag(30),

    // These flags are set by the Sem module.
    //
    // The small exception are the flags AST_ADDED_TO_CHECK_LIST
    // and AST_CAN_EVAL_WITHOUT_VM which can be set by the parser
    // in rare cases involving polymorphic entities.
    AST_SEM_FLAGS =
        AST_ADDRESS_TAKEN | AST_CHECKED | AST_ADDED_TO_CHECK_LIST |
        AST_EVALED | AST_CAN_EVAL | AST_CAN_EVAL_WITHOUT_VM,
};

ienum (AstBaseTag, U64) {
    #define X(TAG, ...) TAG##_NON_FLAG,
        EACH_AST_BASE(X)
    #undef X

    AST_BASE_TAG_COUNT,

    #define X(TAG, ...) TAG = flag(TAG##_NON_FLAG),
        EACH_AST_BASE(X)
    #undef X
};

ienum (AstTag, U8) {
    #define X(TAG, T, ...) TAG, e##T=TAG,
        EACH_AST_NODE(X)
    #undef X

    AST_TAG_COUNT
};

#define X(_, T, ...) istruct (T); array_typedef(T*, T);
    EACH_AST_BASE(X)
    EACH_AST_NODE(X)
#undef X

ienum (AstLevel, U8) {
    AST_LEVEL_FILE,
    AST_LEVEL_FN,
    AST_LEVEL_ENUM,
    AST_LEVEL_STRUCT,
    AST_LEVEL_EXPR,
};

ienum (AstCastTag, U8) {
    AST_CAST_PRIMITIVE,
    AST_CAST_BITWISE,
    AST_CAST_SLICE,
    AST_CAST_ANY,
};

// Fields starting with "sem_" are set by the Sem module.
istruct (Ast)               { AstTag tag; AstFlags flags; AstId id; SrcPos pos; Type *sem_type; Scope *sem_scope; };
istruct (AstBaseBinary)     { Ast base; Ast *op1, *op2; };
istruct (AstBaseFn)         { Ast base; ArrayAst inputs; Ast *output; };
istruct (AstBaseUnary)      { Ast base; Ast *op; };

istruct (AstAdd)            { AstBaseBinary base; };
istruct (AstAddressOf)      { AstBaseUnary base; };
istruct (AstAlignof)        { AstBaseUnary base; };
istruct (AstArgPolyCode)    { Ast base; IString *name; Ast *constraint, *init; U64 n; };
istruct (AstArgPolyType)    { Ast base; IString *name; Ast *constraint, *init; Bool is_tuple; };
istruct (AstArgPolyValue)   { Ast base; IString *name; Ast *constraint, *init; };
istruct (AstArrayLiteral)   { Ast base; Ast *element; ArrayAst inits; };
istruct (AstArrayType)      { Ast base; Ast *element, *length; };
istruct (AstAssign)         { AstBaseBinary base; AstTag fused_op /* AST_ASSIGN for =, AST_ADD for +=, ... */; };
istruct (AstAttribute)      { Ast base; IString *key; Ast *val; };
istruct (AstBitwiseAnd)     { AstBaseBinary base; };
istruct (AstBitwiseNot)     { AstBaseUnary base; };
istruct (AstBitwiseOr)      { AstBaseBinary base; };
istruct (AstBitwiseXor)     { AstBaseBinary base; };
istruct (AstBlock)          { Ast base; ArrayAst statements; IString *label; };
istruct (AstBoolLiteral)    { Ast base; Bool val; };
istruct (AstBreak)          { Ast base; IString *label; Ast *sem_edge; };
istruct (AstCall)           { Ast base; ArrayAst args; Ast *lhs, *sem_edge; };
istruct (AstCallDefaultArg) { Ast base; Ast *arg; };
istruct (AstCallMacro)      { Ast base; ArrayAst args; Ast *lhs, *sem_edge; };
istruct (AstCallMacroArg)   { Ast base; String code; Bool escaped; Ast *parsed_ast; };
istruct (AstCallMacroBArg)  { Ast base; Ast *code; };
istruct (AstCallNamedArg)   { Ast base; IString *name; Ast *arg; };
istruct (AstCallerInfo)     { Ast base; Bool as_default_arg; };
istruct (AstCast)           { Ast base; Ast *to, *expr; Bool implicit; AstCastTag tag; };
istruct (AstCodeGen)        { Ast base; ArrayAst children; Ast *origin; };
istruct (AstContinue)       { Ast base; IString *label; Ast *sem_edge; };
istruct (AstCtAssert)       { AstBaseUnary base; };
istruct (AstDefer)          { Ast base; Ast *stmt, *sem_edge; };
istruct (AstDeref)          { AstBaseUnary base; };
istruct (AstDiv)            { AstBaseBinary base; };
istruct (AstDot)            { Ast base; Ast *lhs, *sem_edge; IString *rhs; };
istruct (AstDummy)          { Ast base; };
istruct (AstEmbed)          { Ast base; AstLevel level; ArrayAst refs; Ast *sem_edge, *generator, *break_hit, *break_miss, *continue_hit, *continue_miss; };
istruct (AstEnum)           { Ast base; IString *name; Ast *type; ArrayAst members; Bool is_implicit, is_explicit, is_flags, is_indistinct; };
istruct (AstEnumField)      { Ast base; IString *name; Ast *init; };
istruct (AstEnumLiteral)    { Ast base; IString *name; Ast *sem_edge; };
istruct (AstEqual)          { AstBaseBinary base; };
istruct (AstEval)           { Ast base; Ast *child; };
istruct (AstF64Literal)     { Ast base; F64 val; };
istruct (AstFile)           { Ast base; IString *path; String content; ArrayAst statements; };
istruct (AstFn)             { AstBaseFn base; IString *name; ArrayAst statements; };
istruct (AstFnLinux)        { AstBaseFn base; IString *name; U32 num; };
istruct (AstFnPoly)         { AstBaseFn base; IString *name; ArrayAst statements; Ast *sem_edge; };
istruct (AstFnType)         { AstBaseFn base; };
istruct (AstGreater)        { AstBaseBinary base; };
istruct (AstGreaterEqual)   { AstBaseBinary base; };
istruct (AstI64Literal)     { Ast base; I64 val; };
istruct (AstIdent)          { Ast base; IString *name; Ast *sem_edge; };
istruct (AstIf)             { Ast base; Ast *cond, *then_arm, *else_arm; };
istruct (AstIfCt)           { Ast base; Ast *cond; ArrayAst then_arm, else_arm; };
istruct (AstImport)         { Ast base; Ast *path_gen; IString *path, *alias; ArrayAstImportConfig configs; };
istruct (AstImportConfig)   { Ast base; IString *name, *init; Ast *sem_edge; };
istruct (AstIndex)          { Ast base; Ast *lhs, *sem_edge; Ast *idx; };
istruct (AstInterface)      { Ast base; IString *name; };
istruct (AstLess)           { AstBaseBinary base; };
istruct (AstLessEqual)      { AstBaseBinary base; };
istruct (AstLogicalAnd)     { AstBaseBinary base; };
istruct (AstLogicalOr)      { AstBaseBinary base; };
istruct (AstMod)            { AstBaseBinary base; };
istruct (AstMul)            { AstBaseBinary base; };
istruct (AstNegate)         { AstBaseUnary base; };
istruct (AstNil)            { Ast base; };
istruct (AstNot)            { AstBaseUnary base; };
istruct (AstNotEqual)       { AstBaseBinary base; };
istruct (AstPair)           { AstBaseBinary base; };
istruct (AstRaw)            { AstBaseUnary base; };
istruct (AstReturn)         { Ast base; Ast *result, *sem_edge; };
istruct (AstScopeMod)       { Ast base; Ast *stmt; Bool is_public; };
istruct (AstSelf)           { Ast base; Ast *sem_edge; };
istruct (AstShiftLeft)      { AstBaseBinary base; };
istruct (AstShiftRight)     { AstBaseBinary base; };
istruct (AstSizeof)         { AstBaseUnary base; };
istruct (AstStringLiteral)  { Ast base; IString *str; };
istruct (AstStruct)         { Ast base; IString *name; ArrayAst members; };
istruct (AstStructLitInit)  { Ast base; IString *name; Ast *val, *sem_edge; };
istruct (AstStructLiteral)  { Ast base; Ast *lhs; ArrayAstStructLitInit inits; };
istruct (AstStructPoly)     { Ast base; IString *name; ArrayAst members, args; };
istruct (AstSub)            { AstBaseBinary base; };
istruct (AstTuple)          { Ast base; ArrayAst fields; };
istruct (AstTupleField)     { Ast base; IString *name; Ast *rhs; };
istruct (AstTypeAlias)      { Ast base; IString *name; Ast *val; };
istruct (AstTypeConstraint) { Ast base; IString *name; Ast *constraint; };
istruct (AstTypeDistinct)   { Ast base; IString *name; Ast *val; };
istruct (AstTypeId)         { AstBaseUnary base; };
istruct (AstTypeof)         { AstBaseUnary base; };
istruct (AstU64Literal)     { Ast base; U64 val; };
istruct (AstVarDef)         { Ast base; IString *name; Ast *constraint, *init; };
istruct (AstWhile)          { Ast base; Ast *cond; ArrayAst statements; IString *label; };

extern CString ast_tag_to_cstr       [AST_TAG_COUNT];
extern U64     ast_get_node_size     [AST_TAG_COUNT];
extern U8      ast_get_node_align    [AST_TAG_COUNT];
extern U64     ast_get_base_flags    [AST_TAG_COUNT];
extern U64     ast_get_default_flags [AST_TAG_COUNT];

AstId   ast_next_id     ();
Ast    *ast_alloc       (Mem *, AstTag, AstFlags);
Ast    *ast_alloc_id    (Mem *, AstTag, AstFlags, AstId);
Ast    *ast_flat_copy   (Mem *, Ast *);
Ast    *ast_deep_copy   (Mem *, Ast *, Ast *(*fn)(Ast*, Ast*, Void*), Void *fn_data);
SrcPos  ast_trimmed_pos (Interns *, Ast *);

// =============================================================================
// Tree walking:
// -------------
//
// The AST_APPLY macro can be used to compactly implement tree traversal.
// It takes the following 3 macros and applies them onto the given ast node:
//
//     F (field): Applied to node child pointers placed on fields of the node.
//     A (array): Applied to node child pointers placed in arrays on the node.
//     I (init):  Applied to substructures on the node that should be initted.
//
// The F and A macros are never applied to null pointers, and they both have
// the same signature:
//
//     arg0: Child pointer casted to Ast*.
//     arg1: Type of child pointer as declared on containing struct.
//     arg2: Downcasted type of containing struct.
//     arg3: Field name on containing struct.
//     arg4: -1 if F macro, else array index for A macro.
//
// The I macro has the following signature:
//
//     arg0: Field name of substructure.
//     arg1: Downcasted type of containing struct.
//     arg2: Downcasted pointer to containing struct.
//
// Most of the time only the AST_VISIT_CHILDREN macro is needed which
// is a wrapper around AST_APPLY.
//
// Usage example:
// --------------
//
//     Void foo (Ast *node) {
//         ...
//
//         #define FOO(child, ...) foo(child)
//         AST_VISIT_CHILDREN(node, FOO);
//     }
// =============================================================================
#define AST_VISIT_CHILDREN(N, V) AST_APPLY(N, V, V, nop)

#define IM(MACRO, T, F) ({\
    MACRO(F, T, cast(T*, NODE));\
})

#define FM(MACRO, T, F) ({\
    if (cast(T*, NODE)->F) {\
        MACRO(cast(Ast*, cast(T*,NODE)->F), Type(cast(T*,n)->F), T, F, -1);\
    }\
})

#define AM(AMACRO, IMACRO, T, F) ({\
    IM(IMACRO, T, F);\
    array_iter (x, &cast(T*, NODE)->F) {\
        if (x) { AMACRO(cast(Ast*, x), Type(x), T, F, ARRAY_IDX); }\
    }\
})

#define AST_APPLY(N, F, A, I) ({\
    def1(NODE, acast(Ast*, N));\
    U64 _(f) = ast_get_base_flags[NODE->tag];\
    \
    if (_(f) & AST_BASE_UNARY)  { FM(F, AstBaseUnary, op); }\
    if (_(f) & AST_BASE_BINARY) { FM(F, AstBaseBinary, op1); FM(F, AstBaseBinary, op2); }\
    if (_(f) & AST_BASE_FN)     { AM(A, I, AstBaseFn, inputs); FM(F, AstBaseFn, output); }\
    \
    switch (NODE->tag) {\
    case AST_ARG_POLY_CODE:    FM(F, AstArgPolyCode, constraint); FM(F, AstArgPolyCode, init); break;\
    case AST_ARG_POLY_TYPE:    FM(F, AstArgPolyType, constraint); FM(F, AstArgPolyType, init); break;\
    case AST_ARG_POLY_VALUE:   FM(F, AstArgPolyValue, constraint); FM(F, AstArgPolyValue, init); break;\
    case AST_ARRAY_LITERAL:    AM(A, I, AstArrayLiteral, inits); FM(F, AstArrayLiteral, element); break;\
    case AST_ARRAY_TYPE:       FM(F, AstArrayType, length); FM(F, AstArrayType, element); break;\
    case AST_ATTRIBUTE:        FM(F, AstAttribute, val); break;\
    case AST_BLOCK:            AM(A, I, AstBlock, statements); break;\
    case AST_CALL:             AM(A, I, AstCall, args); FM(F, AstCall, lhs); break;\
    case AST_CALL_DEFAULT_ARG: FM(F, AstCallDefaultArg, arg); break;\
    case AST_CALL_MACRO:       AM(A, I, AstCallMacro, args); FM(F, AstCallMacro, lhs); break;\
    case AST_CALL_MACRO_BARG:  FM(F, AstCallMacroBArg, code); break;\
    case AST_CALL_NAMED_ARG:   FM(F, AstCallNamedArg, arg); break;\
    case AST_CAST:             FM(F, AstCast, to); FM(F, AstCast, expr); break;\
    case AST_CODE_GEN:         AM(A, I, AstCodeGen, children); break;\
    case AST_DEFER:            FM(F, AstDefer, stmt); break;\
    case AST_DOT:              FM(F, AstDot, lhs); break;\
    case AST_EMBED:            FM(F, AstEmbed, generator); AM(A, I, AstEmbed, refs); FM(F, AstEmbed, break_hit); FM(F, AstEmbed, break_miss); FM(F, AstEmbed, continue_hit); FM(F, AstEmbed, continue_miss); break;\
    case AST_ENUM:             FM(F, AstEnum, type); AM(A, I, AstEnum, members); break;\
    case AST_ENUM_FIELD:       FM(F, AstEnumField, init); break;\
    case AST_EVAL:             FM(F, AstEval, child); break;\
    case AST_FILE:             AM(A, I, AstFile, statements); break;\
    case AST_FN:               AM(A, I, AstFn, statements); break;\
    case AST_FN_POLY:          AM(A, I, AstFnPoly, statements); break;\
    case AST_IF:               FM(F, AstIf, cond); FM(F, AstIf, then_arm); FM(F, AstIf, else_arm); break;\
    case AST_IF_CT:            FM(F, AstIfCt, cond); AM(A, I, AstIfCt, then_arm); AM(A, I, AstIfCt, else_arm); break;\
    case AST_IMPORT:           AM(A, I, AstImport, configs); FM(F, AstImport, path_gen); break;\
    case AST_INDEX:            FM(F, AstIndex, lhs); FM(F, AstIndex, idx); break;\
    case AST_RETURN:           FM(F, AstReturn, result); break;\
    case AST_SCOPE_MOD:        FM(F, AstScopeMod, stmt); break;\
    case AST_STRUCT:           AM(A, I, AstStruct, members); break;\
    case AST_STRUCT_LITERAL:   FM(F, AstStructLiteral, lhs); AM(A, I, AstStructLiteral, inits); break;\
    case AST_STRUCT_LIT_INIT:  FM(F, AstStructLitInit, val); break;\
    case AST_STRUCT_POLY:      AM(A, I, AstStructPoly, members); AM(A, I, AstStructPoly, args); break;\
    case AST_TUPLE:            AM(A, I, AstTuple, fields); break;\
    case AST_TUPLE_FIELD:      FM(F, AstTupleField, rhs); break;\
    case AST_TYPE_ALIAS:       FM(F, AstTypeAlias, val); break;\
    case AST_TYPE_CONSTRAINT:  FM(F, AstTypeConstraint, constraint); break;\
    case AST_TYPE_DISTINCT:    FM(F, AstTypeDistinct, val); break;\
    case AST_VAR_DEF:          FM(F, AstVarDef, constraint); FM(F, AstVarDef, init); break;\
    case AST_WHILE:            FM(F, AstWhile, cond); AM(A, I, AstWhile, statements); break;\
    default: break;\
    }\
})
