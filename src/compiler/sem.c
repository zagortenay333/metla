#include "compiler/interns.h"
#include "compiler/parser.h"
#include "compiler/sem.h"
#include "compiler/vm.h"
#include "os/fs.h"

istruct (PolyInfo) {
    U64 mark;
    Ast *node;
    ArrayAst *args;
    ArrayAst polyargs;
    ArrayAst instances;
};

istruct (MonoInfo);
istruct (ValueInstance) { TypeVar *var; Ast **val; Ast *instance; };
istruct (TypeInstance)  { TypeVar *var; Type *t; Ast *instance; MonoInfo *i; };

istruct (MonoInfo) {
    U64 depth;
    Ast *instantiator;
    PolyInfo *poly_info;
    SliceAst arg_instances; // Parallel to poly_info->args.
    Array(TypeInstance) type_map;
    Array(ValueInstance) value_map;
    Array(struct { Ast *oldn; Ast *newn; }) instance_map;
};

ienum (Subtype, U8) {
    SUBTYPE_ANY_WAY, // (A > B) or (A < B)
    SUBTYPE_ONE_WAY, // (A > B)
    SUBTYPE_TWO_WAY, // (A > B) and (A < B)
};

ienum (Result, U8) {
    RESULT_OK,
    RESULT_DEFER,
    RESULT_ERROR,
};

istruct (MatchPair) { Ast *n1, *n2; Type *t1, *t2; };
istruct (PendingCast) { Ast *to, **from; Type *to_type; };
istruct (UntypedLit) { Ast *lit; Ast *bind; Type *tvar; };

istruct (Sem) {
    Mem *mem;
    Abi *abi;
    Parser *parser;
    Interns *interns;

    AstFn *main_fn;
    ArrayAstFn fns;
    ArrayType types;
    ArrayAstVarDef globals;
    Bool initted_special_types;

    Scope *autoimports;
    AstFile *core_file;
    CoreTypes core_types;
    AstFile *codegen_file;
    Map(IString*, AstFile*) files;

    U64 error_count;
    U64 next_type_id;
    Bool found_a_sem_edge;
    PolyInfo *poly_info;
    Map(TypeId, Ast*) type_def;
    AstCallNamedArg *dummy_named_arg;
    Map(AstId, U64) cached_struct_field_offsets;

    ArrayAst eval_list;
    ArrayAst check_list;
    Array(struct { Ast *from; Ast *to; }) infer_list;

    Map(AstId, Ast*) ast_consts;
    Map(AstId, Value) bin_consts;
    Map(AstId, MonoInfo*) mono_infos;
    Map(AstId, PolyInfo*) poly_infos;
    Map(AstId, Value) node_to_val;

    struct { // Info about ongoing match().
        U64 ongoing;
        Ast *dummy1;
        Ast *dummy2;
        Bool applied_cast;
        MatchPair top_pair;
        U64 without_error_reporting;
    } match;

    struct { // Info about ongoing check_call().
        Bool ongoing;
        Bool bound_var_to_var;
        Bool bound_var_to_val;
        Array(MonoInfo*) mono_infos;
        Array(MonoInfo*) mono_infos_pool;
        ArrayType simple_untyped_lits;
        Array(PendingCast) casts;
        Array(UntypedLit) untyped_lits;
        Array(struct { MonoInfo *i1; MonoInfo *i2; Ast *a; Ast *b; }) values_to_match;

        // These vars act as implicit arguments to match functions
        // that deal with tvar_types and tvar_values. They must be
        // maintained in pop/push or swap/unswap fashion.
        //
        //     Result match_* (Sem *sem, Type *t1, Type *t2) {}
        //                                     ^^--i1    ^^--i2
        MonoInfo *i1, *i2;
    } call_check;
};

static Result error_n (Sem *, Ast *, CString, ...);
static Ast **get_tvar_value (MonoInfo *, TypeVar *);
static Void add_to_infer_list (Sem *, Ast *, Ast *);
static Void add_to_check_list (Sem *, Ast *, Scope *);
static Result error_nn (Sem *, Ast *, Ast *, CString, ...);
static Void check_for_invalid_cycle (Sem *, AstTag, Ast *);
static Type *get_tvar_type (MonoInfo *, TypeVar *, MonoInfo **);
static Ast *instantiate_poly_arg (Sem *, Ast *, MonoInfo *, Ast *);
static Result match (Sem *, Ast **, Ast **, Type *, Type *, Subtype);
static Result match_tvar_untyped_lit (Sem *, Ast *, Ast *, Type *, Type *);
static Result get_tvar_dot (Sem *, MonoInfo *, TypeVar *, Type **, Ast **);
static Result check_call (Sem *, Ast *, ArrayAst *, Ast *, ArrayAst *, Bool);
static Result match_tuples (Sem *, AstTuple *, AstTuple *, Type *, Type *, Subtype);

#define MAX_RECORDED_ERRORS 32
#define MAX_RECURSIVE_INSTANTIATIONS 1024

static I64 smin [] = { [8]=INT8_MIN,  [16]=INT16_MIN,  [32]=INT32_MIN,  [64]=INT64_MIN };
static I64 smax [] = { [8]=INT8_MAX,  [16]=INT16_MAX,  [32]=INT32_MAX,  [64]=INT64_MAX };
static U64 umax [] = { [8]=UINT8_MAX, [16]=UINT16_MAX, [32]=UINT32_MAX, [64]=UINT64_MAX };

static U64 get_type_struct_size [] = {
    #define X(_, type, ...) cast(U64, sizeof(type)),
        EACH_TYPE(X)
    #undef X
};

static U8 get_type_struct_align [] = {
    #define X(_, type, ...) alignof(type),
        EACH_TYPE(X)
    #undef X
};

static TypeFlags get_default_type_flags [] = {
    #define X(a, b, flags) flags,
        EACH_TYPE(X)
    #undef X
};

static Void flush_codegen (Sem *sem) {
    // fs_write_entire_file(*sem->codegen_file->path, sem->codegen_file->content);
}

Noreturn
static Void sem_panic (Sem *sem) {
    flush_codegen(sem);
    log_scope_end_all();
    panic();
}

#define sem_msg(N, TAG) log_msg(N, TAG, "Typer", 1);

inl Bool is_tvar (Type *t)             { return (t->tag == TYPE_VAR) || (t->flags & TYPE_IS_UNTYPED_LIT); }
inl Bool is_tvar_fn (Type *t)          { return (t->flags & TYPE_IS_TVAR_FN); }
inl Bool is_tvar_ptr (Type *t)         { return (t->tag == TYPE_POINTER) && (t->flags & TYPE_IS_UNTYPED_LIT); }
inl Bool is_tvar_dot (Type *t)         { return (t->tag == TYPE_VAR) && (cast(TypeVar*, t)->node->tag == AST_DOT); }
inl Bool is_tvar_call (Type *t)        { return (t->tag == TYPE_VAR) && (cast(TypeVar*, t)->node->tag == AST_CALL); }
inl Bool is_tvar_type (Type *t)        { return (t->tag == TYPE_VAR) && (cast(TypeVar*, t)->node->tag == AST_ARG_POLY_TYPE); }
inl Bool is_tvar_value (Type *t)       { return (t->tag == TYPE_VAR) && (cast(TypeVar*, t)->node->tag == AST_ARG_POLY_VALUE || cast(TypeVar*, t)->node->tag == AST_ARG_POLY_CODE); }
inl Bool is_tvar_array_lit (Type *t)   { return (t->tag == TYPE_ARRAY) && (t->flags & TYPE_IS_UNTYPED_LIT); }
inl Bool is_tvar_tuple_lit (Type *t)   { return (t->tag == TYPE_TUPLE) && (t->flags & TYPE_IS_UNTYPED_LIT); }
inl Bool is_tvar_untyped_lit (Type *t) { return (t->flags & TYPE_IS_UNTYPED_LIT); }

static AstFile *import_file (Sem *sem, IString *path, Ast *error_node) {
    AstFile *file = map_get_ptr(&sem->files, path);
    if (file) return file;

    file = par_parse_file(sem->parser, path);
    if (! file) {
        if (error_node) {
            error_n(sem, error_node, "Unable to import file [%.*s].", STR(*path));
        } else {
            sem_msg(msg, LOG_ERROR);
            astr_push_fmt(msg, "Unable to import file [%.*s].\n", STR(*path));
        }
        sem_panic(sem);
    }

    add_to_check_list(sem, cast(Ast*, file), sem->autoimports);
    map_add(&sem->files, path, file);
    return file;
}

static Bool type_has_polyargs (Type *type) {
    switch (type->tag) {
    case TYPE_FN:      { Ast *n = cast(Ast*, cast(TypeFn*, type)->node); return n->flags & AST_HAS_POLY_ARGS; }
    case TYPE_ARRAY:   { Ast *n = cast(Ast*, cast(TypeArray*, type)->node); return n->flags & AST_HAS_POLY_ARGS; }
    case TYPE_TUPLE:   { Ast *n = cast(Ast*, cast(TypeTuple*, type)->node); return n->flags & AST_HAS_POLY_ARGS; }
    case TYPE_STRUCT:  { Ast *n = cast(Ast*, cast(TypeStruct*, type)->node); return n->flags & AST_HAS_POLY_ARGS; }
    case TYPE_POINTER: { Ast *n = cast(Ast*, cast(TypePointer*, type)->node); return n && n->flags & AST_HAS_POLY_ARGS; }
    case TYPE_BOOL:    return false;
    case TYPE_ENUM:    return false;
    case TYPE_FLOAT:   return false;
    case TYPE_INT:     return false;
    case TYPE_VOID:    return false;
    case TYPE_MISC:    return false;
    case TYPE_VAR:     return true;
    }
    badpath;
}

Bool sem_type_has_pointers (Sem *sem, Type *type) {
    switch (type->tag) {
    case TYPE_ARRAY:   return sem_type_has_pointers(sem, cast(TypeArray*, type)->element);
    case TYPE_TUPLE:   return array_find_get(&cast(TypeTuple*, type)->node->fields, sem_type_has_pointers(sem, sem_get_type(sem, IT)));
    case TYPE_STRUCT:  return array_find_get(&cast(TypeStruct*, type)->node->members, sem_type_has_pointers(sem, sem_get_type(sem, IT)));
    case TYPE_FN:      return true;
    case TYPE_POINTER: return true;
    case TYPE_BOOL:    return false;
    case TYPE_ENUM:    return false;
    case TYPE_FLOAT:   return false;
    case TYPE_INT:     return false;
    case TYPE_VOID:    return false;
    case TYPE_MISC:    return false;
    case TYPE_VAR:     return false;
    }
    badpath;
}

static Ast *get_type_constructor (Type *type) {
    switch (type->tag) {
    case TYPE_ARRAY:   return cast(Ast*, cast(TypeArray*, type)->node);
    case TYPE_FN:      return cast(Ast*, cast(TypeFn*, type)->node);
    case TYPE_POINTER: return cast(Ast*, cast(TypePointer*, type)->node);
    case TYPE_STRUCT:  return cast(Ast*, cast(TypeStruct*, type)->node);
    case TYPE_TUPLE:   return cast(Ast*, cast(TypeTuple*, type)->node);
    case TYPE_VAR:     return cast(Ast*, cast(TypeVar*, type)->node);
    case TYPE_INT:     return 0;
    case TYPE_MISC:    return 0;
    case TYPE_BOOL:    return 0;
    case TYPE_ENUM:    return 0;
    case TYPE_FLOAT:   return 0;
    case TYPE_VOID:    return 0;
    }
    badpath;
}

static Type *alloc_type (Sem *sem, TypeTag tag) {
    Auto type   = mem_alloc(sem->mem, Type, .zeroed=true, .align=get_type_struct_align[tag], .size=get_type_struct_size[tag]);
    type->id    = sem->next_type_id++;
    type->tag   = tag;
    type->flags = get_default_type_flags[tag];
    array_push(&sem->types, type);
    return type;
}

static Type *alloc_type_fn     (Sem *sem, AstBaseFn *n)        { TypeFn *t = cast(TypeFn*, alloc_type(sem, TYPE_FN)); t->node = n; return cast(Type*, t); }
static Type *alloc_type_var    (Sem *sem, Ast *n, TypeFlags f) { TypeVar *t = cast(TypeVar*, alloc_type(sem, TYPE_VAR)); t->node = n; cast(Type*, t)->flags |= f; return cast(Type*, t); }
static Type *alloc_type_misc   (Sem *sem, Ast *n)              { TypeMisc *t = cast(TypeMisc*, alloc_type(sem, TYPE_MISC)); t->node = n; return cast(Type*, t); }
static Type *alloc_type_tuple  (Sem *sem, AstTuple *n)         { TypeTuple *t = cast(TypeTuple*, alloc_type(sem, TYPE_TUPLE)); t->node = n; return cast(Type*, t); }
static Type *alloc_type_struct (Sem *sem, AstStruct *n)        { TypeStruct *t = cast(TypeStruct*, alloc_type(sem, TYPE_STRUCT)); t->node = n; return cast(Type*, t); }

static Type *alloc_type_array (Sem *sem, Ast *node, U64 length, Type *element) {
    TypeArray *t = cast(TypeArray*, alloc_type(sem, TYPE_ARRAY));
    t->node = node;
    t->length = length;
    t->element = element;
    return cast(Type*, t);
}

static Type *alloc_type_pointer (Sem *sem, Ast *node, Type *pointee) {
    TypePointer *t = cast(TypePointer*, alloc_type(sem, TYPE_POINTER));
    t->node = node;
    t->pointee = pointee;
    return cast(Type*, t);
}

Type *sem_alloc_type_pointer (Sem *sem, Mem *mem, Type *pointee) {
    TypeTag tag = TYPE_POINTER;
    Auto t      = mem_alloc(mem, Type, .zeroed=true, .align=get_type_struct_align[tag], .size=get_type_struct_size[tag]);
    t->id       = sem->next_type_id++;
    t->tag      = tag;
    t->flags    = get_default_type_flags[tag];
    cast(TypePointer*, t)->pointee = pointee;
    return t;
}

CoreTypes       *sem_get_core_types (Sem *sem)            { return &sem->core_types; }
MonoInfo        *sem_get_mono_info  (Sem *sem, Ast *node) { return map_get_ptr(&sem->mono_infos, node->id); }
static PolyInfo *get_poly_info      (Sem *sem, Ast *node) { return map_get_ptr(&sem->poly_infos, node->id); }

static Ast *get_target (Ast *node) {
    switch (node->tag) {
    #define X(TAG, T, ...) case TAG: return cast(T*, node)->sem_edge;
        EACH_AST_SELECTOR(X);
    #undef X
    default: return 0;
    }
}

static Void sem_set_target (Sem *sem, Ast *node, Ast *target) {
    switch (node->tag) {
    #define X(TAG, T, ...) case TAG: cast(T*, node)->sem_edge = target; break;
        EACH_AST_SELECTOR(X);
    #undef X
    default: badpath;
    }

    sem->found_a_sem_edge = true;
}

#define get_file(NODE)         (sem_get_file(sem, NODE))
#define get_type(NODE)         ((NODE)->sem_type)
#define set_type(NODE, TYPE)   ((NODE)->sem_type = TYPE)
#define get_scope(NODE)        ((NODE)->sem_scope)
#define set_scope(NODE, SCOPE) ((NODE)->sem_scope = SCOPE)

SemIter *sem_iter_new (Mem *mem, Sem *sem, ArrayAst *nodes) {
    SemIter *iter = mem_new(mem, SemIter);
    iter->sem = sem;
    array_init(&iter->stack, mem);
    array_push_lit(&iter->stack, .nodes=nodes, .idx=0);
    return iter;
}

Bool sem_iter_next (SemIter *iter)  {
    if (iter->stack.count == 0) return 0;

    while (true) {
        SemIterLevel *lvl = array_ref_last(&iter->stack);
        iter->node = array_try_get(lvl->nodes, lvl->idx);
        lvl->idx++;

        if (! iter->node) {
            if (iter->stack.count == 1) return false;
            iter->stack.count--;
        } else if (iter->node->tag == AST_IF_CT) {
            AstIfCt *n = cast(AstIfCt*, iter->node);
            U8 cond = sem_get_const(iter->sem, n->cond).u8;
            array_push_lit(&iter->stack, .nodes=(cond ? &n->then_arm : &n->else_arm));
        } else if (iter->node->tag == AST_EMBED) {
            AstCodeGen *gen = cast(AstCodeGen*, cast(AstEmbed*, iter->node)->sem_edge);
            array_push_lit(&iter->stack, .nodes=&gen->children);
        } else {
            return true;
        }
    }
}

#define try_get_type(NODE) ({\
    Type *t = get_type(NODE);\
    if (! t) return RESULT_DEFER;\
    t;\
})

#define try_get_type_v(NODE) ({\
    def1(n, acast(Ast*, NODE));\
    Type *t = try_get_type(n);\
    if ((t->tag == TYPE_MISC) || (n->flags & AST_IS_TYPE)) return error_n(sem, n, "Expected value expression.");\
    t;\
})

#define try_get_type_t(NODE) ({\
    def1(n, acast(Ast*, NODE));\
    Type *t = try_get_type(n);\
    if ((t->tag == TYPE_MISC) || !(n->flags & AST_IS_TYPE)) return error_n(sem, n, "Expected type expression.");\
    t;\
})

#define try(RESULT, ...) ({\
    def1(R, acast(Result, RESULT));\
    if (R != RESULT_OK) { __VA_ARGS__; return R; }\
    RESULT_OK;\
})

static AstFile *sem_get_file (Sem *sem, Ast *node) {
    for (Scope *s = get_scope(node); s; s = s->parent) {
        Ast *o = s->owner;
        if (o->tag == AST_FILE) return cast(AstFile*, o);
        if ((o->tag == AST_CODE_GEN) && !(o->flags & AST_ENDS_WITH_BLOCK)) return sem->codegen_file;
    }

    return 0;
}

AstAttribute *sem_get_attribute (Sem *sem, Ast *node, IString *key) {
    ArrayAstAttribute *attrs = par_get_attributes(sem->parser, node->id);
    return attrs ? array_find_get(attrs, IT->key == key) : 0;
}

SliceAst sem_get_arg_instances (Sem *sem, Ast *node) {
    switch (node->tag) {
    case AST_FN: {
        MonoInfo *info = sem_get_mono_info(sem, node);
        return info ? info->arg_instances : slice_from(&cast(AstBaseFn*, node)->inputs, SliceAst);
    }
    case AST_FN_LINUX: return slice_from(&((AstBaseFn*)node)->inputs, SliceAst);
    case AST_FN_TYPE:  return slice_from(&cast(AstBaseFn*, node)->inputs, SliceAst);
    case AST_STRUCT:   return sem_get_mono_info(sem, node)->arg_instances;
    default:           badpath;
    }
}

static IString *get_name (Ast *node) {
    switch (node->tag) {
    #define X(TAG, TYPE) case TAG: return cast(TYPE*, node)->name;
        EACH_STATIC_NAME_GENERATOR(X)
    #undef X

    case AST_IDENT: return cast(AstIdent*, node)->name;
    default: badpath;
    }
}

static Ast *get_init (Ast *node) {
    switch (node->tag) {
    case AST_VAR_DEF:        return cast(AstVarDef*, node)->init;
    case AST_ARG_POLY_TYPE:  return cast(AstArgPolyType*, node)->init;
    case AST_ARG_POLY_CODE:  return cast(AstArgPolyCode*, node)->init;
    case AST_ARG_POLY_VALUE: return cast(AstArgPolyValue*, node)->init;
    default:                 return 0;
    }
}

// To interpret the returned Value follow these steps:
//
//     1. If the type of node has the flag TYPE_IS_PRIMITIVE,
//        read one of the Value fields: u8..u64, i8..i64, f32
//        or f64. Read Value.u8 for Bool types.
//
//     2. Else if the node has the flag AST_CAN_EVAL_WITHOUT_VM,
//        read the Value.ast field which can either be a literal,
//        a type expression (meaning 0 init), or a cast operator.
//
//     3. Else read the Value.ptr field which points to an object
//        compiled by the VM thus using the vm abi.
//
Value sem_get_const (Sem *sem, Ast *node) {
    assert_dbg(node->flags & AST_EVALED);

    if (node->tag == AST_TUPLE_FIELD) node = cast(AstTupleField*, node)->rhs;

    if (get_type(node)->flags & TYPE_IS_PRIMITIVE) {
        switch (node->tag) {
        case AST_I64_LITERAL:  return (Value){ .i64 = cast(AstI64Literal*, node)->val };
        case AST_U64_LITERAL:  return (Value){ .u64 = cast(AstU64Literal*, node)->val };
        case AST_F64_LITERAL:  return (Value){ .f64 = cast(AstF64Literal*, node)->val };
        case AST_BOOL_LITERAL: return (Value){ .u8  = cast(AstBoolLiteral*, node)->val };
        default:               return map_get_assert(&sem->bin_consts, node->id);
        }
    } else if (! (node->flags & AST_CAN_EVAL_WITHOUT_VM)) {
        return map_get_assert(&sem->bin_consts, node->id);
    } else if (node->flags & AST_IS_LITERAL) {
        return (Value){ .ast = node };
    } else {
        return (Value){ .ast = map_get_assert(&sem->ast_consts, node->id) };
    }
}

static Value get_const (Sem *sem, MonoInfo *info, Ast *node, Type **out_type) {
    Type *type = get_type(node);

    assert_dbg(sem->call_check.ongoing);
    assert_dbg(type->flags & TYPE_IS_PRIMITIVE);

    if (is_tvar_dot(type)) {
        get_tvar_dot(sem, info, cast(TypeVar*, type), &type, &node);
    } else if (is_tvar_value(type)) {
        node = *get_tvar_value(info, cast(TypeVar*, type));
        type = get_type(node);
    }

    Value v = sem_get_const(sem, node);
    PendingCast *cast = array_find_ref(&sem->call_check.casts, *IT->from == node);
    if (cast) { type = cast->to_type; v = vm_value_cast(cast->to_type, type, v); }
    if (out_type) *out_type = type;
    return v;
}

static Void infer_const (Sem *sem, Type *type, Value val, Ast *from, Ast *to) {
    if ((type->flags & TYPE_IS_PRIMITIVE) || !(from->flags & AST_CAN_EVAL_WITHOUT_VM)) {
        map_add(&sem->bin_consts, to->id, val);
    } else {
        map_add(&sem->ast_consts, to->id, val.ast);
    }

    to->flags |= AST_CAN_EVAL | AST_EVALED | (from->flags & AST_CAN_EVAL_WITHOUT_VM);
}

static String get_string_const (Sem *sem, Ast *node) {
    assert_dbg(node->flags & AST_EVALED);

    Value c = sem_get_const(sem, node);
    if (c.ast->tag == AST_STRING_LITERAL) return *cast(AstStringLiteral*, c.ast)->str;
    if (c.ast->tag == AST_CALL_MACRO_ARG) return cast(AstCallMacroArg*, c.ast)->code;

    assert_dbg(get_type(node) == sem->core_types.type_string);

    if (! (node->flags & AST_CAN_EVAL_WITHOUT_VM)) return *cast(String*, c.ptr);
    if (c.ast->flags & AST_IS_TYPE) return (String){};
    if (c.ast->tag == AST_CAST) return get_string_const(sem, cast(AstCast*, c.ast)->expr);

    badpath; // @todo Implement the vm for this case.
}

static Result can_eval (Sem *sem, Ast *node, Bool allow_untyped_lits) {
    if (node->flags & (AST_VISITED | AST_CAN_EVAL)) return RESULT_OK;
    if (! (node->flags & AST_ADDED_TO_CHECK_LIST)) return RESULT_OK; // For example a dead if:ct branch.

    Type *t = try_get_type(node);

    if (! (node->flags & AST_CHECKED)) {
        if (! allow_untyped_lits) return RESULT_DEFER;
        if (is_tvar_fn(t)) return RESULT_OK;
        if (! is_tvar_untyped_lit(t)) return RESULT_DEFER;
    }

    node->flags |= AST_VISITED;

    reach(r);
    #define RETURN(R) { reached(r); node->flags &= ~AST_VISITED; return R; }

    #define CAN_EVAL(child, ...) ({\
        try(can_eval(sem, child, allow_untyped_lits), RETURN(R));\
        if ((t->tag != TYPE_FN) && !(child->flags & (AST_IS_TYPE | AST_CAN_EVAL_WITHOUT_VM))) node->flags &= ~AST_CAN_EVAL_WITHOUT_VM;\
        if ((node->tag == AST_DOT) && (child->tag == AST_CAST) && !(get_type(child)->flags & TYPE_IS_PRIMITIVE)) node->flags &= ~AST_CAN_EVAL_WITHOUT_VM;\
    })

    AST_VISIT_CHILDREN(node, CAN_EVAL);

    Ast *d = get_target(node);
    if (d) {
        if ((d->tag == AST_VAR_DEF) && !(d->flags & (AST_IS_GLOBAL | AST_CAN_EVAL))) RETURN(error_nn(sem, node, d, "Cannot eval this node."));
        CAN_EVAL(d);
    }

    node->flags |= AST_CAN_EVAL;
    RETURN(RESULT_OK);
    #undef RETURN
}

static Value ast_eval (Sem *sem, Ast *node) {
    assert_dbg(node->flags & AST_CAN_EVAL);
    assert_dbg(! (node->flags & AST_VISITED));
    assert_dbg(node->flags & (AST_CAN_EVAL_WITHOUT_VM | AST_IS_TYPE));

    if (node->flags & AST_EVALED) return sem_get_const(sem, node);
    IF_BUILD_DEBUG(node->flags |= AST_VISITED);

    Value result;

    reach(r);
    #define RETURN(R) { result = (R); goto done; }

    #define biop(op) ({\
        Value c1 = ast_eval(sem, cast(AstBaseBinary*, node)->op1);\
        Value c2 = ast_eval(sem, cast(AstBaseBinary*, node)->op2);\
        op(get_type(node), c1, c2);\
    })

    switch (node->tag) {
    case AST_DOT: {
        AstDot *n = cast(AstDot*, node);
        Type *t = get_type(n->lhs);

        if (t->tag == TYPE_STRUCT) {
            Ast *d = ast_eval(sem, n->lhs).ast;
            if (d->tag == AST_STRUCT) RETURN(ast_eval(sem, n->sem_edge));
            assert_dbg(d->tag == AST_STRUCT_LITERAL);
            array_iter (i, &cast(AstStructLiteral*, d)->inits) if (i->name == n->rhs) RETURN(ast_eval(sem, cast(Ast*, i)));
            RETURN(ast_eval(sem, n->sem_edge));
        } else if (t->tag == TYPE_TUPLE) {
            AstTuple *d = cast(AstTuple*, ast_eval(sem, n->lhs).ast);
            Ast *field = array_find_get(&d->fields, cast(AstTupleField*, IT)->name == n->rhs);
            RETURN(ast_eval(sem, cast(Ast*, field)));
        } else {
            assert_dbg(t->tag == TYPE_ENUM || t->tag == TYPE_MISC);
            RETURN(ast_eval(sem, n->sem_edge));
        }
    }

    case AST_INDEX: {
        AstIndex *n = cast(AstIndex*, node);
        Type *t     = get_type(n->lhs);
        Ast *d      = ast_eval(sem, n->lhs).ast;
        U64 idx     = ast_eval(sem, n->idx).u64;

        if (t->tag == TYPE_ARRAY) {
            U64 len = cast(TypeArray*, t)->length;
            if (idx >= len) { error_nn(sem, n->idx, d, "Array out of bounds access (idx = %i, len = %i).", idx, len); sem_panic(sem); }
            if (d->tag == AST_ARRAY_TYPE) RETURN(ast_eval(sem, cast(AstArrayType*, d)->element));
            assert_dbg(d->tag == AST_ARRAY_LITERAL);
            RETURN(ast_eval(sem, array_get(&cast(AstArrayLiteral*, d)->inits, idx)));
        } else {
            assert_dbg(t->tag == TYPE_TUPLE);
            RETURN(ast_eval(sem, array_get(&cast(AstTuple*, d)->fields, idx)));
        }
    }

    case AST_CAST: {
        AstCast *n = cast(AstCast*, node);
        Value v    = ast_eval(sem, n->expr);
        Type *to   = get_type(node);
        Type *from = get_type(n->expr);
        if (n->tag == AST_CAST_BITWISE) RETURN(vm_value_bitcast(to, from, v));
        if (to->flags & TYPE_IS_PRIMITIVE) RETURN(vm_value_cast(to, from, v));
        RETURN((Value){ .ast=node });
    }

    case AST_DIV: {
        AstBaseBinary *n = cast(AstBaseBinary*, node);
        Value c1 = ast_eval(sem, n->op1);
        Value c2 = ast_eval(sem, n->op2);
        if (vm_value_to_u64(get_type(n->op2), c2) != 0) RETURN(vm_value_div(get_type(node), c1, c2));
        error_n(sem, n->op2, "Attempting to divide by 0.");
        sem_panic(sem);
    }

    case AST_FN_POLY: {
        Type *t = get_type(node);
        assert_dbg(t->tag == TYPE_FN);
        RETURN((Value){ .ast = cast(Ast*, cast(TypeFn*, t)->node) });
    }

    case AST_DEREF: {
        Ast *val = ast_eval(sem, cast(AstBaseUnary*, node)->op).ast;
        assert_dbg(val->tag == AST_ADDRESS_OF);
        RETURN(ast_eval(sem, cast(AstBaseUnary*, val)->op));
    }

    case AST_EMBED: {
        AstEmbed *n = cast(AstEmbed*, node);
        AstCodeGen *g = cast(AstCodeGen*, n->sem_edge);
        assert_dbg(n->level == AST_LEVEL_EXPR);
        RETURN(ast_eval(sem, array_get(&g->children, 0)));
    }

    case AST_ADD:              RETURN(biop(vm_value_add));
    case AST_ADDRESS_OF:       ast_eval(sem, cast(AstBaseUnary*, node)->op); RETURN((Value){ .ast=node });
    case AST_ALIGNOF:          RETURN((Value){ .u64 = abi_of_obj(sem->abi, get_type(node)).align });
    case AST_ARRAY_LITERAL:    array_iter (i, &cast(AstArrayLiteral*, node)->inits) { ast_eval(sem, i); } RETURN((Value){ .ast = node });
    case AST_ARRAY_TYPE:       RETURN((Value){ .ast = node });
    case AST_BITWISE_AND:      RETURN(biop(vm_value_bitand));
    case AST_BITWISE_NOT:      RETURN(vm_value_bitnot(get_type(node), ast_eval(sem, cast(AstBaseUnary*, node)->op)));
    case AST_BITWISE_OR:       RETURN(biop(vm_value_bitor));
    case AST_BITWISE_XOR:      RETURN(biop(vm_value_bitxor));
    case AST_BOOL_LITERAL:     RETURN((Value){ .u8 = cast(AstBoolLiteral*, node)->val });
    case AST_CALL:             { assert_dbg(cast(AstCall*, node)->sem_edge); return (Value){ .ast = cast(AstCall*, node)->sem_edge}; }
    case AST_CALL_DEFAULT_ARG: RETURN(ast_eval(sem, cast(AstCallDefaultArg*, node)->arg));
    case AST_DUMMY:            assert_dbg(get_type(node)->flags & TYPE_IS_PRIMITIVE); RETURN((Value){});
    case AST_ENUM:             RETURN((Value){ .ast = node });
    case AST_ENUM_FIELD:       RETURN(ast_eval(sem, cast(AstEnumField*, node)->init));
    case AST_ENUM_LITERAL:     RETURN(ast_eval(sem, cast(AstEnumLiteral*, node)->sem_edge));
    case AST_EQUAL:            RETURN(biop(vm_value_equal));
    case AST_EVAL:             RETURN(ast_eval(sem, cast(AstEval*, node)->child));
    case AST_F64_LITERAL:      RETURN((Value){ .f64 = cast(AstF64Literal*, node)->val });
    case AST_FN:               RETURN((Value){ .ast = node });
    case AST_GREATER:          RETURN(biop(vm_value_greater));
    case AST_GREATER_EQUAL:    RETURN(biop(vm_value_greater_eq));
    case AST_I64_LITERAL:      RETURN((Value){ .i64 = cast(AstI64Literal*, node)->val });
    case AST_IDENT:            RETURN(ast_eval(sem, cast(AstIdent*, node)->sem_edge));
    case AST_IMPORT:           RETURN((Value){ .ast = node });
    case AST_IMPORT_CONFIG:    RETURN(ast_eval(sem, cast(AstImportConfig*, node)->sem_edge));
    case AST_LESS:             RETURN(biop(vm_value_less));
    case AST_LESS_EQUAL:       RETURN(biop(vm_value_less_eq));
    case AST_MOD:              RETURN(biop(vm_value_mod));
    case AST_MUL:              RETURN(biop(vm_value_mul));
    case AST_NEGATE:           RETURN(vm_value_negate(get_type(node), ast_eval(sem, cast(AstBaseUnary*, node)->op)));
    case AST_NIL:              { Type *t = get_type(node); RETURN((t->flags & TYPE_IS_PRIMITIVE) ? (Value){} : (Value){ .ast=get_type_constructor(t) }); }
    case AST_NOT:              RETURN(vm_value_not(get_type(node), ast_eval(sem, cast(AstBaseUnary*, node)->op)));
    case AST_NOT_EQUAL:        RETURN(biop(vm_value_not_eq));
    case AST_RAW:              RETURN((node->flags & AST_IS_TYPE) ? (Value){} : ast_eval(sem, cast(AstBaseUnary*, node)->op));
    case AST_SHIFT_LEFT:       RETURN(biop(vm_value_lshift));
    case AST_SHIFT_RIGHT:      RETURN(biop(vm_value_rshift));
    case AST_SIZEOF:           RETURN((Value){ .u64 = abi_of_obj(sem->abi, get_type(node)).size });
    case AST_STRING_LITERAL:   RETURN((Value){ .ast = node });
    case AST_STRUCT:           RETURN((Value){ .ast = node });
    case AST_STRUCT_LITERAL:   array_iter (i, &cast(AstStructLiteral*, node)->inits) { ast_eval(sem, cast(Ast*, i)); } RETURN((Value){ .ast = node });
    case AST_STRUCT_LIT_INIT:  RETURN(ast_eval(sem, cast(AstStructLitInit*, node)->val));
    case AST_SUB:              RETURN(biop(vm_value_sub));
    case AST_TUPLE:            array_iter (i, &cast(AstTuple*, node)->fields) { ast_eval(sem, i); } RETURN((Value){ .ast = node });
    case AST_TUPLE_FIELD:      RETURN(ast_eval(sem, cast(AstTupleField*, node)->rhs));
    case AST_U64_LITERAL:      RETURN((Value){ .u64 = cast(AstU64Literal*, node)->val });
    case AST_VAR_DEF:          { AstVarDef *n = cast(AstVarDef*, node); RETURN(ast_eval(sem, n->init ? n->init : n->constraint)); }
    default: badpath;
    }

    badpath;

    done: {
        if (! (node->flags & AST_IS_LITERAL)) {
            if (get_type(node)->flags & TYPE_IS_PRIMITIVE) {
                map_add(&sem->bin_consts, node->id, result);
            } else {
                map_add(&sem->ast_consts, node->id, result.ast);
            }
        }

        IF_BUILD_DEBUG(node->flags &= ~AST_VISITED);
        node->flags |= AST_EVALED;
        #undef biop
        #undef RETURN
        reached(r);
        return result;
    }
}

static Result eval (Sem *sem, Ast *node) {
    try(can_eval(sem, node, false));

    if (! (node->flags & AST_CAN_EVAL_WITHOUT_VM)) {
        sem_msg(msg, LOG_ERROR);
        astr_push_cstr(msg, "You need to implement the VM to eval this.\n\n");
        sem_print_node(sem, msg, node);
        sem_panic(sem);
    }

    ast_eval(sem, node);
    return RESULT_OK;
}

static Scope *scope_new (Sem *sem, Scope *parent, Ast *owner) {
    Scope *scope = mem_new(sem->mem, Scope);
    scope->parent = parent;
    scope->owner = owner;
    set_scope(owner, scope);
    map_init(&scope->map, sem->mem);
    array_init(&scope->namegens, sem->mem);
    return scope;
}

static Scope *scope_get_ancestor (Scope *s, AstTag tag) {
    for (; s; s = s->parent) if (s->owner->tag == tag) return s;
    return 0;
}

static Scope *scope_get_non_codegen_ancestor (Scope *s) {
    for (; s; s = s->parent) if (s->owner->tag != AST_CODE_GEN) return s;
    return 0;
}

static AstEmbed *scope_get_constraint (Scope *s) {
    if (s->owner->tag != AST_CODE_GEN) return 0;
    Ast *c = cast(AstCodeGen*, s->owner)->origin;
    return (c->tag == AST_EMBED) ? cast(AstEmbed*, c ): 0;
}

static Scope *scope_of_instance (Ast *node) {
    for (Scope *s = get_scope(node); s && s->owner; s = s->parent) {
        if (s->owner->flags & AST_IS_POLYMORPH_INSTANCE) return s;
    }
    return 0;
}

static Ast *scope_lookup_outside_in (Sem *sem, Scope *scope, IString *key, Ast *selector) {
    selector->flags &= ~AST_WAITING_FOR_SCOPE_SEAL;
    if (! (scope->owner->flags & AST_IS_SEALED_SCOPE)) { selector->flags |= AST_WAITING_FOR_SCOPE_SEAL; return 0; }
    Ast *target = map_get_ptr(&scope->map, key);
    if (!target || (target->flags & AST_IS_PRIVATE)) return 0;
    sem_set_target(sem, selector, target);
    return target;
}

static Ast *scope_lookup_inside_out (Sem *sem, Scope *scope, IString *key, Ast *selector) {
    tmem_new(tm);

    selector->flags &= ~ AST_WAITING_FOR_SCOPE_SEAL;

    Bool crossed_fn_scope  = false;
    Ast *original_selector = selector;
    U64 selector_offset    = selector->pos.offset;

    Array(struct { Scope *scope; U64 offset; }) trace;
    array_init(&trace, tm);

    while (scope) {
        if ((scope->owner->tag != AST_FILE) &&
            !(scope->owner->flags & AST_IS_SEALED_SCOPE) &&
            (selector_offset > array_get(&scope->namegens, 0))
        ) {
            // Lookups that originate from a position that is below an
            // unresolved namegen are blocked:
            //
            //     var foo = 1;
            //     var bar = true;
            //
            //     {
            //         if:ct bar { var foo = 2; } // Lookup for bar not blocked.
            //         print(foo);                // Lookup for foo waits on if:ct.
            //     }
            //
            // This does not apply to file scopes because those allow
            // forward referencing which would cause a lockup any time
            // a namegen forward references:
            //
            //     var foo = true;
            //     if:ct bar {}    // Waits for bar.
            //     var bar = foo;  // Waits for the if:ct.
            //
            // Since this rule is implemented in case we shadow a variable
            // in an outer scope like in the first example above, and since
            // the parent of the file scope (the autoimports scope) cannot
            // be shadowed, we make an exception for file scopes.
            original_selector->flags |= AST_WAITING_FOR_SCOPE_SEAL;
            return 0;
        }

        Ast *target = map_get_ptr(&scope->map, key);

        if (target) {
            if ((scope->owner->tag == AST_FILE) || (scope == sem->autoimports)) {
                sem_set_target(sem, original_selector, target);
                return target;
            }

            U64 s_offset = selector_offset;
            U64 t_offset = target->pos.offset;

            Scope *s = get_scope(target);
            if (target->flags & AST_CREATES_SCOPE) s = s->parent ? s->parent : s;

            if (s->owner->tag == AST_CODE_GEN) { // Adjust offsets if in different files.
                Ast *n = target;

                while (true) {
                    Auto x = array_find_ref(&trace, IT->scope == s);
                    if (x) { s_offset = x->offset; break; }
                    n = cast(AstCodeGen*, s->owner)->origin;
                    s = s->parent;
                    if (s->owner->tag != AST_CODE_GEN) break;
                }

                t_offset = n->pos.offset;
                trace.count = 0;
            }

            // Forward references to non-globals are invalid and are handled
            // by continuing the lookup instead of error reporting. We do this
            // because in the following code whether or not we print an error
            // depends on when the if:ct resolves:
            //
            //     var foo = 42;
            //     {
            //         foo;
            //         if:ct ... { var foo = 42; }
            //     }
            //
            if (s_offset >= t_offset) {
                if (crossed_fn_scope) {
                    if (target->flags & AST_HAS_POLY_ARGS) {
                        error_nn(sem, selector, target, "Cannot reference polymorphic expressions of enclosing fn.");
                        return 0;
                    }

                    if ((target->tag != AST_FN) &&
                        (target->tag != AST_FN_POLY) &&
                        (target->tag != AST_STRUCT_POLY) &&
                        !(target->flags & AST_IS_TYPE)
                    ) {
                        error_nn(sem, selector, target, "Invalid reference to target in enclosing function.");
                        return 0;
                    }
                }

                sem_set_target(sem, original_selector, target);
                return target;
            }
        }

        if (scope->owner->flags & AST_IS_MACRO_INSTANCE) {
            MonoInfo *info = sem_get_mono_info(sem, scope->owner);

            if (selector->flags & AST_BACKTICKED) {
                selector_offset = info->instantiator->pos.offset;
                scope = scope->parent;
            } else {
                crossed_fn_scope = true;
                selector_offset = scope->owner->pos.offset;
                scope = get_scope(info->poly_info->node)->parent;
            }
        } else if (scope->owner->tag == AST_CODE_GEN) {
            array_push_lit(&trace, .scope=scope, .offset=selector_offset);
            selector_offset = cast(AstCodeGen*, scope->owner)->origin->pos.offset;

            AstEmbed *constraint = scope_get_constraint(scope);
            if (! constraint) { scope = scope->parent; continue; }

            Bool going_to_parent_scope_allowed = false;

            array_iter (ref, &constraint->refs) {
                if (ref->tag == AST_PAIR) {
                    String n = get_string_const(sem, cast(AstBaseBinary*, ref)->op1);
                    if (str_match(*key, n)) {
                        Ast *op2 = cast(AstBaseBinary*, ref)->op2;
                        key = intern_str(sem->interns, get_string_const(sem, op2));
                        selector = op2;
                        going_to_parent_scope_allowed = true;
                        break;
                    }
                } else if (str_match(*key, get_string_const(sem, ref))) {
                    going_to_parent_scope_allowed = true;
                    break;
                }
            }

            if (going_to_parent_scope_allowed) {
                scope = scope->parent;
            } else {
                Scope *a = scope_get_ancestor(scope, AST_FN);
                if (a && (a->owner->flags & AST_IS_MACRO_INSTANCE)) {
                    scope = a->parent;
                    selector_offset = sem_get_mono_info(sem, a->owner)->instantiator->pos.offset;
                } else {
                    scope = sem->autoimports;
                }
            }
        } else if ((scope->owner->tag == AST_FN) || (scope->owner->tag == AST_FN_POLY)) {
            crossed_fn_scope = true;
            scope = scope->parent;
        } else {
            scope = scope->parent;
        }
    }

    return 0;
}

static Result scope_add (Sem *sem, Scope *scope, IString *key, Ast *val, Ast *error_node) {
    scope = scope_get_non_codegen_ancestor(scope);

    Ast *def = map_get_ptr(&scope->map, key);
    if (def) return error_nn(sem, error_node, def, "Attempting to redeclare definition.");

    def = map_get_ptr(&sem->autoimports->map, key);
    if (def) return error_nn(sem, error_node, def, "Attempting to shadow name that is auto-imported.");

    map_add(&scope->map, key, val);
    return RESULT_OK;
}

// This marks the scope as immutable.
static Void scope_seal (Sem *sem, Scope *scope) {
    scope->owner->flags |= AST_IS_SEALED_SCOPE;

    if (scope->owner->tag == AST_FILE) { // Handle any AstScopeMod.
        tmem_new(tm);
        AstFlags flag = 0;
        SemIter *it = sem_iter_new(tm, sem, &cast(AstFile*, scope->owner)->statements);
        while (sem_iter_next(it)) {
            it->node->flags |= flag;
            if (it->node->tag == AST_SCOPE_MOD) flag = cast(AstScopeMod*, it->node)->is_public ? 0 : AST_IS_PRIVATE;
        }
    }
}

static U64 get_namegen_offset (Ast *namegen) {
    switch (namegen->tag) {
    case AST_EMBED:  { SrcPos p = namegen->pos; return p.offset + p.length; }
    case AST_IF_CT:  { SrcPos p = cast(AstIfCt*, namegen)->cond->pos; return p.offset + p.length; }
    case AST_IMPORT: { SrcPos p = cast(AstImport*, namegen)->path_gen->pos; return p.offset + p.length; }
    default: badpath;
    }
}

// The Scope.namegens array holds source code offsets of nodes which
// can codegen name bindings: if:ct, embed, ... This array is used by
// scope_lookup_inside_out() and controlled by the push/pop_namegen()
// functions that keep it sorted from smallest to biggest offset.
static Void push_namegen (Ast *namegen) {
    Scope *scope = get_scope(namegen);
    U64 offset = get_namegen_offset(namegen);

    while (true) {
        assert_dbg(! (scope->owner->flags & AST_IS_SEALED_SCOPE));
        U64 idx = array_find(&scope->namegens, offset < IT);
        array_insert(&scope->namegens, offset, min(idx, scope->namegens.count));
        if (scope->owner->tag != AST_CODE_GEN) break;
        offset = cast(AstCodeGen*, scope->owner)->origin->pos.offset;
        scope  = scope->parent;
    }
}

static Void pop_namegen (Sem *sem, Ast *namegen) {
    Scope *scope = get_scope(namegen);
    U64 offset = get_namegen_offset(namegen);

    while (true) {
        array_find_remove(&scope->namegens, IT == offset);
        if (scope->namegens.count == 0) scope_seal(sem, scope);
        if (scope->owner->tag != AST_CODE_GEN) break;
        offset = cast(AstCodeGen*, scope->owner)->origin->pos.offset;
        scope  = scope->parent;
    }
}

static Ast *alloc_caller_struct (Sem *sem, Ast *caller) {
    tmem_new(tm);

    SrcPos *p    = &caller->pos;
    AstFn *fn    = cast(AstFn*, scope_get_ancestor(get_scope(caller), AST_FN)->owner);
    AString astr = astr_new(tm);

    astr_push_fmt(&astr, "CallerInfo{ line=%lu, offset=%lu, name=\"%.*s\", file_path=", p->first_line, p->offset, STR(*fn->name));
    astr_push_str_quoted(&astr, *get_file(caller)->path);
    astr_push_cstr(&astr, " }");

    AstCodeGen *gen = par_parse_codegen(sem->parser, astr_to_str(&astr), caller, get_file(caller), AST_LEVEL_EXPR);
    add_to_check_list(sem, cast(Ast*, gen), get_scope(caller));

    return array_get(&gen->children, 0);
}

static Void implicit_cast (Sem *sem, Ast **pn, Ast *to, Type *to_type) {
    Ast *n = *pn;

    if (to_type->tag == TYPE_TUPLE) {
        print_stack_trace();
        sem_print_node_out(sem, *pn);
    }

    assert_dbg(! is_tvar_type(to_type));
    assert_dbg(! (n->flags & AST_IN_POLY_ARG_POSITION));
    assert_dbg((n != sem->match.dummy1) && (n != sem->match.dummy2));

    if (sem->call_check.ongoing) {
        assert_dbg((to != sem->match.dummy1) && (to != sem->match.dummy2));
        PendingCast *found = array_find_ref(&sem->call_check.casts, (IT->to == to) && (IT->from == pn));
        if (! found) array_push_lit(&sem->call_check.casts, .to=to, .to_type=to_type, .from=pn);
    } else if ((n->flags & AST_EVALED) && (get_type(n)->tag == TYPE_INT) && (to_type->flags & TYPE_IS_PRIMITIVE)) {
        set_type(n, to_type);
    } else {
        Ast *c = ast_alloc(sem->mem, AST_CAST, 0);
        c->pos = n->pos;
        c->flags |= (n->flags & AST_MUST_EVAL);
        cast(AstCast*, c)->expr = n;
        cast(AstCast*, c)->implicit = true;
        add_to_check_list(sem, c, get_scope(n));

        if (to == sem->match.dummy1 || to == sem->match.dummy2) {
            assert_dbg(! is_tvar_untyped_lit(to_type));
            set_type(c, to_type);
        } else {
            cast(AstCast*, c)->to = to;
        }

        *pn = c;
        sem->match.applied_cast = true;
    }
}

static Void log_type (Sem *sem, AString *astr, Type *type) {
    if (! type) {
        astr_push_cstr(astr, "$");
        return;
    } else if (type->flags & TYPE_VISITED) {
        switch (type->tag) {
        #define X(TAG, NAME, ...) case TAG: astr_push_cstr(astr, #NAME); break;
            EACH_TYPE(X);
        #undef X
        }
        return;
    }

    type->flags |= TYPE_VISITED;

    if (type->flags & TYPE_IS_DISTINCT) {
        AstTypeDistinct *n = cast(AstTypeDistinct*, map_get_assert(&sem->type_def, type->id));
        astr_push_fmt(astr, "%.*s (distinct ", STR(*n->name));
    }

    switch (type->tag) {
    case TYPE_BOOL:  astr_push_cstr(astr, "Bool"); break;
    case TYPE_VOID:  astr_push_cstr(astr, "Void"); break;
    case TYPE_FLOAT: astr_push_fmt(astr, "F%i", cast(TypeFloat*, type)->bitwidth); break;

    case TYPE_VAR: {
        Ast *n = cast(TypeVar*, type)->node;

        if (n->tag == AST_FN_POLY) {
            IString *name = cast(AstFnPoly*, n)->name;
            astr_push_fmt(astr, "%.*s", STR(*name));
        } else if (n->tag == AST_CALL) {
            IString *name = get_name(cast(AstCall*, n)->sem_edge);
            astr_push_fmt(astr, "%.*s(", STR(*name));
            array_iter (arg, &cast(AstCall*, n)->args) {
                log_type(sem, astr, get_type(arg));
                if (! ARRAY_ITER_DONE) astr_push_cstr(astr, ", ");
            }
            astr_push_byte(astr, ')');
        } else if (is_tvar_type(type)) {
            IString *name = get_name(cast(TypeVar*, type)->node);
            astr_push_fmt(astr, "$%.*s", STR(*name));
        } else {
            astr_push_cstr(astr, "$");
        }
    } break;

    case TYPE_MISC: {
        astr_push_cstr(astr, "Type(");
        astr_push_cstr(astr, ast_tag_to_cstr[cast(TypeMisc*, type)->node->tag]);
        astr_push_byte(astr, ')');
    } break;

    case TYPE_ENUM: {
        AstEnum *n = cast(TypeEnum*, type)->node;
        astr_push_fmt(astr, "%.*s", STR(*n->name));
    } break;

    case TYPE_STRUCT: {
        Ast *node = cast(Ast*, cast(TypeStruct*, type)->node);

        if (node->flags & AST_IS_POLYMORPH_INSTANCE) {
            MonoInfo *info = sem_get_mono_info(sem, node);
            IString *name = get_name(info->poly_info->node);
            astr_push_fmt(astr, "%.*s(", STR(*name));

            array_iter (b, &info->type_map, *) {
                log_type(sem, astr, b->t);
                if (! ARRAY_ITER_DONE) astr_push_cstr(astr, ", ");
            }

            astr_push_byte(astr, ')');
        } else {
            IString *name = cast(TypeStruct*, type)->node->name;
            astr_push_fmt(astr, "%.*s", STR(*name));
        }
    } break;

    case TYPE_ARRAY: {
        TypeArray *t = cast(TypeArray*, type);
        astr_push_fmt(astr, "[%lu]", t->length);
        log_type(sem, astr, t->element);
    } break;

    case TYPE_POINTER: {
        TypePointer *t = cast(TypePointer*, type);
        astr_push_byte(astr, '~');
        log_type(sem, astr, t->pointee);
    } break;

    case TYPE_INT: {
        TypeInt *t = cast(TypeInt*, type);
        astr_push_fmt(astr, "%c%i", (t->is_signed ? 'I' : 'U'), t->bitwidth);
    } break;

    case TYPE_TUPLE: {
        AstTuple *n = cast(TypeTuple*, type)->node;
        astr_push_byte(astr, '(');

        array_iter (f, &n->fields) {
            if (f->tag == AST_TUPLE_FIELD) {
                astr_push_str(astr, *cast(AstTupleField*, f)->name);
                astr_push_cstr(astr, ": ");
            }

            log_type(sem, astr, get_type(f));
            if (! ARRAY_ITER_DONE) astr_push_cstr(astr, ", ");
        }

        astr_push_byte(astr, ')');
    } break;

    case TYPE_FN: {
        AstBaseFn *n = cast(TypeFn*, type)->node;
        astr_push_cstr(astr, "Fn (");

        array_iter (n, &n->inputs) {
            log_type(sem, astr, get_type(n));
            if (! ARRAY_ITER_DONE) astr_push_cstr(astr, ", ");
        }

        astr_push_byte(astr, ')');
        if (n->output) { astr_push_cstr(astr, " -> "); log_type(sem, astr, get_type(n->output)); }
    } break;
    }

    if (type->flags & TYPE_IS_DISTINCT) astr_push_byte(astr, ')');
    type->flags &= ~TYPE_VISITED;
}

static Void log_node_no_flush (Sem *sem, SrcLog *slog, AString *astr, Ast *node) {
    AstFile *file = get_file(node);
    if (! file) return;

    Scope *gen_scope = scope_get_ancestor(get_scope(node), AST_CODE_GEN);

    if (gen_scope && (file == sem->codegen_file)) {
        U64 margin = slog_default_config->left_margin;
        Ast *origin = cast(AstCodeGen*, gen_scope->owner)->origin;
        AstFile *origin_file = get_file(origin);
        astr_push_fmt(
            astr,
            "%*s" TERM_RED("CODEGEN") ": (byte=%lu, line=%lu, file=\"%.*s\")\n",
            cast(Int,margin), "",
            origin->pos.offset,
            origin->pos.first_line,
            STR(*origin_file->path)
        );
    }

    slog_add_src(slog, cast(Ast*, file)->id, *file->path, file->content);
    slog_add_pos(slog, cast(Ast*, file)->id, ast_trimmed_pos(sem->interns, node));
}

static Void log_node (Sem *sem, AString *astr, Ast *node) {
    tmem_new(tm);
    SrcLog *slog = slog_new(tm, slog_default_config);
    log_node_no_flush(sem, slog, astr, node);
    slog_flush(slog, astr);
}

static Void log_nodes (Sem *sem, AString *astr, Ast *n1, Ast *n2) {
    tmem_new(tm);
    SrcLog *slog = slog_new(tm, slog_default_config);
    log_node_no_flush(sem, slog, astr, n1);
    log_node_no_flush(sem, slog, astr, n2);
    slog_flush(slog, astr);
}

static Void log_poly_trace (Sem *sem, AString *astr, Ast *node) {
    Scope *scope = scope_of_instance(node);
    if (! scope) return;

    astr_push_cstr(astr, "\nPolymorph instantiation trace:\n\n");

    U64 margin = slog_default_config->left_margin;

    while (scope) {
        MonoInfo *info = sem_get_mono_info(sem, scope->owner);
        AstFile *file  = get_file(info->instantiator);

        astr_push_fmt(astr, "%*s" TERM_RED("FILE") ": (byte=%lu, line=%lu, file=", cast(Int,margin), "", info->instantiator->pos.offset, info->instantiator->pos.first_line);
        astr_push_str_quoted(astr, *file->path);

        if (info->type_map.count) {
            astr_push_byte(astr, ' ');
            array_iter (x, &info->type_map, *) {
                IString *n = get_name(x->var->node);
                astr_push_fmt(astr, "%.*s=", STR(*n));
                log_type(sem, astr, x->t);
                if (! ARRAY_ITER_DONE) astr_push_cstr(astr, ", ");
            }
        }

        astr_push_cstr(astr, ")");
        scope = scope_of_instance(info->instantiator);
        if (scope) astr_push_byte(astr, '\n');
    }

    astr_push_byte(astr, '\n');
}

Void sem_print_node (Sem *sem, AString *astr, Ast *node) {
    U64 margin = slog_default_config->left_margin;
    astr_push_fmt(astr, "%*s" TERM_RED("TAG") ": %s\n", cast(Int,margin), "", ast_tag_to_cstr[node->tag]);
    log_node(sem, astr, node);
}

Void sem_print_node_out (Sem *sem, Ast *node) {
    tmem_new(tm);
    AString a = astr_new(tm);
    sem_print_node(sem, &a, node);
    astr_println(&a);
}

#define NO_ERROR_REPORTING() (sem->match.without_error_reporting || sem->error_count >= MAX_RECORDED_ERRORS)

static Void error_no_progress (Sem *sem) {
    array_iter (n, &sem->check_list) {
        if (!get_type(n) && ((n->tag == AST_VAR_DEF) || (n->tag == AST_TYPE_ALIAS) || (n->tag == AST_TYPE_DISTINCT))) {
            check_for_invalid_cycle(sem, n->tag, n);
        }
    }

    array_iter (n, &sem->check_list) {
        Ast *d = get_target(n);
        if (d) continue;

        switch (n->tag) {
        case AST_DOT:           if (!(n->flags & AST_WAITING_FOR_SCOPE_SEAL) && get_type(cast(AstDot*, n)->lhs)) { error_n(sem, n, "Reference to undeclared member."); sem_panic(sem); } break;
        case AST_IDENT:         if (! (n->flags & AST_WAITING_FOR_SCOPE_SEAL)) { error_n(sem, n, "Reference to undeclared identifier."); sem_panic(sem); } break;
        case AST_ENUM_LITERAL:  if (get_type(n)->tag == TYPE_ENUM) { error_nn(sem, n, cast(Ast*, cast(TypeEnum*, get_type(n))->node), "Reference to undeclared enum member."); sem_panic(sem); } break;
        case AST_IMPORT_CONFIG: if (! cast(AstImportConfig*, n)->init) { error_n(sem, n, "Reference to undeclared identifer."); sem_panic(sem); } break;
        default: break;
        }
    }

    array_iter (n, &sem->check_list) {
        Type *t = get_type(n);
        if (t && is_tvar_untyped_lit(t)) { error_n(sem, n, "Unbound literal."); sem_panic(sem); }
    }

    { // Unkown reason:
        sem_msg(msg, LOG_ERROR);
        astr_push_fmt(msg, "Unable to check the following nodes:\n\n");
        array_iter (n, &sem->check_list) log_node(sem, msg, n);
        sem_panic(sem);
    }
}

Fmt(3, 4)
static Result error_n (Sem *sem, Ast *n, CString fmt, ...) {
    if (NO_ERROR_REPORTING()) return RESULT_ERROR;
    sem_msg(msg, LOG_ERROR);
    astr_push_fmt_vam(msg, fmt);
    astr_push_byte(msg, '\n');
    astr_push_byte(msg, '\n');
    log_node(sem, msg, n);
    log_poly_trace(sem, msg, n);
    sem->error_count++;
    return RESULT_ERROR;
}

Fmt(4, 5)
static Result error_nn (Sem *sem, Ast *n1, Ast *n2, CString fmt, ...) {
    if (NO_ERROR_REPORTING()) return RESULT_ERROR;
    sem_msg(msg, LOG_ERROR);
    astr_push_fmt_vam(msg, fmt);
    astr_push_byte(msg, '\n');
    astr_push_byte(msg, '\n');
    log_nodes(sem, msg, n1, n2);
    log_poly_trace(sem, msg, n2);
    sem->error_count++;
    return RESULT_ERROR;
}

Fmt(4, 5)
static Result error_nt (Sem *sem, Ast *n, Type *t, CString fmt, ...) {
    if (NO_ERROR_REPORTING()) return RESULT_ERROR;
    sem_msg(msg, LOG_ERROR);
    astr_push_cstr(msg, "Got type " TERM_START_RED);
    log_type(sem, msg, t);
    astr_push_cstr(msg, TERM_END ", ");
    astr_push_fmt_vam(msg, fmt);
    astr_push_byte(msg, '\n');
    astr_push_byte(msg, '\n');
    log_node(sem, msg, n);
    log_poly_trace(sem, msg, n);
    sem->error_count++;
    return RESULT_ERROR;
}

static Result error_unbound_polyvars (Sem *sem, Ast *caller, Ast *target) {
    assert_dbg(sem->call_check.ongoing);
    if (NO_ERROR_REPORTING()) return RESULT_ERROR;

    tmem_new(tm);
    sem_msg(msg, LOG_ERROR);
    SrcLog *slog = slog_new(tm, slog_default_config);

    astr_push_cstr(msg, "Unable to bind all poly variables.\n\n");
    log_nodes(sem, msg, caller, target);

    astr_push_cstr(msg, "Here are the unbound variables:\n\n");
    array_iter (info, &sem->call_check.mono_infos) {
        array_iter (x, &info->type_map, *)  if (!x->t || is_tvar_type(x->t)) log_node_no_flush(sem, slog, msg, get_type_constructor(cast(Type*, x->var)));
        array_iter (x, &info->value_map, *) if (! x->val) log_node_no_flush(sem, slog, msg, get_type_constructor(cast(Type*, x->var)));
    }

    slog_flush(slog, msg);
    log_poly_trace(sem, msg, caller);
    sem->error_count++;
    return RESULT_ERROR;
}

#define ERROR_MATCH() (error_match(sem, n1, n2, t1, t2))

static Result error_match (Sem *sem, Ast *n1, Ast *n2, Type *t1, Type *t2) {
    if (NO_ERROR_REPORTING()) return RESULT_ERROR;

    MatchPair top = sem->match.top_pair;
    sem_msg(msg, LOG_ERROR);

    astr_push_cstr(msg, "Mismatch " TERM_START_CYAN);
    log_type(sem, msg, top.t1);
    astr_push_cstr(msg, TERM_END " vs " TERM_START_CYAN);
    log_type(sem, msg, top.t2);

    astr_push_cstr(msg, TERM_END ".\n\n");
    log_nodes(sem, msg, top.n1, top.n2);

    if (!(top.t1 == t1 && top.t2 == t2) &&
        !(top.t1 == t2 && top.t2 == t1) &&
        (t1 != sem->core_types.type_any) &&
        (t2 != sem->core_types.type_any)
    ) {
        astr_push_cstr(msg, "\nSpecifically: " TERM_START_CYAN);
        log_type(sem, msg, t1);
        astr_push_cstr(msg, TERM_END " vs " TERM_START_CYAN);
        log_type(sem, msg, t2);
        astr_push_cstr(msg, TERM_END ".\n");
    }

    if (n1 && !(top.n1 == n1 && top.n2 == n2) && !(top.n1 == n2 && top.n2 == n1)) {
        astr_push_byte(msg, '\n');
        log_nodes(sem, msg, n1, n2);
    }

    log_poly_trace(sem, msg, top.n2);
    sem->error_count++;
    return RESULT_ERROR;
}

static MonoInfo *alloc_mono_info (Sem *sem, Ast *polymorph, Ast *instantiator) {
    assert_dbg(polymorph->flags & (AST_IS_POLYMORPH | AST_IS_MACRO));

    MonoInfo *info = array_pop_or(&sem->call_check.mono_infos_pool, 0);

    if (info) {
        info->type_map.count     = 0;
        info->value_map.count    = 0;
        info->instance_map.count = 0;
    } else {
        info = mem_new(sem->mem, MonoInfo);
        array_init(&info->type_map, sem->mem);
        array_init(&info->value_map, sem->mem);
        array_init(&info->instance_map, sem->mem);
    }

    info->poly_info    = get_poly_info(sem, polymorph);
    info->instantiator = instantiator;
    array_push(&sem->call_check.mono_infos, info);

    array_iter (n, &info->poly_info->polyargs) {
        TypeVar *t = cast(TypeVar*, get_type(n));
        if (n->tag == AST_ARG_POLY_TYPE) array_push_lit(&info->type_map, .var=t);
        else                             array_push_lit(&info->value_map, .var=t);
    }

    return info;
}

static PolyInfo *alloc_poly_info (Sem *sem, Ast *polymorph) {
    PolyInfo *info = mem_new(sem->mem, PolyInfo);

    if (polymorph->tag == AST_STRUCT_POLY) {
        info->args = &cast(AstStructPoly*, polymorph)->args;
    } else {
        assert_dbg(ast_get_base_flags[polymorph->tag] & AST_BASE_FN);
        info->args = &cast(AstBaseFn*, polymorph)->inputs;
    }

    info->node = polymorph;
    array_init(&info->polyargs, sem->mem);
    array_init(&info->instances, sem->mem);
    map_add(&sem->poly_infos, polymorph->id, info);
    return info;
}

static Void bind_simple_untyped_lit (Sem *sem, Type *t) {
    assert_dbg(is_tvar_ptr(t) || is_tvar_array_lit(t) || is_tvar_tuple_lit(t));

    if (sem->call_check.ongoing) {
        array_push(&sem->call_check.simple_untyped_lits, t);
    } else {
        t->flags &= ~TYPE_IS_UNTYPED_LIT;
    }
}

static Void bind_simple_untyped_lit_recursively (Sem *sem, Type *t) {
    if (is_tvar_ptr(t)) {
        t->flags &= ~TYPE_IS_UNTYPED_LIT;
        bind_simple_untyped_lit_recursively(sem, cast(TypePointer*, t)->pointee);
    } else if (is_tvar_array_lit(t)) {
        t->flags &= ~TYPE_IS_UNTYPED_LIT;
        AstArrayLiteral *lit = cast(AstArrayLiteral*, cast(TypeArray*, t)->node);
        array_iter (x, &lit->inits) bind_simple_untyped_lit_recursively(sem, get_type(x));
    } else if (is_tvar_tuple_lit(t)) {
        t->flags &= ~TYPE_IS_UNTYPED_LIT;
        array_iter (x, &cast(TypeTuple*, t)->node->fields) bind_simple_untyped_lit_recursively(sem, get_type(x));
    }
}

// The following wrappers around match() use the nomenclature:
//
//     c (constraint): Assert argument is a type expression.
//     v (value):      Assert argument is a value expression.
//     n (node):       Use argument type whether it's a value or type expression.
//     t (type):       Argument is a Type and a dummy node is used to call match().
//
static Result match_vv (Sem *sem, Ast **v1, Ast **v2) { return match(sem, v1, v2, try_get_type_v(*v1), try_get_type_v(*v2), SUBTYPE_ANY_WAY); }
static Result match_nn (Sem *sem, Ast *n1, Ast *n2)   { return match(sem, &n1, &n2, try_get_type(n1), try_get_type(n2), SUBTYPE_TWO_WAY); }
static Result match_nv (Sem *sem, Ast *n, Ast **v)    { return match(sem, &n, v, try_get_type(n), try_get_type_v(*v), SUBTYPE_ONE_WAY); }
static Result match_nc (Sem *sem, Ast *n, Ast *c)     { return match(sem, &n, &c, try_get_type(n), try_get_type_t(c), SUBTYPE_TWO_WAY); }
static Result match_tt (Sem *sem, Type *t1, Type *t2) { return match(sem, &sem->match.dummy1, &sem->match.dummy2, t1, t2, SUBTYPE_TWO_WAY); }
static Result match_tv (Sem *sem, Type *t, Ast **v)   { return match(sem, &sem->match.dummy1, v, t, try_get_type_v(*v), SUBTYPE_ONE_WAY); }

static Result match_values (Sem *sem, Ast **pn1, Ast **pn2) {
    assert_dbg(sem->call_check.ongoing);
    U64 c = sem->call_check.values_to_match.count;
    try(match_vv(sem, pn1, pn2));
    if (c == sem->call_check.values_to_match.count) array_push_lit(&sem->call_check.values_to_match, .a=*pn1, .b=*pn2);
    return RESULT_OK;
}

// Match a polymorphic function to the variable it is
// being assigned to via the assignment operator or
// by being passed as argument to a fn:
//
//     fn foo (x: $T) -> T {}
//     x = foo;
//         ^^^-------------------- assignment via identifier
//     bar(fn (x: $T) {});
//         ^^^^^^^^^^^^^---------- assignment via fn literal
//
static Result match_tvar_fn (Sem *sem, Ast *n1, Ast *n2, Type *t1, Type *t2) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(is_tvar_fn(t1));

    if (t2->tag != TYPE_FN) return ERROR_MATCH();

    AstBaseFn *fn = cast(TypeFn*, t2)->node;
    Ast *instantiator = cast(TypeVar*, t1)->node;
    assert_dbg(instantiator->tag == AST_IDENT || instantiator->tag == AST_FN_POLY);

    if (! sem->call_check.ongoing) {
        ArrayAst a1 = { .data=cast(Ast**, &fn), .count=1, .capacity=1 };
        ArrayAst a2 = { .data=&instantiator, .count=1, .capacity=1 };
        return check_call(sem, cast(Ast*, fn), &a1, instantiator, &a2, false);
    }

    AstBaseFn *poly_fn = (instantiator->tag == AST_FN_POLY) ? cast(AstBaseFn*, instantiator ): cast(AstBaseFn*, get_target(instantiator));
    if ((poly_fn->inputs.count != fn->inputs.count) || (!!poly_fn->output != !!fn->output)) return ERROR_MATCH();

    MonoInfo *prev_m1 = sem->call_check.i1;
    sem->call_check.i1 = array_find_get(&sem->call_check.mono_infos, IT->instantiator == instantiator);
    if (! sem->call_check.i1) sem->call_check.i1 = alloc_mono_info(sem, cast(Ast*, poly_fn), instantiator);

    reach(r);
    #define RETURN(R) { reached(r); sem->call_check.i1 = prev_m1; return R; }

    array_iter (a, &poly_fn->inputs) try(match_nn(sem, a, array_get(&fn->inputs, ARRAY_IDX)), RETURN(R));
    if (fn->output) try(match_nn(sem, poly_fn->output, fn->output), RETURN(R));

    RETURN(RESULT_OK);
    #undef RETURN
}

// Array literals not in standalone position have a variable
// type so that we can implicitly cast it's inits to the type
// of the expression that the array literal is being matched
// against. For example, here the 42 and 420 literals cast to
// I32 instead of being the default U64 type:
//
//     var x: [2]I32 = [42, 420];
//                     ^^^^^^^^^---- tvar_array_lit
//
static Result match_tvar_array_lit (Sem *sem, Ast *n1, Ast **pn2, Type *t1, Type *t2) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(is_tvar_array_lit(t2));

    Ast *n2 = *pn2;
    AstArrayLiteral *lit = cast(AstArrayLiteral*, cast(TypeArray*, t2)->node);
    Ast **init0 = array_ref(&lit->inits, 0);

    if (t1 == sem->core_types.type_any) {
        implicit_cast(sem, pn2, n1, t1);
        bind_simple_untyped_lit(sem, t2);
        return RESULT_OK;
    }

    if (is_tvar_array_lit(t1)) {
        AstArrayLiteral *lit1 = cast(AstArrayLiteral*, cast(TypeArray*, t1)->node);
        if (lit->inits.count != lit1->inits.count) return ERROR_MATCH();
        try(match_vv(sem, array_ref(&lit1->inits, 0), init0));
        bind_simple_untyped_lit(sem, t1);
        bind_simple_untyped_lit(sem, t2);
        return RESULT_OK;
    }

    if (is_tvar_call(t1)) {
        AstCall *call = cast(AstCall*, cast(TypeVar*, t1)->node);
        if (get_type(call->lhs) != sem->core_types.type_slice) return ERROR_MATCH();
        Ast *slice_arg = array_get(&call->args, 0);
        try(match_nv(sem, slice_arg, init0));
        implicit_cast(sem, pn2, n1, t1);
        bind_simple_untyped_lit(sem, t2);
        return RESULT_OK;
    }

    if (t1->tag == TYPE_ARRAY) {
        TypeArray *a = cast(TypeArray*, t1);
        if (a->length != lit->inits.count) return ERROR_MATCH();

        if (a->node->tag == AST_ARRAY_TYPE) {
            try(match_nv(sem, cast(AstArrayType*, a->node)->element, init0));
        } else {
            try(match_tv(sem, a->element, init0));
        }

        bind_simple_untyped_lit(sem, t2);
        return RESULT_OK;
    }

    if (t1->tag == TYPE_STRUCT) {
        MonoInfo *info = sem_get_mono_info(sem, cast(Ast*, cast(TypeStruct*, t1)->node));
        if (!info || get_type(info->poly_info->node) != sem->core_types.type_slice) return ERROR_MATCH();
        assert_dbg(info->instantiator->tag == AST_CALL);
        AstCall *call = cast(AstCall*, info->instantiator);
        Ast *slice_arg = array_get(&call->args, 0);
        try(match_nv(sem, slice_arg, init0));
        implicit_cast(sem, pn2, n1, t1);
        bind_simple_untyped_lit(sem, t2);
        return RESULT_OK;
    }

    return ERROR_MATCH();
}

// Tuple literals not in standalone position have variable
// type for the same reason outlined in match_tvar_array_lit().
static Result match_tvar_tuple_lit (Sem *sem, Ast *n1, Ast **pn2, Type *t1, Type *t2) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(is_tvar_tuple_lit(t2));

    Ast *n2 = *pn2;
    AstTuple *lit = cast(TypeTuple*, t2)->node;

    if (t1 == sem->core_types.type_any) {
        implicit_cast(sem, pn2, n1, t1);
        bind_simple_untyped_lit(sem, t2);
        return RESULT_OK;
    }

    if (t1->tag == TYPE_STRUCT) {
        MonoInfo *info = sem_get_mono_info(sem, cast(Ast*, cast(TypeStruct*, t1)->node));
        if (!info || get_type(info->poly_info->node) != sem->core_types.type_slice) return ERROR_MATCH();
        if (array_ref(&info->type_map, 0)->t != sem->core_types.type_any) return ERROR_MATCH();
        AstCall *call = cast(AstCall*, info->instantiator);
        Ast *slice_arg = array_get(&call->args, 0);
        array_iter (f, &lit->fields, *) try(match_nv(sem, slice_arg, f));
        implicit_cast(sem, pn2, n1, t1);
        bind_simple_untyped_lit(sem, t2);
        return RESULT_OK;
    }

    if (is_tvar_tuple_lit(t1)) {
        try(match_tuples(sem, cast(TypeTuple*, t1)->node, lit, t1, t2, SUBTYPE_ANY_WAY));
        bind_simple_untyped_lit(sem, t1);
        bind_simple_untyped_lit(sem, t2);
        return RESULT_OK;
    }

    if (t1->tag == TYPE_TUPLE) {
        try(match_tuples(sem, cast(TypeTuple*, t1)->node, lit, t1, t2, SUBTYPE_ONE_WAY));
        bind_simple_untyped_lit(sem, t2);
        return RESULT_OK;
    }

    return ERROR_MATCH();
}

// This is a tvar assigned to an address_of node whose target
// is an untyped lit. This is because we might want the target
// to implicitly cast which is not supported via the normal
// code path in match_structural() and match_substructural().
//
//     var x: [2]I32 = ~[42, 420];
//                     ^------------- tvar_ptr
//
static Result match_tvar_ptr (Sem *sem, Ast *n1, Ast *n2, Type *t1, Type *t2) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(is_tvar_ptr(t2));

    if (is_tvar_ptr(t1)) {
        AstBaseUnary *c1 = cast(AstBaseUnary*, cast(TypePointer*, t1)->node);
        AstBaseUnary *c2 = cast(AstBaseUnary*, cast(TypePointer*, t2)->node);
        try(match_vv(sem, &c1->op, &c2->op));
        bind_simple_untyped_lit(sem, t1);
        bind_simple_untyped_lit(sem, t2);
        return RESULT_OK;
    }

    if (t1->tag == TYPE_POINTER) {
        Ast *c1 = cast(TypePointer*, t1)->node;
        AstBaseUnary *c2 = cast(AstBaseUnary*, cast(TypePointer*, t2)->node);

        if (c1->tag == AST_ADDRESS_OF) {
            match_nv(sem, cast(AstBaseUnary*, c1)->op, &c2->op);
        } else {
            match_tv(sem, cast(TypePointer*, t1)->pointee, &c2->op);
        }

        bind_simple_untyped_lit(sem, t2);
        return RESULT_OK;
    }

    return ERROR_MATCH();
}

// This is a type variable assigned to a struct call whose
// arguments contain type variables:
//
//     struct Foo ($T) {}
//
//     fn foo (x: Foo($T)) {}
//                ^^^^^^^------ tvar_call
//
// Instead of instantiating a struct with type vars, we assign
// a type variable to the invocation itself and match against
// it structurally.
static Result match_tvar_call (Sem *sem, Ast *n1, Ast **pn2, Type *t1, Type *t2) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(is_tvar_call(t1));
    assert_dbg(cast(TypeVar*, t1)->node->tag == AST_CALL);

    Ast *n2 = *pn2;
    AstCall *call = cast(AstCall*, cast(TypeVar*, t1)->node);
    Ast *target = get_target(call->lhs);
    ArrayAst *defs = &cast(AstStructPoly*, target)->args;

    if (is_tvar_array_lit(t2))   return match_tvar_array_lit(sem, n1, pn2, t1, t2);
    if (is_tvar_untyped_lit(t2)) return (n2->tag != AST_STRUCT_LITERAL) ? ERROR_MATCH() : match_tvar_untyped_lit(sem, n1, n2, t1, t2);

    if (t2->tag == TYPE_ARRAY) {
        if (get_type(target) != sem->core_types.type_slice) return ERROR_MATCH();
        Ast *arg = array_get(&call->args, 0);
        Result r = match_tt(sem, get_type(arg), cast(TypeArray*, t2)->element);
        if (r == RESULT_OK) implicit_cast(sem, pn2, n1, t1);
        return r;
    }

    if (is_tvar_call(t2)) {
        AstCall *call2 = cast(AstCall*, cast(TypeVar*, t2)->node);
        if (target != get_target(call2->lhs)) return ERROR_MATCH();

        array_iter (a, &call->args, *) {
            Ast **b = array_ref(&call2->args, ARRAY_IDX);
            Bool v = (AST_ARG_POLY_VALUE == array_get(defs, ARRAY_IDX)->tag);
            try(v ? match_values(sem, a, b) : match_nn(sem, *a, *b));
        }

        return RESULT_OK;
    }

    if (t2->tag == TYPE_STRUCT) {
        Ast *poly = get_target(call->lhs);
        MonoInfo *info = sem_get_mono_info(sem, cast(Ast*, cast(TypeStruct*, t2)->node));
        ArrayAst *args = &cast(AstCall*, info->instantiator)->args;

        if (!info || (info->poly_info->node != poly)) return ERROR_MATCH();

        array_iter (a, &call->args, *) {
            Ast **b = array_ref(args, ARRAY_IDX);
            Bool v = (AST_ARG_POLY_VALUE == array_get(defs, ARRAY_IDX)->tag);
            try(v ? match_values(sem, a, b) : match_nn(sem, *a, *b));
        }

        return RESULT_OK;
    }

    return ERROR_MATCH();
}

// Untyped literals are values that will obtain a type
// from the thing they are being matched against:
//
//    var x: Foo = .foo;          // Anonymous enum literal.
//    var x: Foo = {};            // Anonymous struct literal.
//    var x: Foo = .cast(foo);    // Ast *cast.
//    var x: Foo = .bitcast(foo); // Ast *bitcast.
//
// Note that pointer, array and tuple literals can also
// have the TYPE_IS_UNTYPED_LIT flag but those are both
// matched and bound using different functions.
static Result match_tvar_untyped_lit (Sem *sem, Ast *n1, Ast *n2, Type *t1, Type *t2) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(is_tvar_untyped_lit(t2));

    if (is_tvar_untyped_lit(t1)) return ERROR_MATCH();

    Ast *lit = cast(TypeVar*, t2)->node;
    set_type(lit, t1);

    if (sem->call_check.ongoing) {
        UntypedLit *found = array_find_ref(&sem->call_check.untyped_lits, IT->lit == lit);
        if (! found) array_push_lit(&sem->call_check.untyped_lits, .lit=lit, .bind=n1, .tvar=t2);
    }

    return RESULT_OK;
}

static Ast **get_tvar_value (MonoInfo *info, TypeVar *var) {
    assert_dbg(is_tvar_value(cast(Type*, var)));
    return info ? array_find_ref(&info->value_map, IT->var == var)->val : 0;
}

static Void set_tvar_value (MonoInfo *info, TypeVar *var, Ast **val) {
    assert_dbg(is_tvar_value(cast(Type*, var)));
    ValueInstance *e = array_find_ref(&info->value_map, IT->var == var);
    e->val = val;
}

// Match a node against a polymorphic value or code argument:
//
//     macro foo (x$: I32, y: $) {}
//                ^^-------^^^^-------- tvar_value
//
static Result match_tvar_value (Sem *sem, Ast **pn1, Ast **pn2, Type *t1, Type *t2) {
    assert_dbg(is_tvar_value(t1));
    assert_dbg(sem->match.ongoing && sem->call_check.ongoing);

    Ast *n1 = *pn1;
    Ast *n2 = *pn2;

    if (cast(TypeVar*, t1)->node->tag == AST_ARG_POLY_CODE) {
        if (n2->tag != AST_CALL_MACRO_ARG) return ERROR_MATCH();
        set_tvar_value(sem->call_check.i1, cast(TypeVar*, t1), pn2);
        return RESULT_OK;
    }

    Type *base_t1 = get_type(cast(AstArgPolyValue*, cast(TypeVar*, t1)->node)->constraint);
    Type *base_t2 = is_tvar_value(t2) ? get_type(cast(AstArgPolyValue*, cast(TypeVar*, t2)->node)->constraint) : t2;

    try(match(sem, pn1, pn2, base_t1, base_t2, SUBTYPE_ANY_WAY));

    Ast **bind1 = get_tvar_value(sem->call_check.i1, cast(TypeVar*, t1));
    Ast **bind2 = is_tvar_value(t2) ? get_tvar_value(sem->call_check.i2, cast(TypeVar*, t2)) : pn2;

    if (!bind1 && !bind2) {
        sem->call_check.bound_var_to_var = true;
    } else if (! bind1) {
        try((get_type(*bind2)->flags & TYPE_IS_PRIMITIVE) ? eval(sem, *bind2) : can_eval(sem, *bind2, true));
        set_tvar_value(sem->call_check.i1, cast(TypeVar*, t1), bind2);
        sem->call_check.bound_var_to_val = true;
    } else if (! bind2) {
        try((get_type(*bind1)->flags & TYPE_IS_PRIMITIVE) ? eval(sem, *bind1) : can_eval(sem, *bind1, true));
        set_tvar_value(sem->call_check.i2, cast(TypeVar*, t2), bind1);
        sem->call_check.bound_var_to_val = true;
    } else {
        try((get_type(*bind1)->flags & TYPE_IS_PRIMITIVE) ? eval(sem, *bind1) : can_eval(sem, *bind1, true));
        try((get_type(*bind2)->flags & TYPE_IS_PRIMITIVE) ? eval(sem, *bind2) : can_eval(sem, *bind2, true));
        array_push_lit(&sem->call_check.values_to_match, .i1=sem->call_check.i1, .i2=sem->call_check.i2, .a=*bind1, .b=*bind2);
    }

    return RESULT_OK;
}

static Type *get_tvar_type (MonoInfo *info, TypeVar *var, MonoInfo **out_info) {
    assert_dbg(is_tvar_type(cast(Type*, var)));
    if (! info) return 0;
    TypeInstance *e = array_find_ref(&info->type_map, IT->var == var);
    if (!e->t || is_tvar_type(e->t)) return 0;
    if (out_info) *out_info = e->i;
    return e->t;
}

static Void set_tvar_type (Sem *sem, MonoInfo *i1, MonoInfo *i2, TypeVar *var, Type *t) {
    assert_dbg(is_tvar_type(cast(Type*, var)));
    TypeInstance *e = array_find_ref(&i1->type_map, IT->var == var);
    e->t   = t;
    e->i   = i2;
    if (is_tvar_type(t)) sem->call_check.bound_var_to_var = true;
    else                 sem->call_check.bound_var_to_val = true;
}

// Match against a polymorphic type argument:
//
//        fn foo ($T, x: $R) {}
//                ^^-----^^------------ tvar_type
//
static Result match_tvar_type (Sem *sem, Ast *n1, Ast *n2, Type *t1, Type *t2) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(is_tvar_type(t1));
    if (t2->tag == TYPE_MISC) return ERROR_MATCH();
    set_tvar_type(sem, sem->call_check.i1, sem->call_check.i2, cast(TypeVar*, t1), t2);
    if (is_tvar_type(t2)) set_tvar_type(sem, sem->call_check.i2, sem->call_check.i1, cast(TypeVar*, t2), t1);
    return RESULT_OK;
}

// This is a type var assigned to a dot expression whose
// left operand is a tvar_type:
//
//     fn f (x: $T, y: x.R) {}
//                     ^^^------------- tvar_dot
//
static Result get_tvar_dot (Sem *sem, MonoInfo *info, TypeVar *tvar, Type **out_type, Ast **out_node) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(is_tvar_dot(cast(Type*, tvar)));

    AstDot *dot = cast(AstDot*, tvar->node);
    Type *lhs = get_type(dot->lhs);

    assert_dbg(is_tvar_type(lhs));

    Type *bind = get_tvar_type(info, cast(TypeVar*, lhs), 0);
    if (! bind) return RESULT_OK;

    Ast *c = (bind->tag == TYPE_STRUCT) ? cast(Ast*, cast(TypeStruct*, bind)->node) :
             (bind->tag == TYPE_ENUM)   ? cast(Ast*, cast(TypeEnum*, bind)->node) :
             0;

    if (! c) return error_nt(sem, dot->lhs, bind, "expected a struct or enum type.");
    Ast *d = scope_lookup_outside_in(sem, get_scope(c), dot->rhs, cast(Ast*, dot));

    if (d) {
        if (out_type) *out_type = try_get_type(d);
        if (out_node) *out_node = d;
        return RESULT_OK;
    } else if (cast(Ast*, dot)->flags & AST_WAITING_FOR_SCOPE_SEAL) {
        return RESULT_DEFER;
    } else {
        return error_nn(sem, cast(Ast*, dot), c, "Reference to undeclared member.");
    }
}

static Result match_tvar (Sem *sem, Ast **pn1, Ast **pn2, Type *t1, Type *t2, Subtype subtype) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(is_tvar(t1) || is_tvar(t2));

    Ast *n1 = *pn1;
    Ast *n2 = *pn2;
    MonoInfo *prev_m1 = sem->call_check.i1;
    MonoInfo *prev_m2 = sem->call_check.i2;

    Result r;

    if (is_tvar_type(t1)) { Type *t = get_tvar_type(sem->call_check.i1, cast(TypeVar*, t1), &sem->call_check.i1); t1 = t ? t : t1; }
    if (is_tvar_type(t2)) { Type *t = get_tvar_type(sem->call_check.i2, cast(TypeVar*, t2), &sem->call_check.i2); t2 = t ? t : t2; }

    if (is_tvar_dot(t1)) try(get_tvar_dot(sem, sem->call_check.i1, cast(TypeVar*, t1), &t1, 0));
    if (is_tvar_dot(t2)) try(get_tvar_dot(sem, sem->call_check.i2, cast(TypeVar*, t2), &t2, 0));

    reach(r);
    #define RETURN(R)   { r = R; goto done; }
    #define RETURN_S(R) { swap(sem->call_check.i1, sem->call_check.i2); RETURN(R); }

    if (is_tvar_dot(t1) || is_tvar_dot(t2)) RETURN(RESULT_OK);
    if (t1 == t2)                           RETURN(RESULT_OK);
    if (!is_tvar(t1) && !is_tvar(t2))       RETURN(match(sem, pn1, pn2, t1, t2, subtype));
    if (is_tvar_type(t1))                   RETURN(match_tvar_type(sem, n1, n2, t1, t2));
    if (is_tvar_type(t2))                   RETURN_S(match_tvar_type(sem, n2, n1, t2, t1));
    if (is_tvar_value(t1))                  RETURN(match_tvar_value(sem, pn1, pn2, t1, t2));
    if (is_tvar_value(t2))                  RETURN_S(match_tvar_value(sem, pn2, pn1, t2, t1));
    if (is_tvar_ptr(t2))                    RETURN(match_tvar_ptr(sem, n1, n2, t1, t2));
    if (is_tvar_ptr(t1))                    RETURN_S(match_tvar_ptr(sem, n2, n1, t2, t1));
    if (is_tvar_call(t1))                   RETURN(match_tvar_call(sem, n1, pn2, t1, t2));
    if (is_tvar_call(t2))                   RETURN_S(match_tvar_call(sem, n2, pn1, t2, t1));
    if (is_tvar_array_lit(t2))              RETURN(match_tvar_array_lit(sem, n1, pn2, t1, t2));
    if (is_tvar_array_lit(t1))              RETURN_S(match_tvar_array_lit(sem, n2, pn1, t2, t1));
    if (is_tvar_tuple_lit(t2))              RETURN(match_tvar_tuple_lit(sem, n1, pn2, t1, t2));
    if (is_tvar_tuple_lit(t1))              RETURN_S(match_tvar_tuple_lit(sem, n2, pn1, t2, t1));
    if (is_tvar_fn(t1))                     RETURN(match_tvar_fn(sem, n1, n2, t1, t2));
    if (is_tvar_fn(t2))                     RETURN_S(match_tvar_fn(sem, n2, n1, t2, t1));
    if (is_tvar_untyped_lit(t2))            RETURN(match_tvar_untyped_lit(sem, n1, n2, t1, t2));
    if (is_tvar_untyped_lit(t1))            RETURN_S(match_tvar_untyped_lit(sem, n2, n1, t2, t1));

    badpath;

    done: {
        sem->call_check.i1 = prev_m1;
        sem->call_check.i2 = prev_m2;
        #undef RETURN
        #undef RETURN_S
        reached(r);
        return r;
    }
}

static Result match_tuples (Sem *sem, AstTuple *tup1, AstTuple *tup2, Type *t1, Type *t2, Subtype subtype) {
    assert_dbg(sem->match.ongoing);

    Ast *n1 = cast(Ast*, tup1);
    Ast *n2 = cast(Ast*, tup2);

    if (tup1->fields.count != tup2->fields.count) return ERROR_MATCH();
    if ((n1->flags & AST_CREATES_SCOPE) != (n2->flags & AST_CREATES_SCOPE)) return ERROR_MATCH();

    array_iter (pf1, &tup1->fields, *) {
        Ast **pf2 = array_ref(&tup2->fields, ARRAY_IDX);
        Ast *f1 = *pf1;
        Ast *f2 = *pf2;
        if ((f1->tag == AST_TUPLE_FIELD) && (cast(AstTupleField*, f1)->name != cast(AstTupleField*, f2)->name)) return ERROR_MATCH();
        try(match(sem, pf1, pf2, get_type(f1), get_type(f2), subtype));
    }

    return RESULT_OK;
}

static Result match_structural (Sem *sem, Ast *n1, Ast *n2, Type *t1, Type *t2) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(t1 != t2);

    if (t1->tag != t2->tag) return ERROR_MATCH();

    switch (t1->tag) {
    case TYPE_FN: {
        TypeFn *ty1   = cast(TypeFn*, t1);
        TypeFn *ty2   = cast(TypeFn*, t2);
        ArrayAst *in1 = &ty1->node->inputs;
        ArrayAst *in2 = &ty2->node->inputs;
        Ast *out1     = ty1->node->output;
        Ast *out2     = ty2->node->output;

        if (!out1 != !out2) return ERROR_MATCH();
        if (in1->count != in2->count) return ERROR_MATCH();
        array_iter (x, in1) try(match_nn(sem, x, array_get(in2, ARRAY_IDX)), return R);
        if (out1) try(match_nn(sem, out1, out2), return R);

        return RESULT_OK;
    }

    case TYPE_POINTER: {
        TypePointer *ty1 = cast(TypePointer*, t1);
        TypePointer *ty2 = cast(TypePointer*, t2);
        return ((t1->flags & TYPE_IS_CONST_POINTER) != (t2->flags & TYPE_IS_CONST_POINTER)) ?
               ERROR_MATCH() :
               match_tt(sem, ty1->pointee, ty2->pointee);
    }

    case TYPE_ARRAY: {
        TypeArray *ty1 = cast(TypeArray*, t1);
        TypeArray *ty2 = cast(TypeArray*, t2);
        if (ty1->length != ty2->length) return ERROR_MATCH();
        return match_tt(sem, ty1->element, ty2->element);
    }

    case TYPE_INT:   return (t1 == t2) ? RESULT_OK : ERROR_MATCH();
    case TYPE_FLOAT: return (t1 == t2) ? RESULT_OK : ERROR_MATCH();
    case TYPE_TUPLE: return match_tuples(sem, cast(TypeTuple*, t1)->node, cast(TypeTuple*, t2)->node, t1, t2, SUBTYPE_TWO_WAY);
    default:         return ERROR_MATCH();
    }
}

// Check if n2 is a subtype of n1.
static Result match_substructural (Sem *sem, Ast *n1, Ast **pn2, Type *t1, Type *t2) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(t1 != t2);

    Ast *n2 = *pn2;

    reach(r);
    #define RETURN(R, ...) {\
        def1(r, R);\
        reached(r);\
        __VA_OPT__(if (false)) if (r == RESULT_OK) implicit_cast(sem, pn2, n1, t1);\
        return r;\
    }

    if (t1 == sem->core_types.type_any) {
        RETURN(RESULT_OK);
    } else if (t1->tag == TYPE_STRUCT) {
        MonoInfo *info = sem_get_mono_info(sem, cast(Ast*, cast(TypeStruct*, t1)->node));

        if (!info || get_type(info->poly_info->node) != sem->core_types.type_slice) RETURN(ERROR_MATCH());

        if (t2->tag == TYPE_ARRAY) {
            RETURN(match_tt(sem, array_ref(&info->type_map, 0)->t, cast(TypeArray*, t2)->element));
        } else if (t2->tag == TYPE_POINTER && cast(TypePointer*, t2)->pointee->tag == TYPE_ARRAY) {
            TypeArray *array = cast(TypeArray*, cast(TypePointer*, t2)->pointee);
            RETURN(match_tt(sem, array_ref(&info->type_map, 0)->t, array->element));
        } else {
            RETURN(ERROR_MATCH());
        }
    }

    switch (t1->tag) {
    case TYPE_POINTER: {
        if (t2->tag != TYPE_POINTER) RETURN(ERROR_MATCH());
        TypePointer *ty1 = cast(TypePointer*, t1);
        TypePointer *ty2 = cast(TypePointer*, t2);
        Bool c1 = t1->flags & TYPE_IS_CONST_POINTER;
        Bool c2 = t2->flags & TYPE_IS_CONST_POINTER;
        if (!c1 && c2) RETURN(ERROR_MATCH());
        RETURN(match_tt(sem, ty1->pointee, ty2->pointee));
    }

    case TYPE_FLOAT: {
        if (t2->tag != TYPE_FLOAT) RETURN(ERROR_MATCH());
        TypeFloat *ty1 = cast(TypeFloat*, t1);
        TypeFloat *ty2 = cast(TypeFloat*, t2);
        if (n2->tag == AST_F64_LITERAL || ty1->bitwidth >= ty2->bitwidth) RETURN(RESULT_OK);
        RETURN(ERROR_MATCH());
    }

    case TYPE_INT: {
        if (t2->tag != TYPE_INT) RETURN(ERROR_MATCH());

        TypeInt *ty1 = cast(TypeInt*, t1);
        TypeInt *ty2 = cast(TypeInt*, t2);

        if (n2->flags & AST_EVALED) {
            Value c = sem_get_const(sem, n2);

            if (ty2->is_signed) {
                I64 v = vm_value_to_i64(t2, c);
                if (ty1->is_signed) { if (v >= smin[ty1->bitwidth] && v <= smax[ty1->bitwidth]) RETURN(RESULT_OK); }
                else                { if (v >= 0 && cast(U64, v) <= umax[ty1->bitwidth]) RETURN(RESULT_OK); }
            } else {
                U64 v = vm_value_to_u64(t2, c);
                if (ty1->is_signed) { if (v <= cast(U64, smax[ty1->bitwidth])) RETURN(RESULT_OK); }
                else                { if (v <= umax[ty1->bitwidth]) RETURN(RESULT_OK); }
            }

            RETURN(ERROR_MATCH());
        } else if (n2->flags & AST_MUST_EVAL) {
            RETURN(RESULT_DEFER);
        } else if (ty1->bitwidth < ty2->bitwidth) {
            RETURN(ERROR_MATCH());
        } else if (ty1->is_signed) {
            if (ty1->bitwidth == ty2->bitwidth) RETURN(ERROR_MATCH());
        } else if (ty2->is_signed) {
            RETURN(ERROR_MATCH());
        }

        RETURN(RESULT_OK);
    }

    default: RETURN(match_structural(sem, n1, n2, t1, t2), NOCAST);
    }

    #undef RETURN
}

// This function will potentially perform an implicit cast
// by wrapping the casted node using the double pointer
// argument given here.
//
// If an implicit cast occurs and Sem.call_check.ongoing
// is not set, then this function returns RESULT_DEFER
// in order to simplify the caller code.
static Result match (Sem *sem, Ast **pn1, Ast **pn2, Type *t1, Type *t2, Subtype subtype) {
    if (!t1 || !t2) return RESULT_DEFER;
    if (t1 == t2)   return RESULT_OK;

    Ast *n1 = *pn1;
    Ast *n2 = *pn2;

    if (! sem->match.ongoing) sem->match.top_pair = (MatchPair){n1,n2,t1,t2};
    sem->match.ongoing++;

    Result r = RESULT_DEFER;
    reach(r);
    #define RETURN(R) { r = R; goto done; }

    if ((t1->flags & TYPE_IS_DISTINCT) && !(n2->flags & AST_IS_LITERAL)) RETURN(ERROR_MATCH());
    if ((t2->flags & TYPE_IS_DISTINCT) && !(n1->flags & AST_IS_LITERAL)) RETURN(ERROR_MATCH());
    if (is_tvar(t1) || is_tvar(t2)) RETURN(match_tvar(sem, pn1, pn2, t1, t2, subtype));
    if (subtype == SUBTYPE_TWO_WAY) RETURN(match_structural(sem, n1, n2, t1, t2));
    if (subtype == SUBTYPE_ONE_WAY) RETURN(match_substructural(sem, n1, pn2, t1, t2));

    sem->match.without_error_reporting++;
    r = match_substructural(sem, n1, pn2, t1, t2);
    sem->match.without_error_reporting--;

    if (r == RESULT_ERROR) {
        swap(sem->call_check.i1, sem->call_check.i2);
        r = match_substructural(sem, n2, pn1, t2, t1);
        swap(sem->call_check.i1, sem->call_check.i2);
    }

    done: {
        reached(r);
        #undef RETURN
        sem->match.ongoing--;
        if (sem->call_check.ongoing || !sem->match.applied_cast) return r;
        sem->match.applied_cast = 0;
        return RESULT_DEFER;
    }
}

static IString *instantiate_poly_name (Sem *sem, IString *base, Ast *instantiator, U64 n) {
    IString *path = get_file(instantiator)->path;
    String name   = astr_fmt(sem->mem, "%.*s:%.*s:%lu:%lu", STR(*base), STR(*path), instantiator->pos.offset, n);
    return intern_str(sem->interns, name);
}

static Ast *instantiate_poly_arg_helper (Ast *old_node, Ast *new_node, Void *context) {
    Auto sem      = cast(Sem*, cast(Void**, context)[0]);
    Auto info     = cast(MonoInfo*, cast(Void**, context)[1]);
    Auto instance = cast(Ast*, cast(Void**, context)[2]);

    if (new_node) {
        new_node->flags &= ~(AST_IN_POLY_ARG_POSITION | AST_HAS_POLY_ARGS);
        if (old_node->flags & AST_HAS_POLY_ARGS) array_push_lit(&info->instance_map, .oldn=old_node, .newn=new_node);
        if (old_node->tag == AST_DOT) new_node->flags &= ~AST_IS_TYPE;
        if ((old_node->tag == AST_CAST) && !cast(AstCast*, old_node)->to) {
            assert_dbg(! (old_node->flags & AST_IN_POLY_ARG_POSITION));
            add_to_infer_list(sem, old_node, new_node);
        }
        return 0;
    } else {
        switch (old_node->tag) {
        case AST_ARG_POLY_TYPE:  return instantiate_poly_arg(sem, old_node, info, instance);
        case AST_ARG_POLY_CODE:  return instantiate_poly_arg(sem, old_node, info, instance);
        case AST_ARG_POLY_VALUE: return instantiate_poly_arg(sem, old_node, info, instance);
        default:                 return 0;
        }
    }
}

static Ast *instantiate_poly_arg (Sem *sem, Ast *arg, MonoInfo *info, Ast *instance) {
    Scope *instance_scope = get_scope(instance);

    switch (arg->tag) {
    case AST_VAR_DEF: {
        AstVarDef *n = cast(AstVarDef*, arg);
        Ast *r = ast_alloc(sem->mem, AST_VAR_DEF, 0);

        r->pos = arg->pos;
        cast(AstVarDef*, r)->name = n->name;
        if (arg->flags & AST_HAS_POLY_ARGS) array_push_lit(&info->instance_map, .oldn=arg, .newn=r);

        if (n->constraint) {
            Void *ctx [] = { sem, info, instance };
            cast(AstVarDef*, r)->constraint = ast_deep_copy(sem->mem, n->constraint, instantiate_poly_arg_helper, ctx);
        } else {
            Ast *c = ast_alloc(sem->mem, AST_DUMMY, AST_IS_TYPE);
            c->pos = n->init->pos;
            add_to_check_list(sem, c, instance_scope);
            set_type(c, get_type(n->init));
            cast(AstVarDef*, r)->constraint = c;
        }

        if (instance->tag == AST_FN) array_push(&cast(AstBaseFn*, instance)->inputs, r);
        add_to_check_list(sem, r, instance_scope);
        return r;
    }

    case AST_ARG_POLY_TYPE: {
        TypeVar *t = cast(TypeVar*, get_type(arg));
        TypeInstance *b = array_find_ref(&info->type_map, IT->var == t);
        Ast *c = get_type_constructor(b->t);
        Ast *r = ast_alloc(sem->mem, AST_DUMMY, AST_IS_POLYMORPH_INSTANCE | AST_IS_TYPE | AST_EVALED);

        if (c) b->t = get_type(c);
        b->instance = r;
        r->pos = arg->pos;
        add_to_check_list(sem, r, instance_scope);
        scope_add(sem, instance_scope, cast(AstArgPolyType*, arg)->name, r, r);
        array_push_lit(&info->instance_map, .oldn=arg, .newn=r);

        if (! type_has_polyargs(b->t)) {
            set_type(r, b->t);
            bind_simple_untyped_lit_recursively(sem, b->t);
        }

        return r;
    }

    case AST_ARG_POLY_VALUE: {
        AstArgPolyValue *n = cast(AstArgPolyValue*, arg);
        TypeVar *t = cast(TypeVar*, get_type(arg));
        ValueInstance *b = array_find_ref(&info->value_map, IT->var == t);
        Ast *r = ast_alloc(sem->mem, AST_VAR_DEF, AST_IS_POLYMORPH_INSTANCE | AST_CAN_EVAL);

        r->pos = arg->pos;
        cast(AstVarDef*, r)->name = n->name;
        Void *ctx [] = { sem, info, instance };
        cast(AstVarDef*, r)->constraint = (n->constraint->tag == AST_DUMMY) ? n->constraint : ast_deep_copy(sem->mem, n->constraint, instantiate_poly_arg_helper, ctx);

        b->instance = r;
        add_to_check_list(sem, r, instance_scope);
        array_push_lit(&info->instance_map, .oldn=arg, .newn=r);
        assert_dbg(b->val);
        map_add(&sem->node_to_val, r->id, (Value){ .ptr=b->val });
        return r;
    }

    case AST_ARG_POLY_CODE: {
        TypeVar *t = cast(TypeVar*, get_type(arg));
        ValueInstance *b = array_find_ref(&info->value_map, IT->var == t);
        Ast *r = ast_alloc(sem->mem, AST_CALL_MACRO_ARG, 0);

        r->pos = arg->pos;
        cast(AstCallMacroArg*, r)->code = ((AstCallMacroArg*)*b->val)->code;
        cast(AstCallMacroArg*, r)->parsed_ast = ((AstCallMacroArg*)*b->val)->parsed_ast;

        b->instance = r;
        add_to_check_list(sem, r, instance_scope);
        scope_add(sem, instance_scope, cast(AstArgPolyCode*, arg)->name, r, r);
        array_push_lit(&info->instance_map, .oldn=arg, .newn=r);
        return r;
    }

    default: badpath;
    }
}

static Ast *instantiate_polymorph (Sem *sem, MonoInfo *info, MonoInfo **out_instance_info) {
    assert_dbg(sem->call_check.ongoing);

    Ast *polymorph      = info->poly_info->node;
    ArrayAst *instances = &info->poly_info->instances;
    AstFlags is_macro   = (polymorph->flags & AST_IS_MACRO) ? AST_IS_MACRO_INSTANCE : 0;

    if (! is_macro) { // Look for a cached instance:
        sem->match.without_error_reporting++;
        MonoInfo *prev = sem->call_check.i1;
        sem->call_check.i1 = info;

        array_iter (prev_instance, instances) {
            MonoInfo *prev_info = sem_get_mono_info(sem, prev_instance);

            array_iter (a, &info->type_map, *) {
                TypeInstance *b = array_ref(&prev_info->type_map, ARRAY_IDX);
                Result r = match_tt(sem, a->t, b->t);
                assert_dbg(r != RESULT_DEFER);
                if (r != RESULT_OK) goto continue_outer;
            }

            array_iter (a, &info->value_map, *) {
                Ast *b = *array_ref(&prev_info->value_map, ARRAY_IDX)->val;
                Type *t = get_type(b);
                if (! (t->flags & TYPE_IS_PRIMITIVE)) goto continue_outer;
                if (! vm_value_match(t, get_const(sem, info, *a->val, 0), sem_get_const(sem, b))) goto continue_outer;
            }

            sem->call_check.i1 = prev;
            sem->match.without_error_reporting--;
            *out_instance_info = prev_info;
            return prev_instance;
            continue_outer:;
        }

        sem->call_check.i1 = prev;
        sem->match.without_error_reporting--;
    }

    AstTag tag     = (polymorph->tag == AST_STRUCT_POLY) ? AST_STRUCT : AST_FN;
    Ast *fn_output = (tag == AST_FN) ? cast(AstBaseFn*, polymorph)->output : 0;
    Ast *instance  = ast_alloc(sem->mem, tag, AST_IS_POLYMORPH_INSTANCE | is_macro);
    instance->pos  = polymorph->pos;

    if (tag == AST_FN) {
        AstFnPoly *p = cast(AstFnPoly*, polymorph);
        cast(AstFn*, instance)->name = instantiate_poly_name(sem, p->name, info->instantiator, instances->count);
        if (fn_output && (fn_output->tag != AST_ARG_POLY_TYPE)) cast(AstBaseFn*, instance)->output = ast_deep_copy(sem->mem, fn_output, 0, 0);
        array_iter (s, &p->statements) {
            Ast *copy = ast_deep_copy(sem->mem, s, 0, 0);
            array_push(&cast(AstFn*, instance)->statements, copy);
        }
    } else {
        assert_dbg(tag == AST_STRUCT);
        AstStructPoly *p = cast(AstStructPoly*, polymorph);
        cast(AstStruct*, instance)->name = instantiate_poly_name(sem, p->name, info->instantiator, instances->count);
        array_iter (f, &p->members) {
            Ast *copy = ast_deep_copy(sem->mem, f, 0, 0);
            array_push(&cast(AstStruct*, instance)->members, copy);
        }
    }

    add_to_check_list(sem, instance, get_scope(is_macro ? info->instantiator : polymorph));
    map_add(&sem->mono_infos, instance->id, info);
    array_push(instances, instance);

    ArrayAst arg_instances;
    array_init(&arg_instances, sem->mem);
    array_iter (arg, info->poly_info->args) array_push(&arg_instances, instantiate_poly_arg(sem, arg, info, instance));
    if (fn_output && (fn_output->tag == AST_ARG_POLY_TYPE)) cast(AstBaseFn*, instance)->output = instantiate_poly_arg(sem, fn_output, info, instance);
    info->arg_instances = slice_from(&arg_instances, SliceAst);

    *out_instance_info = info;
    return instance;
}

static Result check_call_args_layout (Sem *sem, Ast *target, ArrayAst *target_args, Ast *call, ArrayAst *call_args) {
    if (call_args->count > target_args->count)
        return error_nn(sem, call, target, "Too many call args. Got %lu, but expected %lu.", call_args->count, target_args->count);

    array_ensure_count(call_args, target_args->count, true);

    // Reorder named arguments:
    array_iter (arg, call_args) {
        if (!arg || arg->tag != AST_CALL_NAMED_ARG) continue;

        IString *name = cast(AstCallNamedArg*, arg)->name;
        U64 def = array_find(target_args, get_name(IT) == name);

        if (def == ARRAY_NIL_IDX) return error_nn(sem, arg, target, "Referencing unknown argument");
        if (def == ARRAY_IDX) continue;

        Ast *arg2 = array_get(call_args, def);
        if (arg2 && (arg2->tag != AST_CALL_NAMED_ARG || name == cast(AstCallNamedArg*, arg2)->name))
            return error_nn(sem, arg, arg2, "Duplicate call args.");

        array_swap(call_args, def, ARRAY_IDX);
        ARRAY_IDX--; // To stay on current index next iteration.
    }

    // Insert missing default arguments:
    array_iter (arg, call_args) {
        if (arg) {
            if (arg->tag == AST_CALL_NAMED_ARG) array_set(call_args, ARRAY_IDX, cast(AstCallNamedArg*, arg)->arg);
            continue;
        }

        Ast *def  = array_get(target_args, ARRAY_IDX);
        Ast *init = get_init(def);

        if (! init) return error_nn(sem, def, call, "Argument does not have default value and is omitted from call.");
        assert_dbg(init->flags & AST_EVALED);

        if (init->tag == AST_CALLER_INFO) {
            Ast *n = alloc_caller_struct(sem, call);
            array_set(call_args, ARRAY_IDX, n);
        } else {
            Ast *n    = ast_alloc(sem->mem, AST_CALL_DEFAULT_ARG, 0);
            n->pos    = call->pos;
            n->flags |= (def->flags & AST_IS_TYPE);

            if (init->flags & AST_MUST_EVAL) {
                cast(AstCallDefaultArg*, n)->arg = init;
            } else {
                Ast *arg = ast_deep_copy(sem->mem, init, 0, 0);
                arg->flags |= AST_MUST_EVAL;
                cast(AstCallDefaultArg*, n)->arg = arg;
                add_to_check_list(sem, arg, get_scope(def));
            }

            add_to_check_list(sem, n, get_scope(call));
            array_set(call_args, ARRAY_IDX, n);
        }
    }

    return RESULT_OK;
}

static Result check_call (Sem *sem, Ast *target, ArrayAst *target_args, Ast *caller, ArrayAst *call_args, Bool check_layout) {
    Auto c = &sem->call_check;

    assert_dbg(! c->i1);
    assert_dbg(! c->ongoing);

    if (target->flags & AST_IS_POLYMORPH) {
        PolyInfo *poly_info = get_poly_info(sem, target);

        array_iter_from (i, &poly_info->instances, poly_info->mark) {
            MonoInfo *info = sem_get_mono_info(sem, i);
            array_iter (x, &info->type_map, *)  try_get_type(x->instance);
            array_iter (x, &info->value_map, *) if (! (x->instance->flags & AST_EVALED)) return RESULT_DEFER;
            poly_info->mark++;
        }
    }

    if (check_layout) try(check_call_args_layout(sem, target, target_args, caller, call_args));
    if (target->flags & (AST_IS_POLYMORPH | AST_IS_MACRO)) c->i1 = alloc_mono_info(sem, target, caller);

    Result r = RESULT_OK;
    reach(r);
    #define RETURN(R) { r = R; goto done; }

    c->ongoing          = true;
    c->bound_var_to_var = true;
    c->bound_var_to_val = true;

    while (c->bound_var_to_var && c->bound_var_to_val) {
        c->bound_var_to_var = false;
        c->bound_var_to_val = false;

        array_iter (argt, target_args) {
            Ast **argc = array_ref(call_args, ARRAY_IDX);
            r = (argt->tag == AST_ARG_POLY_TYPE) ? match_nc(sem, argt, *argc) : match_nv(sem, argt, argc);
            if (r != RESULT_OK) RETURN(r);
        }
    }

    array_iter (info, &c->mono_infos) {
        if (array_find_ref(&info->value_map, !IT->val)) RETURN(error_unbound_polyvars(sem, caller, target));
        if (array_find_ref(&info->type_map, !IT->t || is_tvar_type(IT->t))) RETURN(error_unbound_polyvars(sem, caller, target));
    }

    array_iter (x, &c->values_to_match, *) {
        Type *t1; Value v1 = get_const(sem, x->i1, x->a, &t1);
        Type *t2; Value v2 = get_const(sem, x->i2, x->b, &t2);
        if (! vm_value_match(t1, v1, v2)) RETURN(error_nn(sem, x->a, x->b, "Value mismatch."));
    }

    array_iter (info, &c->mono_infos) {
        Scope *parent_instance = scope_of_instance(info->instantiator);
        if (! parent_instance) continue;
        MonoInfo *parent_info = sem_get_mono_info(sem, parent_instance->owner);
        if (parent_info->depth >= MAX_RECURSIVE_INSTANTIATIONS) RETURN(error_n(sem, info->instantiator, "Too many recursive instantiations."));
        info->depth = parent_info->depth + 1;
    }

    array_iter (info, &c->mono_infos) {
        MonoInfo *instance_info = 0;
        Ast *instance = instantiate_polymorph(sem, info, &instance_info);

        if (instance_info != info) { // Cached instance used, so this MonoInfo is obsolete.
            array_remove_fast(&c->mono_infos, ARRAY_IDX);
            ARRAY_IDX--; // Because of the remove above.
            array_iter (i, &c->mono_infos) array_iter (x, &i->type_map, *) if (x->i == info) x->i = instance_info;
        }

        array_iter (i, &instance_info->instance_map, *) {
            array_iter (x, &c->untyped_lits, *) if (i->oldn == x->bind) { x->bind = i->newn; break; }
            array_iter (x, &c->casts, *) {
                if (i->oldn != x->to) continue;
                x->to = (i->oldn->tag == AST_ARG_POLY_VALUE) ? cast(AstVarDef*, i->newn)->constraint : i->newn;
                break;
            }
        }

        if (info != c->i1) {
            map_add(&sem->mono_infos, info->instantiator->id, info);
            add_to_infer_list(sem, instance, info->instantiator);
        }

        sem_set_target(sem, info->instantiator, instance);
    }

    array_iter (info, &c->mono_infos) {
        array_iter (x, &info->type_map, *) {
            if (get_type(x->instance)) continue;
            Ast *c = get_type_constructor(x->t);
            Type *t = get_type(c);
            Ast *b = is_tvar_fn(t) ? get_target(cast(TypeVar*, t)->node) : (x->i ? array_find_ref(&x->i->instance_map, IT->oldn == c)->newn : c);
            add_to_infer_list(sem, b, x->instance);
        }
    }

    done: {
        c->ongoing = false;

        if (r == RESULT_OK) {
            array_iter (x, &c->casts, *)            implicit_cast(sem, x->from, x->to, x->to_type);
            array_iter (x, &c->untyped_lits, *)     add_to_infer_list(sem, x->bind, x->lit);
            array_iter (x, &c->simple_untyped_lits) x->flags &= ~TYPE_IS_UNTYPED_LIT;
        } else {
            array_iter (x, &c->untyped_lits, *) set_type(x->lit, x->tvar);
            array_push_many(&c->mono_infos_pool, &c->mono_infos);
        }

        c->i1 = 0;
        c->i2 = 0;
        c->casts.count = 0;
        c->mono_infos.count = 0;
        c->untyped_lits.count = 0;
        c->values_to_match.count = 0;
        c->simple_untyped_lits.count = 0;

        #undef RETURN
        reached(r);
        return r;
    }
}

static Void check_type_is_finite_ (Sem *sem, Type *type, Ast *node, ArrayAst *path) {
    if (node) {
        U64 prev = array_find(path, IT == node);
        array_push(path, node);

        if (prev != ARRAY_NIL_IDX) {
            sem_msg(msg, LOG_ERROR);
            astr_push_fmt(msg, "Infinite sized types are not supported.\n\n");
            array_iter_from (n, path, prev) log_node(sem, msg, n);
            sem_panic(sem);
        }
    }

    if (type->tag == TYPE_ARRAY) {
        TypeArray *t = cast(TypeArray*, type);
        check_type_is_finite_(sem, t->element, 0, path);
    } else if (type->tag == TYPE_STRUCT) {
        TypeStruct *t = cast(TypeStruct*, type);
        array_iter (f, &t->node->members) check_type_is_finite_(sem, get_type(f), f, path);
    }

    if (node) path->count--;
}

static Void check_type_is_finite (Sem *sem, Type *type, Ast *node) {
    tmem_new(tm);
    ArrayAst path;
    array_init(&path, tm);
    check_type_is_finite_(sem, type, node, &path);
}

static Void check_for_invalid_cycle_ (Sem *sem, AstTag tag, Ast *node, ArrayAst *path) {
    if (! (node->flags & AST_ADDED_TO_CHECK_LIST)) return;

    U64 prev = array_find(path, IT == node);

    if (prev == ARRAY_NIL_IDX) {
        if (node->tag == tag || node->tag == AST_IDENT) array_push(path, node);

        Ast *d = get_target(node);
        if (d && !get_type(d) && (d->tag == tag)) check_for_invalid_cycle_(sem, tag, d, path);

        #define CHECK_FOR_INVALID_CYCLE(child, ...) check_for_invalid_cycle_(sem, tag, child, path);
        AST_VISIT_CHILDREN(node, CHECK_FOR_INVALID_CYCLE);

        if (node->tag == tag || node->tag == AST_IDENT) path->count--;
    } else {
        sem_msg(msg, LOG_ERROR);
        astr_push_fmt(msg, "Invalid cycle.\n\n");
        array_iter_from (d, path, prev) log_node(sem, msg, d);
        sem_panic(sem);
    }
}

static Void check_for_invalid_cycle (Sem *sem, AstTag tag, Ast *node) {
    tmem_new(tm);
    ArrayAst path;
    array_init(&path, tm);
    check_for_invalid_cycle_(sem, tag, node, &path);
}

// RESULT_ERROR means that it's not read only.
static Result check_is_read_only (Sem *sem, Ast *n) {
    if (n->flags & (AST_IS_READ_ONLY | AST_IS_TYPE)) return RESULT_OK;

    reach(r);
    #define RETURN(R) {\
        def1(r, acast(Result, R));\
        reached(r);\
        if (r == RESULT_OK) n->flags |= AST_IS_READ_ONLY;\
        return r;\
    }

    switch (n->tag) {
    case AST_DOT:   {
        Ast *d = cast(AstDot*, n)->sem_edge;
        if (d->tag == AST_TUPLE_FIELD) RETURN(RESULT_ERROR);
        RETURN(d ? check_is_read_only(sem, d) : RESULT_DEFER);
    }
    case AST_DEREF: { Ast *o = cast(AstBaseUnary*, n)->op;   RETURN((try_get_type(o)->flags & TYPE_IS_CONST_POINTER) ? RESULT_OK : RESULT_ERROR); }
    case AST_IDENT: { Ast *d = cast(AstIdent*, n)->sem_edge; RETURN((d && (d->flags & AST_IS_READ_ONLY)) ? RESULT_OK : RESULT_ERROR); }
    case AST_INDEX: { Ast *l = cast(AstIndex*, n)->lhs;      RETURN(check_is_read_only(sem, l)); }
    default:        RETURN(RESULT_ERROR);
    }

    #undef RETURN
}

// This performs checks common to ops that are fusable with
// the assign op (+=, /=, ...) and their unfused counterparts.
static Result check_assign_fusable_op (Sem *sem, AstBaseBinary *n, AstTag op) {
    Type *t1 = try_get_type_v(n->op1);
    Type *t2 = try_get_type_v(n->op2);

    switch (op) {
    case AST_ADD:
    case AST_SUB:
        if (t1->tag != TYPE_INT && t1->tag != TYPE_FLOAT && !is_tvar_untyped_lit(t1) && t1->tag != TYPE_POINTER) return error_nt(sem, n->op1, t1, "expected pointer, int or float type.");
        if (t2->tag != TYPE_INT && t2->tag != TYPE_FLOAT && !is_tvar_untyped_lit(t2)) return error_nt(sem, n->op2, t2, "expected int or float type.");
        return RESULT_OK;

    case AST_MUL:
    case AST_DIV:
        if (t1->tag != TYPE_INT && t1->tag != TYPE_FLOAT && !is_tvar_untyped_lit(t1)) return error_nt(sem, n->op1, t1, "expected int or float type.");
        if (t2->tag != TYPE_INT && t2->tag != TYPE_FLOAT && !is_tvar_untyped_lit(t2)) return error_nt(sem, n->op2, t2, "expected int or float type.");
        return RESULT_OK;

    case AST_MOD:
        if (t1->tag != TYPE_INT && !is_tvar_untyped_lit(t1)) return error_nt(sem, n->op1, t1, "expected int type.");
        if (t2->tag != TYPE_INT && !is_tvar_untyped_lit(t2)) return error_nt(sem, n->op2, t2, "expected int type.");
        return RESULT_OK;

    case AST_BITWISE_OR:
    case AST_BITWISE_XOR:
    case AST_BITWISE_AND:
        if (t1->tag != TYPE_INT && !is_tvar_untyped_lit(t1) && !(t1->tag == TYPE_ENUM && cast(TypeEnum*, t1)->node->is_flags)) return error_nt(sem, n->op1, t1, "expected int or flag enum type.");
        if (t2->tag != TYPE_INT && !is_tvar_untyped_lit(t2) && !(t2->tag == TYPE_ENUM && cast(TypeEnum*, t2)->node->is_flags)) return error_nt(sem, n->op2, t2, "expected int or flag enum type.");
        return RESULT_OK;

    case AST_SHIFT_LEFT:
    case AST_SHIFT_RIGHT:
        if (t1->tag != TYPE_INT && !is_tvar_untyped_lit(t1)) return error_nt(sem, n->op1, t1, "expected int type.");
        if (t2->tag != TYPE_INT && !is_tvar_untyped_lit(t2)) return error_nt(sem, n->op2, t2, "expected int type.");
        return match_tv(sem, sem->core_types.type_U64, &n->op2);

    default: badpath;
    }
}

static Result check_loop_target (Sem *sem, Scope *s, Ast *selector, IString *label, Bool for_break) {
    for (; s; s = s->parent) {
        Ast *o = s->owner;

        if (o->tag == AST_WHILE) {
            IString *l = cast(AstWhile*, o)->label;
            if (!label || (label == l)) { sem_set_target(sem, selector, o); return RESULT_OK; }
        } else if (o->tag == AST_BLOCK) {
            IString *l = cast(AstBlock*, o)->label;
            AstEmbed *c = scope_get_constraint(s->parent);

            if (! c) {
                if (l) return error_n(sem, o, "Blocks with labels must be children of 'embed' with break/continue constraints.");
                continue;
            }

            if (label && (label != l)) continue;

            Ast *h = for_break ? c->break_hit : c->continue_hit;
            if (! h) { sem_set_target(sem, selector, o); return RESULT_OK; }

            label = (h->tag == AST_STRING_LITERAL) ? cast(AstStringLiteral*, h)->str : intern_str(sem->interns, get_string_const(sem, h));
            s = s->parent;
        } else {
            AstEmbed *c = scope_get_constraint(s);
            if (! c) continue;

            Ast *m = for_break ? c->break_miss : c->continue_miss;
            if (! m) continue;

            IString *l = (m->tag == AST_STRING_LITERAL) ? cast(AstStringLiteral*, m)->str : intern_str(sem->interns, get_string_const(sem, m));
            try(check_loop_target(sem, s->parent, selector, l, for_break));

            if (! (m->flags & AST_ENDS_WITH_BLOCK)) return RESULT_OK;
            s = get_scope(get_target(selector));
        }
    }

    return error_n(sem, selector, "Undeclared loop label [%.*s].", STR(*label));
}

// This function performs a shallow check of @node without
// recursing down the tree; therefore, a node can be marked
// checked even if some node reachable from it is not.
//
// The checks done here include the bulk of the work such
// as setting types, checking that operand types match,
// binding selectors to their targets such as identifiers
// or dot expressions, etc...
static Result check_node (Sem *sem, Ast *node) {
    switch (node->tag) {
    case AST_TAG_COUNT:       badpath;
    case AST_BITWISE_NOT:     badpath;
    case AST_INTERFACE:       badpath;
    case AST_TYPE_CONSTRAINT: badpath;
    case AST_BLOCK:           return RESULT_OK;
    case AST_FILE:            return RESULT_OK;
    case AST_PAIR:            return RESULT_OK;
    case AST_CODE_GEN:        return RESULT_OK;
    case AST_ATTRIBUTE:       return RESULT_OK;
    case AST_SCOPE_MOD:       return RESULT_OK;
    case AST_CALL_NAMED_ARG:  return RESULT_OK;
    case AST_CALL_MACRO_BARG: return RESULT_OK;
    case AST_IF:              return match_tv(sem, sem->core_types.type_Bool, &cast(AstIf*, node)->cond);
    case AST_WHILE:           return match_tv(sem, sem->core_types.type_Bool, &cast(AstWhile*, node)->cond);
    case AST_BREAK:           return check_loop_target(sem, get_scope(node), node, cast(AstBreak*, node)->label, true);
    case AST_CONTINUE:        return check_loop_target(sem, get_scope(node), node, cast(AstContinue*, node)->label, false);
    case AST_DUMMY:           return ((node->flags & AST_IS_POLYMORPH_INSTANCE) && !get_type(node)) ? RESULT_DEFER : RESULT_OK;
    case AST_SIZEOF:          set_type(node, sem->core_types.type_U64); return RESULT_OK;
    case AST_ALIGNOF:         set_type(node, sem->core_types.type_U8); return RESULT_OK;
    case AST_F64_LITERAL:     set_type(node, sem->core_types.type_F64); return RESULT_OK;
    case AST_I64_LITERAL:     set_type(node, sem->core_types.type_I64); return RESULT_OK;
    case AST_U64_LITERAL:     set_type(node, sem->core_types.type_U64); return RESULT_OK;
    case AST_BOOL_LITERAL:    set_type(node, sem->core_types.type_Bool); return RESULT_OK;
    case AST_TYPE_ALIAS:      set_type(node, try_get_type_t(cast(AstTypeAlias*, node)->val)); return RESULT_OK;

    case AST_NIL: {
        Type *t = get_type(node);

        if (! t) {
            set_type(node, alloc_type_var(sem, node, TYPE_IS_UNTYPED_LIT));
            return RESULT_DEFER;
        } else if (t->tag == TYPE_VAR) {
            return RESULT_DEFER;
        } else if (!(t->flags & (TYPE_IS_PRIMITIVE | TYPE_IS_STRUCTURAL)) && (t->tag != TYPE_STRUCT)) {
            return error_nt(sem, node, t, "which is not nilable.");
        } else {
            return RESULT_OK;
        }
    }

    case AST_EVAL: {
        AstEval *n = cast(AstEval*, node);
        if (! (n->child->flags & AST_EVALED)) return RESULT_DEFER;
        set_type(node, get_type(n->child));
        return RESULT_OK;
    }

    case AST_IMPORT_CONFIG: {
        try_get_type(node); // Wait for type to be set by AST_IMPORT handling code.
        return RESULT_OK;
    }

    case AST_IMPORT: {
        AstImport *n = cast(AstImport*, node);

        if (! (n->path_gen->flags & AST_EVALED)) return RESULT_DEFER;

        if (! n->path) {
            n->path = par_parse_import_path(sem->parser, get_string_const(sem, n->path_gen));
            import_file(sem, n->path, n->path_gen);
        }

        Scope *scope      = get_scope(node);
        Scope *file_scope = get_scope(cast(Ast*, map_get_assert(&sem->files, n->path)));

        array_iter (c, &n->configs) {
            if (! c->init) {
                Ast *d = scope_lookup_outside_in(sem, file_scope, c->name, cast(Ast*, c));
                if (! d) return RESULT_DEFER;
                scope_add(sem, scope, c->name, d, cast(Ast*, c));
            }

            set_type(cast(Ast*, c), sem->core_types.type_Void);
        }

        if (! n->alias) {
            String a = str_suffix_from_last(*n->path, '/');
            assert_dbg(str_ends_with(a, sem->interns->file_extension));
            a.count -= sem->interns->file_extension.count;
            n->alias = intern_str(sem->interns, a);
        }

        scope_add(sem, scope, n->alias, node, node);
        pop_namegen(sem, node);
        set_type(node, alloc_type_misc(sem, node));
        return RESULT_OK;
    }

    case AST_INDEX: {
        AstIndex *n = cast(AstIndex*, node);
        Type *t = try_get_type(n->lhs);

        try(match_tv(sem, sem->core_types.type_U64, &n->idx));

        if (t->tag == TYPE_ARRAY) {
            set_type(node, cast(TypeArray*, t)->element);
            node->flags |= AST_IS_LVALUE;
            return RESULT_OK;
        } else if (t->tag == TYPE_TUPLE) {
            try(eval(sem, n->idx));
            if (n->lhs->flags & AST_IS_TYPE) return error_n(sem, node, "Cannot index into tuple type whose fields have names.");

            AstTuple *tup = cast(TypeTuple*, t)->node;
            U64 idx       = sem_get_const(sem, n->idx).u64;
            Ast *field    = array_try_get(&tup->fields, idx);

            if (! field) return error_nn(sem, n->idx, cast(Ast*, tup), "Tuple out of bounds access. (idx = %lu, n_fields = %lu)", idx, tup->fields.count);
            node->flags |= AST_IS_LVALUE;
            set_type(node, try_get_type(field));
            sem_set_target(sem, node, field);
            return RESULT_OK;
        }

        return error_nt(sem, n->lhs, t, "expected array or tuple with unnamed fields.");
    }

    case AST_STRING_LITERAL: {
        AstStringLiteral *n = cast(AstStringLiteral*, node);
        Type *a = alloc_type_array(sem, node, n->str->count, sem->core_types.type_U8);
        set_type(node, alloc_type_pointer(sem, node, a));
        return RESULT_OK;
    }

    case AST_ENUM: {
        AstEnum *n = cast(AstEnum*, node);
        Type *raw = n->type ? try_get_type_t(n->type) : sem->core_types.type_U64;

        if (n->type) {
            if ((raw->tag != TYPE_INT) || (raw->flags & TYPE_IS_DISTINCT)) return error_nt(sem, n->type, raw, "but expected indistinct int type.");
            if (n->is_flags && cast(TypeInt*, raw)->is_signed) return error_nt(sem, n->type, raw, "but the raw type of flag enums must be unsigned.");
        }

        if (! get_type(node)) {
            Type *t = alloc_type(sem, TYPE_ENUM);
            cast(TypeEnum*, t)->node = n;
            cast(TypeEnum*, t)->raw = raw;
            set_type(node, t);
        }

        Scope *scope = get_scope(node);
        if (! (scope->owner->flags & AST_IS_SEALED_SCOPE)) return RESULT_DEFER;

        { // Wait for fields to get types and explicit inits to eval:
            Bool found; Auto val = map_uadd(&sem->node_to_val, node->id, &found);

            map_iter_from (field, &scope->map, found ? val->u32 : 0) {
                assert_dbg(field->val->tag == AST_ENUM_FIELD);

                Ast *init = cast(AstEnumField*, field->val)->init;

                if (! get_type(field->val)) {
                    val->u32 = MAP_IDX;
                    return RESULT_DEFER;
                } else if (! init) {
                    if (n->is_explicit) return error_n(sem, field->val, "All fields in this enum must have explicit initializers.");
                } else if (! (init->flags & AST_EVALED)) {
                    val->u32 = MAP_IDX;
                    return RESULT_DEFER;
                }
            }
        }

        { // Handle implicit field values and the mask section if any:
            tmem_new(tm);

            Ast *mask_mark = 0;
            Bool overflow  = false;
            Value value    = n->is_flags ? vm_value_box(raw, 1) : (Value){};
            SemIter *iter  = sem_iter_new(tm, sem, &n->members);

            while (sem_iter_next(iter)) {
                if (iter->node->tag == AST_DUMMY) {
                    if (! n->is_flags) return error_n(sem, iter->node, "Only enums with the flags attribute can have a mask section.");
                    mask_mark = iter->node;
                    break;
                }

                assert_dbg(iter->node->tag == AST_ENUM_FIELD);
                AstEnumField *f = cast(AstEnumField*, iter->node);

                if (f->init) {
                    overflow = false;
                    value = sem_get_const(sem, f->init);
                    if (n->is_implicit) return error_n(sem, cast(Ast*, f), "All fields in this enum must have implicit initializers.");
                    if (n->is_flags) if (! is_pow2(vm_value_to_u64(raw, value))) return error_n(sem, f->init, "Entries in flag enums must be powers of 2.");
                } else if (overflow) {
                    return error_n(sem, cast(Ast*, f), "enum field value overflows.");
                } else {
                    map_add(&sem->bin_consts, iter->node->id, value);
                    iter->node->flags |= AST_EVALED;
                }

                #define Y(V) ({ Type(V) v = cast(Type(V), n->is_flags ? V<<1 : V+1); overflow = (v < V); V = v; })
                    #define X(T, S, W) else if (raw == sem->core_types.type_##T) { if (S) Y(value.i##W); else Y(value.u##W); }
                        if (false); EACH_BUILTIN_INT_TYPE(X)
                    #undef X
                #undef Y
            }

            if (mask_mark) {
                while (sem_iter_next(iter)) {
                    assert_dbg(iter->node->tag == AST_ENUM_FIELD);
                    AstEnumField *f = cast(AstEnumField*, iter->node);
                    if (! f->init) return error_nn(sem, cast(Ast*, f), mask_mark, "enum fields in the masks section must have an explicit initializor.");
                }
            }
        }

        if (! n->is_indistinct) {
            tmem_new(tm);
            Map(U64, Ast*) dedup; map_init(&dedup, tm);

            map_iter (entry, &scope->map) {
                Ast *f = entry->val;
                Ast *init = cast(AstEnumField*, f)->init;
                Value c = sem_get_const(sem, init ? init : f);
                U64 k = vm_value_to_u64(raw, c);
                Bool found; Auto val = map_uadd(&dedup, k, &found);
                if (found) return error_nn(sem, f, *val, "Fields in this enum must have distinct values.\n");
                *val = f;
            }
        }

        map_remove(&sem->node_to_val, node->id);
        return RESULT_OK;
    }

    case AST_ENUM_FIELD: {
        AstEnumField *n = cast(AstEnumField*, node);
        TypeEnum *t = cast(TypeEnum*, try_get_type(get_scope(node)->owner));
        if (n->init) try(match_tv(sem, t->raw, &n->init));
        set_type(node, cast(Type*, t));
        return RESULT_OK;
    }

    case AST_ENUM_LITERAL: {
        AstEnumLiteral *n = cast(AstEnumLiteral*, node);
        Type *t = get_type(node);

        if (! t) {
            set_type(node, alloc_type_var(sem, node, TYPE_IS_UNTYPED_LIT));
            return RESULT_DEFER;
        } else if (t->tag == TYPE_VAR) {
            return RESULT_DEFER;
        } else if (t->tag != TYPE_ENUM) {
            return error_nt(sem, node, t, "but anonymous enum literals can only be bound to an enum type.");
        } else {
            Scope *s = get_scope(cast(Ast*, cast(TypeEnum*, t)->node));
            Ast *d = scope_lookup_outside_in(sem, s, n->name, node);
            return d ? RESULT_OK : RESULT_DEFER;
        }
    }

    case AST_TUPLE: {
        AstTuple *n = cast(AstTuple*, node);
        Ast *f = array_get(&n->fields, 0);

        try_get_type(f);
        if (f->flags & AST_IS_TYPE) array_iter_from (f, &n->fields, 1) try_get_type_t(f);
        else                        array_iter_from (f, &n->fields, 1) try_get_type_v(f);

        node->flags |= (f->flags & AST_IS_TYPE) ? AST_IS_TYPE : AST_IS_LITERAL;
        Type *t = set_type(node, alloc_type_tuple(sem, n));
        if ((node->flags & AST_IS_LITERAL) && !(node->flags & AST_IN_STANDALONE_POSITION)) t->flags |= TYPE_IS_UNTYPED_LIT;
        return RESULT_OK;
    }

    case AST_TUPLE_FIELD: {
        AstTupleField *n = cast(AstTupleField*, node);
        Type *t = (node->flags & AST_IS_TYPE) ? try_get_type_t(n->rhs) : try_get_type_v(n->rhs);
        set_type(node, t);
        node->flags |= (n->rhs->flags & AST_EVALED);
        return RESULT_OK;
    }

    case AST_STRUCT: {
        AstStruct *n = cast(AstStruct*, node);
        if (! get_type(node)) set_type(node, alloc_type_struct(sem, n)); // Could already have a type if it's a poly instance.
        if (! n->members.count) return error_n(sem, node, "Structs cannot be zero sized.");
        return RESULT_OK;
    }

    case AST_STRUCT_LITERAL: {
        AstStructLiteral *n = cast(AstStructLiteral*, node);
        Type *t = get_type(node);

        if (t) {
            if (t->tag == TYPE_VAR) return RESULT_DEFER;
        } else if (n->lhs) {
            t = try_get_type_t(n->lhs);
        } else {
            set_type(node, alloc_type_var(sem, node, TYPE_IS_UNTYPED_LIT));
            return RESULT_DEFER;
        }

        if (t->tag != TYPE_STRUCT) {
            if (n->lhs) return error_nt(sem, n->lhs, t, "expected a struct.");
            return error_nt(sem, node, t, "but anonymous struct literals can only be bound to a struct type.");
        }

        Ast *d = cast(Ast*, cast(TypeStruct*, t)->node);
        Scope *s = get_scope(d);
        if (! (s->owner->flags & AST_IS_SEALED_SCOPE)) return RESULT_DEFER;

        set_type(node, t);

        if ((d->flags & AST_IS_UNION) && n->inits.count > 1)
            return error_n(sem, cast(Ast*, array_get_last(&n->inits)), "Union literal can only have 1 initializer.");

        tmem_new(tm);
        Map(IString*, Ast*) dedup; map_init(&dedup, tm);
        array_iter (i, &n->inits) {
            Ast *init = cast(Ast*, i);

            Bool found; Auto val = map_uadd(&dedup, i->name, &found);
            if (found) return error_nn(sem, *val, init, "Overriding initializers.");
            *val = init;

            Ast *d = scope_lookup_outside_in(sem, s, i->name, init);
            if (! d) return error_nn(sem, init, s->owner, "Reference to undeclared struct member.");
        }

        return RESULT_OK;
    }

    case AST_STRUCT_LIT_INIT: {
        AstStructLitInit *n = cast(AstStructLitInit*, node);
        Ast *d = n->sem_edge;
        return d ? match_nv(sem, d, &n->val) : RESULT_DEFER;
    }

    case AST_ARRAY_TYPE: {
        AstArrayType *n = cast(AstArrayType*, node);
        Type *elem = try_get_type_t(n->element);

        if (! (n->length->flags & AST_EVALED)) return RESULT_DEFER;
        try(match_tv(sem, sem->core_types.type_U64, &n->length));

        U64 l = sem_get_const(sem, n->length).u64;
        set_type(node, alloc_type_array(sem, node, l, elem));
        return l ? RESULT_OK : error_n(sem, n->length, "Array size cannot be zero.");
    }

    case AST_ARRAY_LITERAL: {
        AstArrayLiteral *n = cast(AstArrayLiteral*, node);

        if (n->element) {
            Type *e = try_get_type_t(n->element);
            if (e->flags & TYPE_IS_SPECIAL) return error_nt(sem, n->element, e, "expected a concrete type.");
            array_iter (init, &n->inits, *) try(match_nv(sem, n->element, init));
            set_type(node, alloc_type_array(sem, node, n->inits.count, e));
        } else {
            Type *t = get_type(node);

            if (! t) {
                t = set_type(node, alloc_type_array(sem, node, n->inits.count, 0));
                if (! (node->flags & AST_IN_STANDALONE_POSITION)) t->flags |= TYPE_IS_UNTYPED_LIT;
            }

            if (t->flags & TYPE_IS_UNTYPED_LIT) return RESULT_DEFER;

            Ast *first = array_get(&n->inits, 0);
            Type *e = try_get_type_v(first);
            cast(TypeArray*, t)->element = e;
            if (e->flags & TYPE_IS_SPECIAL) return error_nt(sem, first, e, "expected a concrete type.");
            array_iter_from (init, &n->inits, 1, *) try(match_nv(sem, first, init));
        }

        return RESULT_OK;
    }

    case AST_DEREF: {
        AstBaseUnary *n = cast(AstBaseUnary*, node);
        Type *t = try_get_type_v(n->op);
        if (t->tag != TYPE_POINTER) return error_nt(sem, n->op, t, "expected a pointer.");
        set_type(node, cast(TypePointer*, t)->pointee);
        return RESULT_OK;
    }

    case AST_ADDRESS_OF: {
        AstBaseUnary *n = cast(AstBaseUnary*, node);
        Type *ot = try_get_type(n->op);
        TypeFlags ptr_const_flag = 0;

        if (! (n->op->flags & AST_IS_TYPE)) {
            Result r = check_is_read_only(sem, n->op);
            if (r == RESULT_DEFER) return r;
            if (r == RESULT_OK) ptr_const_flag = TYPE_IS_CONST_POINTER;
        }

        Type *t = alloc_type_pointer(sem, node, ot);
        t->flags |= ptr_const_flag;
        set_type(node, t);

        if (n->op->flags & AST_IS_TYPE) {
            node->flags |= AST_IS_TYPE;
        } else {
            Ast *target = get_target(n->op);
            if (target) target->flags |= AST_ADDRESS_TAKEN;
            if (is_tvar_untyped_lit(ot)) t->flags |= TYPE_IS_UNTYPED_LIT;
        }

        return RESULT_OK;
    }

    case AST_ARG_POLY_VALUE: {
        AstArgPolyValue *n = cast(AstArgPolyValue*, node);

        if (n->init && n->constraint) {
            try_get_type_t(n->constraint);
            if (! (n->constraint->flags & AST_HAS_POLY_ARGS)) try(match_nv(sem, n->constraint, &n->init));
        } else if (n->init) {
            Type *t = try_get_type_v(n->init);
            if (t->flags & TYPE_IS_SPECIAL) return error_nt(sem, n->init, t, "expected a concrete type.");
            n->constraint = ast_alloc(sem->mem, AST_DUMMY, AST_IS_TYPE);
            n->constraint->pos = ast_trimmed_pos(sem->interns, node);
            add_to_check_list(sem, n->constraint, get_scope(node));
            set_type(n->constraint, t);
        }

        set_type(node, alloc_type_var(sem, node, 0));
        return RESULT_OK;
    }

    case AST_VAR_DEF: {
        AstVarDef *n = cast(AstVarDef*, node);

        if (n->init && n->constraint) {
            Type *t = try_get_type_t(n->constraint);
            if (! (n->constraint->flags & AST_HAS_POLY_ARGS)) try(match_nv(sem, n->constraint, &n->init));
            set_type(node, t);
        } else if (n->init) {
            Type *t = try_get_type_v(n->init);
            if (t->flags & TYPE_IS_SPECIAL) return error_nt(sem, n->init, t, "expected a concrete type.");
            set_type(node, t);
        } else {
            set_type(node, try_get_type_t(n->constraint));
        }

        if (node->flags & AST_IS_POLYMORPH_INSTANCE) {
            Ast *d = *cast(Ast**, map_get_assert(&sem->node_to_val, node->id).ptr);

            if (is_tvar_fn(try_get_type(d))) {
                Ast *instance = get_target(d);
                assert_dbg(instance);
                map_add(&sem->ast_consts, node->id, instance);
                node->flags |= AST_CAN_EVAL | AST_EVALED | AST_CAN_EVAL_WITHOUT_VM;
            } else {
                try(eval(sem, d));
                infer_const(sem, get_type(node), sem_get_const(sem, d), d, node);
            }

            map_remove(&sem->node_to_val, node->id);
        }

        return RESULT_OK;
    }

    case AST_ARG_POLY_TYPE: {
        AstArgPolyType *n = cast(AstArgPolyType*, node);
        if (! (node->flags & AST_IN_POLY_ARG_POSITION)) return error_n(sem, node, "Poly type definition in invalid position.");
        if (n->init) try_get_type_t(n->init);
        set_type(node, alloc_type_var(sem, node, 0));
        return RESULT_OK;
    }

    case AST_ARG_POLY_CODE: {
        set_type(node, alloc_type_var(sem, node, 0));
        return RESULT_OK;
    }

    case AST_STRUCT_POLY: {
        AstStructPoly *n = cast(AstStructPoly*, node);
        array_iter (a, &n->args) { Ast *d = get_init(a); if (d && (d->flags & AST_MUST_EVAL) && !(d->flags & AST_EVALED)) return RESULT_DEFER; }
        set_type(node, alloc_type_misc(sem, node));
        return RESULT_OK;
    }

    case AST_FN_POLY: {
        AstBaseFn *n = cast(AstBaseFn*, node);
        Type *t = get_type(node);

        if (! t) {
            array_iter (a, &n->inputs) {
                Ast *d = get_init(a);
                if (d && (d->flags & AST_MUST_EVAL) && !(d->flags & AST_EVALED)) return RESULT_DEFER;
            }

            if (n->output) try_get_type_t(n->output);

            if (node->flags & AST_IN_STANDALONE_POSITION) {
                set_type(node, alloc_type_misc(sem, node));
                return RESULT_OK;
            } else {
                set_type(node, alloc_type_var(sem, node, TYPE_IS_TVAR_FN));
                U64 i = array_find(&n->inputs, (IT->tag == AST_ARG_POLY_TYPE) || (IT->tag == AST_ARG_POLY_VALUE));
                return (i == ARRAY_NIL_IDX) ? RESULT_DEFER : error_n(sem, node, "Polymorphic functions with comptime arguments cannot be assigned.");
            }
        }

        return (t->tag == TYPE_VAR) ? RESULT_DEFER : RESULT_OK;
    }

    case AST_FN:
    case AST_FN_TYPE: 
    case AST_FN_LINUX: {
        AstBaseFn *n = cast(AstBaseFn*, node);

        array_iter (a, &n->inputs) {
            Ast *d = get_init(a);
            if (d && !(d->flags & AST_EVALED)) return RESULT_DEFER;
        }

        if (n->output) try_get_type_t(n->output);
        Type *t = (node->flags & AST_IS_MACRO) ? alloc_type_misc(sem, node) : alloc_type_fn(sem, n);
        set_type(node, t);
        return RESULT_OK;
    }

    case AST_RETURN: {
        AstReturn *n = cast(AstReturn*, node);
        Scope *scope = get_scope(node);
        Bool backticked = (node->flags & AST_BACKTICKED);

        for (; scope; scope = scope->parent) {
            if (scope->owner->tag == AST_FN) {
                if (!backticked || !(scope->owner->flags & AST_IS_MACRO_INSTANCE)) break;
            } else {
                Ast *c = cast(Ast*, scope_get_constraint(scope));
                if (c && (c->flags & AST_BACKTICKED)) backticked = true;
            }
        }

        if (! scope) return error_n(sem, node, "A return can only appear inside functions.");
        AstBaseFn *p = cast(AstBaseFn*, scope->owner);
        if (!n->result != !p->output) return error_nn(sem, cast(Ast*, p), node, "Number of return values is not matching.");
        if (n->result) try(match_nv(sem, p->output, &n->result));
        sem_set_target(sem, node, cast(Ast*, p));
        return RESULT_OK;
    }

    case AST_EMBED: {
        AstEmbed *n = cast(AstEmbed*, node);

        if (n->sem_edge) return get_type(node) ? RESULT_OK : RESULT_DEFER;
        if (node->flags & AST_IN_POLY_ARG_POSITION) return error_n(sem, node, "An embed cannot appear in a position where a polymorphic parameter definition can be.");

        array_iter (ref, &n->refs) {
            if (ref->tag == AST_PAIR) {
                Ast *l = cast(AstBaseBinary*, ref)->op1;
                Ast *r = cast(AstBaseBinary*, ref)->op2;
                if (!(l->flags & AST_EVALED) || !(r->flags & AST_EVALED)) return RESULT_DEFER;
            } else if (! (ref->flags & AST_EVALED)) {
                return RESULT_DEFER;
            }
        }

        if (! (n->generator->flags & AST_EVALED)) return RESULT_DEFER;
        try(match_tv(sem, sem->core_types.type_string, &n->generator));

        Ast *gen        = (n->generator->tag == AST_CAST) ? cast(AstCast*, n->generator)->expr : 0;
        Ast *val        = (gen && gen->flags & AST_CAN_EVAL_WITHOUT_VM) ? sem_get_const(sem, gen).ast : 0;
        Ast *parsed_ast = (val && (val->tag == AST_CALL_MACRO_ARG)) ? cast(AstCallMacroArg*, val)->parsed_ast: 0;

        if (parsed_ast) {
            // The code we're embedding originates from an already parsed
            // tree like the trailing block of a macro invocation, so we
            // don't want to re-parse it. This improves debugging, error
            // messages, and compile times.
            Ast *code  = ast_deep_copy(sem->mem, parsed_ast, 0, 0);
            gen        = ast_alloc(sem->mem, AST_CODE_GEN, AST_ENDS_WITH_BLOCK);
            gen->pos   = code->pos;
            cast(AstCodeGen*, gen)->origin = node;
            array_push(&cast(AstCodeGen*, gen)->children, code);
        } else {
            String code = get_string_const(sem, n->generator);
            gen = cast(Ast*, par_parse_codegen(sem->parser, code, node, get_file(node), n->level));
        }

        sem_set_target(sem, node, gen);
        add_to_check_list(sem, gen, get_scope(node));
        if (node->flags & AST_IS_BINDGEN) pop_namegen(sem, node);

        if (n->level == AST_LEVEL_EXPR) {
            Ast *g = array_get(&cast(AstCodeGen*, gen)->children, 0);
            g->flags |= (node->flags & AST_IN_STANDALONE_POSITION);
            add_to_infer_list(sem, g, node);
            return RESULT_DEFER;
        }

        return RESULT_OK;
    }

    case AST_DEFER: {
        Scope *s = get_scope(node);

        if (node->flags & AST_BACKTICKED) {
            Scope *scope = scope_get_ancestor(s, AST_FN);
            if (!scope || !(scope->owner->flags & AST_IS_MACRO_INSTANCE)) return error_n(sem, node, "A backticked defer can only appear inside a macro.");
            sem_set_target(sem, node, scope->parent->owner);
        } else {
            Ast *target = scope_get_non_codegen_ancestor(s)->owner;
            sem_set_target(sem, node, target);
        }

        return RESULT_OK;
    }

    case AST_SELF: {
        Scope *s = scope_get_ancestor(get_scope(node), AST_FN);
        if (!s || (s->owner->flags & AST_IS_MACRO_INSTANCE)) return error_n(sem, node, "The .self() builtin can only appear in the body of a function.");
        set_type(node, try_get_type(s->owner));
        sem_set_target(sem, node, s->owner);
        return RESULT_OK;
    }

    case AST_CALLER_INFO: {
        AstCallerInfo *n = cast(AstCallerInfo*, node);
        if (! n->as_default_arg) return error_n(sem, node, "The .caller() builtin can only appear as default argument of fn/macro/struct.");
        set_type(node, sem->core_types.type_caller_info);
        return RESULT_OK;
    }

    case AST_CALL_DEFAULT_ARG: {
        AstCallDefaultArg *n = cast(AstCallDefaultArg*, node);
        set_type(node, try_get_type(n->arg));
        return RESULT_OK;
    }

    case AST_CALL: {
        AstCall *n = cast(AstCall*, node);
        Ast *d = n->sem_edge;

        if (d) { // Wait for poly instance to get typed:
            if (d->tag == AST_FN) {
                Ast *out = cast(AstBaseFn*, d)->output;
                set_type(node, (out ? try_get_type(out) : sem->core_types.type_Void));
            } else {
                assert_dbg(d->tag == AST_STRUCT);
                set_type(node, try_get_type(d));
            }

            return RESULT_OK;
        }

        Type *t = try_get_type(n->lhs);

        if (t->tag == TYPE_FN) {
            try_get_type_v(n->lhs); // Assert it's a value.
            AstBaseFn *fn = cast(TypeFn*, t)->node;
            if (cast(Ast*, fn)->flags & AST_IS_MACRO) return error_nn(sem, node, cast(Ast*, fn), "Cannot call macro using the parens operator (). Use the : operator.");
            set_type(node, fn->output ? try_get_type(fn->output) : sem->core_types.type_Void);
            return check_call(sem, cast(Ast*, fn), &fn->inputs, node, &n->args, true);
        }

        if (t->tag == TYPE_MISC) {
            Ast *c = cast(TypeMisc*, t)->node;

            if (c->flags & AST_IS_MACRO) {
                return error_nn(sem, node, c, "Cannot call macro using the parens operator (). Use the : operator.");
            } else if (c->tag == AST_FN_POLY) {
                try(check_call(sem, c, &cast(AstBaseFn*, c)->inputs, node, &n->args, true));
                if (n->lhs->tag == AST_IDENT) sem_set_target(sem, n->lhs, n->sem_edge);
                return RESULT_DEFER; // Wait for poly instance to get typed.
            } else if (c->tag == AST_STRUCT_POLY) {
                node->flags |= AST_IS_TYPE;

                if (node->flags & AST_HAS_POLY_ARGS) {
                    try(check_call_args_layout(sem, c, &cast(AstStructPoly*, c)->args, node, &n->args));
                    set_type(node, alloc_type_var(sem, node, 0));
                    sem_set_target(sem, node, c);
                    return RESULT_OK;
                } else {
                    try(check_call(sem, c, &cast(AstStructPoly*, c)->args, node, &n->args, true));
                    return RESULT_DEFER; // Wait for poly instance to get typed.
                }
            }
        }

        return error_nt(sem, n->lhs, t, "expected function or poly-struct type.");
    }

    case AST_CALL_MACRO_ARG: {
        AstCallMacroArg *n = cast(AstCallMacroArg*, node);
        Type *a = alloc_type_array(sem, node, n->code.count, sem->core_types.type_U8);
        set_type(node, alloc_type_pointer(sem, node, a));
        return RESULT_OK;
    }

    case AST_CALL_MACRO: {
        AstCallMacro *n = cast(AstCallMacro*, node);
        Type *t = try_get_type(n->lhs);
        Ast *m = (t->tag == TYPE_MISC) ? cast(TypeMisc*, t)->node : 0;

        if (!m || !(m->flags & AST_IS_MACRO)) return error_nt(sem, n->lhs, t, "expected a macro.");

        Ast *out = cast(AstBaseFn*, m)->output;
        ArrayAst *def_args = &cast(AstBaseFn*, m)->inputs;

        if (! get_type(node)) {
            Scope *scope = get_scope(node);

            array_iter (arg, &n->args) { // Rewrite AstCallMacroBArg's into AstCallMacroArg.
                if (arg->tag != AST_CALL_MACRO_BARG) continue;

                AstCallMacroBArg *a = cast(AstCallMacroBArg*, arg);

                if (a->code->flags & AST_EVALED) {
                    Ast *c = ast_alloc(sem->mem, AST_CALL_MACRO_ARG, 0);
                    c->pos = arg->pos;
                    cast(AstCallMacroArg*, c)->code = get_string_const(sem, a->code);
                    add_to_check_list(sem, c, scope);
                    array_set(&n->args, ARRAY_IDX, c);
                } else {
                    return RESULT_DEFER;
                }
            }

            set_type(node, (out ? try_get_type(out) : sem->core_types.type_Void));

            if (node->flags & AST_ENDS_WITH_BLOCK) {
                // Wrap the trailing block argument into an AstCallNamedArg
                // for better error messages. The check_call_args_layout()
                // call below will undo this wrap, which allows us to use
                // the same dummy AstCallNamedArg node for all macro calls.
                Ast *last = array_get_last(&n->args);
                cast(Ast*, sem->dummy_named_arg)->pos = last->pos;
                sem->dummy_named_arg->arg  = last;
                sem->dummy_named_arg->name = get_name(array_get_last(def_args));
                set_scope(cast(Ast*, sem->dummy_named_arg), scope);
                array_set_last(&n->args, cast(Ast*, sem->dummy_named_arg));
            }

            try(check_call_args_layout(sem, m, def_args, node, &n->args));
            par_parse_macro_args(sem->parser, get_file(node), def_args, n);
            array_iter (arg, &n->args) add_to_check_list(sem, arg, scope);
        }

        try(check_call(sem, m, def_args, node, &n->args, false));
        if (n->lhs->tag == AST_IDENT) sem_set_target(sem, n->lhs, n->sem_edge);
        return RESULT_OK;
    }

    case AST_IDENT: {
        AstIdent *n = cast(AstIdent*, node);
        Ast *d = n->sem_edge;

        if (d) {
            if (get_type(node) && (d->tag == AST_FN_POLY)) return RESULT_DEFER;
        } else {
            d = scope_lookup_inside_out(sem, get_scope(node), n->name, node);
            if (! d) return RESULT_DEFER;
        }

        Type *dt = try_get_type(d);

        if (!(node->flags & AST_IN_POLY_ARG_POSITION) && is_tvar_type(dt)) {
            return error_nn(sem, node, d, "Cannot reference a polymorphic expression from this position.");
        } else if (d->tag == AST_FN_POLY) {
            if (node->flags & AST_IN_STANDALONE_POSITION) {
                set_type(node, dt);
            } else {
                ArrayAst *a = &cast(AstBaseFn*, d)->inputs;
                U64 i = array_find(a, (IT->tag == AST_ARG_POLY_TYPE) || (IT->tag == AST_ARG_POLY_VALUE));
                if (i != ARRAY_NIL_IDX) return error_n(sem, node, "Polymorphic functions with comptime arguments cannot be assigned.");
                set_type(node, alloc_type_var(sem, node, TYPE_IS_TVAR_FN));
            }

            return RESULT_DEFER;
        } else {
            set_type(node, dt);
            node->flags |= (d->flags & AST_IS_TYPE);
            return RESULT_OK;
        }
    }

    case AST_DOT: {
        AstDot *n = cast(AstDot*, node);
        Type *t = try_get_type(n->lhs);

        if (t->tag == TYPE_ENUM) {
            Ast *c = cast(Ast*, cast(TypeEnum*, t)->node);
            Ast *d = scope_lookup_outside_in(sem, get_scope(c), n->rhs, node);
            if (! d) return RESULT_DEFER;
            set_type(node, try_get_type(d));
            return RESULT_OK;
        }

        if (t->tag == TYPE_MISC && cast(TypeMisc*, t)->node->tag == AST_IMPORT) {
            AstImport *i = cast(AstImport*, cast(TypeMisc*, t)->node);
            Ast *f = cast(Ast*, map_get_assert(&sem->files, i->path));
            Ast *d = scope_lookup_outside_in(sem, get_scope(f), n->rhs, node);
            if (!d || !get_type(d)) return RESULT_DEFER;
            set_type(node, get_type(d));
            node->flags |= d->flags & (AST_IS_TYPE | AST_IS_LVALUE);
            return RESULT_OK;
        }

        try_get_type_v(n->lhs); // Assert it's a value.

        if (is_tvar_type(t)) {
            node->flags |= AST_IS_TYPE;
            set_type(node, alloc_type_var(sem, node, 0));
            return RESULT_OK;
        }

        if (t->tag == TYPE_STRUCT) {
            Ast *c = cast(Ast*, cast(TypeStruct*, t)->node);
            Ast *d = scope_lookup_outside_in(sem, get_scope(c), n->rhs, node);
            if (! d) return RESULT_DEFER;
            Type *dt = try_get_type(d);
            node->flags |= AST_IS_LVALUE | (d->flags & AST_IS_TYPE);
            if ((d->flags & AST_EVALED) && !(d->flags & AST_IS_TYPE)) infer_const(sem, dt, sem_get_const(sem, d), d, node);
            set_type(node, dt);
            return RESULT_OK;
        }

        if (t->tag == TYPE_TUPLE) {
            Ast *tup = cast(Ast*,  cast(TypeTuple*, t)->node);
            if (! (tup->flags & AST_CREATES_SCOPE)) return error_nn(sem, node, tup, "Cannot use dot operator on tuples with unnamed fields. Use the index operator [] instead.");
            Ast *d = scope_lookup_outside_in(sem, get_scope(tup), n->rhs, node);
            if (!d || !get_type(d)) return RESULT_DEFER;
            node->flags |= AST_IS_LVALUE;
            set_type(node, get_type(d));
            return RESULT_OK;
        }

        return error_n(sem, n->lhs, "Invalid lhs for dot operator.");
    }

    case AST_IF_CT: {
        AstIfCt *n = cast(AstIfCt*, node);

        if (! (n->cond->flags & AST_EVALED)) return RESULT_DEFER;
        try(match_tv(sem, sem->core_types.type_Bool, &n->cond));

        Scope *scope = get_scope(node);
        ArrayAst *arm = sem_get_const(sem, n->cond).u8 ? &n->then_arm : &n->else_arm;
        array_iter (it, arm) add_to_check_list(sem, it, scope);

        pop_namegen(sem, node);
        return RESULT_OK;
    }

    case AST_TYPEOF: {
        AstBaseUnary *n = cast(AstBaseUnary*, node);
        Type *t = try_get_type(n->op);

        if (is_tvar_value(t)) {
            Ast *c = cast(TypeVar*, t)->node;
            if (c->tag == AST_ARG_POLY_CODE) return error_nt(sem, n->op, t, "expected a concrete type.");
            assert_dbg(c->tag == AST_ARG_POLY_VALUE);
            set_type(node, try_get_type_t(cast(AstArgPolyValue*, c)->constraint));
        } else if ((t->flags & TYPE_IS_SPECIAL) && !is_tvar_type(t) && !is_tvar_dot(t) && !is_tvar_call(t)) {
            return error_nt(sem, n->op, t, "expected a concrete type.");
        } else {
            set_type(node, t);
        }

        return RESULT_OK;
    }

    case AST_TYPE_ID: {
        AstBaseUnary *n = cast(AstBaseUnary*, node);
        Type *t = try_get_type(n->op);
        if (t->flags & TYPE_IS_SPECIAL) return error_nt(sem, n->op, t, "expected a concrete type.");
        set_type(node, sem->core_types.type_U64);
        return RESULT_OK;
    }

    case AST_TYPE_DISTINCT: {
        AstTypeDistinct *n = cast(AstTypeDistinct*, node);
        Type *t   = try_get_type_t(n->val);
        Type *dt = 0;

        if (t->flags & TYPE_IS_SPECIAL) {
            return error_nt(sem, n->val, t, "expected a concrete type");
        } else if (n->val->flags & AST_CREATES_TYPE) {
            dt = t;
        } else {
            U64 size = get_type_struct_size[t->tag];
            dt = mem_alloc(sem->mem, Type, .align=get_type_struct_align[t->tag], .size=size);
            memcpy(dt, t, size);
            dt->id = sem->next_type_id++;
        }

        dt->flags |= TYPE_IS_DISTINCT;
        map_add(&sem->type_def, dt->id, node);
        set_type(node, dt);
        return RESULT_OK;
    }

    case AST_CT_ASSERT: {
        Ast *cond = cast(AstBaseUnary*, node)->op;
        if (! (cond->flags & AST_EVALED)) return RESULT_DEFER;
        try(match_tv(sem, sem->core_types.type_Bool, &cast(AstBaseUnary*, node)->op));
        U8 val = sem_get_const(sem, cond).u8;
        return val ? RESULT_OK : error_n(sem, cond, "Compile-time assert failed.");
    }

    case AST_RAW: {
        AstBaseUnary *n = cast(AstBaseUnary*, node);
        Type *t = try_get_type(n->op);
        if (t->tag != TYPE_ENUM) return error_nt(sem, n->op, t, "expected enum type.");
        node->flags |= (n->op->flags & AST_IS_TYPE);
        set_type(node, cast(TypeEnum*, t)->raw);
        return RESULT_OK;
    }

    case AST_CAST: {
        AstCast *n = cast(AstCast*, node);
        Type *et = try_get_type_v(n->expr);
        Type *tt;

        if (n->implicit) {
            if (n->to) {
                tt = try_get_type(n->to);
                set_type(node, tt);
            } else {
                tt = try_get_type(node);
            }
        } else {
            if (n->to) {
                tt = try_get_type(n->to);
                set_type(node, tt);
            } else {
                tt = get_type(node);

                if (! tt) {
                    set_type(node, alloc_type_var(sem, node, TYPE_IS_UNTYPED_LIT));
                    return RESULT_DEFER;
                } else if (is_tvar_untyped_lit(tt)) {
                    return RESULT_DEFER;
                }
            }

            if (!(tt->flags & TYPE_IS_PRIMITIVE) && (tt->tag != TYPE_POINTER)) return error_nt(sem, n->to ? n->to : node, tt, "but expected float|bool|int|enum|pointer.");
            if (!(et->flags & TYPE_IS_PRIMITIVE) && (et->tag != TYPE_POINTER)) return error_nt(sem, n->expr, et, "but expected float|bool|int|enum|pointer.");
            if (tt->tag == TYPE_POINTER || et->tag == TYPE_POINTER) node->flags &= ~AST_CAN_EVAL_WITHOUT_VM;
            if (n->tag == AST_CAST_BITWISE) {
                U64 a = abi_of_obj(sem->abi, et).size;
                U64 b = abi_of_obj(sem->abi, tt).size;
                if (a != b) return error_n(sem, node, "Operands of bitcast must be have same size: (%lu vs %lu).", a, b);
            }
        }

        if (tt == sem->core_types.type_any) {
            n->tag = AST_CAST_ANY;
            Ast *t = get_target(n->expr);
            if (t) t->flags |= AST_ADDRESS_TAKEN;
        } else if (tt->tag == TYPE_STRUCT) {
            n->tag = AST_CAST_SLICE;
        }

        return RESULT_OK;
    }

    case AST_NOT: {
        AstBaseUnary *n = cast(AstBaseUnary*, node);

        sem->match.without_error_reporting++;
        Result r = match_tv(sem, sem->core_types.type_Bool, &n->op);
        sem->match.without_error_reporting--;

        if (r == RESULT_DEFER) {
            return RESULT_DEFER;
        } else if (r == RESULT_OK) {
            set_type(node, sem->core_types.type_Bool);
            return RESULT_OK;
        } else {
            Type *t = get_type(n->op);
            if ((t->tag != TYPE_INT) && !(t->tag == TYPE_ENUM && cast(TypeEnum*, t)->node->is_flags)) return error_nt(sem, n->op, t, "expected int or flag enum type.");
            set_type(node, t);
            node->tag = AST_BITWISE_NOT;
            return RESULT_OK;
        }
    }

    case AST_ADD:
    case AST_SUB: {
        AstBaseBinary *n = cast(AstBaseBinary*, node);
        Type *t = try_get_type_v(n->op1);

        if (t->tag == TYPE_POINTER) {
            node->flags &= ~AST_CAN_EVAL_WITHOUT_VM;
            try(match_tv(sem, sem->core_types.type_U64, &n->op2));
        } else {
            try(check_assign_fusable_op(sem, n, node->tag));
            try(match_vv(sem, &n->op1, &n->op2));
        }

        set_type(node, t);
        return RESULT_OK;
    }

    case AST_MUL:
    case AST_DIV: {
        AstBaseBinary *n = cast(AstBaseBinary*, node);
        try(check_assign_fusable_op(sem, n, node->tag));
        try(match_vv(sem, &n->op1, &n->op2));
        set_type(node, get_type(n->op1));
        return RESULT_OK;
    }

    case AST_MOD:
    case AST_BITWISE_OR:
    case AST_BITWISE_XOR:
    case AST_BITWISE_AND: {
        AstBaseBinary *n = cast(AstBaseBinary*, node);
        try(check_assign_fusable_op(sem, n, node->tag));
        try(match_vv(sem, &n->op1, &n->op2));
        set_type(node, get_type(n->op1));
        return RESULT_OK;
    }

    case AST_NEGATE: {
        AstBaseUnary *n = cast(AstBaseUnary*, node);
        Type *t = try_get_type_v(n->op);
        if (t->tag != TYPE_INT) return error_nt(sem, n->op, t, "expected int type.");
        set_type(node, t);
        return RESULT_OK;
    }

    case AST_LESS:
    case AST_GREATER:
    case AST_LESS_EQUAL:
    case AST_GREATER_EQUAL: {
        AstBaseBinary *n = cast(AstBaseBinary*, node);
        Type *t = try_get_type_v(n->op1);
        if (t->tag != TYPE_INT && t->tag != TYPE_FLOAT && !is_tvar_untyped_lit(t)) return error_nt(sem, n->op1, t, "expected int or float type.");
        try(match_vv(sem, &n->op1, &n->op2));
        set_type(node, sem->core_types.type_Bool);
        return RESULT_OK;
    }

    case AST_EQUAL:
    case AST_NOT_EQUAL: {
        AstBaseBinary *n = cast(AstBaseBinary*, node);
        Type *t1 = try_get_type_v(n->op1);
        Type *t2 = try_get_type_v(n->op2);
        if (!(t1->flags & (TYPE_IS_PRIMITIVE | TYPE_IS_UNTYPED_LIT)) && t1->tag != TYPE_POINTER) return error_nt(sem, n->op1, t1, "expected primitive or pointer type.");
        if (!(t2->flags & (TYPE_IS_PRIMITIVE | TYPE_IS_UNTYPED_LIT)) && t2->tag != TYPE_POINTER) return error_nt(sem, n->op2, t2, "expected primitive or pointer type.");
        try(match_vv(sem, &n->op1, &n->op2));
        set_type(node, sem->core_types.type_Bool);
        return RESULT_OK;
    }

    case AST_LOGICAL_OR:
    case AST_LOGICAL_AND: {
        AstBaseBinary *n = cast(AstBaseBinary*, node);
        Type *t1 = try_get_type_v(n->op1);
        Type *t2 = try_get_type_v(n->op2);
        if (t1->tag != TYPE_BOOL) return error_nt(sem, n->op1, t1, "expected Bool.");
        if (t2->tag != TYPE_BOOL) return error_nt(sem, n->op2, t2, "expected Bool.");
        set_type(node, sem->core_types.type_Bool);
        return RESULT_OK;
    }

    case AST_SHIFT_LEFT:
    case AST_SHIFT_RIGHT: {
        AstBaseBinary *n = cast(AstBaseBinary*, node);
        try(check_assign_fusable_op(sem, n, node->tag));
        set_type(node, get_type(n->op1));
        return RESULT_OK;
    }

    case AST_ASSIGN: {
        AstBaseBinary *n = cast(AstBaseBinary*, node);
        Type *t = try_get_type_v(n->op1);
        Result r = check_is_read_only(sem, n->op1);

        if (r == RESULT_DEFER) return r;
        if (r == RESULT_OK) return error_n(sem, n->op1, "Cannot assign to read only entity.");
        if (! (n->op1->flags & AST_IS_LVALUE)) return error_n(sem, n->op1, "Invalid assign target.");

        AstTag op = cast(AstAssign*, n)->fused_op;

        if ((t->tag == TYPE_POINTER) && (op == AST_ADD || op == AST_SUB)) {
            try(match_tv(sem, sem->core_types.type_U64, &n->op2));
        } else {
            if (op != AST_ASSIGN) try(check_assign_fusable_op(sem, n, op));
            try(match_nv(sem, n->op1, &n->op2));
        }

        set_type(node, t);
        return RESULT_OK;
    }
    }

    badpath;
}

static Void add_to_infer_list (Sem *sem, Ast *from, Ast *to) {
    array_push_lit(&sem->infer_list, .from=from, .to=to);
}

// This is the entry point for semantically analyzing an ast.
// It will recursively add the entire ast into the analyzer.
static Void add_to_check_list (Sem *sem, Ast *n, Scope *scope) {
    if (!n || (n->flags & AST_ADDED_TO_CHECK_LIST)) return;
    n->flags |= AST_ADDED_TO_CHECK_LIST;

    set_scope(n, scope);

    switch (n->tag) {
    #define X(TAG, T) case TAG: if (cast(T*, n)->name) scope_add(sem, scope, cast(T*, n)->name, n, n); break;
        EACH_STATIC_NAME_GENERATOR(X)
    #undef X
    default: break;
    }

    if (n->flags & AST_IS_BINDGEN) push_namegen(n);
    if (n->tag == AST_FN && !(n->flags & (AST_IS_MACRO | AST_IS_MACRO_INSTANCE))) array_push(&sem->fns, cast(AstFn*, n));
    if (n->tag == AST_VAR_DEF && n->flags & AST_IS_GLOBAL) array_push(&sem->globals, cast(AstVarDef*, n));
    if ((n->flags & AST_MUST_EVAL) && !(n->flags & AST_EVALED)) array_push(&sem->eval_list, n);
    if (n->flags & AST_CREATES_SCOPE) scope = scope_new(sem, scope, n);

    if ((n->tag == AST_FN_POLY) || (n->tag == AST_STRUCT_POLY) || (n->flags & AST_IS_MACRO)) {
        PolyInfo *prev = sem->poly_info;
        sem->poly_info = alloc_poly_info(sem, n);
        array_iter (arg, sem->poly_info->args) add_to_check_list(sem, arg, scope);
        if (ast_get_base_flags[n->tag] & AST_BASE_FN) add_to_check_list(sem, cast(AstBaseFn*, n)->output, scope);
        sem->poly_info = prev;
    } else if (n->tag == AST_IF_CT) {
        add_to_check_list(sem, cast(AstIfCt*, n)->cond, scope);
    } else {
        #define ADD_TO_CHECK_LIST(child, ...) add_to_check_list(sem, child, scope);
        AST_VISIT_CHILDREN(n, ADD_TO_CHECK_LIST);
        if ((n->tag == AST_ARG_POLY_TYPE) || (n->tag == AST_ARG_POLY_VALUE) || (n->tag == AST_ARG_POLY_CODE)) array_push(&sem->poly_info->polyargs, n);
    }

    if ((n->flags & AST_CREATES_SCOPE) && (scope->namegens.count == 0)) scope_seal(sem, scope);
    array_push(&sem->check_list, n);
}

static Void check_nodes (Sem *sem) {
    Auto to_eval  = &sem->eval_list;
    Auto to_check = &sem->check_list;
    Auto to_infer = &sem->infer_list;

    while (true) {
        sem->found_a_sem_edge = false;
        U64 prev_to_check = to_check->count;

        array_iter (n, to_check) {
            if (check_node(sem, n) == RESULT_OK) {
                n->flags |= AST_CHECKED;
                if (! get_type(n)) set_type(n, sem->core_types.type_Void);
            }
            if (sem->error_count) sem_panic(sem);
        }

        array_iter (infer, to_infer, *) {
            Type *t = get_type(infer->from);
            if (!t || type_has_polyargs(t)) continue;
            set_type(infer->to, t);
            infer->to->flags |= (infer->from->flags & AST_IS_TYPE);
            infer->from = 0; // Mark for removal.
        }

        array_iter (n, to_eval) {
            eval(sem, n);
            if (sem->error_count) sem_panic(sem);
        }

        Bool new_to_check = (prev_to_check < to_check->count);
        Bool inferred     = to_infer->count - array_find_remove_all(to_infer, !IT.from);
        Bool evaled       = to_eval->count  - array_find_remove_all(to_eval, IT->flags & AST_EVALED);
        Bool checked      = to_check->count - array_find_remove_all(to_check, IT->flags & AST_CHECKED);

        if (!sem->found_a_sem_edge && !new_to_check && !checked && !inferred && !evaled) break;
    }

    if (to_check->count) error_no_progress(sem);
    assert_dbg(to_eval->count == 0);
}

SemProgram sem_check (Sem *sem, String main_file_path, Abi *abi) {
    if (! sem->initted_special_types) {
        IString *path = par_parse_import_path(sem->parser, str("%stdlib/core"));
        sem->core_file = import_file(sem, path, 0);

        IString *linux = par_parse_import_path(sem->parser, str("%stdlib/linux"));
        import_file(sem, linux, 0);

        #define X(N, T)\
            Ast *type_##N = array_find_get(&sem->core_file->statements, get_name(IT) == sem->interns->type_##N);\
            scope_add(sem, sem->autoimports, sem->interns->type_##N, type_##N, type_##N);

            EACH_SPECIAL_TYPE(X)
        #undef X

        check_nodes(sem);

        #define X(N, T) sem->core_types.type_##N = get_type(type_##N);
            EACH_SPECIAL_TYPE(X)
        #undef X

        sem->initted_special_types = true;
    }

    IString *path  = intern_str(sem->interns, main_file_path);
    AstFile *file  = import_file(sem, path, 0);
    IString *entry = sem->interns->entry_fn_name;

    sem->abi = abi;
    sem->main_fn = cast(AstFn*, array_find_get(&file->statements, (IT->tag == AST_FN) && (cast(AstFn*, IT)->name == entry)));

    if (! sem->main_fn) {
        sem_msg(msg, LOG_ERROR)
        astr_push_fmt(msg, "No entry function [%.*s] in main file.\n\n", STR(*entry));
        sem_panic(sem);
    }

    check_nodes(sem);
    array_iter_from (t, &sem->types, 1) if (t && t->tag == TYPE_STRUCT) check_type_is_finite(sem, t, 0);
    flush_codegen(sem);

    return (SemProgram){
        .sem     = sem,
        .fns     = &sem->fns,
        .types   = &sem->types,
        .entry   = sem->main_fn,
        .globals = &sem->globals,
    };
}

Sem *sem_new (Interns *interns, Mem *mem) {
    Sem *sem = mem_new(mem, Sem);
    sem->mem = mem;

    array_init(&sem->call_check.casts, mem);
    array_init(&sem->call_check.simple_untyped_lits, mem);
    array_init(&sem->call_check.untyped_lits, mem);
    array_init(&sem->call_check.values_to_match, mem);
    array_init(&sem->check_list, mem);
    array_init(&sem->eval_list, mem);
    array_init(&sem->infer_list, mem);
    map_init(&sem->files, mem);
    map_init(&sem->node_to_val, mem);

    array_init(&sem->call_check.mono_infos, mem);
    array_init(&sem->call_check.mono_infos_pool, mem);
    array_init(&sem->fns, mem);
    array_init(&sem->globals, mem);
    array_init(&sem->types, mem);
    map_init(&sem->ast_consts, mem);
    map_init(&sem->bin_consts, mem);
    map_init(&sem->cached_struct_field_offsets, mem);
    map_init(&sem->mono_infos, mem);
    map_init(&sem->poly_infos, mem);
    map_init(&sem->type_def, mem);

    sem->interns = interns;
    sem->parser = par_new(interns, mem);
    sem->codegen_file = par_get_codegen_file(sem->parser);

    { // Init autoimports scope:
        Ast *owner = ast_alloc(mem, AST_DUMMY, AST_CREATES_SCOPE);
        sem->autoimports = scope_new(sem, 0, owner);
        scope_seal(sem, sem->autoimports);
        add_to_check_list(sem, owner, sem->autoimports);
    }

    sem->match.dummy1    = ast_alloc(sem->mem, AST_DUMMY, 0);
    sem->match.dummy2    = ast_alloc(sem->mem, AST_DUMMY, 0);
    sem->dummy_named_arg = cast(AstCallNamedArg*, ast_alloc(mem, AST_CALL_NAMED_ARG, 0));

    add_to_check_list(sem, sem->match.dummy1, sem->autoimports);
    add_to_check_list(sem, sem->match.dummy2, sem->autoimports);
    add_to_check_list(sem, cast(Ast*, sem->dummy_named_arg), sem->autoimports);

    { // Init builtin types:
        #define X(N, TAG) {\
            Type *t = alloc_type(sem, TAG);\
            Ast *n = ast_alloc(sem->mem, AST_DUMMY, AST_IS_TYPE | ((t->flags & TYPE_IS_PRIMITIVE) ? AST_CAN_EVAL_WITHOUT_VM : 0));\
            add_to_check_list(sem, n, sem->autoimports);\
            set_type(n, t);\
            sem->core_types.type_##N = t;\
            scope_add(sem, sem->autoimports, intern_cstr(sem->interns, #N), n, n);\
        }
            EACH_BUILTIN_TYPE(X)
        #undef X

        #define X(N, S, W) {\
            cast(TypeInt*, sem->core_types.type_##N)->bitwidth  = W;\
            cast(TypeInt*, sem->core_types.type_##N)->is_signed = S;\
        }
            EACH_BUILTIN_INT_TYPE(X)
        #undef X

        cast(TypeFloat*, sem->core_types.type_F32)->bitwidth = 32;
        cast(TypeFloat*, sem->core_types.type_F64)->bitwidth = 64;

        sem->core_types.type_void_ptr = alloc_type_pointer(sem, 0, sem->core_types.type_Void);
    }

    return sem;
}
