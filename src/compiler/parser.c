#include <math.h>

#include "base/map.h"
#include "base/log.h"
#include "base/string.h"
#include "compiler/ast.h"
#include "compiler/interns.h"
#include "compiler/lexer.h"
#include "compiler/parser.h"
#include "os/fs.h"

istruct (ArgContext) {
    ArrayAst args;
    Array(IString*) polyargs;
};

istruct (CodeGen) {
    U64 last_line;
    AstFile *file;
    AString content;
};

istruct (Parser) {
    Mem *mem;
    Interns *interns;
    Lexer *lexer;
    AstFile *file;
    CodeGen codegen;
    Bool struct_literal_allowed;
    Array(ArgContext*) arg_context_pool;
    Array(ArgContext*) arg_context_stack;
    Map(AstId, ArrayAstAttribute*) attributes;
};

#define lex (par->lexer)

static Ast *parse_defer (Parser *);
static Ast *parse_ident (Parser *);
static Ast *parse_struct (Parser *);
static Ast *parse_fn_type (Parser *);
static Ast *parse_fn (Parser *, Bool);
static Ast *parse_statement (Parser *);
static Ast *parse_enum_member (Parser *);
static Ast *parse_struct_member (Parser *);
static Ast *parse_top_statement (Parser *);
static Ast *parse_block_explicit (Parser *);
static Ast *parse_backtick (Parser *, Bool);
static Ast *parse_expression (Parser *, U64);
static Ast *try_parse_expression (Parser *, U64);
static Ast *parse_poly_type (Parser *, Bool, Bool);
static Ast *parse_assign (Parser *, Ast *, AstTag);
static Ast *parse_expression_before_brace (Parser *);
static Void mark_standalone_position (Parser *, Ast *);
static Ast *try_parse_expression_before_brace (Parser *);
static Void mark_poly_arg_position (Parser *, Ast *, Ast *);
static Void try_parse_expression_list (Parser *, ArrayAst *);
static Void parse_block (Parser *, ArrayAst *, Ast *, IString **);

#define prefix(token_tag) (token_tag + TOKEN_TAG_COUNT)

Noreturn Fmt(4, 5)
static Void par_error_pos2 (Parser *par, SrcPos p1, SrcPos p2, CString fmt, ...) {
    tmem_new(tm);
    log_msg(msg, LOG_ERROR, "Parser", 1);

    AstFile *f = par->file;
    SrcLog *slog = slog_new(tm, slog_default_config);
    slog_add_src(slog, cast(Ast*, f)->id, *f->path, f->content);
    slog_add_pos(slog, cast(Ast*, f)->id, p1);
    if (p2.first_line) slog_add_pos(slog, cast(Ast*, f)->id, p2);

    astr_push_fmt_vam(msg, fmt);
    array_push_n(msg, '\n', '\n');
    slog_flush(slog, msg);
    log_scope_end_all();
    panic();
}

#define par_error_pos(PAR, POS, ...) par_error_pos2(PAR, POS, (SrcPos){}, __VA_ARGS__);
#define par_error(PAR, ...)          par_error_pos2(PAR, lex_peek(lex)->pos, (SrcPos){}, __VA_ARGS__);

static Void set_content (Parser *par, AstFile *file, SrcPos *adjust) {
    par->file = file;
    lex_reset(lex, file, adjust);
}

static Ast *complete_node (Parser *par, Void *node) {
    Auto n = cast(Ast*, node);
    SrcPos prev = lex_get_prev_pos(lex);
    n->pos.last_line = prev.last_line;
    n->pos.length = prev.offset + prev.length - n->pos.offset;
    return n;
}

static Void *make_node_by_tag (Parser *par, AstTag tag) {
    Ast *node = ast_alloc(par->mem, tag, 0);
    SrcPos pos = lex_peek(lex)->pos;
    node->pos.offset = pos.offset;
    node->pos.first_line = pos.first_line;
    return node;
}

static Void *make_node_lhs_by_tag (Parser *par, AstTag tag, Ast *lhs) {
    Ast *node = ast_alloc(par->mem, tag, 0);
    node->pos.offset = lhs->pos.offset;
    node->pos.first_line = lhs->pos.first_line;
    return node;
}

#define make_node(PAR, T)        cast(T*, make_node_by_tag(PAR, e##T))
#define make_node_lhs(PAR, T, L) cast(T*, make_node_lhs_by_tag(PAR, e##T, L))

ArrayAstAttribute *par_get_attributes (Parser *par, AstId id) {
    return map_get_ptr(&par->attributes, id);
}

static Void attach_attribute (Parser *par, AstId id, AstAttribute *attr) {
    ArrayAstAttribute *attrs = par_get_attributes(par, id);

    if (! attrs) {
        attrs = mem_new(par->mem, ArrayAstAttribute);
        array_init(attrs, par->mem);
        map_add(&par->attributes, id, attrs);
    }

    AstAttribute **prev = array_find_ref(attrs, (*IT)->key == attr->key);
    if (prev) *prev = attr;
    else      array_push(attrs, attr);
}

static Ast *try_parse_custom_attribute (Parser *par, AstId id) {
    if (! lex_try_eat(lex, '#')) return 0;
    Auto attr = make_node(par, AstAttribute);
    attr->key = lex_eat_this(lex, TOKEN_IDENT)->str;
    if (lex_try_eat(lex, '=')) attr->val = parse_expression(par, 0);
    attach_attribute(par, id, attr);
    return complete_node(par, attr);
}

#define try_peek_attribute(ATTR) ({\
    Token *token = lex_try_peek(lex, TOKEN_IDENT);\
    (token && token->str == par->interns->attr_##ATTR) ? token : 0;\
})

#define try_eat_attribute(ATTR) ({\
    Token *token = lex_try_peek(lex, TOKEN_IDENT);\
    (token && token->str == par->interns->attr_##ATTR) ? lex_eat(lex) : 0;\
})

#define eat_attribute(ATTR) ({\
    Token *token = lex_eat_this(lex, TOKEN_IDENT);\
    IString *attr = par->interns->attr_##ATTR;\
    if (token->str != attr) par_error_pos(par, token->pos, "Expected attribute '%.*s'.", STR(*attr));\
    token;\
})

#define starts_with_attribute(ATTR) ({\
    Bool result = false;\
    if (lex_try_peek_nth(lex, 2, ':')) {\
        Token *token = lex_peek_nth(lex, 3);\
        if (token->tag == TOKEN_IDENT) {\
            result = (token->str == par->interns->attr_##ATTR);\
        } else if (token->tag == '(') {\
            token = lex_try_peek_nth(lex, 4, TOKEN_IDENT);\
            result = (token && token->str == par->interns->attr_##ATTR);\
        }\
    }\
    result;\
})

#define parse_attributes(NODE_ID, PRE_LOOP, ...) ({\
    def1(id, NODE_ID);\
    lex_eat_this(lex, ':');\
    Bool _(in_parens) = lex_try_eat(lex, '(');\
    U64 _(start) = lex_peek(lex)->pos.offset;\
    PRE_LOOP;\
    lex_try_eat(lex, ',');\
    do {\
        if (! try_parse_custom_attribute(par, id)) { __VA_ARGS__; }\
    } while (_(in_parens) && lex_try_eat(lex, ','));\
    if (_(in_parens)) {\
        if (!lex_try_eat(lex, ')')) par_error(par, "Invalid attribute.");\
    } else if (_(start) == lex_peek(lex)->pos.offset) {\
        par_error(par, "Invalid attribute.");\
    }\
})

#define try_parse_attributes(NODE_ID, PRE_LOOP, ...) ({\
    if (lex_try_peek(lex, ':')) parse_attributes(NODE_ID, PRE_LOOP, __VA_ARGS__);\
})

static Ast *parse_builtin_unary (Parser *par, AstTag tag, Bool in_standalone_position) {
    Auto node = cast(AstBaseUnary*, make_node_by_tag(par, tag));
    lex_eat_this(lex, '.');
    lex_eat_this(lex, TOKEN_IDENT);
    lex_eat_this(lex, '(');
    node->op = parse_expression(par, 0);
    lex_eat_this(lex, ')');
    if (in_standalone_position) mark_standalone_position(par, node->op);
    return complete_node(par, node);
}

static Ast *parse_builtin_nullary (Parser *par, AstTag tag) {
    AstSelf *node = cast(AstSelf*, make_node_by_tag(par, tag));
    lex_eat_this(lex, '.');
    lex_eat_this(lex, TOKEN_IDENT);
    lex_eat_this(lex, '(');
    lex_eat_this(lex, ')');
    return complete_node(par, node);
}

static Ast *parse_cast (Parser *par, Bool bitwise) {
    Auto node = make_node(par, AstCast);
    assert_static(AST_CAST_BITWISE != 0);
    if (bitwise) node->tag = AST_CAST_BITWISE;
    lex_eat_this(lex, '.');
    lex_eat_this(lex, TOKEN_IDENT);
    lex_eat_this(lex, '(');
    node->expr = parse_expression(par, 0);
    if (lex_try_eat(lex, ',')) node->to = parse_expression(par, 0);
    lex_eat_this(lex, ')');
    return complete_node(par, node);
}

static Ast *parse_special_float (Parser *par, F64 val) {
    Auto node = make_node(par, AstF64Literal);
    lex_eat_this(lex, '.');
    lex_eat_this(lex, TOKEN_IDENT);
    lex_eat_this(lex, '(');
    lex_eat_this(lex, ')');
    node->val = val;
    return complete_node(par, node);
}

static Ast *parse_builtin (Parser *par) {
    Token *token = lex_peek_nth(lex, 2);

    if (token->tag != TOKEN_IDENT) par_error_pos(par, token->pos, "Expected identifier.");

    if (token->str == par->interns->builtin_cast)    return parse_cast(par, false);
    if (token->str == par->interns->builtin_bitcast) return parse_cast(par, true);
    if (token->str == par->interns->builtin_alignof) return parse_builtin_unary(par, AST_ALIGNOF, true);
    if (token->str == par->interns->builtin_sizeof)  return parse_builtin_unary(par, AST_SIZEOF, true);
    if (token->str == par->interns->builtin_nan)     return parse_special_float(par, NAN);
    if (token->str == par->interns->builtin_inf)     return parse_special_float(par, INFINITY);
    if (token->str == par->interns->builtin_raw)     return parse_builtin_unary(par, AST_RAW, true);
    if (token->str == par->interns->builtin_self)    return parse_builtin_nullary(par, AST_SELF);
    if (token->str == par->interns->builtin_caller)  return parse_builtin_nullary(par, AST_CALLER_INFO);
    if (token->str == par->interns->builtin_typeid)  return parse_builtin_unary(par, AST_TYPE_ID, true);

    if (token->str == par->interns->builtin_assert) {
        Ast *node = parse_builtin_unary(par, AST_CT_ASSERT, false);
        cast(AstBaseUnary*, node)->op->flags |= AST_MUST_EVAL;
        return node;
    }

    par_error(par, "Unknown builtin.");
}

static Bool eat_until (Parser *par, TokenTag until) {
    Bool escaped = false;

    while (true) {
        TokenTag t = lex_eat(lex)->tag;
        if      (t == until) { break; }
        else if (t == 0)     { lex_eat_this(lex, until); }
        else if (t == '\\')  { escaped = true; lex_eat(lex); }
        else if (t == '(')   { escaped = eat_until(par, ')'); }
        else if (t == '[')   { escaped = eat_until(par, ']'); }
        else if (t == '{')   { escaped = eat_until(par, '}'); }
    }

    return escaped;
}

static Ast *parse_backticked_code_arg (Parser *par) {
    Auto node = make_node(par, AstCallMacroBArg);
    lex_eat_this(lex, '`');
    node->code = parse_expression(par, 0);
    node->code->flags |= AST_MUST_EVAL;
    return complete_node(par, node);
}

static Ast *parse_code_arg (Parser *par, TokenTag until, Bool escape) {
    assert_dbg(until != '\\');

    Auto node = make_node(par, AstCallMacroArg);
    Bool escaped = false;

    while (true) {
        TokenTag t = lex_peek(lex)->tag;

        if (until) {
            if (t == until) break;
        } else if (t == ';' || t == '{' || t == TOKEN_DO) {
            break;
        }

        switch (t) {
        case '\\': escaped = true; lex_eat(lex); lex_eat(lex); break;
        case '(':  lex_eat(lex); escaped = eat_until(par, ')'); break;
        case '[':  lex_eat(lex); escaped = eat_until(par, ']'); break;
        case '{':  lex_eat(lex); escaped = eat_until(par, '}'); break;
        case 0:    lex_eat_this(lex, until); break;
        case ',':  goto done;
        default:   lex_eat(lex); break;
        }
    } done:;

    complete_node(par, node);

    SrcPos pos = cast(Ast*, node)->pos;
    if (pos.length == 0) par_error(par, "Expected a code snippet.");

    node->code    = (String){ .data=(par->file->content.data + pos.offset), .count=pos.length };
    node->escaped = escaped;
    if (escaped && escape) node->code = lex_escape_str(lex, &cast(Ast*, node)->pos, node->code, false);

    return cast(Ast*, node);
}

static Ast *parse_code_arg_array (Parser *par, U64 n) {
    if (n == 0) return parse_code_arg(par, ']', true);

    Auto node = make_node(par, AstArrayLiteral);
    lex_eat_this(lex, '[');

    while (true) {
        array_push(&node->inits, parse_code_arg_array(par, n - 1));
        if (! lex_try_eat(lex, ',')) break;
    }

    lex_eat_this(lex, ']');
    return complete_node(par, node);
}

Void par_parse_macro_args (Parser *par, AstFile *file, ArrayAst *def_args, AstCallMacro *call) {
    assert_dbg(def_args->count == call->args.count);

    array_iter (call_arg, &call->args) {
        assert_dbg(call_arg->tag != AST_CALL_NAMED_ARG);

        Ast *def_arg = array_get(def_args, ARRAY_IDX);

        if (def_arg->tag == AST_ARG_POLY_CODE) {
            U64 n = cast(AstArgPolyCode*, def_arg)->n;
            if (n > 0) {
                set_content(par, file, &call_arg->pos);
                Ast *new_arg = parse_code_arg_array(par, n);
                array_set(&call->args, ARRAY_IDX, new_arg);
            }
        } else if (cast(AstCallMacroArg*, call_arg)->escaped) {
            String code = lex_escape_str(lex, &call_arg->pos, cast(AstCallMacroArg*, call_arg)->code, false);
            AstCodeGen *gen = par_parse_codegen(par, code, call_arg, file, AST_LEVEL_EXPR);
            if (gen->children.count != 1) par_error_pos(par, call_arg->pos, "Expected only 1 expression.");
            array_set(&call->args, ARRAY_IDX, array_get(&gen->children, 0));
        } else if (call_arg->tag != AST_CALL_DEFAULT_ARG) {
            set_content(par, file, &call_arg->pos);
            Ast *expr = parse_expression(par, 0);
            array_set(&call->args, ARRAY_IDX, expr);
        }
    }
}

static Ast *parse_call_macro (Parser *par, Ast *lhs) {
    Auto node = make_node_lhs(par, AstCallMacro, lhs);
    node->lhs = lhs;
    mark_standalone_position(par, lhs);
    lex_eat_this(lex, ':');

    if (lex_try_eat(lex, '(')) {
        while (! lex_try_peek(lex, ')')) {
            if (lex_try_peek(lex, TOKEN_IDENT) && lex_try_peek_nth(lex, 2, '=')) {
                Auto a = make_node(par, AstCallNamedArg);
                a->name = lex_eat(lex)->str;
                lex_eat(lex);
                a->arg = lex_try_peek(lex, '`') ? parse_backticked_code_arg(par) : parse_code_arg(par, ')', false);
                array_push(&node->args, complete_node(par, a));
            } else {
                Ast *arg = lex_try_peek(lex, '`') ? parse_backticked_code_arg(par) : parse_code_arg(par, ')', false);
                array_push(&node->args, arg);
            }

            if (! lex_try_eat(lex, ',')) break;
        }

        lex_eat_this(lex, ')');
    } else if (!lex_try_peek(lex, ';') && !lex_try_peek(lex, '{') && !lex_try_peek(lex, TOKEN_DO)) {
        Ast *arg = lex_try_peek(lex, '`') ? parse_backticked_code_arg(par) : parse_code_arg(par, 0, false);
        array_push(&node->args, arg);
    }

    if (lex_try_peek(lex, '{') || lex_try_peek(lex, TOKEN_DO)) {
        cast(Ast*, node)->flags |= AST_ENDS_WITH_BLOCK;
        Ast *block = parse_block_explicit(par);
        Ast *arg = ast_alloc(par->mem, AST_CALL_MACRO_ARG, 0);
        arg->pos = block->pos;
        cast(AstCallMacroArg*, arg)->parsed_ast = block;
        cast(AstCallMacroArg*, arg)->code = (String){ .data=(par->file->content.data + block->pos.offset), .count=block->pos.length };
        array_push(&node->args, cast(Ast*, arg));
    }

    return complete_node(par, node);
}

static Ast *parse_call (Parser *par, Ast *lhs) {
    Auto node = make_node_lhs(par, AstCall, lhs);
    node->lhs = lhs;
    mark_standalone_position(par, node->lhs);
    lex_eat_this(lex, '(');

    while (true) {
        if (lex_try_peek(lex, ')')) {
            break;
        } else if (lex_try_peek(lex, TOKEN_IDENT) && lex_try_peek_nth(lex, 2, '=')) {
            Auto arg = make_node(par, AstCallNamedArg);
            arg->name = lex_eat(lex)->str;
            lex_eat(lex);
            arg->arg = parse_expression(par, 0);
            array_push(&node->args, complete_node(par, arg));
        } else {
            array_push(&node->args, parse_expression(par, 0));
        }

        if (! lex_try_eat(lex, ',')) break;
    }

    lex_eat_this(lex, ')');
    return complete_node(par, node);
}

static Ast *parse_typeof (Parser *par) {
    Auto node = &make_node(par, AstTypeof)->base;
    lex_eat_this(lex, TOKEN_TYPEOF);
    lex_eat_this(lex, '(');
    node->op = parse_expression(par, 0);
    lex_eat_this(lex, ')');
    mark_standalone_position(par, node->op);
    return complete_node(par, node);
}

static Ast *parse_prefix_op (Parser *par, AstTag tag) {
    Auto node = cast(AstBaseUnary*, make_node_by_tag(par, tag));
    TokenTag op = lex_eat(lex)->tag;
    node->op = parse_expression(par, prefix(op));
    return complete_node(par, node);
}

static Ast *parse_binary_op (Parser *par, AstTag tag, Ast *lhs) {
    Auto node = cast(AstBaseBinary*, make_node_lhs_by_tag(par, tag, lhs));
    node->op1 = lhs;
    TokenTag op = lex_eat(lex)->tag;
    node->op2 = parse_expression(par, op);
    return complete_node(par, node);
}

static Ast *parse_dot (Parser *par, Ast *lhs) {
    Auto node = make_node_lhs(par, AstDot, lhs);
    node->lhs = lhs;
    mark_standalone_position(par, node->lhs);
    lex_eat_this(lex, '.');
    node->rhs = lex_eat_this(lex, TOKEN_IDENT)->str;
    return complete_node(par, node);
}

static Ast *parse_tuple_named (Parser *par, TokenTag sep) {
    Auto node = make_node(par, AstTuple);
    cast(Ast*, node)->flags |= AST_CREATES_SCOPE;
    if (sep == ':') cast(Ast*, node)->flags |= AST_IS_TYPE;
    lex_eat_this(lex, '(');

    while (true) {
        Auto f = make_node(par, AstTupleField);
        f->name = lex_eat_this(lex, TOKEN_IDENT)->str;
        lex_eat_this(lex, sep);
        f->rhs = parse_expression(par, 0);
        if (sep == ':') cast(Ast*, f)->flags |= AST_IS_TYPE;
        array_push(&node->fields, complete_node(par, cast(Ast*, f)));
        if (! lex_try_eat(lex, ',')) break;
    }

    lex_eat_this(lex, ')');
    return complete_node(par, node);
}

static Ast *parse_tuple_or_parens (Parser *par) {
    if (lex_try_peek_nth(lex, 2, TOKEN_IDENT)) {
        Token *t = lex_peek_nth(lex, 3);
        if (t->tag == ':') return parse_tuple_named(par, ':');
        if (t->tag == '=') return parse_tuple_named(par, '=');
    }

    SrcPos p1 = lex_eat_this(lex, '(')->pos;
    Ast *result = parse_expression(par, 0);

    if (lex_try_eat(lex, ',')) {
        Auto n = make_node(par, AstTuple);
        array_push(&n->fields, result);
        try_parse_expression_list(par, &n->fields);
        result = cast(Ast*, n);
    }

    SrcPos p2 = lex_eat_this(lex, ')')->pos;
    result->pos = (SrcPos){
        .offset     = p1.offset,
        .length     = p2.offset - p1.offset + 1,
        .first_line = p1.first_line,
        .last_line  = p2.last_line,
    };

    return result;
}

static Ast *parse_negate (Parser *par) {
    Ast *node = 0;
    SrcPos pos = lex_eat_this(lex, '-')->pos;
    Ast *op = parse_expression(par, prefix('-'));

    switch (op->tag) {
    case AST_I64_LITERAL: {
        node = op;
        cast(AstI64Literal*, op)->val = -cast(AstI64Literal*, op)->val;
    } break;

    case AST_F64_LITERAL: {
        node = op;
        cast(AstF64Literal*, op)->val = -cast(AstF64Literal*, op)->val;
    } break;

    case AST_U64_LITERAL: {
        U64 val = cast(AstU64Literal*, op)->val;
        if (val > cast(U64, INT64_MAX )+ 1) par_error_pos(par, op->pos, "Type I64 cannot represent this negated value.");
        node = op;
        node->tag = AST_I64_LITERAL;
        cast(AstI64Literal*, node)->val = -val;
    } break;

    default: {
        node = cast(Ast*, make_node(par, AstNegate));
        cast(AstBaseUnary*, node)->op = op;
    } break;
    }

    node->pos = pos;
    return complete_node(par, node);
}

static Ast *parse_interface (Parser *par) {
    Auto node = make_node(par, AstInterface);
    lex_eat_this(lex, '/');
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    return complete_node(par, node);
}

static Ast *parse_ident (Parser *par) {
    Auto node = make_node(par, AstIdent);
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    return complete_node(par, node);
}

static Ast *parse_ident_as_string_literal (Parser *par) {
    Auto node = make_node(par, AstStringLiteral);
    node->str = lex_eat_this(lex, TOKEN_IDENT)->str;
    return complete_node(par, node);
}

static Ast *parse_string_literal (Parser *par) {
    Auto node = make_node(par, AstStringLiteral);
    node->str = lex_eat_this(lex, TOKEN_STRING_LITERAL)->str;
    return complete_node(par, node);
}

static Ast *parse_bool_literal (Parser *par, TokenTag tag) {
    Auto node = make_node(par, AstBoolLiteral);
    lex_eat_this(lex, tag);
    node->val = (tag == TOKEN_TRUE);
    return complete_node(par, node);
}

static Ast *parse_u64_literal (Parser *par) {
    Auto node = make_node(par, AstU64Literal);
    node->val = lex_eat(lex)->u64;
    return complete_node(par, node);
}

static Ast *parse_f64_literal (Parser *par) {
    Auto node = make_node(par, AstF64Literal);
    node->val = lex_eat(lex)->f64;
    return complete_node(par, node);
}

static Ast *parse_nil (Parser *par) {
    Auto node = make_node(par, AstNil);
    lex_eat_this(lex, TOKEN_NIL);
    return complete_node(par, node);
}

static Ast *parse_struct_lit_init (Parser *par) {
    Auto node = make_node(par, AstStructLitInit);
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    lex_eat_this(lex, '=');
    node->val = parse_expression(par, 0);
    return complete_node(par, node);
}

static Ast *parse_struct_literal (Parser *par, Ast *lhs) {
    AstStructLiteral *node;

    if (lhs) {
        node = make_node_lhs(par, AstStructLiteral, lhs);
        node->lhs = lhs;
    } else {
        node = make_node(par, AstStructLiteral);
    }

    lex_eat_this(lex, '{');

    while (! lex_try_peek(lex, '}')) {
        AstStructLitInit *init = cast(AstStructLitInit*, parse_struct_lit_init(par));
        array_push(&node->inits, init);
        if (! lex_try_eat(lex, ',')) break;
    }

    lex_eat_this(lex, '}');
    return complete_node(par, node);
}

static Ast *parse_array_literal_or_type (Parser *par) {
    SrcPos start = lex_peek(lex)->pos;
    lex_eat_this(lex, '[');
    Ast *expr = parse_expression(par, 0);

    if (lex_try_eat(lex, ']')) {
        Auto node = make_node(par, AstArrayType);
        cast(Ast*, node)->pos = start;
        node->length = expr;
        node->element = parse_expression(par, prefix('['));
        node->length->flags |= AST_MUST_EVAL;
        return complete_node(par, node);
    } else {
        Auto node = make_node(par, AstArrayLiteral);
        cast(Ast*, node)->pos = start;
        array_push(&node->inits, expr);
        if (lex_try_eat(lex, ',')) try_parse_expression_list(par, &node->inits);
        lex_eat_this(lex, ']');
        return complete_node(par, node);
    }
}

static Ast *parse_array_literal_or_index (Parser *par, Ast *lhs) {
    lex_eat_this(lex, '[');
    Ast *expr = parse_expression(par, 0);

    if (lex_try_eat(lex, ',')) {
        Auto node = make_node_lhs(par, AstArrayLiteral, lhs);
        node->element = lhs;
        array_push(&node->inits, expr);
        try_parse_expression_list(par, &node->inits);
        lex_eat_this(lex, ']');
        return complete_node(par, node);
    } else {
        Auto node = make_node_lhs(par, AstIndex, lhs);
        node->lhs = lhs;
        node->idx = expr;
        mark_standalone_position(par, node->lhs);
        lex_eat_this(lex, ']');
        return complete_node(par, node);
    }
}

static Ast *parse_enum_literal (Parser *par) {
    Auto node = make_node(par, AstEnumLiteral);
    lex_eat_this(lex, '.');
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    return complete_node(par, node);
}

static Ast *parse_deref (Parser *par, Ast *lhs) {
    Auto node = cast(AstBaseUnary*, make_node_lhs(par, AstDeref, lhs));
    lex_eat_this(lex, '~');
    node->op = lhs;
    return complete_node(par, node);
}

static Ast *parse_embed (Parser *par, AstLevel level) {
    Auto node = make_node(par, AstEmbed);

    node->level = level;
    lex_eat_this(lex, TOKEN_EMBED);

    try_parse_attributes(cast(Ast*, node)->id, {}, {
        if (try_eat_attribute(add_return_backticks)) {
            cast(Ast*, node)->flags |= AST_BACKTICKED;
        } else if (try_eat_attribute(breaks)) {
            lex_eat_this(lex, '=');
            lex_eat_this(lex, '(');

            eat_attribute(hit);
            lex_eat_this(lex, '=');
            node->break_hit = parse_ident_as_string_literal(par);
            if (lex_try_eat(lex, TOKEN_2DOT)) cast(Ast*, node->break_hit)->flags |= AST_ENDS_WITH_BLOCK;

            lex_eat_this(lex, ',');

            eat_attribute(miss);
            lex_eat_this(lex, '=');
            node->break_miss = parse_ident_as_string_literal(par);
            if (lex_try_eat(lex, TOKEN_2DOT)) cast(Ast*, node->break_miss)->flags |= AST_ENDS_WITH_BLOCK;

            lex_eat_this(lex, ')');
        } else if (try_eat_attribute(continues)) {
            lex_eat_this(lex, '=');
            lex_eat_this(lex, '(');

            eat_attribute(hit);
            lex_eat_this(lex, '=');
            node->continue_hit = parse_ident_as_string_literal(par);
            if (lex_try_eat(lex, TOKEN_2DOT)) cast(Ast*, node->continue_hit)->flags |= AST_ENDS_WITH_BLOCK;

            lex_eat_this(lex, ',');

            eat_attribute(miss);
            lex_eat_this(lex, '=');
            node->continue_miss = parse_ident_as_string_literal(par);
            if (lex_try_eat(lex, TOKEN_2DOT)) cast(Ast*, node->continue_miss)->flags |= AST_ENDS_WITH_BLOCK;

            lex_eat_this(lex, ')');
        } else if (try_eat_attribute(refs)) {
            lex_eat_this(lex, '=');

            if (! lex_try_eat(lex, '(')) {
                Ast *ref = lex_try_eat(lex, '`') ? parse_expression(par, 0) : parse_ident_as_string_literal(par);
                ref->flags |= AST_MUST_EVAL;
                array_push(&node->refs, ref);
            } else {
                while (! lex_try_peek(lex, ')')) {
                    Ast *ref = lex_try_eat(lex, '`') ? parse_expression(par, 0) : parse_ident_as_string_literal(par);
                    ref->flags |= AST_MUST_EVAL;

                    if (lex_try_eat(lex, '=')) {
                        Auto b = cast(AstBaseBinary*, make_node_lhs(par, AstPair, ref));
                        b->op1 = ref;
                        b->op2 = lex_try_eat(lex, '`') ? parse_expression(par, 0) : parse_ident_as_string_literal(par);
                        b->op2->flags |= AST_MUST_EVAL;
                        ref = complete_node(par, b);
                    }

                    array_push(&node->refs, ref);
                    if (! lex_try_eat(lex, ',')) break;
                }

                lex_eat_this(lex, ')');
            }
        }
    });

    if (lex_try_peek(lex, '{')) {
        node->generator = parse_block_explicit(par);
    } else {
        node->generator = parse_expression(par, 0);
        if (level != AST_LEVEL_EXPR) lex_eat_this(lex, ';');
    }

    node->generator->flags |= AST_MUST_EVAL;

    if (level == AST_LEVEL_EXPR) {
        cast(Ast*, node)->flags &= ~AST_IS_BINDGEN;
    } else {
        cast(Ast*, node)->flags &= ~AST_CAN_EVAL_WITHOUT_VM;
    }

    return complete_node(par, node);
}

static Ast *parse_eval (Parser *par, Bool in_expr) {
    Auto node = make_node(par, AstEval);
    lex_eat_this(lex, TOKEN_EVAL);
    try_parse_attributes(cast(Ast*, node)->id,);

    if (lex_try_peek(lex, '{')) {
        node->child = parse_block_explicit(par);
    } else {
        node->child = parse_expression(par, 0);
        if (! in_expr) lex_eat_this(lex, ';');
    }

    node->child->flags |= AST_MUST_EVAL;
    return complete_node(par, node);
}

static Ast *parse_array_type (Parser *par) {
    Auto node = make_node(par, AstArrayType);
    lex_eat_this(lex, '[');
    node->length = parse_expression(par, 0);
    lex_eat_this(lex, ']');
    node->element = parse_expression(par, 0);
    return complete_node(par, node);
}

static Ast *parse_suffix_expression (Parser *par, Ast *lhs) {
    switch (lex_peek(lex)->tag) {
    case '.':                 return parse_dot(par, lhs);
    case '~':                 return parse_deref(par, lhs);
    case ':':                 return parse_call_macro(par, lhs);
    case '(':                 return parse_call(par, lhs);
    case '{':                 return parse_struct_literal(par, lhs);
    case '[':                 return parse_array_literal_or_index(par, lhs);
    case '+':                 return parse_binary_op(par, AST_ADD, lhs);
    case '-':                 return parse_binary_op(par, AST_SUB, lhs);
    case '*':                 return parse_binary_op(par, AST_MUL, lhs);
    case '/':                 return parse_binary_op(par, AST_DIV, lhs);
    case '%':                 return parse_binary_op(par, AST_MOD, lhs);
    case '<':                 return parse_binary_op(par, AST_LESS, lhs);
    case '>':                 return parse_binary_op(par, AST_GREATER, lhs);
    case '|':                 return parse_binary_op(par, AST_BITWISE_OR, lhs);
    case '^':                 return parse_binary_op(par, AST_BITWISE_XOR, lhs);
    case '&':                 return parse_binary_op(par, AST_BITWISE_AND, lhs);
    case TOKEN_2VBAR:         return parse_binary_op(par, AST_LOGICAL_OR, lhs);
    case TOKEN_2AMPERSAND:    return parse_binary_op(par, AST_LOGICAL_AND, lhs);
    case TOKEN_2EQUAL:        return parse_binary_op(par, AST_EQUAL, lhs);
    case TOKEN_NOT_EQUAL:     return parse_binary_op(par, AST_NOT_EQUAL, lhs);
    case TOKEN_2LESS:         return parse_binary_op(par, AST_SHIFT_LEFT, lhs);
    case TOKEN_LESS_EQUAL:    return parse_binary_op(par, AST_LESS_EQUAL, lhs);
    case TOKEN_2GREATER:      return parse_binary_op(par, AST_SHIFT_RIGHT, lhs);
    case TOKEN_GREATER_EQUAL: return parse_binary_op(par, AST_GREATER_EQUAL, lhs);
    default:                  badpath;
    }
}

static Ast *parse_prefix_expression (Parser *par) {
    switch (lex_peek(lex)->tag) {
    case '.':                  return lex_try_peek_nth(lex, 3, '(') ? parse_builtin(par) : parse_enum_literal(par);
    case '-':                  return parse_negate(par);
    case '/':                  return parse_interface(par);
    case '`':                  return parse_backtick(par, true);
    case '$':                  return parse_poly_type(par, false, false);
    case '(':                  return parse_tuple_or_parens(par);
    case '{':                  return par->struct_literal_allowed ? parse_struct_literal(par, 0) : 0;
    case '[':                  return parse_array_literal_or_type(par);
    case '!':                  return parse_prefix_op(par, AST_NOT);
    case '~':                  return parse_prefix_op(par, AST_ADDRESS_OF);
    case TOKEN_EMBED:          return parse_embed(par, AST_LEVEL_EXPR);
    case TOKEN_EVAL:           return parse_eval(par, true);
    case TOKEN_F64_LITERAL:    return parse_f64_literal(par);
    case TOKEN_FALSE:          return parse_bool_literal(par, TOKEN_FALSE);
    case TOKEN_FN:             return parse_fn(par, true);
    case TOKEN_FN_TYPE:        return parse_fn_type(par);
    case TOKEN_NIL:            return parse_nil(par);
    case TOKEN_STRING_LITERAL: return parse_string_literal(par);
    case TOKEN_TRUE:           return parse_bool_literal(par, TOKEN_TRUE);
    case TOKEN_TYPEOF:         return parse_typeof(par);
    case TOKEN_U64_LITERAL:    return parse_u64_literal(par);
    case TOKEN_IDENT:          return parse_ident(par);
    default:                   return 0;
    }
}

// For prefix operators, do precedence_of(prefix(token_tag)).
//
// Note that the weird value progression of decreasing powers
// of 10 is used to simplify the code in try_parse_expression()
// which checks whether any two given infix operators can be
// chained without the use of parens.
static U64 precedence_of (U64 op) {
    switch (op) {
    case '.':
    case '~':
    case ':':
    case '(':
    case '[':
    case '{':
        return 100000;

    case prefix('.'):
    case prefix('!'):
    case prefix('~'):
    case prefix('-'):
    case prefix('`'):
    case prefix('$'):
    case prefix('/'):
    case prefix('('):
    case prefix('['):
    case prefix('{'):
        return 10000;

    case '*':
    case '/':
    case '%':
        return 1000;

    case '+':
    case '-':
        return 100;

    case '|':
    case '&':
    case '^':
    case '<':
    case '>':
    case TOKEN_2LESS:
    case TOKEN_2GREATER:
    case TOKEN_2EQUAL:
    case TOKEN_NOT_EQUAL:
    case TOKEN_LESS_EQUAL:
    case TOKEN_GREATER_EQUAL:
    case TOKEN_2VBAR:
    case TOKEN_2AMPERSAND:
        return 10;

    default:
        return 0;
    }
}

// The argument "left_op" can be one of the following:
//
//     1. A TokenTag representing the operator to the left of the expresion.
//     2. A value given by prefix() representing a prefix op to the left.
//     3. The value 0 indicating that there is no operator to the left.
//     4. The value 1 indicating that there is no operator to the left,
//        and indicating that we don't want to re-enable struct literal
//        parsing -- see parse_expression_before_brace() for more.
//
static Ast *try_parse_expression (Parser *par, U64 left_op) {
    SrcPos left_pos = lex_get_prev_pos(lex);
    U64 left_prec   = precedence_of(left_op);

    Bool literal_allowed = par->struct_literal_allowed;
    if (left_op == 0) par->struct_literal_allowed = true;

    Ast *result = parse_prefix_expression(par);

    if (result) while (true) {
        Token *right_op = lex_peek(lex);

        if (left_op == right_op->tag) break;
        if ((right_op->tag == '{') && !par->struct_literal_allowed) break;

        U64 right_prec = precedence_of(right_op->tag);
        U64 s = left_prec + right_prec;

        if (s == 20 || s == 110 || s == 1010) par_error_pos2(par, left_pos, right_op->pos, "Cannot chain these ops. Use parens.");
        if (left_prec >= right_prec) break;

        result = parse_suffix_expression(par, result);
    }

    par->struct_literal_allowed = literal_allowed;
    return result;
}

static Ast *parse_expression (Parser *par, U64 left_op) {
    Ast *e = try_parse_expression(par, left_op);
    if (! e) par_error(par, "Expected expression.");
    return e;
}

// Use this function when parsing an expression that could be
// terminated by an opening brace. This fixes an ambiguity in
// which the opening brace is interpreted as a struct literal
// rather than a construct that appears after the expression.
//
// For example, the following code:
//
//     if 1 < Foo {}
//
// would get parsed as:
//
//     if (1 < Foo{}) [expecting if body here]
//
// instead of:
//
//     if (1 < Foo) {}
//
// This function disables the struct literal operator '{', and
// whenever try_parse_expression() is called with left_op == 0
// it will temporarily re-enable this operator. For example,
// this happens when we start parsing an expression in parens.
// Thus you can still put struct literals in places like an if
// condition by wrapping it in parens:
//
//     if 1 < Foo{ x = 42 }.x   {} // Doesn't work.
//     if (1 < Foo{ x = 42 }.x) {} // Ok.
//
static Ast *try_parse_expression_before_brace (Parser *par) {
    Bool prev = par->struct_literal_allowed;
    par->struct_literal_allowed = false;
    Ast *e = try_parse_expression(par, 1);
    par->struct_literal_allowed = prev;
    return e;
}

static Ast *parse_expression_before_brace (Parser *par) {
    Ast *e = try_parse_expression_before_brace(par);
    if (! e) par_error(par, "Expected expression.");
    return e;
}

static Void try_parse_expression_list (Parser *par, ArrayAst *out) {
    while (true) {
        Ast *e = try_parse_expression(par, 0);
        if (! e) break;
        array_push(out, e);
        if (! lex_try_eat(lex, ',')) break;
    }
}

static Ast *parse_var_def (Parser *par, Bool with_semicolon, Bool with_keyword) {
    Auto node = make_node(par, AstVarDef);

    if (with_keyword) {
        lex_eat_this(lex, TOKEN_VAR);
        try_parse_attributes(cast(Ast*, node)->id,);
        cast(Ast*, node)->flags |= AST_ENDS_WITH_BLOCK; // @todo Hacky.
    }

    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    if (lex_try_eat(lex, ':')) node->constraint = parse_expression(par, 0);
    if (lex_try_eat(lex, '=')) node->init = parse_expression(par, 0);
    if (!node->constraint && !node->init) lex_eat_this(lex, ':');
    if (with_semicolon) lex_eat_this(lex, ';');
    if (node->constraint) node->constraint->flags |= AST_CAN_EVAL_WITHOUT_VM;
    else mark_standalone_position(par, node->init);

    return complete_node(par, node);
}

static Ast *parse_break (Parser *par) {
    Auto node = make_node(par, AstBreak);
    lex_eat_this(lex, TOKEN_BREAK);
    try_parse_attributes(cast(Ast*, node)->id,);
    Token *token = lex_try_eat(lex, TOKEN_IDENT);
    if (token) node->label = token->str;
    lex_eat_this(lex, ';');
    return complete_node(par, node);
}

static Ast *parse_continue (Parser *par) {
    Auto node = make_node(par, AstContinue);
    lex_eat_this(lex, TOKEN_CONTINUE);
    try_parse_attributes(cast(Ast*, node)->id,);
    Token *token = lex_try_eat(lex, TOKEN_IDENT);
    if (token) node->label = token->str;
    lex_eat_this(lex, ';');
    return complete_node(par, node);
}

static Ast *parse_while (Parser *par) {
    Auto node = make_node(par, AstWhile);
    lex_eat_this(lex, TOKEN_WHILE);
    try_parse_attributes(cast(Ast*, node)->id,);
    node->cond = parse_expression_before_brace(par);
    parse_block(par, &node->statements, cast(Ast*, node), &node->label);
    return complete_node(par, node);
}

static Ast *parse_if (Parser *par) {
    Auto node = make_node(par, AstIf);
    lex_eat_this(lex, TOKEN_IF);
    try_parse_attributes(cast(Ast*, node)->id,);
    node->cond = parse_expression_before_brace(par);
    node->then_arm = parse_block_explicit(par);
    if (lex_try_eat(lex, TOKEN_ELSE)) node->else_arm = lex_try_peek(lex, TOKEN_IF) ? parse_if(par) : parse_block_explicit(par);
    return complete_node(par, node);
}

static Ast *parse_if_ct (Parser *par, AstLevel level) {
    Auto node = make_node(par, AstIfCt);
    Bool with_commas = (level == AST_LEVEL_ENUM);
    Ast *(*parselet)(Parser*) = 0;

    switch (level) {
    case AST_LEVEL_FN:     parselet = parse_statement; break;
    case AST_LEVEL_ENUM:   parselet = parse_enum_member; break;
    case AST_LEVEL_FILE:   parselet = parse_top_statement; break;
    case AST_LEVEL_STRUCT: parselet = parse_struct_member; break;
    case AST_LEVEL_EXPR:   badpath;
    }

    lex_eat_this(lex, TOKEN_IF);
    parse_attributes(cast(Ast*, node)->id, eat_attribute(ct));
    node->cond = parse_expression_before_brace(par);
    node->cond->flags |= AST_MUST_EVAL;

    #define parse_arm(OUT) ({\
        if (lex_try_eat(lex, TOKEN_DO)) {\
            array_push(OUT, parselet(par));\
        } else {\
            lex_eat_this(lex, '{');\
            while (true) {\
                Ast *n = parselet(par);\
                if (! n) break;\
                array_push(OUT, n);\
                if (with_commas && !(n->flags & AST_IS_BINDGEN) && !lex_try_eat(lex, ',')) break;\
            }\
            lex_eat_this(lex, '}');\
        }\
    })

    parse_arm(&node->then_arm);

    if (lex_try_eat(lex, TOKEN_ELSE)) {
        if (lex_try_peek(lex, TOKEN_IF)) {
            array_push(&node->else_arm, parselet(par));
        } else {
            parse_arm(&node->else_arm);
        }
    }

    #undef parse_arm
    return complete_node(par, node);
}

static Ast *parse_return (Parser *par) {
    Auto node = make_node(par, AstReturn);
    lex_eat_this(lex, TOKEN_RETURN);
    try_parse_attributes(cast(Ast*, node)->id,);
    node->result = try_parse_expression(par, 0);
    lex_eat_this(lex, ';');
    return complete_node(par, node);
}

static Ast *parse_backtick (Parser *par, Bool at_expr_level) {
    lex_eat_this(lex, '`');

    Ast *result = 0;

    if (at_expr_level) {
        result = parse_ident(par);
    } else if (lex_try_peek(lex, TOKEN_RETURN)) {
        result = parse_return(par);
    } else {
        result = parse_defer(par);
    }

    result->flags |= AST_BACKTICKED;
    return result;
}

static ArgContext *push_arg_context (Parser *par) {
    ArgContext *ctx;

    if (par->arg_context_pool.count) {
        ctx = array_pop(&par->arg_context_pool);
        ctx->args.count = 0;
        ctx->polyargs.count = 0;
    } else {
        ctx = mem_new(par->mem, ArgContext);
        array_init(&ctx->args, par->mem);
        array_init(&ctx->polyargs, par->mem);
    }

    array_push(&par->arg_context_stack, ctx);
    return ctx;
}

static Void pop_arg_context (Parser *par) {
    ArgContext *ctx = array_pop(&par->arg_context_stack);
    array_push(&par->arg_context_pool, ctx);
}

static IString *make_anon_fn_name (Parser *par, U64 file_byte_offset) {
    IString *f = par->file->path;
    String s   = astr_fmt(par->mem, "fn:%.*s:0x%lx", STR(*f), file_byte_offset);
    return intern_str(par->interns, s);
}

static Ast *make_anon_poly_type (Parser *par, Ast *parent, IString *name) {
    Auto node = cast(Ast*, make_node(par, AstArgPolyType));
    node->pos = ast_trimmed_pos(par->interns, parent);
    String n = astr_fmt(par->mem, "Type(%.*s)", STR(*name));
    cast(AstArgPolyType*, node)->name = intern_str(par->interns, n);
    mark_poly_arg_position(par, parent, node);
    ArgContext *ctx = array_try_get_last(&par->arg_context_stack);
    if (ctx) array_push(&ctx->polyargs, cast(AstArgPolyType*, node)->name);
    return node;
}

static Ast *parse_poly_type (Parser *par, Bool double_dollar_allowed, Bool init_allowed) {
    Auto node = make_node(par, AstArgPolyType);

    lex_eat_this(lex, '$');
    if (double_dollar_allowed && lex_try_eat(lex, '$')) node->is_tuple = true;
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;

    if      (lex_try_eat(lex, ':'))  node->constraint = parse_expression(par, 0);
    else if (lex_try_peek(lex, '/')) node->constraint = parse_interface(par);

    if (init_allowed && lex_try_eat(lex, '=')) {
        node->init = parse_expression(par, 0);
        node->init->flags |= AST_MUST_EVAL;
    }

    ArgContext *ctx = array_try_get_last(&par->arg_context_stack);
    if (ctx) array_push(&ctx->polyargs, node->name);
    return complete_node(par, node);
}

static Ast *parse_poly_value (Parser *par, ArgContext *ctx) {
    Auto node = make_node(par, AstArgPolyValue);
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    lex_eat_this(lex, '$');
    if (lex_try_eat(lex, ':')) node->constraint = parse_expression(par, 0);
    if (lex_try_eat(lex, '=')) { node->init = parse_expression(par, 0); node->init->flags |= AST_MUST_EVAL; }
    if (!node->constraint && !node->init) node->constraint = make_anon_poly_type(par, cast(Ast*, node), node->name);
    array_push(&ctx->polyargs, node->name);
    return complete_node(par, node);
}

static Ast *parse_poly_code (Parser *par, ArgContext *ctx) {
    Auto node = make_node(par, AstArgPolyCode);

    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    lex_eat_this(lex, ':');
    lex_eat_this(lex, '$');
    while (lex_try_eat(lex, '$')) node->n++;

    if (lex_try_eat(lex, '=')) {
        node->init = node->n ? parse_code_arg_array(par, node->n) : parse_code_arg(par, ')', true);
        node->init->flags |= AST_MUST_EVAL;
    }

    array_push(&ctx->polyargs, node->name);
    return complete_node(par, node);
}

// An AST in standalone position is an expression that won't
// be matched against other types during semantic analysis:
//
//     var x = foo;
//             ^^^--------- standalone position
//     var x: Foo = foo;
//                  ^^^---- not standalone; matched with Foo
//
// This info is mainly used to handle untyped literals which
// can or must infer their type from the expression they are
// matched against. For example, an anonymous struct literal
// in standalone position is an error. An array literal in
// standalone position will infer the array element type
// from it's first initializer.
static Void mark_standalone_position (Parser *par, Ast *node) {
    node->flags |= AST_IN_STANDALONE_POSITION;

    switch (node->tag) {
    case AST_ARRAY_LITERAL: {
        AstArrayLiteral *n = cast(AstArrayLiteral*, node);
        if (! n->element) mark_standalone_position(par, array_get(&n->inits, 0));
    } break;

    case AST_TUPLE: {
        ArrayAst *fields = &cast(AstTuple*, node)->fields;
        array_iter (f, fields) mark_standalone_position(par, f);
    } break;

    case AST_TUPLE_FIELD: mark_standalone_position(par, cast(AstTupleField*, node)->rhs); break;
    case AST_ADDRESS_OF:  mark_standalone_position(par, cast(AstBaseUnary*, node)->op); break;
    default: break;
    }
}

// Recurse down a fn arg constraint and mark positions where
// it's legal to put a reference or definition to a polyarg
// with the AST_IN_POLY_ARG_POSITION flag. For example:
//
//     fn a ($T, y: Type($R)) {}
//           ^^----------^^---------- Ok.
//     fn b { var x: $T; }
//                   ^^-------------- Error.
//
// We also mark trees with the AST_HAS_POLY_ARGS flag if they
// contain definitions or references of polyargs.
static Void mark_poly_arg_position (Parser *par, Ast *parent, Ast *node) {
    if (! node) return;

    switch (node->tag) {
    case AST_IDENT: {
        ArgContext *ctx = array_get_last(&par->arg_context_stack);
        IString *name = cast(AstIdent*, node)->name;

        node->flags |= AST_IN_POLY_ARG_POSITION;
        if (array_has(&ctx->polyargs, name)) { node->flags |= AST_HAS_POLY_ARGS; break; }

        array_iter (arg, &ctx->args) {
            Bool found = false;

            switch (arg->tag) {
            #define X(TAG, TYPE) case TAG: found = (name == cast(TYPE*, arg)->name); break;
                EACH_STATIC_NAME_GENERATOR(X)
            #undef X
            default: badpath;
            }

            if (found && (arg->flags & AST_HAS_POLY_ARGS)) { node->flags |= AST_HAS_POLY_ARGS; break; }
        }
    } break;
    case AST_VAR_DEF: {
        AstVarDef *n = cast(AstVarDef*, node);
        node->flags |= AST_IN_POLY_ARG_POSITION;
        mark_poly_arg_position(par, node, n->constraint);

        if (n->init && n->constraint && (n->constraint->flags & AST_HAS_POLY_ARGS)) {
            // Since the constraint contains polyargs we don't want
            // to typecheck the initializer at all, since it could
            // be something that is also polymorphic like an anon
            // struct literal. We will simply make copies of the
            // initializer for each call. To this end we add the
            // AST_ADDED_TO_CHECK_LIST flag.
            n->init->flags &= ~AST_MUST_EVAL;
            n->init->flags |= AST_ADDED_TO_CHECK_LIST;
        }
    } break;
    case AST_ARG_POLY_VALUE: {
        AstArgPolyValue *n = cast(AstArgPolyValue*, node);
        node->flags |= (AST_IN_POLY_ARG_POSITION | AST_HAS_POLY_ARGS);
        mark_poly_arg_position(par, node, n->constraint);

        if (n->init && n->constraint && (n->constraint->flags & AST_HAS_POLY_ARGS)) {
            // Same as in the AST_VAR_DEF case.
            n->init->flags &= ~AST_MUST_EVAL;
            n->init->flags |= AST_ADDED_TO_CHECK_LIST;
        }
    } break;
    case AST_ARG_POLY_TYPE:
        node->flags |= (AST_IN_POLY_ARG_POSITION | AST_HAS_POLY_ARGS);
        break;
    case AST_ADDRESS_OF:
        node->flags |= AST_IN_POLY_ARG_POSITION;
        mark_poly_arg_position(par, node, cast(AstBaseUnary*, node)->op);
        break;
    case AST_ARRAY_TYPE:
        node->flags |= AST_IN_POLY_ARG_POSITION;
        mark_poly_arg_position(par, node, cast(AstArrayType*, node)->element);
        break;
    case AST_DOT:
        node->flags |= AST_IN_POLY_ARG_POSITION;
        mark_poly_arg_position(par, node, cast(AstDot*, node)->lhs);
        break;
    case AST_TUPLE_FIELD:
        node->flags |= AST_IN_POLY_ARG_POSITION;
        mark_poly_arg_position(par, node, cast(AstTupleField*, node)->rhs);
        break;
    case AST_TUPLE:
        node->flags |= AST_IN_POLY_ARG_POSITION;
        array_iter (f, &cast(AstTuple*, node)->fields) mark_poly_arg_position(par, node, cast(Ast*, f));
        break;
    case AST_CALL:
        node->flags |= AST_IN_POLY_ARG_POSITION;
        array_iter (a, &cast(AstCall*, node)->args) mark_poly_arg_position(par, node, a);
        break;
    case AST_FN_TYPE: {
        node->flags |= AST_IN_POLY_ARG_POSITION;
        AstBaseFn *n = cast(AstBaseFn*, node);
        array_iter (i, &n->inputs) mark_poly_arg_position(par, node, i);
        mark_poly_arg_position(par, node, n->output);
    } break;
    case AST_TYPEOF:
        node->flags |= AST_IN_POLY_ARG_POSITION;
        mark_poly_arg_position(par, node, cast(AstBaseUnary*, node)->op);
        break;
    default: break;
    }

    parent->flags |= (node->flags & AST_HAS_POLY_ARGS);
}

static ArgContext *parse_args (Parser *par, Bool runtime_args_allowed, Bool code_args_allowed) {
    ArgContext *ctx = push_arg_context(par);
    if (! lex_try_eat(lex, '(')) return ctx;

    while (true) {
        Ast *arg = 0;
        TokenTag tok = lex_peek(lex)->tag;

        if (tok == '$') {
            arg = parse_poly_type(par, true, true);
        } else if (tok != TOKEN_IDENT) {
            break;
        } else if (lex_try_peek_nth(lex, 2, '$')) {
            arg = parse_poly_value(par, ctx);
        } else if (lex_try_peek_nth(lex, 3, '$') && !lex_try_peek_nth(lex, 4, TOKEN_IDENT)) {
            arg = parse_poly_code(par, ctx);
            if (! code_args_allowed) par_error_pos(par, arg->pos, "Code arguments are only allowed in macros.");
        } else if (!lex_try_peek_nth(lex, 2, ':') && !lex_try_peek_nth(lex, 2, '=')) {
            arg = cast(Ast*, make_node(par, AstVarDef));
            AstVarDef *a = cast(AstVarDef*, arg);
            a->name = lex_eat_this(lex, TOKEN_IDENT)->str;
            complete_node(par, arg);
            a->constraint = make_anon_poly_type(par, arg, a->name);
        } else {
            arg = parse_var_def(par, false, false);
            AstVarDef *a = cast(AstVarDef*, arg);
            if (a->init && a->init->tag == AST_CALLER_INFO) cast(AstCallerInfo*, a->init)->as_default_arg = true;
            if (cast(AstVarDef*, arg)->init) cast(AstVarDef*, arg)->init->flags |= AST_MUST_EVAL;
            if (! runtime_args_allowed) par_error_pos(par, arg->pos, "Runtime arguments not allowed here.");
        }

        array_push(&ctx->args, arg);
        if (! lex_try_eat(lex, ',')) break;
    }

    lex_eat_this(lex, ')');
    return ctx;
}

static Ast *parse_fn (Parser *par, Bool as_expression) {
    AstId id = ast_next_id();
    SrcPos start = lex_peek(lex)->pos;
    AstFlags is_macro = (lex_eat(lex)->tag == TOKEN_MACRO) ? AST_IS_MACRO : 0;

    try_parse_attributes(id,);

    IString *name = as_expression ? 0 : lex_eat_this(lex, TOKEN_IDENT)->str;
    if (! name) name = make_anon_fn_name(par, start.offset);

    ArgContext *ctx = parse_args(par, true, is_macro);
    AstBaseFn *node = 0;

    if (lex_try_eat(lex, TOKEN_FAT_ARROW)) {
        node = cast(AstBaseFn*, ast_alloc_id(par->mem, AST_FN_POLY, 0, id));
        cast(Ast*, node)->pos = start;
        String return_name = astr_fmt(par->mem, "Return(%.*s)", STR(*name));
        node->output = make_anon_poly_type(par, cast(Ast*, node), intern_str(par->interns, return_name));
    } else {
        node = cast(AstBaseFn*, ast_alloc_id(par->mem, (ctx->polyargs.count ? AST_FN_POLY : AST_FN), is_macro, id));
        cast(Ast*, node)->pos = start;
        if (lex_try_eat(lex, TOKEN_ARROW)) node->output = parse_expression_before_brace(par);
    }

    if (ctx->polyargs.count) {
        AstFnPoly *n = cast(AstFnPoly*, node);
        n->name = name;

        if (!lex_try_peek(lex, '{') && !lex_try_peek(lex, TOKEN_DO)) { // Fat arrow.
            Auto body = make_node(par, AstReturn);
            body->result = parse_expression(par, 0);
            array_push(&n->statements, complete_node(par, body));
        } else {
            parse_block(par, &n->statements, cast(Ast*, n), 0);
        }

        array_iter (arg, &ctx->args) mark_poly_arg_position(par, cast(Ast*, node), arg);
        mark_poly_arg_position(par, cast(Ast*, node), node->output);
        cast(Ast*, n)->flags &= ~AST_HAS_POLY_ARGS;
        if (as_expression) cast(Ast*, n)->flags |= AST_CAN_EVAL_WITHOUT_VM;
    } else {
        AstFn *n = cast(AstFn*, node);
        n->name = name;
        parse_block(par, &n->statements, cast(Ast*, node), 0);
    }

    swap(node->inputs, ctx->args);
    pop_arg_context(par);
    return complete_node(par, node);
}

static Ast *parse_fn_type (Parser *par) {
    Auto node = cast(AstBaseFn*, make_node(par, AstFnType));
    lex_eat_this(lex, TOKEN_FN_TYPE);
    try_parse_attributes(cast(Ast*, node)->id,);

    if (lex_try_eat(lex, '(')) {
        while (! lex_try_peek(lex, ')')) {
            if (lex_try_peek(lex, TOKEN_IDENT) && lex_try_peek_nth(lex, 2, ':')) { lex_eat(lex); lex_eat(lex); }
            array_push(&node->inputs, parse_expression(par, 0));
            if (! lex_try_eat(lex, ',')) break;
        }

        lex_eat_this(lex, ')');
    }

    if (lex_try_eat(lex, TOKEN_ARROW)) node->output = parse_expression(par, 0);
    return complete_node(par, node);
}

static Ast *parse_fn_linux (Parser *par) {
    Auto node = cast(AstBaseFn*, make_node(par, AstFnLinux));
    lex_eat_this(lex, TOKEN_FN);

    try_parse_attributes(((Ast*)node)->id, {
        eat_attribute(linux);
        lex_eat_this(lex, '=');
        cast(AstFnLinux*, node)->num = cast(U32, lex_eat_this(lex, TOKEN_U64_LITERAL)->u64);
    });

    cast(AstFnLinux*, node)->name = lex_eat_this(lex, TOKEN_IDENT)->str;

    if (lex_try_eat(lex, '(')) {
        while (! lex_try_peek(lex, ')')) {
            if (lex_try_peek(lex, TOKEN_IDENT) && lex_try_peek_nth(lex, 2, ':')) { lex_eat(lex); lex_eat(lex); }
            array_push(&node->inputs, parse_expression(par, 0));
            if (! lex_try_eat(lex, ',')) break;
        }

        lex_eat_this(lex, ')');
    }

    if (lex_try_eat(lex, TOKEN_ARROW)) node->output = parse_expression(par, 0);
    return complete_node(par, node);
}

static Ast *parse_struct_member (Parser *par) {
    switch (lex_peek(lex)->tag) {
    case TOKEN_UNION:  return parse_struct(par);
    case TOKEN_STRUCT: return parse_struct(par);
    case TOKEN_IDENT:  return parse_var_def(par, true, false);
    case TOKEN_EMBED:  return parse_embed(par, AST_LEVEL_STRUCT);
    case TOKEN_IF:     return parse_if_ct(par, AST_LEVEL_STRUCT);
    default:           return 0;
    }
}

static Ast *parse_struct_poly (Parser *par) {
    Auto node = make_node(par, AstStructPoly);

    if (lex_eat(lex)->tag == TOKEN_UNION) cast(Ast*, node)->flags |= AST_IS_UNION;
    try_parse_attributes(cast(Ast*, node)->id,);
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;

    ArgContext *ctx = parse_args(par, false, false);
    swap(node->args, ctx->args);
    array_iter (arg, &node->args) mark_poly_arg_position(par, cast(Ast*, node), arg);
    cast(Ast*, node)->flags &= ~AST_HAS_POLY_ARGS;
    pop_arg_context(par);

    lex_eat_this(lex, '{');

    while (! lex_try_peek(lex, '}')) {
        Ast *member = parse_struct_member(par);
        if (! member) break;
        array_push(&node->members, member);
    }

    lex_eat_this(lex, '}');
    return complete_node(par, node);
}

static Ast *parse_struct (Parser *par) {
    Auto node = make_node(par, AstStruct);

    if (lex_eat(lex)->tag == TOKEN_UNION) cast(Ast*, node)->flags |= AST_IS_UNION;
    try_parse_attributes(cast(Ast*, node)->id,);
    Token *name = lex_try_eat(lex, TOKEN_IDENT);
    if (name) node->name = name->str;
    lex_eat_this(lex, '{');

    while (! lex_try_peek(lex, '}')) {
        Ast *member = parse_struct_member(par);
        if (! member) break;
        array_push(&node->members, member);
    }

    lex_eat_this(lex, '}');
    return complete_node(par, node);
}

static Ast *parse_enum_member (Parser *par) {
    switch (lex_peek(lex)->tag) {
    case TOKEN_IDENT: {
        Auto field = make_node(par, AstEnumField);
        field->name = lex_eat_this(lex, TOKEN_IDENT)->str;
        if (lex_try_eat(lex, '=')) {
            field->init = parse_expression(par, 0);
            field->init->flags |= AST_MUST_EVAL;
        }
        return complete_node(par, field);
    }
    case TOKEN_IF:    return parse_if_ct(par, AST_LEVEL_ENUM);
    case TOKEN_EMBED: return parse_embed(par, AST_LEVEL_ENUM);
    default:          return 0;
    }
}

static Ast *parse_enum (Parser *par) {
    Auto node = make_node(par, AstEnum);

    lex_eat_this(lex, TOKEN_ENUM);

    try_parse_attributes(cast(Ast*, node)->id, {}, {
        if (try_eat_attribute(indistinct)) {
            node->is_indistinct = true;
        } else if (try_eat_attribute(explicit)) {
            node->is_explicit = true;
        } else if (try_eat_attribute(implicit)) {
            node->is_implicit = true;
        } else if (try_eat_attribute(flags)) {
            node->is_flags = true;
        } else if (node->type) {
            par_error_pos2(par, node->type->pos, lex_peek(lex)->pos, "Redeclaring enum type constraint or invalid attribute.");
        } else {
            node->type = try_parse_expression(par, 0);
        }
    });

    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    lex_eat_this(lex, '{');

    Bool in_masks_section = false;

    while (true) {
        if (!in_masks_section && try_peek_attribute(masks) && lex_try_peek_nth(lex, 2, ':')) {
            Auto dummy = cast(Ast*, make_node(par, AstDummy));
            eat_attribute(masks);
            lex_eat_this(lex, ':');
            array_push(&node->members, complete_node(par, dummy));
            in_masks_section = true;
        } else {
            Ast *n = parse_enum_member(par);
            if (! n) break;
            array_push(&node->members, n);
            if (!lex_try_eat(lex, ',') && !(n->flags & AST_IS_BINDGEN)) break;
        }
    }

    lex_eat_this(lex, '}');
    return complete_node(par, node);
}

static Ast *parse_defer (Parser *par) {
    Auto node = make_node(par, AstDefer);
    lex_eat_this(lex, TOKEN_DEFER);

    if (lex_try_peek(lex, TOKEN_DO)) {
        node->stmt = parse_block(par);
    } else if (lex_try_peek(lex, '{')) {
        node->stmt = parse_block(par);
    } else {
        node->stmt = try_parse_expression(par, 0);
        if (! node->stmt) par_error(par, "Expected block or expression.");
        lex_eat_this(lex, ';');
    }

    return complete_node(par, node);
}


static Ast *parse_import (Parser *par) {
    Auto node = make_node(par, AstImport);

    lex_eat_this(lex, TOKEN_IMPORT);
    try_parse_attributes(cast(Ast*, node)->id,);
    node->path_gen = parse_expression_before_brace(par);
    node->path_gen->flags |= AST_MUST_EVAL;

    if (! lex_try_eat(lex, ';')) {
        lex_eat_this(lex, '{');

        while (! lex_try_peek(lex, '}')) {
            Auto config = make_node(par, AstImportConfig);
            config->name = lex_eat_this(lex, TOKEN_IDENT)->str;
            if (lex_try_eat(lex, '=')) { config->init = lex_eat_this(lex, '*')->str; node->alias = config->name; }
            complete_node(par, config);
            array_push(&node->configs, config);
            if (! lex_try_eat(lex, ',')) break;
        }

        lex_eat_this(lex, '}');
    }

    return complete_node(par, node);
}

static Ast *parse_assign (Parser *par, Ast *lhs, AstTag fused_op) {
    Auto result = cast(AstBaseBinary*, make_node_lhs(par, AstAssign, lhs));
    lex_eat(lex);
    result->op1 = lhs;
    result->op2 = parse_expression(par, 0);
    cast(AstAssign*, result)->fused_op = fused_op;
    return complete_node(par, result);
}

static Void parse_block (Parser *par, ArrayAst *out, Ast *tag_holder, IString **label) {
    Bool without_braces = lex_try_eat(lex, TOKEN_DO);
    if (! without_braces) lex_eat_this(lex, '{');

    try_parse_attributes(tag_holder->id, {
        if (label && lex_try_peek(lex, TOKEN_IDENT)) *label = lex_eat(lex)->str;
    });

    if (without_braces) {
        Ast *stmt = parse_statement(par);
        if (! stmt) par_error(par, "Expected statement.");
        array_push(out, stmt);
    } else {
        while (true) {
            Ast *stmt = parse_statement(par);
            if (! stmt) break;
            array_push(out, stmt);
        }

        lex_eat_this(lex, '}');
    }
}

static Ast *parse_block_explicit (Parser *par) {
    Auto node = make_node(par, AstBlock);
    if (lex_try_peek(lex, '{')) cast(Ast*, node)->flags |= AST_ENDS_WITH_BLOCK;
    parse_block(par, &node->statements, cast(Ast*, node), &node->label);
    return complete_node(par, node);
}

static Ast *parse_scope_mod (Parser *par) {
    Auto node = make_node(par, AstScopeMod);

    lex_eat_this(lex, TOKEN_SCOPE);

    parse_attributes(cast(Ast*, node)->id, {
        if (try_eat_attribute(public)) {
            node->is_public = true;
        } else {
            eat_attribute(private);
        }
    });

    if (! lex_try_eat(lex, ';')) {
        if (lex_try_peek(lex, TOKEN_SCOPE)) par_error(par, "Cannot apply 'scope' to 'scope'.");
        node->stmt = parse_top_statement(par);
    }

    return complete_node(par, node);
}

static Ast *parse_type_alias (Parser *par) {
    Auto node = make_node(par, AstTypeAlias);
    lex_eat_this(lex, TOKEN_TYPE);
    parse_attributes(cast(Ast*, node)->id, eat_attribute(alias));
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    lex_eat_this(lex, '=');
    node->val = parse_expression(par, 0);
    lex_eat_this(lex, ';');
    return complete_node(par, node);
}

static Ast *parse_type_distinct (Parser *par) {
    Auto node = make_node(par, AstTypeDistinct);
    lex_eat_this(lex, TOKEN_TYPE);
    try_parse_attributes(cast(Ast*, node)->id,);
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    lex_eat_this(lex, '=');
    node->val = parse_expression(par, 0);
    lex_eat_this(lex, ';');
    return complete_node(par, node);
}

static Ast *parse_type_constraint_def (Parser *par) {
    Auto node = make_node(par, AstTypeConstraint);
    lex_eat_this(lex, TOKEN_TYPE);
    parse_attributes(cast(Ast*, node)->id, eat_attribute(constraint));
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    lex_eat_this(lex, '=');
    node->constraint = parse_expression(par, 0);
    lex_eat_this(lex, ';');
    return complete_node(par, node);
}

static Ast *parse_top_statement (Parser *par) {
    Ast *result = 0;

    switch (lex_peek(lex)->tag) {
    case TOKEN_IF: {
        if (! starts_with_attribute(ct)) par_error(par, "Invalid file level statement.");
        result = parse_if_ct(par, AST_LEVEL_FILE);
    } break;
    case TOKEN_VAR: {
        result = parse_var_def(par, true, true);
        result->flags |= AST_MUST_EVAL;
    } break;
    case '.': {
        result = parse_builtin(par);
        if (result->tag != AST_CT_ASSERT) par_error(par, "Invalid file level statement.");
        lex_eat_this(lex, ';');
    } break;
    case TOKEN_FN: {
        if (lex_try_peek(lex, TOKEN_FN) && starts_with_attribute(linux)) {
            result = parse_fn_linux(par);
        } else {
            result = parse_fn(par, false);
        }
    } break;
    case ';':           while (lex_try_eat(lex, ';')); return parse_top_statement(par);
    case TOKEN_EMBED:   result = parse_embed(par, AST_LEVEL_FILE); break;
    case TOKEN_ENUM:    result = parse_enum(par); break;
    case TOKEN_FN_TYPE: result = parse_fn_type(par); break;
    case TOKEN_IMPORT:  result = parse_import(par); break;
    case TOKEN_MACRO:   result = parse_fn(par, false); break;
    case TOKEN_SCOPE:   result = parse_scope_mod(par); break;
    case TOKEN_STRUCT:  result = lex_try_peek_nth(lex, 3, '(') ? parse_struct_poly(par) : parse_struct(par); break;
    case TOKEN_TYPE:    result = starts_with_attribute(alias) ? parse_type_alias(par) : parse_type_distinct(par); break;
    case TOKEN_UNION:   result = lex_try_peek_nth(lex, 3, '(') ? parse_struct_poly(par) : parse_struct(par); break;
    default:            return 0;
    }

    result->flags |= AST_IS_GLOBAL;
    mark_standalone_position(par, result);
    return result;
}

static Ast *parse_statement (Parser *par) {
    Ast *result = 0;

    switch (lex_peek(lex)->tag) {
    case TOKEN_EOF:      return 0;
    case ';':            while (lex_try_eat(lex, ';')); return parse_statement(par);
    case '{':            result = parse_block_explicit(par); break;
    case TOKEN_BREAK:    result = parse_break(par); break;
    case TOKEN_CONTINUE: result = parse_continue(par); break;
    case TOKEN_DEFER:    result = parse_defer(par); break;
    case TOKEN_DO:       result = parse_block_explicit(par); break;
    case TOKEN_EMBED:    result = parse_embed(par, AST_LEVEL_FN); break;
    case TOKEN_ENUM:     result = parse_enum(par); break;
    case TOKEN_EVAL:     result = parse_eval(par, false); break;
    case TOKEN_FN:       result = parse_fn(par, false); break;
    case TOKEN_FN_TYPE:  result = parse_fn_type(par); break;
    case TOKEN_IMPORT:   result = parse_import(par); break;
    case TOKEN_MACRO:    result = parse_fn(par, false); break;
    case TOKEN_RETURN:   result = parse_return(par); break;
    case TOKEN_STRUCT:   result = lex_try_peek_nth(lex, 3, '(') ? parse_struct_poly(par) : parse_struct(par); break;
    case TOKEN_UNION:    result = lex_try_peek_nth(lex, 3, '(') ? parse_struct_poly(par) : parse_struct(par); break;
    case TOKEN_VAR:      result = parse_var_def(par, true, true); break;
    case TOKEN_WHILE:    result = parse_while(par); break;
    case TOKEN_TYPE:     result = starts_with_attribute(alias) ? parse_type_alias(par) : parse_type_distinct(par); break;
    case TOKEN_IF:       result = starts_with_attribute(ct) ? parse_if_ct(par, AST_LEVEL_FN) : parse_if(par); break;
    case '`': {
        if (! lex_try_peek_nth(lex, 2, TOKEN_IDENT)) return parse_backtick(par, false);
    } through;
    default: {
        Ast *n = try_parse_expression_before_brace(par);
        if (! n) return 0;

        switch (lex_peek(lex)->tag) {
        case '=':                   result = parse_assign(par, n, AST_ASSIGN); break;
        case TOKEN_2GREATER_EQUAL:  result = parse_assign(par, n, AST_SHIFT_RIGHT); break;
        case TOKEN_2LESS_EQUAL:     result = parse_assign(par, n, AST_SHIFT_LEFT); break;
        case TOKEN_AMPERSAND_EQUAL: result = parse_assign(par, n, AST_BITWISE_AND); break;
        case TOKEN_ASTERISK_EQUAL:  result = parse_assign(par, n, AST_MUL); break;
        case TOKEN_MINUS_EQUAL:     result = parse_assign(par, n, AST_SUB); break;
        case TOKEN_PERCENT_EQUAL:   result = parse_assign(par, n, AST_MOD); break;
        case TOKEN_PLUS_EQUAL:      result = parse_assign(par, n, AST_ADD); break;
        case TOKEN_SLASH_EQUAL:     result = parse_assign(par, n, AST_DIV); break;
        case TOKEN_VBAR_EQUAL:      result = parse_assign(par, n, AST_BITWISE_OR); break;
        default:                    result = n; break;
        }

        if (! (n->flags & AST_ENDS_WITH_BLOCK)) lex_eat_this(lex, ';');
    } break;
    }

    mark_standalone_position(par, result);
    return result;
}

AstFile *par_parse_file (Parser *par, IString *filepath) {
    String content = fs_read_entire_file(mem_base(par->mem), *filepath, 0);
    if (! content.data) return 0;

    par->file = cast(AstFile*, ast_alloc(par->mem, AST_FILE, 0));
    par->file->path = filepath;
    par->file->content = content;
    lex_reset(lex, par->file, 0);

    while (true) {
        Ast *stmt = parse_top_statement(par);
        if (! stmt) break;
        array_push(&par->file->statements, stmt);
    }

    if (! lex_try_peek(lex, TOKEN_EOF)) par_error(par, "Invalid file level statement.");
    return cast(AstFile*, complete_node(par, par->file));
}

AstFile *par_get_codegen_file (Parser *par) {
    return par->codegen.file;
}

AstCodeGen *par_parse_codegen (Parser *par, String code, Ast *origin, AstFile *origin_file, AstLevel level) {
    // @todo We can't realloc the codegen file buffer because Ast
    // nodes have slices into it. Probably the only way to do this
    // elegantly is to use virtual memory.
    U64 remaining = par->codegen.content.capacity - par->codegen.content.count;
    assert_always(code.count <= remaining);

    Auto gen = cast(AstCodeGen*, ast_alloc(par->mem, AST_CODE_GEN, 0));

    gen->origin = origin;
    cast(Ast*, gen)->pos.offset = par->codegen.content.count;
    cast(Ast*, gen)->pos.first_line = par->codegen.last_line;

    astr_push_fmt(&par->codegen.content, "CODEGEN: (byte=%lu, line=%lu, file=", origin->pos.offset, origin->pos.first_line);
    astr_push_str_quoted(&par->codegen.content, *origin_file->path);
    astr_push_cstr(&par->codegen.content, ") {\n");

    par->codegen.last_line++;
    array_iter (c, origin_file->path) if (c == '\n') par->codegen.last_line++;
    U64 start = par->codegen.content.count;

    astr_push_fmt(&par->codegen.content, "%.*s", STR(code));
    par->codegen.file->content = astr_to_str(&par->codegen.content);
    set_content(par, par->codegen.file, &(SrcPos){ .offset=start, .first_line=par->codegen.last_line, .length=code.count });

    switch (level) {
    case AST_LEVEL_ENUM:
        while (true) {
            Ast *n = parse_enum_member(par);
            if (! n) break;
            array_push(&gen->children, n);
            if (!lex_try_eat(lex, ',') && !(n->flags & AST_IS_BINDGEN)) break;
        }
        break;
    case AST_LEVEL_EXPR:   array_push(&gen->children, parse_expression(par, 0)); break;
    case AST_LEVEL_FILE:   while (true) { Ast *n = parse_top_statement(par); if (n) array_push(&gen->children, n); else break; } break;
    case AST_LEVEL_FN:     while (true) { Ast *n = parse_statement(par);     if (n) array_push(&gen->children, n); else break; } break;
    case AST_LEVEL_STRUCT: while (true) { Ast *n = parse_struct_member(par); if (n) array_push(&gen->children, n); else break; } break;
    }

    lex_eat_this(lex, TOKEN_EOF);

    astr_push_cstr(&par->codegen.content, "\n}\n\n"); // @end
    par->codegen.last_line = lex_get_prev_pos(lex).last_line + 3; // @end.
    par->codegen.file->content = astr_to_str(&par->codegen.content);

    complete_node(par, gen);
    cast(Ast*, gen)->pos.length += 2; // @end.
    cast(Ast*, gen)->pos.last_line += 1; // @end.

    return gen;
}

IString *par_parse_import_path (Parser *par, String path) {
    String ext   = par->interns->file_extension;
    String spec  = par->interns->file_path_lib_spec;
    AString astr = astr_new(par->mem);

    if (str_starts_with(path, spec)) {
        astr_push_str(&astr, par->interns->stdlib_file_path);
        astr_push_str(&astr, str_suffix_from(path, spec.count));
    } else {
        astr_push_str(&astr, path);
    }

    if (! str_ends_with(path, ext)) astr_push_str(&astr, ext);
    return intern_str(par->interns, astr_to_str(&astr));
}

Parser *par_new (Interns *interns, Mem *mem) {
    Parser *par = mem_new(mem, Parser);

    par->mem                    = mem;
    par->interns                = interns;
    par->lexer                  = lex_new(interns, mem);
    par->struct_literal_allowed = true;
    par->codegen.content        = astr_new_cap(mem, 1*MB);
    par->codegen.file           = cast(AstFile*, ast_alloc(mem, AST_FILE, 0));
    par->codegen.file->path     = intern_str(interns, interns->codegen_file_path);
    par->codegen.file->content  = astr_to_str(&par->codegen.content);
    par->codegen.last_line      = 1;

    map_init(&par->attributes, mem);
    array_init(&par->arg_context_pool, mem);
    array_init(&par->arg_context_stack, mem);

    return par;
}
