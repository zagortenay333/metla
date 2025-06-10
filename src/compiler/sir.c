// =============================================================================
// SSA construction algorithm:
// ---------------------------
//
// The initial build of Sir is in SSA form since we build the
// SSA form in a single pass right from the AST. The algorithm
// used is described in this paper:
//
//     Braun M., Buchwald S., Hack S., Leißa R., Mallon C.,
//     Zwinkau A. (2013) Simple and Efficient Construction of
//     Static Single Assignment Form. In: Jhala R., De Bosschere
//     K. (eds) Compiler Construction. CC 2013. Lecture Notes in
//     Computer Science, vol 7791. Springer, Berlin, Heidelberg.
//     https://doi.org/10.1007/978-3-642-37051-9_6
//
// The ssa_scope_lookup() function comprises most of the algorithm.
//
// The IR is emitted in a single pass while going down the AST. Phi
// ops are inserted on the fly when looking up what virtual register
// a particular variable is currently bound to. The possible cases
// during this lookup are:
//
//   1. The current basic block into which you're emitting ops has a
//      binding in it's SirSsaScope for the variable to some virtual
//      register. Use that virtual reg.
//
//   2. The current block knows all of it's predecessors (the block
//      is "sealed"), and after recursively looking up the variable
//      in each predecessor you get back the same virtual register.
//      Use that virtual reg.
//
//   3. The current block knows all of it's predecessors, and after
//      recursively looking up the variable in each predecessor you
//      get back different virtual registers. Insert a phi into the
//      current block and add the returned registers as arguments to
//      that phi. Bind the phi to the variable in the scope of the
//      current block and use that phi virtual register.
//
//   4. The current block doesn't know all it's predecessors, which
//      can happen since we are generating the SSA graph in one pass.
//      Insert an empty phi (without arguments) into the current block
//      and bind it to the variable in the current block. Later when
//      all of the block's predecessors become known (block "sealed"),
//      call sir_update_phi() on the empty phi which will fill up it's
//      arguments or maybe even delete it in case it's a trivial phi.
//
// Note that the above lookup process only applies to variables whose
// value is in a register. However, some variable values cannot be in
// a register either because they are globals, or they are local vars
// whose address was taken, or they can't fit into registers, etc...
//
// These memory bound variables are bound to virtual registers that
// hold the address of the value rather than the value itself. When
// looking up which virtual register such a varable is bound to, all
// you have to do is call ssa_scope_lookup_flat() on SirFn.ssa_scope.
//
// To determine if the variable you are about to lookup is an ssa or
// a memory bound variable, use the function value_is_in_register().
// =============================================================================
#include "base/string.h"
#include "base/log.h"
#include "os/fs.h"
#include "compiler/sir.h"
#include "compiler/sir_reg.h"
#include "compiler/sir_optimizer.h"

istruct (LoopBlocks) {
    Ast *node;
    SirBlock *break_block;
    SirBlock *continue_block;
};

istruct (SirOpArgCount) {
    I16 inputs;
    I16 outputs;
    I16 specials;
};

istruct (Builder) {
    Mem *mem;
    Sem *sem;
    Abi *abi;
    SirFn *fn;
    Interns *interns;
    SirVar next_var;
    SirBlock *block;
    SirBlock *dummy_block;
    SirOp *return_address_fn_arg;
    Array(LoopBlocks*) loop_blocks;
    Array(struct { AstId ast; SirVar var; }) var_scope;
    Array(struct { Ast *code; Ast *scope_owner; }) defers;
    Array(struct { SirVar var; SirBlock *block; }) pseudo_return_targets;
};

#define SIR_VAR_MEMORY ((SirVar)0)

static SirOp *emit (Builder *, Ast *);
Bool sir_update_phi (SirFn *, SirOp *);
static SirOp *emit_phi (SirFn *, SirBlock *, SirVar, Type *);
static SirOp *ssa_scope_lookup (SirFn *, SirBlock *, SirVar, Type *);

SirOpFlags sir_op_get_default_flags [] = {
    #define X(a,b,c,d,flags) flags,
    #include "sir_ops.h"
};

static SirOpArgCount get_op_arg_count [] = {
    #define X(_, s, o, i, ...) { .specials=s, .outputs=o, .inputs=i },
    #include "sir_ops.h"
};

Char *sir_op_tag_to_str [] = {
    #define X(tag, ...) #tag,
    #include "sir_ops.h"
};

Char *sir_block_tag_to_str [] = {
    #define ADD_BLOCK_TAG(tag) #tag,
    EACH_SIR_BLOCK(ADD_BLOCK_TAG)
};

static Void check_integrity_dfs (SirFn *fn, SirBlock *block) {
    if (block->flags & SIR_BLOCK_IS_VISITED) return;

    SirOp *last = array_try_get_last(&block->ops);

    if (! last) {
        assert_dbg(block->succs.count < 2);
    } else if (last->tag == SIR_OP_BRANCH) {
        assert_dbg(block->succs.count == 2);
    } else if (last->tag == SIR_OP_RETURN) {
        assert_dbg(block->succs.count == 1);
        assert_dbg(cast(AstBaseFn*, fn->ast)->output);
        assert_dbg(array_get(&block->succs, 0)->tag == SIR_BLOCK_EXIT);
    } else {
        assert_dbg(block->succs.count < 2);
    }

    array_iter (phi, &block->phis) {
        assert_dbg(phi->block == block);
        assert_dbg(array_has(&block->phis, phi));
        assert_dbg(phi->args.count == block->preds.count);

        array_iter (user, &phi->users) {
            assert_dbg((user->tag == SIR_OP_PHI) || !(user->block->flags & SIR_BLOCK_IS_VISITED));
            assert_dbg(! (user->block->flags & SIR_BLOCK_IS_DEAD));
            assert_dbg(array_has(&user->args, phi));
        }
    }

    array_iter (op, &block->ops) {
        assert_dbg(op->block == block);
        assert_dbg(array_has(&block->ops, op));

        array_iter (user, &op->users) {
            assert_dbg(!(user->block->flags & SIR_BLOCK_IS_VISITED) || (user->tag == SIR_OP_PHI) || (user->tag == SIR_OP_PHI_MEM));
            assert_dbg(! (user->block->flags & SIR_BLOCK_IS_DEAD));
            assert_dbg(array_has(&user->args, op));
        }
    }

    block->flags |= SIR_BLOCK_IS_VISITED;

    array_iter (succ, &block->succs) {
        assert_dbg(succ->idom->flags & SIR_BLOCK_IS_VISITED);
        check_integrity_dfs(fn, succ);
    }

    block->flags &= ~SIR_BLOCK_IS_VISITED;
}

Void sir_check_integrity (SirFn *fn) {
    IF_BUILD_RELEASE(return);

    sir_mark_reachable_blocks(fn, fn->entry_block);
    assert_dbg(! fn->entry_block->idom);

    if (!(fn->exit_block->flags & SIR_BLOCK_IS_DEAD) && cast(AstBaseFn*, fn->ast)->output) {
        array_iter (pred, &fn->exit_block->preds) {
            assert_dbg(array_get_last(&pred->ops)->tag == SIR_OP_RETURN);
        }
    }

    array_iter (block, &fn->blocks) {
        assert_dbg(block->scratch == 0);
        assert_dbg(block->flags & SIR_BLOCK_ALL_PREDS_KNOWN);
        assert_dbg(block->flags & SIR_BLOCK_IS_REACHABLE);
        assert_dbg(! (block->flags & SIR_BLOCK_IS_DEAD));
        assert_dbg(! (block->flags & SIR_BLOCK_IS_VISITED));
    }

    check_integrity_dfs(fn, fn->entry_block);
}

#define PRINT_LIVE_INS  false
#define PRINT_LIVE_OUTS false
#define FONT_NAME       "Monospace"
#define FONT_SIZE       "10"
#define DIRECTION       "TB"
#define BACKGROUND      "#221A0F"
#define FOREGROUND      "#B48E56"
#define FOREGROUND2     "#83705C"
#define CFG_EDGE        "#689d6a"
#define DOM_EDGE        "#D2651D"
#define VALUE           "#83705C"
#define VIRTUAL_REG     FOREGROUND
#define PHYSICAL_REG    FOREGROUND
#define MEM             "#9E5D46"
#define USERS           FOREGROUND2
#define PHI             "#D2651D"
#define MEM_PHI         "#9E5D46"
#define BLOCK_BG        "#261D11"
#define BLOCK_ID        "#689d6a"
#define BLOCK_TXT       FOREGROUND
#define BLOCK_BORDER    "#130F08"
#define BLOCK_NAME      "#83705C"
#define FN_BG           "#302617"
#define FN_NAME         "#C19030"
#define FN_BORDER       "#130F08"
#define LIVE_REG        "#D2651D"
#define BR              "<br align=\"left\"/>"

istruct (Printer) {
    SirFn *fn;
    AString astr;
    SirRegAlloc *ra;
    U32 max_op_name_len;
};

static String get_op_tag_str (SirOp *op) {
    return str_cut_prefix(str(sir_op_tag_to_str[op->tag]), str("SIR_OP_"));
}

static Void print_op_indent (Printer *printer, U32 op_name_len) {
    U32 len = printer->max_op_name_len - op_name_len + 1;
    astr_push_fmt(&printer->astr, "%*s", (int)len, "");
}

static Void print_indent (Printer *printer) {
    astr_push_cstr(&printer->astr, "        ");
}

static Void print_value (Printer *printer, Type *type, Value val) {
    astr_push_fmt(&printer->astr, "<font color=\"" VALUE "\">(");
    vm_value_log(&printer->astr, type, val);
    astr_push_fmt(&printer->astr, ") </font>");
}

static Void print_users (Printer *printer, SirOp *op) {
    if (printer->ra) return;
    if (op->users.count == 0) return;
    astr_push_cstr(&printer->astr, "<font color=\"" USERS "\">(users:");
    array_iter (it, &op->users) astr_push_fmt(&printer->astr, " v%i", it->id);
    astr_push_cstr(&printer->astr, ") </font>");
}

static Void print_block_tag (Printer *printer, SirBlock *block) {
    Auto tag = str_cut_prefix(str(sir_block_tag_to_str[block->tag]), str("SIR_BLOCK_"));
    astr_push_fmt(&printer->astr, "<font color=\"" BLOCK_NAME "\">(%.*s) </font>", STR(tag));
}

static Void print_block_id (Printer *printer, SirBlockId id) {
    astr_push_fmt(&printer->astr, "<b><font color=\"" BLOCK_ID "\">b%i </font></b>", id);
}

static Void print_virtual_reg_as_comment (Printer *printer, SirOpId id) {
    astr_push_fmt(&printer->astr, "<font color=\"" FOREGROUND2 "\">(v%i) </font>", id);
}

static Void print_fn_name_as_comment (Printer *printer, IString *name) {
    astr_push_fmt(&printer->astr, "<font color=\"" FOREGROUND2 "\">(%.*s) </font>", STR(*name));
}

static Void print_virtual_reg (Printer *printer, SirOpId id) {
    astr_push_fmt(&printer->astr, "<b><font color=\"" VIRTUAL_REG "\">v%i </font></b>", id);
}

static Void print_physical_reg (Printer *printer, SirReg *reg) {
    Auto n = sir_reg_name(reg);
    astr_push_fmt(&printer->astr, "<b><font color=\"" PHYSICAL_REG "\">%.*s </font></b>", STR(n));
}

static Void print_self (Printer *printer, SirOp *op) {
    if (printer->ra) {
        Auto regs = array_get(&printer->ra->bindings, op->id);
        print_physical_reg(printer, regs->self);
    } else {
        print_virtual_reg(printer, op->id);
    }
}

static Void print_input_arg (Printer *printer, SirOp *op, U32 arg_idx) {
    if (printer->ra) {
        Auto regs = array_get(&printer->ra->bindings, op->id);
        print_physical_reg(printer, array_get(&regs->inputs, arg_idx));
    } else {
        Auto inputs = sir_op_get_inputs(op);
        print_virtual_reg(printer, inputs.data[arg_idx]->id);
    }
}

static Void print_output_arg (Printer *printer, SirOp *op, U32 arg_idx) {
    if (printer->ra) {
        Auto regs = array_get(&printer->ra->bindings, op->id);
        print_physical_reg(printer, array_get(&regs->outputs, arg_idx));
    } else {
        Auto outputs = sir_op_get_outputs(op);
        print_virtual_reg(printer, outputs.data[arg_idx]->id);
    }
}

static Void print_fn_name (Printer *printer) {
    Auto n = printer->fn->ast->name;
    astr_push_fmt(&printer->astr, "<b><font color=\"" FN_NAME "\">%.*s </font></b>", STR(*n));
}

static Void print_mem (Printer *printer, SirOp *old, SirOp *new) {
    if (printer->ra) {
        return;
    } else if (new) {
        astr_push_fmt(&printer->astr, "<font color=\"" MEM "\">[v%i:v%i] </font>", old->id, new->id);
    } else {
        astr_push_fmt(&printer->astr, "<font color=\"" MEM "\">[v%i] </font>", old->id);
    }
}

static Void print_arrow (Printer *printer) {
    astr_push_cstr(&printer->astr, "&lt;- ");
}

static Void print_op_tag (Printer *printer, SirOp *op) {
    Auto tag = get_op_tag_str(op);
    astr_push_fmt(&printer->astr, "%.*s", STR(tag));
    print_op_indent(printer, tag.count);
}

static Void print_op (Printer *printer, SirOp *op) {
    switch (op->tag) {
    case SIR_OP_NOP:
        return;

    case SIR_OP_MEMORY: {
        if (printer->ra) return;
        print_op_tag(printer, op);
    } break;

    case SIR_OP_PHI:
    case SIR_OP_PHI_MEM: {
        if (printer->ra && op->tag == SIR_OP_PHI_MEM) return;

        Auto tag = get_op_tag_str(op);

        astr_push_fmt(&printer->astr, "<font color=\"" PHI "\">%.*s</font>", STR(tag));
        print_op_indent(printer, tag.count);
        print_self(printer, op);
        print_arrow(printer);

        array_iter (arg, &op->args) {
            Auto arg_block = array_get(&op->block->preds, ARRAY_IDX);
            astr_push_fmt(&printer->astr, "<b><font color=\"" VIRTUAL_REG "\">v%i</font>:", arg->id);
            astr_push_fmt(&printer->astr, "<font color=\"" BLOCK_ID "\">b%i</font> </b>", arg_block->id);
        }
    } break;

    case SIR_OP_CONST: {
        print_op_tag(printer, op);
        print_self(printer, op);
        Auto val = sir_op_get_value(printer->fn, op);
        print_value(printer, op->type, val);
    } break;

    case SIR_OP_LINUX_SYSCALL: {
        print_op_tag(printer, op);
        print_self(printer, op);
        print_arrow(printer);
        Auto inputs = sir_op_get_inputs(op);
        array_iter (_, &inputs) { _; print_input_arg(printer, op, ARRAY_IDX); }
        Auto ast = cast(AstFnLinux*, sir_op_get_value(printer->fn, op).ast);
        Auto n = ast->name;
        astr_push_fmt(&printer->astr, "<font color=\"" VALUE "\">(%.*s) </font>", STR(*n)); break;
    } break;

    case SIR_OP_FN_ARG: {
        print_op_tag(printer, op);
        print_self(printer, op);
    } break;

    case SIR_OP_OFFSET: {
        print_op_tag(printer, op);
        print_self(printer, op);
        print_arrow(printer);
        print_input_arg(printer, op, 0);
        Auto offset = sir_op_get_value(printer->fn, op).u32;
        astr_push_fmt(&printer->astr, "+%i ", offset);
    } break;

    case SIR_OP_STORE: {
        print_op_tag(printer, op);
        print_input_arg(printer, op, 0);
        print_arrow(printer);
        print_input_arg(printer, op, 1);
        Auto offset = sir_op_get_value(printer->fn, op).u32;
        if (offset) astr_push_fmt(&printer->astr, "+%i ", offset);
    } break;

    case SIR_OP_REG_STORE:
    case SIR_OP_REG_LOAD: {
        print_op_tag(printer, op);
        Auto arg0 = array_try_get(&op->args, 0);
        if (arg0) print_virtual_reg(printer, arg0->id);
        Auto regs = array_get(&printer->ra->bindings, op->id);
        print_physical_reg(printer, array_get(&regs->inputs, 0));
    } break;

    case SIR_OP_REG_MOVE: {
        print_op_tag(printer, op);
        Auto regs = array_get(&printer->ra->bindings, op->id);
        print_physical_reg(printer, array_get(&regs->outputs, 0));
        print_arrow(printer);
        print_physical_reg(printer, array_get(&regs->inputs, 0));
    } break;

    default: {
        Auto inputs  = sir_op_get_inputs(op);
        Auto outputs = sir_op_get_outputs(op);

        print_op_tag(printer, op);
        array_iter (_, &outputs) { _; print_output_arg(printer, op, ARRAY_IDX); }

        if (op->flags & SIR_OP_SELF_IS_REG) {
            print_self(printer, op);
            if (inputs.count) print_arrow(printer);
        } else if (outputs.count && inputs.count) {
            print_arrow(printer);
        }

        array_iter (_, &inputs) { _; print_input_arg(printer, op, ARRAY_IDX); }

        if (op->flags & SIR_OP_IS_DIRECT_CALL) {
            Auto fn = cast(AstFn*, sir_op_get_value(printer->fn, op).ast);
            print_fn_name_as_comment(printer, fn->name);
        }
    } break;
    }

    if (op->flags & SIR_OP_TOUCHES_MEMORY && op->tag != SIR_OP_MEMORY) {
        Auto arg0 = array_get(&op->args, 0);
        print_mem(printer, arg0, (op->flags & SIR_OP_MODIFIES_MEMORY) ? op : 0);
    }

    print_users(printer, op);
    print_virtual_reg_as_comment(printer, op->id);
    astr_push_cstr(&printer->astr, BR);
}

static Void print_edge (Printer *printer, SirBlock *from, SirBlock *to, Char *color) {
    Auto n = printer->fn->ast->name;
    print_indent(printer);
    astr_push_fmt(&printer->astr, "\"b%i_%.*s\" -> \"b%i_%.*s\" [color=\"%s\"]\n", from->id, STR(*n), to->id, STR(*n), color);
}

static Void print_block (Printer *printer, SirBlock *block) {
    Auto n           = printer->fn->ast->name;
    SirOp *mem_phi   = printer->fn->in_ssa_form ? block->mem_phi : 0;
    ArraySirOp *phis = printer->fn->in_ssa_form ? &block->phis : 0;

    { // Find longest op name:
        printer->max_op_name_len = 0;

        array_iter (op, &block->ops) {
            if ((op->tag == SIR_OP_PHI || op->tag == SIR_OP_PHI_MEM) && !printer->fn->in_ssa_form) continue;
            Auto len = strlen(sir_op_tag_to_str[op->tag]);
            if (len > printer->max_op_name_len) printer->max_op_name_len = len;
        }

        printer->max_op_name_len -= strlen("SIR_OP_");
    }

    astr_push_cstr(&printer->astr, "\n");
    print_indent(printer);
    astr_push_fmt(&printer->astr, "\"b%i_%.*s\" [label=<<font color=\"" BLOCK_TXT "\">", block->id, STR(*n));
    print_block_id(printer, block->id);
    print_block_tag(printer, block);

    if (mem_phi || phis || block->ops.count) {
        astr_push_cstr(&printer->astr, BR BR);

        #if PRINT_LIVE_INS
            astr_push_fmt(&printer->astr, "LIVE IN: ");
            array_iter (it, &block->live_in) print_virtual_reg(printer, it->id);
            astr_push_cstr(&printer->astr, BR BR);
        #endif

        if (block->fn->in_ssa_form) {
            if (mem_phi) print_op(printer, mem_phi);
            if (phis) array_iter (phi, phis) print_op(printer, phi);
        }

        array_iter (op, &block->ops) print_op(printer, op);

        #if PRINT_LIVE_OUTS
            astr_push_fmt(&printer->astr, BR "LIVE OUT: ");
            array_iter (it, &block->live_out) print_virtual_reg(printer, it->id);
            astr_push_cstr(&printer->astr, BR);
        #endif
    }

    astr_push_cstr(&printer->astr, "</font>>]\n");
    array_iter (succ, &block->succs) print_edge(printer, block, succ, CFG_EDGE);
    if (block->idom) print_edge(printer, block->idom, block, DOM_EDGE);
}

static Void print_fn (Printer *printer) {
    Auto n = printer->fn->ast->name;
    astr_push_fmt(&printer->astr, "\n    subgraph \"cluster_%.*s\" {\n", STR(*n));

    print_indent(printer);
    astr_push_cstr(&printer->astr, "color=\"" FN_BORDER "\" fillcolor=\"" FN_BG "\" style=\"filled\"\n");

    print_indent(printer);
    astr_push_cstr(&printer->astr, "labeljust=\"l\" label=<<br/>");
    print_fn_name(printer);
    astr_push_cstr(&printer->astr, ">\n");

    array_iter (block, &printer->fn->blocks) print_block(printer, block);

    astr_push_cstr(&printer->astr, "    }\n");
}

// Serializes the control flow graph into the well known 'dot' format.
Void sir_to_dot (SirFn *fn, Mem *mem, String filepath, SirRegAlloc *ra) {
    Printer printer = {};
    printer.fn = fn;
    printer.ra = ra;
    // printer.ra = ra;
    printer.astr = astr_new_cap(mem, 1024);
    astr_push_cstr(&printer.astr, "digraph {\n"
                                  "    graph [ranksep=.3 nodesep=.1 fontsize=" FONT_SIZE " fgcolor=\"" FOREGROUND "\" bgcolor=\"" BACKGROUND "\" fontname=\"" FONT_NAME "\" rankdir="DIRECTION"]\n"
                                  "    node  [fontsize=" FONT_SIZE " fontname=\"" FONT_NAME "\" color=\"" BLOCK_BORDER "\" fillcolor=\"" BLOCK_BG "\" shape=box style=filled]\n"
                                  "    edge  [arrowsize=.5]\n");
    print_fn(&printer);
    astr_push_cstr(&printer.astr, "}\n");
    fs_write_entire_file(filepath, astr_to_str(&printer.astr));
}

// Calls sir_to_dot if the functions has the user attribute sir:
//
//     fn: #sir foo () {
//     }
//
Void sir_to_dot_if_marked (SirFn *fn, Mem *mem, String filepath, SirRegAlloc *ra) {
    IF_BUILD_RELEASE(return);
    Bool print = sem_get_attribute(fn->sem, cast(Ast*, fn->ast), intern_cstr(fn->interns, "sir"));
    if (print) sir_to_dot(fn, mem, filepath, ra);
}

static Bool value_is_in_register (Builder *builder, Ast *node) {
    Ast *target = node;

    switch (node->tag) {
    #define X(TAG, T, ...) case TAG: target = cast(T*, node)->sem_edge; break;
        EACH_AST_SELECTOR(X);
    #undef X
    default: break;
    }

    if (target->flags & AST_ADDRESS_TAKEN) return false;
    if (target->flags & AST_IS_GLOBAL) return false;
    if (target->flags & AST_IS_FN_ARG_PASSED_BY_MEM) return false;

    Auto t = sem_get_type(builder->sem, target);
    return abi_can_be_in_reg(builder->abi, t);
}

SirBlock *sir_alloc_block (SirFn *fn, Mem *mem, SirBlockTag tag) {
    Auto block = mem_new(mem, SirBlock);
    block->id  = fn->next_block_id++;
    block->tag = tag;
    block->fn  = fn;

    array_init(&block->ops, mem);
    array_init(&block->preds, mem);
    array_init(&block->succs, mem);
    array_init(&block->live_in, mem);
    array_init(&block->live_out, mem);

    array_push(&fn->blocks, block);

    if (fn->in_ssa_form) {
        array_init(&block->phis, mem);
        array_init(&block->scope, mem);
        array_init(&block->phi_scratch_buf, mem);
    }

    return block;
}

// Finds the "immediate dominator" of the given block which
// is the parent node in the the dominator tree.
Void sir_update_idom (SirBlock *block) {
    if (block->preds.count == 0) return;

    Auto first_pred = array_get(&block->preds, 0);
    if (block->preds.count == 1) { block->idom = first_pred; return; }

    U32 depth = 0;
    for (Auto b = first_pred; b; b = b->idom) {
        b->flags |= SIR_BLOCK_IS_VISITED;
        b->scratch = depth++;
    }

    Auto result = first_pred;
    array_iter_from (b, &block->preds, 1) {
        while (b->preds.count && !(b->flags & SIR_BLOCK_IS_VISITED)) b = b->idom;
        if (b->scratch > result->scratch) result = b;
    }

    for (Auto b = first_pred; b; b = b->idom) {
        b->scratch = 0;
        b->flags &= ~SIR_BLOCK_IS_VISITED;
    }

    block->idom = result;
}

static Void seal_block (SirFn *fn, SirBlock *block) {
    block->flags |= SIR_BLOCK_ALL_PREDS_KNOWN;
    if (block->mem_phi && block->mem_phi->args.count == 0) sir_update_phi(fn, block->mem_phi);
    sir_update_phis(fn, block);
    array_find_remove_all_fast(&block->phis, IT->tag == SIR_OP_NOP);
    sir_update_idom(block);
}

static Void connect_blocks (SirBlock *from, SirBlock *to) {
    if (to->flags & SIR_BLOCK_IS_DEAD) return;
    if (from->flags & SIR_BLOCK_IS_DEAD) return;
    array_push_if_unique(&from->succs, to);
    array_push_if_unique(&to->preds, from);
}

static Void set_current_block (Builder *builder, SirBlock *block) {
    builder->block = block;
}

Void sir_op_add_to_block (SirBlock *block, SirOp *op) {
    op->block = block;
    array_push(&block->ops, op);
}

SliceSirOp sir_op_get_inputs (SirOp *op) {
    Auto argc = get_op_arg_count[op->tag];

    if (argc.specials == -1) {
        assert_dbg(argc.inputs == 0);
        assert_dbg(argc.outputs == 0);
        return (SliceSirOp){};
    } else if (argc.inputs) {
        assert_dbg(argc.outputs != -1);
        Auto n = argc.specials + argc.outputs;
        return (SliceSirOp){ .data=array_try_ref(&op->args, n), .count=op->args.count-n };
    } else {
        return (SliceSirOp){};
    }
}

SliceSirOp sir_op_get_outputs (SirOp *op) {
    Auto argc = get_op_arg_count[op->tag];

    if (argc.specials == -1) {
        assert_dbg(argc.inputs == 0);
        assert_dbg(argc.outputs == 0);
        return (SliceSirOp){};
    } else if (argc.outputs) {
        assert_dbg(argc.outputs != -1);
        return (SliceSirOp){ .data=array_try_ref(&op->args, argc.specials), .count=argc.outputs };
    } else {
        return (SliceSirOp){};
    }
}

static Bool sir_op_is_proper_user (SirOp *op, SirOp *user) {
    Auto outputs = sir_op_get_outputs(user);
    if (array_has(&outputs, op)) return true;

    Auto inputs = sir_op_get_inputs(user);
    return array_has(&inputs, op);
}

Void sir_op_set_value (SirFn *fn, SirOp *op, Value data) {
    map_add(&fn->op_data, op->id, data);
}

Value sir_op_get_value (SirFn *fn, SirOp *op) {
    Value val = {};
    map_get(&fn->op_data, op->id, &val);
    return val;
}

Void sir_op_remove_args (SirOp *op) {
    array_iter (arg, &op->args) array_find_remove_fast(&arg->users, IT == op);
    op->args.count = 0;
}

Void sir_op_delete (SirFn *fn, SirOp *op) {
    if (op->tag == SIR_OP_PHI_MEM) {
        op->block->mem_phi = 0;
    } else if (op->tag == SIR_OP_PHI) {
        array_find_remove_fast(&op->block->phis, IT == op);
    }

    sir_op_remove_args(op);
    op->tag = SIR_OP_NOP;
    op->flags = 0;
}

Bool sir_op_try_delete (SirFn *fn, SirOp *op) {
    if (op->users.count || !(op->flags & SIR_OP_DEAD_IF_UNUSED)) {
        return false;
    } else {
        sir_op_delete(fn, op);
        return true;
    }
}

Void sir_op_replace (SirFn *fn, SirOp *op, SirOp *replacement) {
    Auto users = op->users;
    op->users.count = 0;
    sir_op_try_delete(fn, op);
    array_iter (user, &users) {
        if (user == op) continue;
        array_find_replace_all(&user->args, IT == op, replacement);
        array_push_if_unique(&replacement->users, user);
    }
}

Bool sir_op_try_replace (SirFn *fn, SirOp *op, SirOp *replacement) {
    Auto users = op->users;

    op->users.count = 0;
    if (! sir_op_try_delete(fn, op)) {
        op->users.count = users.count;
        return false;
    }

    array_iter (user, &users) {
        if (user == op) continue;
        array_find_replace_all(&user->args, IT == op, replacement);
        array_push_if_unique(&replacement->users, user);
    }

    return true;
}

Void sir_op_remove_arg (SirOp *op, U32 arg_idx) {
    Auto old_arg = array_get(&op->args, arg_idx);
    array_find_remove_fast(&old_arg->users, IT == op);
    array_remove_fast(&op->args, arg_idx);
}

Void sir_op_set_arg (SirOp *op, U32 arg_idx, SirOp *new_arg) {
    Auto old_arg = array_get(&op->args, arg_idx);
    if (old_arg) array_find_remove_fast(&old_arg->users, IT == op);
    array_set(&op->args, arg_idx, new_arg);
    array_push_if_unique(&new_arg->users, op);
}

Void sir_op_add_arg (SirOp *op, SirOp *arg) {
    array_push(&op->args, arg);
    array_push_if_unique(&arg->users, op);
}

// The @phi arg can be NULL. This is lets you check whether
// the given set of phi args would result in a trivial phi.
static SirOp *replace_if_trivial_phi (SirFn *fn, SirOp *phi, ArraySirOp *phi_args) {
    SirOp *replacement = 0;

    array_iter (arg, phi_args) {
        if (arg == replacement || arg == phi) continue;
        if (replacement) return 0; // Not trivial.
        replacement = arg;
    }

    if (phi) {
        Auto users = phi->users; // Since sir_op_try_replace() sets users.count = 0.
        Bool success = sir_op_try_replace(fn, phi, replacement);
        assert_dbg(success);

        // Some of the users of this phi might be phis that now
        // became trivial. Let's also replace them recursively.
        array_iter (phi_user, &users) {
            if (phi_user != phi && (phi_user->tag == SIR_OP_PHI || phi_user->tag == SIR_OP_PHI_MEM)) {
                Auto r = replace_if_trivial_phi(fn, phi_user, &phi_user->args);
                if (r && phi_user == replacement) replacement = r; // Replacement candidate got replaced!
            }
        }
    }

    assert_dbg(replacement);
    return replacement;
}

static Void ssa_scope_add (SirSsaScope *scope, SirVar var, SirOp *val) {
    array_push_lit(scope, var, val);
}

static SirOp *ssa_scope_lookup_flat (SirSsaScope *scope, SirVar var) {
    array_iter_back (e, scope, *) if (var == e->var && e->val->tag != SIR_OP_NOP) return e->val;
    return 0;
}

// The @phi arg can be NULL in which case a new phi op will
// be added to the block in case the lookup in preds returns
// more than 1 result. If it is not NULL, then the phi will
// be updated.
//
// If the block doesn't have predecessors then a SIR_OP_NOP
// will be returned. This is done to handle lookups that
// originate from unreachable blocks.
static SirOp *ssa_scope_lookup_preds (SirFn *fn, SirBlock *block, SirVar var, Type *type, SirOp *phi) {
    if (block->preds.count == 0) return sir_op_emit(fn, block, SIR_OP_NOP, type);

    block->flags |= SIR_BLOCK_IS_VISITED;
    block->phi_scratch_buf.count = 0;
    block->phi_inserted_recursively = 0;

    array_iter (pred, &block->preds) {
        Auto result = ssa_scope_lookup(fn, pred, var, type);
        array_push(&block->phi_scratch_buf, result);
    }

    assert_dbg(block->phi_scratch_buf.count);
    block->flags &= ~SIR_BLOCK_IS_VISITED;

    if (! phi) phi = block->phi_inserted_recursively;

    Auto replacement = replace_if_trivial_phi(fn, phi, &block->phi_scratch_buf);
    if (replacement) return replacement;

    if (! phi) phi = emit_phi(fn, block, var, type);
    array_iter (arg, &block->phi_scratch_buf) sir_op_add_arg(phi, arg);
    return phi;
}

static SirOp *ssa_scope_lookup (SirFn *fn, SirBlock *block, SirVar var, Type *type) {
    Auto found = ssa_scope_lookup_flat(&block->scope, var);

    if (found) {
        return found;
    } else if (block->flags & SIR_BLOCK_IS_VISITED) {
        Auto phi = emit_phi(fn, block, var, type);
        ssa_scope_add(&block->scope, var, phi);
        block->phi_inserted_recursively = phi;
        return phi;
    } else if (! (block->flags & SIR_BLOCK_ALL_PREDS_KNOWN)) {
        Auto phi = emit_phi(fn, block, var, type);
        ssa_scope_add(&block->scope, var, phi);
        return phi;
    } else if (block->preds.count == 1) {
        Auto b = array_get(&block->preds, 0);
        return ssa_scope_lookup(fn, b, var, type);
    } else {
        found = ssa_scope_lookup_preds(fn, block, var, type, 0);
        ssa_scope_add(&block->scope, var, found);
        return found;
    }
}

// This function is the main tool used for the repair of the
// SSA property. All it does is perform an ssa_scope_lookup()
// for the variable the phi was bound in the predecessors of
// the phi's block. The returned registers will be the new
// argument list for the phi.
//
// The phi could also be deleted in case it turns out to be
// trivial in which case this function will return true.
//
// Any other damages to SSA are to be fixed ad-hoc style.
Bool sir_update_phi (SirFn *fn, SirOp *phi) {
    assert_dbg(phi->tag == SIR_OP_PHI || phi->tag == SIR_OP_PHI_MEM);
    sir_op_remove_args(phi);
    Auto var = sir_op_get_value(fn, phi).u32;
    Auto op = ssa_scope_lookup_preds(fn, phi->block, var, phi->type, phi);
    return op != phi;
}

// The call to sir_update_phi() can delete phis making it
// awkward to loop over an array of phis while calling this
// function on the elements. Here is a convenience function.
Void sir_update_phis (SirFn *fn, SirBlock *block) {
    Bool looping = true;
    while (looping) {
        looping = false;

        array_iter (phi, &block->phis) {
            if (sir_update_phi(fn, phi)) {
                looping = true;
                break;
            }
        }
    }
}

SirOp *sir_op_alloc (SirFn *fn, SirOpTag tag, Type *type) {
    Auto op    = mem_new(fn->mem, SirOp);
    op->id     = fn->next_op_id++;
    op->tag    = tag;
    op->type   = type;
    op->flags |= sir_op_get_default_flags[tag];
    array_init(&op->users, fn->mem);
    array_init(&op->args, fn->mem);
    return op;
}

static SirOp *emit_phi (SirFn *fn, SirBlock *block, SirVar var, Type *type) {
    SirOp *op;

    if (var == SIR_VAR_MEMORY) {
        op = sir_op_alloc(fn, SIR_OP_PHI_MEM, type);
        block->mem_phi = op;
    } else {
        op = sir_op_alloc(fn, SIR_OP_PHI, type);
        array_push(&block->phis, op);
    }

    op->block = block;
    sir_op_set_value(fn, op, (Value){ .u32 = var });

    return op;
}

SirOp *sir_op_emit (SirFn *fn, SirBlock *block, SirOpTag tag, Type *type) {
    Auto op = sir_op_alloc(fn, tag, type);
    sir_op_add_to_block(block, op);
    return op;
}

static SirOp *emit_op1 (SirFn *fn, SirBlock *block, SirOpTag tag, Type *type, SirOp *arg) {
    Auto op = sir_op_emit(fn, block, tag, type);
    sir_op_add_arg(op, arg);
    return op;
}

static SirOp *emit_op2 (SirFn *fn, SirBlock *block, SirOpTag tag, Type *type, SirOp *arg1, SirOp *arg2) {
    Auto op = sir_op_emit(fn, block, tag, type);
    sir_op_add_arg(op, arg1);
    sir_op_add_arg(op, arg2);
    return op;
}

static SirOp *emit_op3 (SirFn *fn, SirBlock *block, SirOpTag tag, Type *type, SirOp *arg1, SirOp *arg2, SirOp *arg3) {
    Auto op = sir_op_emit(fn, block, tag, type);
    sir_op_add_arg(op, arg1);
    sir_op_add_arg(op, arg2);
    sir_op_add_arg(op, arg3);
    return op;
}

static SirOp *emit_return (SirFn *fn, SirBlock *block) {
    return sir_op_emit(fn, block, SIR_OP_RETURN, 0);
}

static SirOp *emit_branch (SirFn *fn, SirBlock *block, Type *type, SirOp *cond) {
    return emit_op1(fn, block, SIR_OP_BRANCH, type, cond);
}

static SirOp *emit_fn_address (SirFn *fn, SirBlock *block, AstFn *ast) {
    Auto t = sem_get_type(fn->sem, cast(Ast*, ast));
    Auto op = sir_op_emit(fn, block, SIR_OP_FN_ADDRESS, t);
    sir_op_set_value(fn, op, (Value){ .fn=ast });
    return op;
}

static SirOp *emit_address_of_value (SirFn *fn, SirBlock *block, Type *type, SirOp *op) {
    Auto ptr = sem_alloc_type_pointer(fn->sem, fn->mem, type);
    return emit_op1(fn, block, SIR_OP_VALUE_ADDRESS, ptr, op);
}

static SirOp *emit_string_literal (SirFn *fn, SirBlock *block, Type *type, IString *str) {
    assert_dbg(type->tag == TYPE_POINTER);
    Auto op = sir_op_emit(fn, block, SIR_OP_STRING_LITERAL, type);
    sir_op_set_value(fn, op, (Value){ .str=str });
    return op;
}

static SirOp *emit_global_object (SirFn *fn, SirBlock *block, Ast *global) {
    Auto t = sem_get_type(fn->sem, global);
    Auto ptr = sem_alloc_type_pointer(fn->sem, fn->mem, t);
    Auto op = sir_op_emit(fn, block, SIR_OP_GLOBAL_OBJECT, ptr);
    sir_op_set_value(fn, op, (Value){ .ast=global });
    return op;
}

static SirOp *emit_stack_object (SirFn *fn, SirBlock *block, Type *type) {
    Auto ptr = sem_alloc_type_pointer(fn->sem, fn->mem, type);
    return sir_op_emit(fn, block, SIR_OP_STACK_OBJECT, ptr);
}

static SirOp *emit_move (SirFn *fn, SirBlock *block, SirOp *to, SirOp *from) {
    return emit_op2(fn, block, SIR_OP_MOVE, to->type, to, from);
}

static SirOp *emit_copy (SirFn *fn, SirBlock *block, Type *type, SirOp *from) {
    return emit_op1(fn, block, SIR_OP_COPY, type, from);
}

static SirOp *emit_load (SirFn *fn, SirBlock *block, Type *type, SirOp *from) {
    assert_dbg(from->type->tag == TYPE_POINTER);
    Auto mem = ssa_scope_lookup(fn, block, SIR_VAR_MEMORY, 0);
    Auto op = emit_op2(fn, block, SIR_OP_LOAD, type, mem, from);
    op->flags |= SIR_OP_TOUCHES_MEMORY;
    return op;
}

static SirOp *emit_store (SirFn *fn, SirBlock *block, Type *type, SirOp *to, SirOp *from, U32 offset) {
    Auto mem = ssa_scope_lookup(fn, block, SIR_VAR_MEMORY, 0);
    Auto op = emit_op3(fn, block, SIR_OP_STORE, type, mem, to, from);
    if (offset) sir_op_set_value(fn, op, (Value){ .u32=offset });
    ssa_scope_add(&block->scope, SIR_VAR_MEMORY, op);
    op->flags |= (SIR_OP_TOUCHES_MEMORY | SIR_OP_MODIFIES_MEMORY);
    return op;
}

static SirOp *emit_memcpy (SirFn *fn, SirBlock *block, Type *type, SirOp *to, SirOp *from) {
    Auto mem = ssa_scope_lookup(fn, block, SIR_VAR_MEMORY, 0);
    Auto op = emit_op3(fn, block, SIR_OP_MEMCPY, type, mem, to, from);
    ssa_scope_add(&block->scope, SIR_VAR_MEMORY, op);
    op->flags |= (SIR_OP_TOUCHES_MEMORY | SIR_OP_MODIFIES_MEMORY);
    return op;
}

static SirOp *emit_offset (SirFn *fn, SirBlock *block, Type *type, SirOp *base, U32 offset) {
    Auto ptr = sem_alloc_type_pointer(fn->sem, fn->mem, type);
    Auto op = emit_op1(fn, block, SIR_OP_OFFSET, ptr, base);
    sir_op_set_value(fn, op, (Value){ .u32=offset });
    return op;
}

static SirOp *emit_index (SirFn *fn, SirBlock *block, Type *type, SirOp *base, SirOp *idx) {
    Auto ptr = sem_alloc_type_pointer(fn->sem, fn->mem, type);
    return emit_op2(fn, block, SIR_OP_INDEX, ptr, base, idx);
}

static SirOp *emit_fn_arg (SirFn *fn, SirBlock *block, Type *type, U32 arg_idx, Bool is_in_mem) {
    Auto op = sir_op_emit(fn, block, SIR_OP_FN_ARG, type);
    if (is_in_mem) op->type = sem_alloc_type_pointer(fn->sem, fn->mem, type);
    sir_op_set_value(fn, op, (Value){ .u32=arg_idx });
    return op;
}

static SirOp *emit_const_primitive (SirFn *fn, SirBlock *block, Type *type, Value val) {
    assert_dbg(abi_can_be_in_reg(fn->abi->abi, type));
    Auto op = sir_op_emit(fn, block, SIR_OP_CONST, type);
    sir_op_set_value(fn, op, val);
    return op;
}

static SirVar new_var (Builder *builder, AstId ast) {
    SirVar var = builder->next_var++;
    if (ast) array_push_lit(&builder->var_scope, .var=var, .ast=ast);
    return var;
}

static SirVar get_var (Builder *builder, AstId ast) {
    array_iter_back (x, &builder->var_scope, *) if (x->ast == ast) return x->var;
    badpath;
}

static SirOp *emit_const (Builder *builder, Ast *node) {
    Auto t = sem_get_type(builder->sem, node);
    Auto v = sem_get_const(builder->sem, node);

    if (t->flags & TYPE_IS_PRIMITIVE) {
        return emit_const_primitive(builder->fn, builder->block, t, v);
    } else if (! (node->flags & AST_CAN_EVAL_WITHOUT_VM)) {
        assert_dbg(! sem_type_has_pointers(builder->sem, t)); // @todo: Turn this into a sem error.
        Auto r = emit_stack_object(builder->fn, builder->block, t);
        r->flags |= SIR_OP_INIT_BY_MEMCPY;
        sir_op_set_value(builder->fn, r, v);
        return r;
    } else if (v.ast->flags & AST_IS_TYPE) {
        Auto r = emit_stack_object(builder->fn, builder->block, t);
        r->flags |= SIR_OP_DEFAULT_INITIALIZED;
        return r;
    } else {
        return emit(builder, v.ast);
    }
}

static SirOp *emit_biop (Builder *builder, AstBaseBinary *node, SirOpTag tag) {
    Auto t   = sem_get_type(builder->sem, cast(Ast*, node));
    Auto op1 = emit(builder, node->op1);
    Auto op2 = emit(builder, node->op2);
    return emit_op2(builder->fn, builder->block, tag, t, op1, op2);
}

static SirOp *emit_unop (Builder *builder, AstBaseUnary *node, SirOpTag tag) {
    Auto t  = sem_get_type(builder->sem, cast(Ast*, node));
    Auto op = emit(builder, node->op);
    return emit_op1(builder->fn, builder->block, tag, t, op);
}

static SirOp *try_emit_load (Builder *builder, SirOp *from) {
    if (from->type->tag != TYPE_POINTER) return from;
    Auto pointee = cast(TypePointer*, from->type)->pointee;
    if (! abi_can_be_in_reg(builder->abi, pointee)) return from;
    return emit_load(builder->fn, builder->block, pointee, from);
}

static SirOp *emit_ident (Builder *builder, SirBlock *block, AstIdent *node) {
    Auto target = node->sem_edge;

    if (target->tag == AST_FN) {
        return emit_fn_address(builder->fn, builder->block, cast(AstFn*, target));
    } else if (target->flags & AST_IS_GLOBAL) {
        return emit_global_object(builder->fn, builder->block, target);
    } else if (value_is_in_register(builder, target)) {
        return ssa_scope_lookup(builder->fn, builder->block, get_var(builder, target->id), sem_get_type(builder->sem, target));
    } else {
        return ssa_scope_lookup_flat(&builder->fn->ssa_scope, get_var(builder, target->id));
    }
}

// This function is used for emitting defers right before
// explicit terminators like return, break, continue, ...
//
// The defers that appear at the end of a scope are emitted
// by the emit_sequence() function.
static Void emit_defers (Builder *builder, Ast *outermost_scope_owner) {
    Auto until = array_find(&builder->defers, IT.scope_owner == outermost_scope_owner);
    assert_dbg(until != ARRAY_NIL_IDX);

    array_iter_back (d, &builder->defers, *) {
        if (ARRAY_IDX == until) break;
        if (d->code) emit(builder, d->code);
    }
}

static Void emit_sequence (Builder *builder, Ast *scope_owner, ArrayAst *statements) {
    assert_dbg(scope_owner->flags & AST_CREATES_SCOPE);
    array_push_lit(&builder->defers, .code=0, .scope_owner=scope_owner); // Push sentinel.

    array_iter (s, statements) {
        emit(builder, s);

        if (s->tag == AST_BREAK || s->tag == AST_CONTINUE || s->tag == AST_RETURN) {
            if (ARRAY_ITER_DONE) {
                set_current_block(builder, builder->dummy_block);
            } else {
                Auto block = sir_alloc_block(builder->fn, builder->mem, SIR_BLOCK_UNREACHABLE);
                connect_blocks(builder->block, block);
                set_current_block(builder, block);
                seal_block(builder->fn, block);
            }
        } else if (ARRAY_ITER_DONE) {
            array_iter_back (d, &builder->defers, *) {
                if (d->code && (d->scope_owner == scope_owner)) emit(builder, d->code);
            }
        }
    }

    array_find_remove_all(&builder->defers, IT.scope_owner == scope_owner);
}

static Void emit_var_def (Builder *builder, Ast *node, SirOp *init, Type *type) {
    Auto var = new_var(builder, node->id);

    if (init) {
        Auto init_can_be_in_reg = abi_can_be_in_reg(builder->abi, type);

        if (value_is_in_register(builder, node)) {
            assert_dbg(init_can_be_in_reg);
            ssa_scope_add(&builder->block->scope, var, init);
        } else if (init_can_be_in_reg) {
            Auto obj = emit_stack_object(builder->fn, builder->block, type);
            emit_store(builder->fn, builder->block, type, obj, init, 0);
            ssa_scope_add(&builder->fn->ssa_scope, var, obj);
        } else if (array_find_ref(&builder->fn->ssa_scope, IT->val == init)) {
            Auto obj = emit_stack_object(builder->fn, builder->block, type);
            emit_memcpy(builder->fn, builder->block, type, obj, init);
            ssa_scope_add(&builder->fn->ssa_scope, var, obj);
        } else {
            ssa_scope_add(&builder->fn->ssa_scope, var, init);
        }
    } else if (value_is_in_register(builder, node)) {
        Auto init = emit_const_primitive(builder->fn, builder->block, type, (Value){});
        init->flags |= SIR_OP_DEFAULT_INITIALIZED;
        ssa_scope_add(&builder->block->scope, var, init);
    } else {
        Auto init = emit_stack_object(builder->fn, builder->block, type);
        init->flags |= SIR_OP_DEFAULT_INITIALIZED;
        ssa_scope_add(&builder->fn->ssa_scope, var, init);
    }
}

static SirOp *emit_inline_call (Builder *builder, AstFn *fn, ArrayAst *args) {
    Auto fn_output      = cast(AstBaseFn*, fn)->output;
    Auto exit_block     = sir_alloc_block(builder->fn, builder->mem, SIR_BLOCK_NORMAL);
    Auto arg_instances  = sem_get_arg_instances(builder->sem, cast(Ast*, fn));
    Auto prev_var_count = builder->var_scope.count;

    array_iter (arg, args) {
        if (arg->flags & AST_IS_TYPE) continue;
        Auto def  = array_get(&arg_instances, ARRAY_IDX);
        Auto init = (!(def->flags & AST_IS_TYPE) && (def->flags & AST_EVALED)) ? emit_const(builder, arg) : emit(builder, arg);
        Auto type = sem_get_type(builder->sem, def);
        emit_var_def(builder, def, init, type);
    }

    #define EMIT_BODY(VAR) ({\
        array_push_lit(&builder->pseudo_return_targets, .var=VAR, .block=exit_block);\
        emit_sequence(builder, cast(Ast*, fn), &fn->statements);\
        connect_blocks(builder->block, exit_block);\
        set_current_block(builder, exit_block);\
        seal_block(builder->fn, exit_block);\
        builder->pseudo_return_targets.count--;\
        builder->var_scope.count = prev_var_count;\
    })

    if (! fn_output) { EMIT_BODY(0); return 0; }

    Auto result_var    = new_var(builder, fn_output->id);
    Auto result_type   = sem_get_type(builder->sem, fn_output);
    Auto result_in_reg = abi_can_be_in_reg(builder->abi, result_type);

    if (result_in_reg) {
        Auto op = emit_const_primitive(builder->fn, builder->block, result_type, (Value){});
        ssa_scope_add(&builder->block->scope, result_var, op);
    } else {
        Auto op = emit_stack_object(builder->fn, builder->block, result_type);
        ssa_scope_add(&builder->fn->ssa_scope, result_var, op);
    }

    EMIT_BODY(result_var);
    #undef EMIT_BODY

    return result_in_reg ?
           ssa_scope_lookup(builder->fn, builder->block, result_var, result_type) :
           ssa_scope_lookup_flat(&builder->fn->ssa_scope, result_var);
}

static Void emit_into_compound (Builder *builder, Ast *node, SirOp *base, U32 offset) {
    Auto sem       = builder->sem;
    Auto abi       = builder->abi;
    Auto node_type = sem_get_type(sem, node);

    switch (node->tag) {
    case AST_TUPLE: {
        Auto n = cast(AstTuple*, node);
        abi_of_obj(abi, node_type); // Ensure field offsets computed.
        array_iter (init, &n->fields) {
            Auto field_offset = offset + abi_offset(abi, init);
            Auto field_value  = (init->tag == AST_TUPLE_FIELD) ? cast(AstTupleField*, init)->rhs : init;
            emit_into_compound(builder, field_value, base, field_offset);
        }
    } break;

    case AST_STRUCT_LITERAL: {
        Auto n = cast(AstStructLiteral*, node);
        abi_of_obj(abi, node_type); // Ensure field offsets computed.
        array_iter (init, &n->inits) {
            Auto field_def    = init->sem_edge;
            Auto field_offset = offset + abi_offset(abi, field_def);
            emit_into_compound(builder, init->val, base, field_offset);
        }
    } break;

    case AST_ARRAY_LITERAL: {
        Auto n     = cast(AstArrayLiteral*, node);
        Auto etype = cast(TypeArray*, node_type)->element;
        Auto esize = abi_of_obj(abi, etype).size;

        array_iter (init, &n->inits) {
            Auto field_offset = esize * ARRAY_IDX + offset;
            emit_into_compound(builder, init, base, field_offset);
        }
    } break;

    case AST_CAST: {
        Auto n     = cast(AstCast*, node);
        Auto from  = sem_get_type(sem, n->expr);
        Auto types = sem_get_core_types(sem);

        switch (n->tag) {
        case AST_CAST_ANY: {
            Auto op = emit(builder, n->expr);
            Auto objt = (abi_of_obj(abi, from).size <= abi->any_value_size) ? from : types->type_U64;
            emit_store(builder->fn, builder->block, objt, base, op, offset + abi->any_value_offset);
            Auto id = emit_const_primitive(builder->fn, builder->block, types->type_type_id, (Value){ .u32 = from->id });
            emit_store(builder->fn, builder->block, types->type_type_id, base, id, offset + abi->any_id_offset);
        } break;

        case AST_CAST_SLICE: {
            Auto op = emit(builder, n->expr);
            emit_store(builder->fn, builder->block, op->type, base, op, offset + abi->slice_data_offset);
            U32 count = (n->expr->tag == AST_TUPLE) ? cast(AstTuple*, n->expr)->fields.count : cast(TypeArray*, from)->length;
            Auto count_op = emit_const_primitive(builder->fn, builder->block, types->type_U32, (Value){ .u32 = count });
            emit_store(builder->fn, builder->block, types->type_U32, base, count_op, offset + abi->slice_count_offset);
        } break;

        default: {
            Auto op = emit(builder, node);
            emit_store(builder->fn, builder->block, node_type, base, op, offset);
        } break;
        }
    } break;

    default: {
        Auto op = emit(builder, node);

        if (abi_can_be_in_reg(abi, node_type)) {
            emit_store(builder->fn, builder->block, node_type, base, op, offset);
        } else {
            Auto off = emit_offset(builder->fn, builder->block, node_type, base, offset);
            emit_memcpy(builder->fn, builder->block, node_type, off, op);
        }
    } break;
    }
}

static SirOp *emit_lvalue (Builder *builder, Ast *node) {
    assert_dbg(node->flags & AST_IS_LVALUE);

    switch (node->tag) {
    case AST_IDENT: return emit_ident(builder, builder->block, cast(AstIdent*, node));
    case AST_DEREF: return emit(builder, cast(AstBaseUnary*, node)->op);

    case AST_INDEX: {
        Auto n      = cast(AstIndex*, node);
        Auto base   = emit(builder, n->lhs);
        Auto type   = sem_get_type(sem, node);
        Auto target = n->sem_edge;

        Auto idx_type = sem_get_type(sem, n->idx);
        assert_dbg(idx_type->tag == TYPE_INT);
        assert_dbg(cast(TypeInt*, idx_type)->bitwidth == 64);

        abi_of_obj(builder->abi, sem_get_type(sem, n->lhs)); // Ensure field offsets computed.

        if (target) {
            Auto offset = abi_offset(builder->abi, target);
            return emit_offset(builder->fn, builder->block, type, base, offset);
        } else {
            Auto idx = emit(builder, n->idx);
            return emit_index(builder->fn, builder->block, type, base, idx);
        }
    }

    case AST_DOT: {
        Auto n = cast(AstDot*, node);
        Auto t = sem_get_type(sem, n->lhs);
        Auto target = n->sem_edge;

        abi_of_obj(builder->abi, t); // Ensure field offsets computed.

        if (t->tag == TYPE_STRUCT || t->tag == TYPE_TUPLE) {
            Auto offset = abi_offset(builder->abi, target);
            Auto base   = emit(builder, n->lhs);
            return emit_offset(builder->fn, builder->block, sem_get_type(sem, target), base, offset);
        } else if (t->tag == TYPE_MISC && cast(TypeMisc*, t)->node->tag == AST_IMPORT) {
            return emit_global_object(builder->fn, builder->block, target);
        } else {
            badpath;
        }
    }

    default: badpath;
    }
}

// This function can be applied to statements and expressions.
// If applied to a statement, it will return 0. Otherwise, it
// will return the register containing the expression value.
static SirOp *emit (Builder *builder, Ast *node) {
    Auto sem = builder->sem;
    Auto abi = builder->abi;

    switch (node->tag) {
    case AST_CALL_MACRO_BARG:
    case AST_CALL_NAMED_ARG:
    case AST_CODE_GEN:
    case AST_IMPORT_CONFIG:
    case AST_INTERFACE:
    case AST_PAIR:
    case AST_TAG_COUNT:
        badpath;

    case AST_ARRAY_TYPE:
    case AST_ATTRIBUTE:
    case AST_CALLER_INFO:
    case AST_CT_ASSERT:
    case AST_DUMMY:
    case AST_ENUM:
    case AST_ENUM_FIELD:
    case AST_FILE:
    case AST_FN_LINUX:
    case AST_ARG_POLY_CODE:
    case AST_ARG_POLY_TYPE:
    case AST_ARG_POLY_VALUE:
    case AST_FN_TYPE:
    case AST_IMPORT:
    case AST_SCOPE_MOD:
    case AST_STRUCT:
    case AST_STRUCT_LIT_INIT:
    case AST_STRUCT_POLY:
    case AST_TUPLE_FIELD:
    case AST_TYPEOF:
    case AST_TYPE_ALIAS:
    case AST_TYPE_CONSTRAINT:
    case AST_TYPE_DISTINCT:
        return 0;

    case AST_NIL: {
        Auto t = sem_get_type(sem, node);
        if (abi_can_be_in_reg(abi, t)) return emit_const_primitive(builder->fn, builder->block, t, (Value){});
        Auto r = emit_stack_object(builder->fn, builder->block, t);
        r->flags |= SIR_OP_DEFAULT_INITIALIZED;
        return r;
    }

    case AST_CALL_MACRO_ARG: {
        Auto n = cast(AstCallMacroArg*, node);
        Auto s = intern_str(builder->interns, n->code);
        Auto t = sem_get_type(sem, node);
        return emit_string_literal(builder->fn, builder->block, t, s);
    }

    case AST_CALL_DEFAULT_ARG: {
        Auto n = cast(AstCallDefaultArg*, node);
        return emit_const(builder, n->arg);
    }

    case AST_EVAL: {
        Auto n = cast(AstEval*, node);
        return emit_const(builder, n->child);
    }

    case AST_ENUM_LITERAL: {
        Auto f = cast(AstEnumField*, cast(AstEnumLiteral*, node)->sem_edge);
        Auto v = sem_get_const(sem, f->init ? f->init : cast(Ast*, f));
        Auto t = cast(TypeEnum*, sem_get_type(sem, cast(Ast*, f)));
        return emit_const_primitive(builder->fn, builder->block, t->raw, v);
    }

    case AST_RAW: {
        if (node->flags & AST_IS_TYPE) return 0;
        return emit(builder, cast(AstBaseUnary*, node)->op);
    }

    case AST_IF_CT: {
        Auto n = cast(AstIfCt*, node);
        Auto seq = sem_get_const(sem, n->cond).u8 ? &n->then_arm : &n->else_arm;
        Auto scope_owner = array_ref_last(&builder->defers)->scope_owner;
        emit_sequence(builder, scope_owner, seq);
        return 0;
    }

    case AST_ALIGNOF: {
        Auto n   = cast(AstBaseUnary*, node)->op;
        Auto abi = abi_of_obj(builder->abi, sem_get_type(sem, n));
        return emit_const_primitive(builder->fn, builder->block, sem_get_type(sem, node), (Value){ .u8=abi.align });
    }

    case AST_SIZEOF: {
        Auto n   = cast(AstBaseUnary*, node)->op;
        Auto abi = abi_of_obj(builder->abi, sem_get_type(sem, n));
        return emit_const_primitive(builder->fn, builder->block, sem_get_type(sem, node), (Value){ .u64=abi.size });
    }

    case AST_EMBED: {
        Auto n = cast(AstEmbed*, node);
        Auto g = cast(AstCodeGen*, n->sem_edge);

        if (n->level == AST_LEVEL_EXPR) {
            assert_dbg(g->children.count == 1);
            return emit(builder, array_get(&g->children, 0));
        } else {
            emit_sequence(builder, cast(Ast*, g), &g->children);
            return 0;
        }
    }

    case AST_TYPE_ID: {
        Auto n = cast(AstBaseUnary*, node)->op;
        Auto t = sem_get_type(sem, n);
        return emit_const_primitive(builder->fn, builder->block, sem_get_type(sem, node), (Value){ .u32 = t->id });
    }

    case AST_VAR_DEF: {
        assert_dbg(! (node->flags & AST_IS_GLOBAL));
        Auto n = cast(AstVarDef*, node);
        Auto i = n->init ? emit(builder, n->init) : 0;
        Auto t = sem_get_type(sem, node);
        emit_var_def(builder, node, i, t);
        return 0;
    }

    case AST_IF: {
        Auto n = cast(AstIf*, node);

        Auto cond = emit(builder, n->cond);

        Auto then_block = sir_alloc_block(builder->fn, builder->mem, SIR_BLOCK_THEN);
        Auto join_block = sir_alloc_block(builder->fn, builder->mem, SIR_BLOCK_JOIN);
        Auto else_block = !n->else_arm ? join_block : sir_alloc_block(builder->fn, builder->mem, SIR_BLOCK_ELSE);

        then_block->idom = builder->block;
        else_block->idom = builder->block;
        connect_blocks(builder->block, then_block);
        connect_blocks(builder->block, else_block);

        emit_branch(builder->fn, builder->block, sem_get_type(sem, n->cond), cond);

        seal_block(builder->fn, then_block);
        set_current_block(builder, then_block);
        emit(builder, n->then_arm);

        if (n->else_arm) {
            connect_blocks(builder->block, join_block);
            seal_block(builder->fn, else_block);
            set_current_block(builder, else_block);
            emit(builder, n->else_arm);
        }

        connect_blocks(builder->block, join_block);
        seal_block(builder->fn, join_block);
        set_current_block(builder, join_block);

        return 0;
    }

    case AST_WHILE: {
        Auto n = cast(AstWhile*, node);

        Auto start_block    = sir_alloc_block(builder->fn, builder->mem, SIR_BLOCK_LOOP_START);
        Auto break_block    = sir_alloc_block(builder->fn, builder->mem, SIR_BLOCK_LOOP_BREAK);
        Auto continue_block = sir_alloc_block(builder->fn, builder->mem, SIR_BLOCK_LOOP_CONTINUE);

        LoopBlocks info = { node, .break_block=break_block, .continue_block=continue_block };
        array_push(&builder->loop_blocks, &info);

        continue_block->idom = builder->block;
        connect_blocks(builder->block, continue_block);
        set_current_block(builder, continue_block);

        if ((n->cond->tag != AST_BOOL_LITERAL) || !cast(AstBoolLiteral*, n->cond)->val) {
            Auto cond = emit(builder, n->cond);
            emit_branch(builder->fn, builder->block, sem_get_type(sem, n->cond), cond);
            connect_blocks(builder->block, break_block);
        }

        connect_blocks(builder->block, start_block);

        start_block->idom = builder->block;
        break_block->idom = builder->block;

        seal_block(builder->fn, start_block);
        set_current_block(builder, start_block);
        emit_sequence(builder, node, &n->statements);

        connect_blocks(builder->block, continue_block);
        seal_block(builder->fn, continue_block);

        seal_block(builder->fn, break_block);
        set_current_block(builder, break_block);

        builder->loop_blocks.count--;
        return 0;
    }

    case AST_BREAK: {
        Ast *target = cast(AstBreak*, node)->sem_edge;
        Auto block = array_find_get(&builder->loop_blocks, IT->node == target)->break_block;
        emit_defers(builder, target);
        connect_blocks(builder->block, block);
        return 0;
    }

    case AST_CONTINUE: {
        Ast *target = cast(AstContinue*, node)->sem_edge;
        Auto block = array_find_get(&builder->loop_blocks, IT->node == target)->continue_block;
        emit_defers(builder, target);
        connect_blocks(builder->block, block);
        return 0;
    }

    case AST_RETURN: {
        Auto n = cast(AstReturn*, node);
        Auto target_ast = n->sem_edge;
        Auto pseudo_target = array_try_ref_last(&builder->pseudo_return_targets);
        Bool is_pseudo_return = (target_ast->flags & AST_IS_MACRO);

        if (n->result) {
            Auto result = emit(builder, cast(AstReturn*, node)->result);

            if (is_pseudo_return) {
                emit_defers(builder, target_ast);
                Auto scope = value_is_in_register(builder, n->result) ? &builder->block->scope : &builder->fn->ssa_scope;
                ssa_scope_add(scope, pseudo_target->var, result);
            } else {
                emit_defers(builder, cast(Ast*, builder->fn->ast));
                Auto ret = emit_return(builder->fn, builder->block);
                sir_op_add_arg(ret, result);
                if (builder->return_address_fn_arg) sir_op_add_arg(ret, builder->return_address_fn_arg);
            }
        } else if (is_pseudo_return) {
            emit_defers(builder, target_ast);
        } else {
            emit_defers(builder, cast(Ast*, builder->fn->ast));
            emit_return(builder->fn, builder->block);
        }

        connect_blocks(builder->block, (is_pseudo_return ? pseudo_target->block : builder->fn->exit_block));
        return 0;
    }

    case AST_DEFER: {
        Auto n = cast(AstDefer*, node);
        Auto t = n->sem_edge;

        array_iter_back (d, &builder->defers, *) {
            if (d->scope_owner == t) {
                array_insert_lit(&builder->defers, ARRAY_IDX + 1, .code=n->stmt, .scope_owner=t);
                return 0;
            }
        }

        badpath;
    }

    case AST_BLOCK: {
        Auto n = cast(AstBlock*, node);
        emit_sequence(builder, node, &n->statements);
        return 0;
    }

    case AST_ASSIGN: {
        Auto n = cast(AstBaseBinary*, node);
        SirOp *rhs = 0;

        if (cast(AstAssign*, n)->fused_op == AST_ASSIGN) {
            rhs = emit(builder, n->op2);
        } else {
            node->tag = cast(AstAssign*, n)->fused_op;
            rhs = emit(builder, node);
            node->tag = AST_ASSIGN;
        }

        if ((n->op1->tag == AST_IDENT) && value_is_in_register(builder, n->op1)) {
            Ast *target = cast(AstIdent*, n->op1)->sem_edge;
            Auto var = get_var(builder, target->id);
            ssa_scope_add(&builder->block->scope, var, rhs);
        } else {
            Auto lhs      = emit_lvalue(builder, n->op1);
            Auto lhs_type = sem_get_type(sem, n->op1);
            Auto rhs_type = sem_get_type(sem, n->op2);

            if (abi_can_be_in_reg(builder->abi, rhs_type)) {
                emit_store(builder->fn, builder->block, lhs_type, lhs, rhs, 0);
            } else {
                emit_memcpy(builder->fn, builder->block, lhs_type, lhs, rhs);
            }
        }

        return 0;
    }

    case AST_IDENT: {
        Auto n = cast(AstIdent*, node);
        Auto result = emit_ident(builder, builder->block, n);

        if (result->type->tag == TYPE_POINTER) {
            // In the following code both x and y are bound to the same
            // SIR_OP_STACK_OBJECT since we treat "address of" as a nop:
            //
            //     var x = 42;
            //     var y = ~x;
            //
            // If emit() is applied to an x reference, it should emit a
            // load. If applied to a y reference, it should not.
            //
            // We can distinguish between these two cases since we know that:
            //
            //     1. The SIR_OP_STACK_OBJECT has SirOp.type == TYPE_POINTER.
            //     2. The x AST node has the same type as SirOp.type.pointee.
            //     3. The y AST node has type pointer to SirOp.type.pointee.
            //
            Auto pointee_type = cast(TypePointer*, result->type)->pointee;
            Auto node_type = sem_get_type(sem, node);
            if (pointee_type == node_type && abi_can_be_in_reg(builder->abi, pointee_type)) {
                return emit_load(builder->fn, builder->block, pointee_type, result);
            }
        }

        return result;
    }

    case AST_ADDRESS_OF: {
        Auto op = cast(AstBaseUnary*, node)->op;

        if (op->flags & AST_IS_LVALUE) {
            return emit_lvalue(builder, op);
        } else {
            // We took the address of a value like: ~42.
            Auto result  = emit(builder, op);
            Auto op_type = sem_get_type(sem, op);

            if (abi_can_be_in_reg(builder->abi, op_type)) {
                // Turn the value into a stack object.
                Auto t = sem_get_type(sem, node);
                result = emit_address_of_value(builder->fn, builder->block, t, result);
            }

            return result;
        }
    }

    case AST_DEREF: {
        Auto op = emit(builder, cast(AstBaseUnary*, node)->op);
        return try_emit_load(builder, op);
    }

    case AST_LOGICAL_OR:
    case AST_LOGICAL_AND: {
        Auto n = cast(AstBaseBinary*, node);
        Auto t = sem_get_type(sem, node);

        Auto lhs = emit(builder, n->op1);
        Auto var = new_var(builder, 0);
        ssa_scope_add(&builder->block->scope, var, lhs);

        Auto else_block = sir_alloc_block(builder->fn, builder->mem, SIR_BLOCK_ELSE);
        Auto join_block = sir_alloc_block(builder->fn, builder->mem, SIR_BLOCK_JOIN);

        else_block->idom = builder->block;
        join_block->idom = builder->block;

        if (node->tag == AST_LOGICAL_OR) {
            emit_branch(builder->fn, builder->block, t, lhs);
            connect_blocks(builder->block, else_block);
            connect_blocks(builder->block, join_block);
        } else {
            emit_branch(builder->fn, builder->block, t, lhs);
            connect_blocks(builder->block, join_block);
            connect_blocks(builder->block, else_block);
        }

        seal_block(builder->fn, else_block);
        set_current_block(builder, else_block);

        Auto rhs = emit(builder, n->op2);
        ssa_scope_add(&builder->block->scope, var, rhs);
        connect_blocks(builder->block, join_block);

        seal_block(builder->fn, join_block);
        set_current_block(builder, join_block);

        Auto result = ssa_scope_lookup(builder->fn, builder->block, var, t);
        assert_dbg(result->tag == SIR_OP_PHI);
        return result;
    }

    case AST_CALL_MACRO: {
        Auto n  = cast(AstCallMacro*, node);
        Auto fn = n->sem_edge;
        return emit_inline_call(builder, cast(AstFn*, fn), &n->args);
    }

    case AST_CALL: {
        Auto n = cast(AstCall*, node);
        Auto t = sem_get_type(sem, node);
        Auto is_stack_obj = (t->tag != TYPE_VOID) && !abi_can_be_in_reg(builder->abi, t);

        Auto target = n->sem_edge;
        if (!target && (n->lhs->tag == AST_DOT)) target = cast(AstDot*, n->lhs)->sem_edge;

        Auto result_type = is_stack_obj ? sem_alloc_type_pointer(sem, builder->mem, t) : t;
        Auto result_tag  = (target && target->tag == AST_FN_LINUX) ? SIR_OP_LINUX_SYSCALL : SIR_OP_CALL;
        Auto result      = sir_op_alloc(builder->fn, result_tag, result_type);

        if (t->tag != TYPE_VOID) result->flags |= SIR_OP_SELF_IS_REG;
        if (is_stack_obj)        result->flags |= SIR_OP_IS_STACK_OBJECT;
        result->flags |= (SIR_OP_TOUCHES_MEMORY | SIR_OP_MODIFIES_MEMORY); // We assume this for all calls.

        // We must reserve space for the memory token argument which
        // we will set after we generated the code for the arguments
        // since the arguments themselves could produce that token.
        array_push(&result->args, 0);

        SliceAst def_args;

        if (target) {
            def_args = sem_get_arg_instances(sem, target);
        } else {
            Auto fn  = cast(TypeFn*, sem_get_type(sem, n->lhs))->node;
            def_args = slice_from(&fn->inputs, SliceAst);
        }

        array_iter (def, &def_args) {
            if (def->flags & AST_EVALED) continue;
            Auto arg = array_get(&n->args, ARRAY_IDX);
            Auto a = emit(builder, arg);
            sir_op_add_arg(result, a);
        }

        if (target) {
            result->flags |= SIR_OP_IS_DIRECT_CALL;
            sir_op_set_value(builder->fn, result, (Value){ .ast=target });
        } else {
            Auto lhs = emit(builder, n->lhs);
            assert_dbg(lhs);
            sir_op_add_arg(result, lhs);
            sir_op_set_value(builder->fn, result, (Value){ .ast=n->lhs });
        }

        Auto mem_token = ssa_scope_lookup(builder->fn, builder->block, SIR_VAR_MEMORY, 0);
        sir_op_set_arg(result, 0, mem_token);
        ssa_scope_add(&builder->block->scope, SIR_VAR_MEMORY, result);
        sir_op_add_to_block(builder->block, result);

        return result;
    }

    case AST_TUPLE: {
        if (node->flags & AST_IS_TYPE) return 0;
        Auto r = emit_stack_object(builder->fn, builder->block, sem_get_type(sem, node));
        emit_into_compound(builder, node, r, 0);
        return r;
    }

    case AST_STRUCT_LITERAL: {
        Auto r = emit_stack_object(builder->fn, builder->block, sem_get_type(sem, node));
        emit_into_compound(builder, node, r, 0);
        return r;
    }

    case AST_ARRAY_LITERAL: {
        Auto r = emit_stack_object(builder->fn, builder->block, sem_get_type(sem, node));
        emit_into_compound(builder, node, r, 0);
        return r;
    }

    case AST_DOT: {
        Auto n = cast(AstDot*, node);
        Auto t = sem_get_type(sem, n->lhs);
        Auto target = n->sem_edge;

        if (target->tag == AST_ENUM_FIELD) {
            Auto t = cast(TypeEnum*, sem_get_type(sem, node));
            Auto v = sem_get_const(builder->sem, target);
            return emit_const_primitive(builder->fn, builder->block, t->raw, v);
        } else if (t->tag == TYPE_STRUCT || t->tag == TYPE_TUPLE) {
            Auto lvalue = emit_lvalue(builder, node);
            return try_emit_load(builder, lvalue);
        } else if (t->tag == TYPE_MISC && cast(TypeMisc*, t)->node->tag == AST_IMPORT) {
            return emit_global_object(builder->fn, builder->block, target);
        } else {
            return emit(builder, target);
        }
    }

    case AST_CAST: {
        Auto n    = cast(AstCast*, node);
        Auto to   = sem_get_type(sem, node);
        Auto from = sem_get_type(sem, n->expr);

        switch (n->tag) {
        case AST_CAST_BITWISE: {
            assert_dbg(abi_of_obj(abi, to).size == abi_of_obj(abi, from).size);
            Auto r = emit(builder, n->expr);
            return emit_op1(builder->fn, builder->block, SIR_OP_CAST, to, r);
        }

        case AST_CAST_PRIMITIVE: {
            Auto r = emit(builder, n->expr);
            return emit_op1(builder->fn, builder->block, SIR_OP_CAST, to, r);
        }

        default: {
            Auto r = emit_stack_object(builder->fn, builder->block, to);
            emit_into_compound(builder, node, r, 0);
            return r;
        }
        }
    }

    case AST_INDEX: {
        assert_dbg(! (node->flags & AST_IS_TYPE));
        Auto lvalue = emit_lvalue(builder, node);
        return try_emit_load(builder, lvalue);
    }

    case AST_FN_POLY: {
        Ast *fn = cast(AstFnPoly*, node)->sem_edge;
        return fn ? emit(builder, fn) : 0;
    }

    case AST_FN: {
        if (node->flags & (AST_IS_MACRO_INSTANCE | AST_IS_MACRO)) return 0;
        return emit_fn_address(builder->fn, builder->block, cast(AstFn*, node));
    }

    case AST_SELF:           return emit(builder, cast(AstSelf*, node)->sem_edge);
    case AST_F64_LITERAL:    return emit_const_primitive(builder->fn, builder->block, sem_get_type(sem, node), (Value){ .f64 = cast(AstF64Literal*, node)->val });
    case AST_I64_LITERAL:    return emit_const_primitive(builder->fn, builder->block, sem_get_type(sem, node), (Value){ .i64 = cast(AstI64Literal*, node)->val });
    case AST_U64_LITERAL:    return emit_const_primitive(builder->fn, builder->block, sem_get_type(sem, node), (Value){ .u64 = cast(AstU64Literal*, node)->val });
    case AST_BOOL_LITERAL:   return emit_const_primitive(builder->fn, builder->block, sem_get_type(sem, node), (Value){ .u8  = cast(AstBoolLiteral*, node)->val });
    case AST_STRING_LITERAL: return emit_string_literal(builder->fn, builder->block, sem_get_type(sem, node), cast(AstStringLiteral*, node)->str);
    case AST_NOT:            return emit_unop(builder, cast(AstBaseUnary*, node), SIR_OP_NOT);
    case AST_NEGATE:         return emit_unop(builder, cast(AstBaseUnary*, node), SIR_OP_NEGATE);
    case AST_BITWISE_NOT:    return emit_unop(builder, cast(AstBaseUnary*, node), SIR_OP_BITWISE_NOT);
    case AST_ADD:            return emit_biop(builder, cast(AstBaseBinary*, node), SIR_OP_ADD);
    case AST_SUB:            return emit_biop(builder, cast(AstBaseBinary*, node), SIR_OP_SUB);
    case AST_MUL:            return emit_biop(builder, cast(AstBaseBinary*, node), SIR_OP_MUL);
    case AST_DIV:            return emit_biop(builder, cast(AstBaseBinary*, node), SIR_OP_DIV);
    case AST_MOD:            return emit_biop(builder, cast(AstBaseBinary*, node), SIR_OP_MOD);
    case AST_BITWISE_OR:     return emit_biop(builder, cast(AstBaseBinary*, node), SIR_OP_BITWISE_OR);
    case AST_BITWISE_XOR:    return emit_biop(builder, cast(AstBaseBinary*, node), SIR_OP_BITWISE_XOR);
    case AST_BITWISE_AND:    return emit_biop(builder, cast(AstBaseBinary*, node), SIR_OP_BITWISE_AND);
    case AST_SHIFT_LEFT:     return emit_biop(builder, cast(AstBaseBinary*, node), SIR_OP_SHIFT_LEFT);
    case AST_SHIFT_RIGHT:    return emit_biop(builder, cast(AstBaseBinary*, node), SIR_OP_SHIFT_RIGHT);
    case AST_EQUAL:          return emit_biop(builder, cast(AstBaseBinary*, node), SIR_OP_EQUAL);
    case AST_NOT_EQUAL:      return emit_biop(builder, cast(AstBaseBinary*, node), SIR_OP_NOT_EQUAL);
    case AST_LESS:           return emit_biop(builder, cast(AstBaseBinary*, node), SIR_OP_LESS);
    case AST_GREATER:        return emit_biop(builder, cast(AstBaseBinary*, node), SIR_OP_GREATER);
    case AST_LESS_EQUAL:     return emit_biop(builder, cast(AstBaseBinary*, node), SIR_OP_LESS_EQUAL);
    case AST_GREATER_EQUAL:  return emit_biop(builder, cast(AstBaseBinary*, node), SIR_OP_GREATER_EQUAL);
    }

    badpath;
}

SirFn *sir_fn_new (Mem *mem, Interns *interns, Sem *sem, AstFn *ast, Abi *abi) {
    Auto fn = mem_new(mem, SirFn);
    fn->in_ssa_form = true;
    fn->mem = mem;
    fn->sem = sem;
    fn->ast = ast;
    fn->interns = interns;
    fn->abi = abi_of_fn(abi, mem, cast(TypeFn*, sem_get_type(sem, cast(Ast*, ast))));
    map_init(&fn->op_data, mem);
    array_init(&fn->blocks, mem);
    array_init(&fn->ssa_scope, mem);

    Auto builder = mem_new(mem, Builder);
    builder->mem = mem;
    builder->fn  = fn;
    builder->abi = abi;
    builder->sem = sem;
    builder->interns = interns;
    builder->next_var = 1; // 0 is SIR_VAR_MEMORY.
    array_init(&builder->defers, mem);
    array_init(&builder->var_scope, mem);
    array_init(&builder->loop_blocks, mem);
    array_init(&builder->pseudo_return_targets, mem);
    builder->dummy_block = sir_alloc_block(fn, mem, SIR_BLOCK_UNREACHABLE);
    builder->dummy_block->flags |= SIR_BLOCK_IS_DEAD;
    fn->blocks.count--; // Remove the dummy block.

    Auto entry_block = sir_alloc_block(fn, mem, SIR_BLOCK_ENTRY);
    Auto exit_block  = sir_alloc_block(fn, mem, SIR_BLOCK_EXIT);
    fn->exit_block   = exit_block;
    fn->entry_block  = entry_block;
    set_current_block(builder, entry_block);
    seal_block(fn, entry_block);

    Auto mem_init = sir_op_emit(fn, entry_block, SIR_OP_MEMORY, NULL);
    ssa_scope_add(&entry_block->scope, SIR_VAR_MEMORY, mem_init);

    // The first argument will contain the address of the caller.
    if (builder->fn->abi->output == ABI_REG_MEM) {
        Auto t = sem_get_core_types(sem)->type_void_ptr;
        builder->return_address_fn_arg = emit_fn_arg(builder->fn, entry_block, t, 0, false);
    }

    array_iter (input, &cast(AstBaseFn*, ast)->inputs) {
        Auto type = sem_get_type(sem, input);
        Auto idx  = ARRAY_IDX + (fn->abi->output == ABI_REG_MEM); // The addition is for the implicit caller address arg.
        Auto reg  = array_get(&fn->abi->inputs, idx);
        Auto arg  = emit_fn_arg(fn, entry_block, type, idx, reg == ABI_REG_MEM);
        Auto var  = new_var(builder, input->id);

        if (reg == ABI_REG_MEM) {
            input->flags |= AST_IS_FN_ARG_PASSED_BY_MEM; // For value_is_in_register().
            ssa_scope_add(&fn->ssa_scope, var, arg);
        } else if (input->flags & AST_ADDRESS_TAKEN) {
            Auto s = emit_stack_object(fn, entry_block, type);
            emit_store(fn, entry_block, type, s, arg, 0);
            ssa_scope_add(&fn->ssa_scope, var, s);
        } else {
            ssa_scope_add(&entry_block->scope, var, arg);
        }
    }

    Auto args = sem_get_arg_instances(sem, cast(Ast*, ast));
    array_iter (arg, &args) {
        if (!(arg->flags & AST_IS_TYPE) && (arg->flags & AST_EVALED)) {
            Auto t = sem_get_type(sem, arg);
            Auto c = emit_const(builder, arg);
            emit_var_def(builder, arg, c, t);
        }
    }

    emit_sequence(builder, cast(Ast*, ast), &ast->statements);

    connect_blocks(builder->block, exit_block);
    seal_block(fn, exit_block);

    array_iter (b, &fn->blocks) {
        if (b->tag == SIR_BLOCK_UNREACHABLE) {
            assert_dbg(b->preds.count == 1);
            Auto pred = array_get(&b->preds, 0);
            array_find_remove(&pred->succs, IT == b);
        }
    }

    sir_remove_unreachable_blocks(fn);

    if (!(exit_block->flags & SIR_BLOCK_IS_DEAD) && cast(AstBaseFn*, ast)->output) {
        array_iter (pred, &exit_block->preds) {
            Auto last_op = array_try_get_last(&pred->ops);
            if (!last_op || last_op->tag != SIR_OP_RETURN) {
                log_msg(msg, LOG_ERROR, "Sir", 1);
                astr_push_cstr(msg, "Not all control paths return value.\n\n");
                sem_print_node(sem, msg, cast(Ast*, ast)); // @todo Better error message.
                log_scope_end_all();
                panic();
            }
        }
    }

    sir_check_integrity(fn);
    return fn;
}

static U32 assign_reverse_postorder_nums (SirFn *fn, SirBlock *block, U32 pos) {
    if (block->flags & SIR_BLOCK_IS_VISITED) return pos;
    block->flags |= SIR_BLOCK_IS_VISITED;
    array_iter_back (succ, &block->succs) pos = assign_reverse_postorder_nums(fn, succ, pos);
    block->scratch = pos;
    return pos + 1;
}

static U64 _sir_reverse_postorder (SirFn *fn, SirBlock *block, U64 pos) {
    if (block->flags & SIR_BLOCK_IS_VISITED) return pos;
    block->flags |= SIR_BLOCK_IS_VISITED;
    array_iter_back (succ, &block->succs) pos = _sir_reverse_postorder(fn, succ, pos);
    array_set(&fn->blocks, pos, block);
    return pos - 1;
}

// This function will sort the SirFn.blocks array into so called
// "reverse postorder". The main feature of this order is that
// each time you loop over this array you will have visited all
// ancestors of a node before visiting the node. This is only
// true in case the CFG is a acyclic.
Void sir_reverse_postorder (SirFn *fn) {
    _sir_reverse_postorder(fn, fn->entry_block, fn->blocks.count - 1);
    array_iter (b, &fn->blocks) b->flags &= ~SIR_BLOCK_IS_VISITED;
    assert_dbg(array_get(&fn->blocks, 0)->tag == SIR_BLOCK_ENTRY);
}

// This function turns the edge A -> B into A -> N -> B.
SirBlock *sir_edge_split (SirFn *fn, SirBlock *from, SirBlock *to, SirBlockTag tag_of_new_block) {
    Auto result = sir_alloc_block(fn, fn->mem, tag_of_new_block);

    array_push(&result->preds, from);
    array_push(&result->succs, to);

    array_find_replace(&from->succs, IT == to, result);
    array_find_replace(&to->preds, IT == from, result);

    if (to->idom == from) to->idom = result;

    return result;
}

// This function removes all phis from the CFG. This
// is done by replacing phis with moves inserted into
// the predecessor blocks of the phi. For example, the
// following CFG:
//
//     +-----+              +-----+
//     |     |              |     |
//     +-----+              +-----+
//        \                    /
//         \                  /
//          +----------------+
//          | c <- phi(a, b) |
//          +----------------+
//
// will turn into:
//
//     +--------+        +--------+
//     | c <- a |        | c <- b |
//     +--------+        +--------+
//        \                    /
//         \                  /
//          +----------------+
//          |                |
//          +----------------+
//
// This function might have to split edges in order to
// find a place for the new move instructions.
Void sir_leave_ssa_form (SirFn *fn) {
    tmem_new(tm);

    // For each phi P this map answers how many other phis
    // in the same block reference P in their nth arg where
    // the nth arg is specified in the code below.
    Array(struct { SirOp *phi; U32 n; }) refs;
    array_init(&refs, tm);

    // Use this to modify and/or to obtain a phi ref. To
    // update use like REF(op, e.n += 1). To just get the
    // ref use like REF(op,).
    #define REF(PHI, CODE) ({\
        Auto e = array_find_get(&refs, IT.phi == PHI);\
        CODE;\
        e.n;\
    })

    array_iter (block, &fn->blocks) {
        if (block->phis.count == 0) continue;

        array_iter (pred, &block->preds) {
            refs.count = 0;
            array_iter (phi, &block->phis) array_push_lit(&refs, phi, 0);
            array_iter (phi, &block->phis) {
                Auto arg = array_get(&phi->args, ARRAY_IDX);
                if (arg->tag == SIR_OP_PHI && arg != phi && arg->block == block) REF(arg, e.n += 1);
            }

            Auto emit_destination   = (pred->succs.count > 1) ? sir_edge_split(fn, pred, block, SIR_BLOCK_SSA_SPLIT) : pred;
            Auto original_phi_count = block->phis.count;

            while (block->phis.count) {
                U32 idx = 0;
                SirOp *phi = 0;

                array_iter (p, &block->phis) {
                    if (REF(p,) == 0) {
                        phi = p;
                        idx = ARRAY_IDX;
                        break;
                    }
                }

                if (phi) {
                    Auto arg = array_get(&phi->args, ARRAY_IDX);
                    if (arg != phi) {
                        emit_move(fn, emit_destination, phi, arg);
                        if (arg->tag == SIR_OP_PHI) REF(arg, e.n -= 1);
                    }
                    array_find_remove_fast(&arg->users, IT == phi);
                    array_swap_remove(&block->phis, idx);
                } else {
                    Auto any  = array_get(&block->phis, 0);
                    Auto arg  = array_get(&any->args, ARRAY_IDX);
                    Auto copy = emit_copy(fn, emit_destination, arg->type, arg);
                    sir_op_set_arg(any, ARRAY_IDX, copy);
                    REF(arg, e.n -= 1);
                }
            }

            block->phis.count = original_phi_count;
        }
    }

    fn->in_ssa_form = 0;
    #undef REF
}

static Void la_propagate (SirBlock *block, SirOp *def) {
    if (array_try_get_last(&block->live_out) != def) array_push(&block->live_out, def);
    if (block->flags & SIR_BLOCK_DEFINES_OP) return;
    if (array_try_get_last(&block->live_in) == def) return;
    array_push(&block->live_in, def);
    array_iter (pred, &block->preds) la_propagate(pred, def);
}

static Void la_mark_block (SirBlock *block, SirOp *def) {
    array_iter (op, &block->ops) {
        if (block->flags & SIR_BLOCK_DEFINES_OP) break;
        Auto inputs = sir_op_get_inputs(op);
        Auto outputs = sir_op_get_outputs(op);
        if (array_has(&inputs, def)) block->flags |= SIR_BLOCK_UPWARD_EXPOSES_OP;
        if (array_has(&outputs, def)) block->flags |= SIR_BLOCK_DEFINES_OP;
        if (op == def) block->flags |= SIR_BLOCK_DEFINES_OP;
    }
}

static Void la_compute (SirFn *fn, SirOp *op) {
    if (! (op->flags & SIR_OP_SELF_IS_REG)) return;
    if (op->flags & SIR_OP_LIVENESS_COMPUTED) return;

    op->flags |= SIR_OP_LIVENESS_COMPUTED;

    la_mark_block(op->block, op);
    array_iter (user, &op->users) {
        if (user->block->flags & (SIR_BLOCK_DEFINES_OP | SIR_BLOCK_UPWARD_EXPOSES_OP)) continue; // Already marked.
        if (sir_op_is_proper_user(op, user)) la_mark_block(user->block, op);
    }

    array_iter (user, &op->users) {
        if ((user->block->flags & SIR_BLOCK_UPWARD_EXPOSES_OP) && (array_try_get_last(&user->block->live_in) != op)) {
            array_push(&user->block->live_in, op);
            array_iter (pred, &user->block->preds) la_propagate(pred, op);
        }
    }

    op->block->flags &= ~(SIR_BLOCK_DEFINES_OP | SIR_BLOCK_UPWARD_EXPOSES_OP);
    array_iter (user, &op->users) user->block->flags &= ~(SIR_BLOCK_DEFINES_OP | SIR_BLOCK_UPWARD_EXPOSES_OP);
}

// This function will refresh the SirBlock.array_in/out arrays,
// that tell you which virtual registers are alive at the start
// and end of a block. Note that this function can be called
// multiple times.
//
// The algorithm used here works on non-SSA IRs and is described
// in the following paper:
//
//     Florian Brandner, Benoit Boissinot, Alain Darte, Benoît
//     Dupont de Dinechin, Fabrice Rastello. Computing Liveness
//     Sets for SSA-Form Programs. [Research Report] RR-7503,
//     INRIA. 2011, pp.25. inria-00558509v2
//
// The paper describes several algorithms. The one used here
// is the path exploration (var-by-var).
Void sir_do_liveness_analysis (SirFn *fn) {
    array_iter (block, &fn->blocks) {
        block->live_in.count = 0;
        block->live_out.count = 0;
        array_iter (op, &block->ops) op->flags &= ~SIR_OP_LIVENESS_COMPUTED;
    }

    array_iter (block, &fn->blocks) {
        array_iter (op, &block->ops) {
            la_compute(fn, op);
            Auto outputs = sir_op_get_outputs(op);
            array_iter (output, &outputs) la_compute(fn, output);
        }
    }

    assert_dbg(fn->entry_block->live_in.count == 0);
}
