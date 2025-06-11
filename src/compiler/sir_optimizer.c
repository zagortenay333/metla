#include "base/core.h"
#include "compiler/vm.h"
#include "compiler/sir_optimizer.h"

static Void update_phis (SirFn *fn, SirBlock *block) {
    block->flags &= ~SIR_BLOCK_PHIS_NEED_UPDATE;
    if (block->mem_phi) sir_update_phi(fn, block->mem_phi);
    sir_update_phis(fn, block);
}

static Void cut_edge (SirBlock *from, SirBlock *to) {
    array_find_remove(&from->succs, IT == to);
    array_find_remove(&to->preds, IT == from);
    to->flags |= SIR_BLOCK_PHIS_NEED_UPDATE;
    sir_update_idom(to);
}

istruct (Sccp) {
    Mem *mem;
    SirFn *fn;
    Array(Value) infos;
    Array(SirOp*) ops_to_eval;
    Array(SirBlock*) blocks_to_eval;
};

fenum (SccpFlags, U8) {
    SCCP_SIR_OP_CONST     = SIR_OP_0,
    SCCP_SIR_OP_NOT_CONST = SIR_OP_1,
};

ienum (SccpOpStatus, U8) {
    SCCP_MAYBE_CONST = 0,
    SCCP_CONST       = SCCP_SIR_OP_CONST,
    SCCP_NOT_CONST   = SCCP_SIR_OP_NOT_CONST,
};

static Value sccp_get_data (Sccp *sccp, SirOp *op) {
    return array_get(&sccp->infos, op->id);
}

static SccpOpStatus sccp_get_status (SirOp *op) {
    return op->flags & (SCCP_SIR_OP_CONST | SCCP_SIR_OP_NOT_CONST);
}

static Void sccp_mark_const (Sccp *sccp, SirOp *op, Value val) {
    array_set(&sccp->infos, op->id, val);
    op->flags |= SCCP_SIR_OP_CONST;
    op->flags &= ~SCCP_SIR_OP_NOT_CONST;
}

static Void sccp_mark_not_const (SirOp *op) {
    op->flags |= SCCP_SIR_OP_NOT_CONST;
    op->flags &= ~SCCP_SIR_OP_CONST;
}

static Void sccp_mark_maybe_const (SirOp *op) {
    op->flags &= ~SCCP_SIR_OP_CONST;
    op->flags &= ~SCCP_SIR_OP_NOT_CONST;
}

static Void sccp_cleanup_op (Sccp *sccp, SirOp *op) {
    array_find_remove_fast(&op->users, !(IT->block->flags & SIR_BLOCK_WAS_SCCP_EVALED));

    if ((sccp_get_status(op) == SCCP_CONST) && (op->tag != SIR_OP_NOP)) {
        op->tag = SIR_OP_CONST;
        op->flags = sir_op_get_default_flags[SIR_OP_CONST];
        sir_op_set_value(sccp->fn, op, sccp_get_data(sccp, op));
        sir_op_remove_args(op);
    }

    sccp_mark_maybe_const(op);
}

static Void sccp_cleanup (Sccp *sccp) {
    array_iter (block, &sccp->fn->blocks) {
        if (! (block->flags & SIR_BLOCK_WAS_SCCP_EVALED)) continue;

        array_iter (op, &block->ops) sccp_cleanup_op(sccp, op);

        { // Delete branch op if branch not taken:
            Auto last = array_try_get_last(&block->ops);

            if (last && last->tag == SIR_OP_BRANCH) {
                Auto cond = array_get(&last->args, 0);

                if (cond->tag == SIR_OP_CONST || sccp_get_status(cond) == SCCP_CONST) {
                    sir_op_delete(sccp->fn, last);
                    Auto cond_val = sccp_get_data(sccp, cond).u8;
                    Auto not_taken = array_get(&block->succs, cond_val);
                    cut_edge(block, not_taken);
                }
            }
        }

        { // Handle any phis that were converted to consts:
            U32 n = 0;

            array_iter (phi, &block->phis) {
                sccp_cleanup_op(sccp, phi);
                if (phi->tag == SIR_OP_CONST) {
                    array_swap_remove(&block->phis, ARRAY_IDX);
                    ARRAY_IDX--;
                    n++;
                }
            }

            if (n) {
                block->phis.count += n; // Restore the fake removed phis.
                SliceSirOp view = { .data=array_ref(&block->phis, block->phis.count - n), .count=n };
                array_insert_many(&block->ops, &view, 0);
                block->phis.count -= n;
            }
        }
    }

    array_iter (block, &sccp->fn->blocks) {
        if (block->flags & SIR_BLOCK_WAS_SCCP_EVALED) {
            block->flags &= ~SIR_BLOCK_WAS_SCCP_EVALED;
            if (block->flags & SIR_BLOCK_PHIS_NEED_UPDATE) update_phis(sccp->fn, block);
        }
    }
}

static Bool sccp_edge_is_executable (Sccp *sccp, SirBlock *from, SirBlock *to) {
    if (! (from->flags & SIR_BLOCK_WAS_SCCP_EVALED)) return false;
    if (from->succs.count == 1) return true;

    Auto branch = array_get_last(&from->ops);
    assert_dbg(branch->tag == SIR_OP_BRANCH);

    Auto cond_op = array_get(&branch->args, 0);

    if (sccp_get_status(cond_op) == SCCP_NOT_CONST) return true;

    if (sccp_get_status(cond_op) == SCCP_CONST) {
        Auto cond_val = sccp_get_data(sccp, cond_op).u8;
        return to == array_get(&from->succs, cond_val ? 0 : 1);
    }

    return false;
}

#define sccp_fold_biop(OP, FN, ARG0, ARG1) ({\
    if ((sccp_get_status(ARG0) == SCCP_CONST) && (sccp_get_status(ARG1) == SCCP_CONST)) {\
        if (sccp_get_status(OP) != SCCP_CONST) {\
            Value val = FN(ARG0->type, sccp_get_data(sccp, ARG0), sccp_get_data(sccp, ARG1));\
            sccp_mark_const(sccp, OP, val);\
        }\
    } else if ((sccp_get_status(ARG0) == SCCP_NOT_CONST) || (sccp_get_status(ARG1) == SCCP_NOT_CONST)) {\
        sccp_mark_not_const(OP);\
    }\
})

#define sccp_fold_unop(OP, FN, ARG) ({\
    if (sccp_get_status(ARG) == SCCP_CONST) {\
        if (sccp_get_status(OP) != SCCP_CONST) {\
            Value val = FN(ARG->type, sccp_get_data(sccp, ARG));\
            sccp_mark_const(sccp, OP, val);\
        }\
    } else if (sccp_get_status(ARG) == SCCP_NOT_CONST) {\
        sccp_mark_not_const(OP);\
    }\
})

static Void sccp_eval_op (Sccp *sccp, SirOp *op) {
    #define arg0(op) array_get(&(op)->args, 0)
    #define arg1(op) array_get(&(op)->args, 1)

    Auto prev_op_status = sccp_get_status(op);

    if (prev_op_status == SCCP_NOT_CONST) {
        if (op->tag == SIR_OP_PHI_MEM) badpath;
        assert_dbg(op->tag == SIR_OP_PHI);
        return;
    }

    switch (op->tag) {
    case SIR_OP_BRANCH: {
        Auto cond = arg0(op);

        if (sccp_get_status(cond) == SCCP_CONST) {
            U32 idx = sccp_get_data(sccp, cond).u8 ? 0 : 1;
            array_push(&sccp->blocks_to_eval, array_get(&op->block->succs, idx));
        } else if (sccp_get_status(cond) == SCCP_NOT_CONST) {
            array_push(&sccp->blocks_to_eval, array_get(&op->block->succs, 0));
            array_push(&sccp->blocks_to_eval, array_get(&op->block->succs, 1));
        }
    } break;

    case SIR_OP_PHI: {
        array_iter (arg, &op->args) {
            if (! sccp_edge_is_executable(sccp, array_get(&op->block->preds, ARRAY_IDX), op->block)) {
                continue;
            } else if (sccp_get_status(arg) == SCCP_NOT_CONST) {
                sccp_mark_not_const(op);
                break;
            } else if (sccp_get_status(arg) == SCCP_CONST) {
                if (sccp_get_status(op) == SCCP_MAYBE_CONST) {
                    sccp_mark_const(sccp, op, sccp_get_data(sccp, arg));
                } else if (! vm_value_match(op->type, sccp_get_data(sccp, op), sccp_get_data(sccp, arg))) {
                    sccp_mark_not_const(op);
                    break;
                }
            }
        }
    } break;

    case SIR_OP_NOT:           sccp_fold_unop(op, vm_value_not, arg0(op)); break;
    case SIR_OP_NEGATE:        sccp_fold_unop(op, vm_value_negate, arg0(op)); break;
    case SIR_OP_BITWISE_NOT:   sccp_fold_unop(op, vm_value_bitnot, arg0(op)); break;
    case SIR_OP_ADD:           sccp_fold_biop(op, vm_value_add, arg0(op), arg1(op)); break;
    case SIR_OP_SUB:           sccp_fold_biop(op, vm_value_sub, arg0(op), arg1(op)); break;
    case SIR_OP_MUL:           sccp_fold_biop(op, vm_value_mul, arg0(op), arg1(op)); break;
    case SIR_OP_DIV:           sccp_fold_biop(op, vm_value_div, arg0(op), arg1(op)); break;
    case SIR_OP_MOD:           sccp_fold_biop(op, vm_value_mod, arg0(op), arg1(op)); break;
    case SIR_OP_BITWISE_OR:    sccp_fold_biop(op, vm_value_bitor, arg0(op), arg1(op)); break;
    case SIR_OP_BITWISE_XOR:   sccp_fold_biop(op, vm_value_bitxor, arg0(op), arg1(op)); break;
    case SIR_OP_BITWISE_AND:   sccp_fold_biop(op, vm_value_bitand, arg0(op), arg1(op)); break;
    case SIR_OP_SHIFT_LEFT:    sccp_fold_biop(op, vm_value_lshift, arg0(op), arg1(op)); break;
    case SIR_OP_SHIFT_RIGHT:   sccp_fold_biop(op, vm_value_rshift, arg0(op), arg1(op)); break;
    case SIR_OP_EQUAL:         sccp_fold_biop(op, vm_value_equal, arg0(op), arg1(op)); break;
    case SIR_OP_NOT_EQUAL:     sccp_fold_biop(op, vm_value_not_eq, arg0(op), arg1(op)); break;
    case SIR_OP_LESS:          sccp_fold_biop(op, vm_value_less, arg0(op), arg1(op)); break;
    case SIR_OP_LESS_EQUAL:    sccp_fold_biop(op, vm_value_less_eq, arg0(op), arg1(op)); break;
    case SIR_OP_GREATER:       sccp_fold_biop(op, vm_value_greater, arg0(op), arg1(op)); break;
    case SIR_OP_GREATER_EQUAL: sccp_fold_biop(op, vm_value_greater_eq, arg0(op), arg1(op)); break;
    case SIR_OP_CONST:         sccp_mark_const(sccp, op, sir_op_get_value(sccp->fn, op)); break;
    default:                   sccp_mark_not_const(op); break;
    }

    if (prev_op_status != sccp_get_status(op)) {
        array_iter (user, &op->users) {
            if (user->tag == SIR_OP_PHI_MEM) continue;
            if (sccp_get_status(user) == SCCP_NOT_CONST) continue;
            if (! (user->block->flags & SIR_BLOCK_WAS_SCCP_EVALED)) continue;
            array_push(&sccp->ops_to_eval, user);
        }
    }

    #undef arg0
    #undef arg1
}

static Void sccp_eval_block (Sccp *sccp, SirBlock *block) {
    array_iter (phi, &block->phis) sccp_eval_op(sccp, phi);

    if (! (block->flags & SIR_BLOCK_WAS_SCCP_EVALED)) {
        array_iter (it, &block->ops) sccp_eval_op(sccp, it);
        block->flags |= SIR_BLOCK_WAS_SCCP_EVALED;
        if (block->succs.count == 1) array_push(&sccp->blocks_to_eval, array_get(&block->succs, 0));
    }
}

// Sparse Conditional Constants Propagation.
static Void sccp (SirFn *fn, Mem *mem) {
    assert_dbg(fn->in_ssa_form);

    Auto sccp = mem_new(mem, Sccp);
    sccp->mem = mem;
    sccp->fn = fn;
    array_init(&sccp->infos, mem);
    array_init(&sccp->ops_to_eval, mem);
    array_init(&sccp->blocks_to_eval, mem);

    array_ensure_capacity(&sccp->infos, fn->next_op_id);
    sccp->infos.count = fn->next_op_id;

    array_push(&sccp->blocks_to_eval, array_get(&fn->blocks, 0));

    while (sccp->ops_to_eval.count || sccp->blocks_to_eval.count) {
        if (sccp->ops_to_eval.count)    sccp_eval_op(sccp, array_pop(&sccp->ops_to_eval));
        if (sccp->blocks_to_eval.count) sccp_eval_block(sccp, array_pop(&sccp->blocks_to_eval));
    }

    sccp_cleanup(sccp);
}

static SirOp *get_base (SirOp *op) {
    assert_dbg(op->tag == SIR_OP_STORE || op->tag == SIR_OP_LOAD);
    Auto base = array_get(&op->args, 1);
    while (base->tag == SIR_OP_INDEX || base->tag == SIR_OP_OFFSET) base = array_get(&base->args, 0);
    return base;
}

static Bool a_clobbers_b (SirFn *fn, SirOp *a, SirOp *b) {
    if ((a->tag != SIR_OP_STORE) && (a->tag != SIR_OP_LOAD)) return true;
    if ((b->tag != SIR_OP_STORE) && (b->tag != SIR_OP_LOAD)) return true;

    Auto base1 = get_base(a);
    Auto base2 = get_base(b);

    if ((base1->tag == SIR_OP_STACK_OBJECT || base1->tag == SIR_OP_VALUE_ADDRESS) &&
        (base2->tag == SIR_OP_STACK_OBJECT || base2->tag == SIR_OP_VALUE_ADDRESS)
    ) {
        return base1 == base2;
    }

    if (base1->tag == SIR_OP_GLOBAL_OBJECT && base2->tag == SIR_OP_GLOBAL_OBJECT) {
        Auto ast1 = sir_op_get_value(fn, base1).ast;
        Auto ast2 = sir_op_get_value(fn, base2).ast;
        return ast1 == ast2;
    }

    return true;
}

static SirOp *get_earlier_clobber (SirFn *fn, SirOp *clobber, SirOp *op) {
    while (true) {
        if (clobber->tag == SIR_OP_PHI_MEM) {
            SirOp *prev = 0;

            if (clobber->flags & SIR_OP_0) return 0;
            clobber->flags |= SIR_OP_0;

            array_iter (arg, &clobber->args) {
                Auto c = get_earlier_clobber(fn, arg, op);
                if      (! c) continue;
                else if (! prev) prev = c;
                else if (prev != c) { prev = clobber; break; }
            }

            clobber->flags &= ~SIR_OP_0;
            return prev;
        }

        if (a_clobbers_b(fn, clobber, op)) break;
        clobber = array_get(&clobber->args, 0);
    }

    return clobber;
}

// The initial construction of SIR produces a pesimistic memory
// dependence graph. Every op that touches memory depends on the
// version of memory produced by the most recent op that modifies
// memory.
//
// This function tries to make each op depend on a version of
// memory that appears as early as possible in the CFG, thus
// increasing the range in which those ops can be moved and/or
// reordered safely.
static Void relax_memory_dependencies (SirFn *fn) {
    array_iter (block, &fn->blocks) {
        array_iter (op, &block->ops) {
            if ((op->flags & SIR_OP_TOUCHES_MEMORY) && (op->tag != SIR_OP_MEMORY)) {
                Auto arg0 = array_get(&op->args, 0);
                Auto clobber = get_earlier_clobber(fn, arg0, op);
                if (clobber != arg0) sir_op_set_arg(op, 0, clobber);
            }
        }
    }
}

Void sir_mark_reachable_blocks (SirFn *fn, SirBlock *block) {
    if (block->flags & SIR_BLOCK_IS_REACHABLE) return;
    block->flags |= SIR_BLOCK_IS_REACHABLE;
    array_iter (it, &block->succs) sir_mark_reachable_blocks(fn, it);
}

Void sir_remove_unreachable_blocks (SirFn *fn) {
    if (fn->blocks.count == 0) return;

    Auto entry = array_get(&fn->blocks, 0);
    sir_mark_reachable_blocks(fn, entry);

    array_iter (block, &fn->blocks) {
        if (block->flags & SIR_BLOCK_IS_REACHABLE) continue;
        block->flags |= SIR_BLOCK_IS_DEAD;
        array_iter (succ, &block->succs) if (succ->flags & SIR_BLOCK_IS_REACHABLE) cut_edge(block, succ);
    }

    array_iter (block, &fn->blocks) {
        if (block->flags & SIR_BLOCK_IS_REACHABLE) continue;
        array_iter (op, &block->phis) sir_op_remove_args(op);
        array_iter (op, &block->ops)  sir_op_remove_args(op);
    }

    array_find_remove_all_fast(&fn->blocks, IT->flags & SIR_BLOCK_IS_DEAD);

    array_iter (block, &fn->blocks) {
        block->flags &= ~SIR_BLOCK_IS_REACHABLE;
        if (block->flags & SIR_BLOCK_PHIS_NEED_UPDATE && fn->in_ssa_form) update_phis(fn, block);
    }
}

// Delete the block if it's empty and has only 1 successor plus
// some other restrictions. This is a simple form of jump threading.
static Bool try_delete_block (SirFn *fn, SirBlock *block) {
    if (block->ops.count)              return false;
    if (block->succs.count != 1)       return false;
    if (block->tag == SIR_BLOCK_ENTRY) return false;

    Auto succ = array_get(&block->succs, 0);

    if (succ == block) return false;
    if (fn->in_ssa_form && (block->phis.count || succ->phis.count)) return false;

    array_find_remove_fast(&succ->preds, IT == block);

    array_iter (pred, &block->preds) {
        array_find_replace(&pred->succs, IT == block, succ);
        array_push_if_unique(&succ->preds, pred);
        Auto last = array_try_get_last(&pred->ops);
        if (last && last->tag == SIR_OP_BRANCH && pred->succs.count == 1) sir_op_delete(fn, last);
    }

    succ->idom = block->idom;
    block->flags |= SIR_BLOCK_IS_DEAD;

    return true;
}

// If the block has only 1 predecessor, fuse it into the predecessor.
static Bool try_fuse_block_with_predecessor (SirFn *fn, SirBlock *block) {
    if (block->ops.count == 0) return false;
    if (block->preds.count != 1) return false;

    Auto pred = array_get(&block->preds, 0);
    if (pred->succs.count != 1) return false;

    array_iter (op, &block->ops) {
        if (op->tag == SIR_OP_NOP) continue;
        array_push(&pred->ops, op);
        op->block = pred;
    }

    if (fn->in_ssa_form) array_push_many(&block->scope, &pred->scope);
    pred->succs = block->succs;

    array_iter (succ, &pred->succs) {
        array_iter (it, &succ->preds) {
            if (it == block) {
                array_set(&succ->preds, ARRAY_IDX, pred);
                break;
            }
        }
    }

    array_iter (succ, &block->succs) if (succ->idom == block) succ->idom = pred;
    block->flags |= SIR_BLOCK_IS_DEAD;

    return true;
}

Void sir_simplify_cfg (SirFn *fn) {
    sir_remove_unreachable_blocks(fn);

    Bool changed = true;
    while (changed) {
        changed = false;

        array_iter (block, &fn->blocks) {
            if (block->tag == SIR_BLOCK_EXIT || block->flags & SIR_BLOCK_IS_DEAD) {
                continue;
            } else if (try_delete_block(fn, block)) {
                changed = true;
            } else if (try_fuse_block_with_predecessor(fn, block)) {
                changed = true;
            }
        }
    }

    array_find_remove_all_fast(&fn->blocks, IT->flags & SIR_BLOCK_IS_DEAD);
}

Void sir_remove_unused_ops (SirFn *fn) {
    Bool changed = true;
    while (changed) {
        changed = false;

        array_iter (block, &fn->blocks) {
            array_iter (op, &block->phis) if (sir_op_try_delete(fn, op)) changed = true;
            array_iter (op, &block->ops)  if (sir_op_try_delete(fn, op)) changed = true;
        }
    }
}

Void sir_optimize (SirFn *fn, Mem *mem) {
    sir_check_integrity(fn);
    relax_memory_dependencies(fn);
    sccp(fn, mem);
    sir_simplify_cfg(fn);
    sir_remove_unused_ops(fn);
    sir_check_integrity(fn);
}
