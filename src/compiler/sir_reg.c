// =============================================================================
// Algorithm:
// ----------
//
// The algorithm used is called "second chance binpacking" and it comes
// from the linear-scan family. It works on non-SSA based IRs, and it's
// described in this paper:
//
//     Traub, Omri, Glenn Holloway, and Michael D. Smith. 1998. Quality
//     and Speed in Linear-scan Register Allocation. In Fneedings of
//     the ACM SIGPLAN 1998 Conference on Programming Language Design
//     and Implementation, Montreal, QC, June 17-19, 1998: 142-151.
//     doi:10.1145/277650.277714
//
// Deviation from the algorithm:
// -----------------------------
//
// In the paper an optimization is proposed wherein one avoids emitting
// a spill instruction if the value in the register is identical to the
// value in the corresponding stack slot. To do this, it's necessary to
// eventually perform a postpass where one fixes mistakes along block
// edges that are caused due to the fact that the algorithm works on a
// flattened CFG. Of all the passes that this algorithm performs this one
// is the only fixed point dataflow based one. It's slow and complicated
// and we avoid it by doing a simpler version of this optimization.
//
// This simpler version works by only tracking values between registers
// and their corresponding stack slots in the small region right above
// the instruction we are currently processing (assigning registers to).
// We know the following about this region:
//
//     1. It fits entirely within 1 basic block, so there is no need to
//        run the expensive postpass fix.
//
//     2. No virtual registers within this region can be mutated because
//        this region only contains the instructions: SIR_OP_REG_LOAD,
//        SIR_OP_REG_STORE, SIR_OP_REG_MOVE which are emitted by the reg
//        allocator itself. This means that we can use virtual registers
//        (SirOp) to represent values even though we are not in SSA form.
//
// We also use simpler heuristics for which registers to spill.
// =============================================================================
#include "base/map.h"
#include "compiler/sir_reg.h"

fenum (RegFlags, U8) {
    REG_WAS_USED        = flag(0),
    REG_IS_MOVE_SRC     = flag(1),
    REG_IS_CALLEE_SAVED = flag(2),
};

istruct (SirReg) {
    SirRegId id;
    String name;
    RegFlags flags;
    ArraySirOp ops;
    ArraySirOp clobbers;
    U32 latest_use_pos;
    U32 latest_clobber_pos;
    U32 last_preferrer_pos;
    U32 alive_at_end_of_edge;
    struct { U32 pos; SirOp *op; } val;
};

istruct (LiveRange) {
    U32 start; // Start of block or pos *after* op that writes to reg.
    U32 end;   // Pos of last op in this live range that reads the reg.
};

istruct (BlockRegBind) {
    Slice(SirReg*) start;  // Parallel to live_in array of block.
    Slice(SirReg*) end[2]; // Parallel to live_in arrays of first and second successors respectively.
};

istruct (SirOpInfo) {
    // Absolute position of the instruction in the flattened CFG.
    // Note this only applies to SirOps that represent instructions
    // and therefore appear in the CFG. Other SirOps will have pos
    // set to 0 (an invalid position). For example, now that we are
    // not in SSA form, a SIR_OP_PHI will only appear as the target
    // of move ops or in arguments. So phis at this point do not
    // represent instructions and their pos is 0.
    U32 pos;
    SirReg *reg; // Register we are currently bound to. If 0 we are spilled.
    SirOp *spill_link; // Read comment about SIR_OP_REG_STORE in sir_ops.h.
    Array(LiveRange) ranges;
};

istruct (RegAlloc) {
    Mem *mem;
    SirRegAlloc *public;

    SirBlock *block; // Block we're currently reg allocating.
    U32 pos; // Starts at 1. Absolute pos in the flattened CFG.
    U32 rel_pos; // Starts at 0. Pos within current block.
    U32 last_pos; // Pos of last op. last_pos + 1 is guaranteed to be available.

    Bool assigning_regs;
    Bool assigning_inputs; // Else assigning outputs.

    Array(SirOpInfo) infos; // Index is SirOpId. Ops emitted by reg allocator *do not* have entries.
    Array(BlockRegBind) block_reg_binds; // Index is SirBlockId. Blocks created by reg allocator *do not* have entries.
    Array(SirOpRegConstraints) constraints; // Index is SirOpId. Ops emitted by reg allocator also have entries.

    // During register allocation we might have to insert stores,
    // loads or moves into the middle of a basic block. They way
    // we implement this is that as soon as we have to do it, we
    // swap the ops buffer of the current block (SirBlock.ops) we
    // this one, and then we can append the new instructions. The
    // buffer of the old block becomes the next tmp_op_buf. Look
    // at init_tmp_op_buf() for details.
    Bool tmp_op_buf_used;
    ArraySirOp tmp_op_buf;
};

static SirOpRegConstraints *get_constraints (RegAlloc *ra, SirOp *op) {
    return array_ref(&ra->constraints, op->id);
}

static SirOpInfo *get_info (RegAlloc *ra, SirOp *op) {
    return array_ref(&ra->infos, op->id);
}

static BlockRegBind *get_block_reg_bind (RegAlloc *ra, SirBlock *block) {
    return array_ref(&ra->block_reg_binds, block->id);
}

static SirOpRegBind *get_op_reg_bind (RegAlloc *ra, SirOp *op) {
    return array_get(&ra->public->bindings, op->id);
}

// If pos is in a life range of op, return that range.
// If pos is to the right of the last range, return last range.
// If pos is in a life hole, return the range to the right of that hole.
static LiveRange *get_live_range (RegAlloc *ra, SirOpInfo *info, U32 pos) {
    assert_dbg(info->ranges.count != 0);
    Auto last = array_ref(&info->ranges, 0);
    if (pos > last->end) return last;
    array_iter_back (range, &info->ranges, *) if (range->end >= pos) return range;
    badpath;
}

static U32 get_last_live_pos (RegAlloc *ra, SirOp *op) {
    Auto info = get_info(ra, op);
    assert_dbg(info->ranges.count != 0);
    return array_get(&info->ranges, 0).end;
}

static Void init_tmp_op_buf (RegAlloc *ra) {
    if (! ra->tmp_op_buf_used) {
        ra->tmp_op_buf_used = true;
        ra->tmp_op_buf.count = 0;
        array_push_many(&ra->tmp_op_buf, (&(SliceSirOp){ .data=ra->block->ops.data, .count=ra->rel_pos }));
        swap(ra->block->ops, ra->tmp_op_buf);
    }
}

static Void init_op_reg_bind (RegAlloc *ra, SirOpRegBind *bind, SirOp *op, U32 inputs, U32 outputs) {
    if (inputs + outputs == 0) return;

    SirReg **buf        = mem_alloc(ra->mem, SirReg*, .size=(inputs + outputs)*sizeof(SirReg*));
    bind->inputs.data   = buf;
    bind->inputs.count  = inputs;
    bind->outputs.data  = buf+inputs;
    bind->outputs.count = outputs;
}

static SirOp *alloc_op (RegAlloc *ra, SirOpTag tag, Type *type) {
    Auto op = sir_op_alloc(ra->public->fn, tag, type);
    Auto bind = mem_new(ra->mem, SirOpRegBind);
    array_push(&ra->public->bindings, bind);

    switch (tag) {
    case SIR_OP_REG_MOVE:  init_op_reg_bind(ra, bind, op, 1, 1); break;
    case SIR_OP_REG_LOAD:  init_op_reg_bind(ra, bind, op, 1, 0); break;
    case SIR_OP_REG_STORE: init_op_reg_bind(ra, bind, op, 1, 0); break;
    default: badpath;
    }

    return op;
}

static Void add_spill_link (RegAlloc *ra, SirOp *spill_or_load, SirOp *op) {
    Auto info = get_info(ra, op);

    if (info->spill_link) {
        array_push(&spill_or_load->args, info->spill_link);
    } else {
        info->spill_link = spill_or_load;
        array_push(&spill_or_load->args, op);
    }
}

static Void emit_reg_store (RegAlloc *ra, SirReg *reg, SirOp *val) {
    assert_dbg(ra->assigning_regs);

    init_tmp_op_buf(ra);

    Auto store = alloc_op(ra, SIR_OP_REG_STORE, val->type);
    sir_op_add_to_block(ra->block, store);
    add_spill_link(ra, store, val);

    Auto bindings = array_get(&ra->public->bindings, store->id);
    array_set(&bindings->inputs, 0, reg);

    reg->val.pos = ra->pos;
    reg->val.op  = val;
}

static Void emit_reg_load (RegAlloc *ra, SirReg *reg, SirOp *val) {
    assert_dbg(ra->assigning_regs);

    if (reg->val.op == val && reg->val.pos == ra->pos) return;

    init_tmp_op_buf(ra);

    Auto load = alloc_op(ra, SIR_OP_REG_LOAD, val->type);
    sir_op_add_to_block(ra->block, load);
    add_spill_link(ra, load, val);

    Auto bindings = array_get(&ra->public->bindings, load->id);
    array_set(&bindings->inputs, 0, reg);

    reg->val.pos = ra->pos;
    reg->val.op  = val;
    reg->flags  |= REG_WAS_USED;
}

static Void emit_reg_move (RegAlloc *ra, SirOp *val, SirReg *to, SirReg *from) {
    assert_dbg(ra->assigning_regs);

    if (to->val.op == from->val.op && to->val.pos == ra->pos && from->val.pos == ra->pos) return;

    init_tmp_op_buf(ra);

    Auto move = alloc_op(ra, SIR_OP_REG_MOVE, val->type);
    sir_op_add_to_block(ra->block, move);

    Auto bindings = array_get(&ra->public->bindings, move->id);
    array_set(&bindings->inputs, 0, from);
    array_set(&bindings->outputs, 0, to);

    to->val.pos   = ra->pos;
    from->val.pos = ra->pos;
    to->val.op    = val;
    from->val.op  = val;
    to->flags    |= REG_WAS_USED;
}

static SirReg *reg_of (RegAlloc *ra, SirOp *op) {
    return get_info(ra, op)->reg;
}

static Void bind_reg (RegAlloc *ra, SirReg *reg, SirOp *op) {
    if (reg == ra->public->dummy_reg) {
        get_info(ra, op)->reg = 0;
    } else {
        get_info(ra, op)->reg = reg;
        array_push(&reg->ops, op);
        reg->flags |= REG_WAS_USED;
    }
}

static Void unbind_reg (RegAlloc *ra, SirReg *reg, SirOp *op) {
    Auto info = get_info(ra, op);
    assert_dbg(info->reg == reg);
    info->reg = 0;
    array_find_remove_fast(&reg->ops, IT == op);
}

// Check if the entire lifetime of @op can fit into the lifetime hole of
// each op that is assigned to @reg at the current position (ra->pos).
static Bool op_can_be_binpacked (RegAlloc *ra, SirOp *op, SirReg *reg) {
    if (ra->pos > ra->last_pos) return true;

    U32 last_live_pos = get_last_live_pos(ra, op);

    array_iter (it, &reg->ops) {
        Auto range = get_live_range(ra, get_info(ra, it), ra->pos);
        if (ra->pos > range->end) continue;
        if (ra->pos >= range->start || last_live_pos >= range->start) return false;
    }

    return true;
}

// A register preference is computed from a SIR_RC_ONLY.
// If an op has such a constraint in some position ahead of
// the current pos, we prefer to assign that reg right now.
static SirReg *get_preferred_register (RegAlloc *ra, SirOp *op) {
    SirReg *result = 0;
    U32 result_pos = ra->last_pos + 1;

    array_iter (user, &op->users) {
        U32 user_pos = get_info(ra, user)->pos;
        if (user_pos <= ra->pos || result_pos < user_pos) continue;

        Auto inputs      = sir_op_get_inputs(user);
        Auto outputs     = sir_op_get_outputs(user);
        Auto constraints = get_constraints(ra, user);

        SirRegConstraint *constraint = 0;
        Auto input = array_find(&inputs, IT == op);

        if (input != ARRAY_NIL_IDX) {
            constraint = array_ref(&constraints->inputs, input);
        } else {
            Auto output = array_find(&outputs, IT == op);
            if (output == ARRAY_NIL_IDX) continue; // The reference is among the op's special arguments.
            constraint = array_ref(&constraints->outputs, output);
        }

        if (constraint->tag == SIR_RC_ONLY) {
            result = constraint->reg;
            result_pos = user_pos;
        }
    }

    return result;
}

static SirReg *get_available_reg_with_preference (RegAlloc *ra, SirOp *op, SirReg *preferred_reg, Bool callee_saved, SirReg *reg_to_skip) {
    SirReg *result = 0;

    array_iter (reg, &ra->public->registers) {
        if (reg == reg_to_skip) continue;
        if (callee_saved && !(reg->flags & REG_IS_CALLEE_SAVED)) continue;
        if (!callee_saved && (reg->flags & REG_IS_CALLEE_SAVED)) continue;
        if (ra->assigning_inputs && reg->latest_use_pos == ra->pos) continue;
        if (reg->latest_clobber_pos == ra->pos) continue;
        if (! ra->public->is_compatible(ra->public, op, reg)) continue;
        if (! op_can_be_binpacked(ra, op, reg)) continue;

        result = reg;

        if (preferred_reg) {
            if (reg == preferred_reg) break;
        } else if (reg->last_preferrer_pos < ra->pos) {
            break;
        }
    }

    return result;
}

// Returns a register that can be assigned to op immediately or 0.
static SirReg *get_available_reg (RegAlloc *ra, SirOp *op, SirReg *reg_to_skip) {
    Auto preferred_reg = get_preferred_register(ra, op);
    Auto callee_saved  = get_available_reg_with_preference(ra, op, preferred_reg, true, reg_to_skip);
    Auto caller_saved  = get_available_reg_with_preference(ra, op, preferred_reg, false, reg_to_skip);

    if (! callee_saved) return caller_saved;
    if (! caller_saved) return callee_saved;

    if (caller_saved == preferred_reg) return caller_saved;
    if (callee_saved == preferred_reg) return callee_saved;

    U32 next_caller_saved_clobber_pos = ra->last_pos + 1;
    array_iter_back (clobber, &caller_saved->clobbers) {
        U32 pos = get_info(ra, clobber)->pos;
        if (pos >= ra->pos) { next_caller_saved_clobber_pos = pos; break; }
    }

    return (next_caller_saved_clobber_pos < get_last_live_pos(ra, op)) ? callee_saved : caller_saved;
}

static Void evict_op_from_reg (RegAlloc *ra, SirReg *reg, SirOp *op) {
    unbind_reg(ra, reg, op);

    if (! ra->assigning_inputs) {
        Auto range = get_live_range(ra, get_info(ra, op), ra->pos);
        if (ra->pos == range->end) return; // Not alive on next pos; no need to spill.
    }

    Auto available_reg = get_available_reg(ra, op, reg);

    if (available_reg) {
        bind_reg(ra, available_reg, op);
        emit_reg_move(ra, op, available_reg, reg);
    } else {
        emit_reg_store(ra, reg, op);
    }
}

// Evict any op from reg that at the current pos (ra->pos)
// is not in a hole and whose hole doesn't include hole_extent.
static Void make_reg_available (RegAlloc *ra, SirReg *reg, U32 hole_extent) {
    array_iter (op, &reg->ops) {
        Auto range = get_live_range(ra, get_info(ra, op), ra->pos);

        if (ra->pos > range->end) {
            continue;
        } else if (ra->pos >= range->start) {
            evict_op_from_reg(ra, reg, op);
            ARRAY_IDX--; // Because evict_op_from_reg() removes an op.
        } else if (hole_extent >= range->start) {
            unbind_reg(ra, reg, op);
            ARRAY_IDX--; // Because unbind_reg() removes an op.
        }
    }
}

static SirReg *assign_some_reg (RegAlloc *ra, SirOp *op, SirReg *except) {
    Auto reg = get_available_reg(ra, op, except);

    if (! reg) { // We gotta spill something.
        array_iter (candidate, &ra->public->registers) {
            if (! ra->public->is_compatible(ra->public, op, candidate)) continue;
            if (candidate->latest_clobber_pos == ra->pos) continue;
            if (candidate->latest_use_pos == ra->pos) continue;
            make_reg_available(ra, candidate, get_last_live_pos(ra, op));
            reg = candidate;
            break;
        }
    }

    // It's possible that there are no registers we can spill.
    // This can happen when we are processing an instruction
    // that has more arguments then there are registers such
    // as SIR_OP_CALL. All the extra arguments will be bound
    // to the dummy register which indicates that the values
    // are in a stack slot.
    if (! reg) reg = ra->public->dummy_reg;

    bind_reg(ra, reg, op);
    return reg;
}

static Void assign_reg (RegAlloc *ra, SirOp *op, SirReg *reg) {
    make_reg_available(ra, reg, get_last_live_pos(ra, op));
    bind_reg(ra, reg, op);
}

static Void assign_regs_to_inputs (RegAlloc *ra, SirOp *op, SliceSirOp *inputs, SirOpRegBind *bind, SirOpRegConstraints *constraints) {
    array_iter (arg, inputs) {
        Auto reg = reg_of(ra, arg);
        Auto constraint = array_ref(&constraints->inputs, ARRAY_IDX);

        switch (constraint->tag) {
        case SIR_RC_ONLY: {
            if (! reg) {
                make_reg_available(ra, constraint->reg, ra->pos);
                if (constraint->reg->latest_clobber_pos != ra->pos) bind_reg(ra, constraint->reg, arg);
                emit_reg_load(ra, constraint->reg, arg);
            } else if (reg != constraint->reg) {
                make_reg_available(ra, constraint->reg, ra->pos);
                emit_reg_move(ra, arg, constraint->reg, reg);
            }
            constraint->reg->latest_use_pos = ra->pos;
            array_set(&bind->inputs, ARRAY_IDX, constraint->reg);
        } break;

        case SIR_RC_SKIP: array_set(&bind->inputs, ARRAY_IDX, ra->public->dummy_reg); break;
        case SIR_RC_SAME_AS_ARG0: badpath;
        default: break;
        }
    }

    array_iter (arg, inputs) {
        Auto reg = reg_of(ra, arg);
        Auto constraint = array_ref(&constraints->inputs, ARRAY_IDX);

        switch (constraint->tag) {
        case SIR_RC_ANY: {
            if (! reg) {
                reg = assign_some_reg(ra, arg, 0);
                if (reg != ra->public->dummy_reg) emit_reg_load(ra, reg, arg);
            }
            reg->latest_use_pos = ra->pos;
            array_set(&bind->inputs, ARRAY_IDX, reg);
        } break;

        case SIR_RC_ANY_EXCEPT: {
            if (! reg) {
                reg = assign_some_reg(ra, arg, constraint->reg);
                if (reg != ra->public->dummy_reg) emit_reg_load(ra, reg, arg);
            } else if (reg == constraint->reg) {
                make_reg_available(ra, reg, ra->pos);
                reg = assign_some_reg(ra, arg, constraint->reg);
                emit_reg_move(ra, arg, reg, constraint->reg);
            }
            reg->latest_use_pos = ra->pos;
            array_set(&bind->inputs, ARRAY_IDX, reg);
        } break;

        default: break;
        }
    }
}

static Void assign_regs_to_outputs (RegAlloc *ra, SirOp *op, SliceSirOp *outputs, SirOpRegBind *bind, SirOpRegConstraints *constraints) {
    array_iter (arg, outputs) {
        Auto reg = reg_of(ra, arg);
        Auto constraint = array_ref(&constraints->outputs, ARRAY_IDX);

        switch (constraint->tag) {
        case SIR_RC_ONLY: {
            if (! reg) {
                assign_reg(ra, arg, constraint->reg);
            } else if (reg != constraint->reg) {
                unbind_reg(ra, reg, arg);
                assign_reg(ra, arg, constraint->reg);
            }
            constraint->reg->latest_use_pos = ra->pos;
            array_set(&bind->outputs, ARRAY_IDX, constraint->reg);
        } break;

        case SIR_RC_SKIP: array_set(&bind->outputs, ARRAY_IDX, ra->public->dummy_reg); break;
        case SIR_RC_SAME_AS_ARG0: badpath;
        default: break;
        }
    }

    array_iter (arg, outputs) {
        Auto reg = reg_of(ra, arg);
        Auto constraint = array_ref(&constraints->outputs, ARRAY_IDX);

        switch (constraint->tag) {
        case SIR_RC_ANY: {
            if (! reg) reg = assign_some_reg(ra, arg, 0);

            reg->latest_use_pos = ra->pos;
            array_set(&bind->outputs, ARRAY_IDX, reg);
        } break;

        case SIR_RC_ANY_EXCEPT: {
            if (! reg) {
                reg = assign_some_reg(ra, arg, constraint->reg);
            } else if (reg == constraint->reg) {
                unbind_reg(ra, reg, arg);
                reg = assign_some_reg(ra, arg, constraint->reg);
            }
            reg->latest_use_pos = ra->pos;
            array_set(&bind->outputs, ARRAY_IDX, reg);
        } break;

        default: break;
        }
    }
}

static Void assign_reg_to_self (RegAlloc *ra, SirOp *op, SirOpRegBind *bind, SirOpRegConstraints *constraints) {
    Auto reg = reg_of(ra, op);
    Auto con = &constraints->self;

    switch (con->tag) {
    case SIR_RC_SKIP: {
        reg = ra->public->dummy_reg;
    } break;

    case SIR_RC_ANY: {
        if (! reg) reg = assign_some_reg(ra, op, 0);
    } break;

    case SIR_RC_ONLY: {
        if (reg != con->reg) {
            if (reg) unbind_reg(ra, reg, op);
            assign_reg(ra, op, con->reg);
            reg = con->reg;
        }
    } break;

    case SIR_RC_SAME_AS_ARG0: {
        Auto reg_of_first_input = array_get(&bind->inputs, 0);

        if (reg != reg_of_first_input) {
            if (reg) unbind_reg(ra, reg, op);
            assign_reg(ra, op, reg_of_first_input);
            reg = reg_of_first_input;
        }
    } break;

    case SIR_RC_ANY_EXCEPT: {
        if (! reg) {
            reg = assign_some_reg(ra, op, con->reg);
        } else if (reg == con->reg) {
            unbind_reg(ra, reg, op);
            reg = assign_some_reg(ra, op, con->reg);
        }
    } break;
    }

    bind->self = reg;
}

static Void assign_regs_to_op (RegAlloc *ra, SirOp *op) {
    ra->assigning_inputs = true;

    if (op->flags & SIR_OP_USES_TMP_REG0) {
        make_reg_available(ra, ra->public->tmp_reg0, ra->pos + 1);
        ra->public->tmp_reg0->latest_clobber_pos = ra->pos;
    }

    if (op->flags & SIR_OP_USES_TMP_REG1) {
        make_reg_available(ra, ra->public->tmp_reg1, ra->pos + 1);
        ra->public->tmp_reg1->latest_clobber_pos = ra->pos;
    }

    array_iter (reg, &ra->public->registers) {
        if (! array_has(&reg->clobbers, op)) continue;

        // Evict ops from clobbered registers.
        array_iter (it, &reg->ops) {
            Auto range = get_live_range(ra, get_info(ra, it), ra->pos);
            if (ra->pos >= range->start && ra->pos < range->end) {
                evict_op_from_reg(ra, reg, it);
                break;
            }
        }

        reg->latest_clobber_pos = ra->pos;
    }

    Auto bind        = get_op_reg_bind(ra, op);
    Auto inputs      = sir_op_get_inputs(op);
    Auto outputs     = sir_op_get_outputs(op);
    Auto constraints = get_constraints(ra, op);

    init_op_reg_bind(ra, bind, op, inputs.count, outputs.count);
    if (inputs.count) assign_regs_to_inputs(ra, op, &inputs, bind, constraints);
    ra->assigning_inputs = false;
    if (outputs.count) assign_regs_to_outputs(ra, op, &outputs, bind, constraints);
    if (op->flags & SIR_OP_SELF_IS_REG) assign_reg_to_self(ra, op, bind, constraints);
}

static Void allocate_registers (RegAlloc *ra) {
    ra->assigning_regs = true;

    array_iter (block, &ra->public->fn->blocks) {
        // Try assigning registers to unbound ops that are alive at
        // the start of the block start. It's an optimization which
        // might stop fix_bind_mismatch_between_edges() from adding
        // a store at the start of this block.
        array_iter (op, &block->live_in) {
            if (! reg_of(ra, op)) {
                Auto reg = get_available_reg(ra, op, 0);
                if (reg) bind_reg(ra, reg, op);
            }
        }

        if (block->live_in.count) { // Save which registers were bound to ops at the start of the block:
            U32 count         = block->live_in.count;
            Auto bind         = get_block_reg_bind(ra, block);
            bind->start.count = count;
            bind->start.data  = mem_alloc(ra->mem, SirReg*, .size=count*array_esize(&block->live_in));
            array_iter (op, &block->live_in) array_set(&bind->start, ARRAY_IDX, reg_of(ra, op));
        }

        { // Assign registers:
            ra->rel_pos = 0;
            ra->block = block;
            ra->tmp_op_buf_used = false;
            Auto block_ops = block->ops;

            array_iter (op, &block_ops) {
                assign_regs_to_op(ra, op);
                ra->pos++;
                if (ra->tmp_op_buf_used) array_push(&block->ops, op);
                ra->rel_pos++;
            }
        }

        { // Save which registers were bound to ops at end of the block:
            assert_dbg(block->succs.count <= 2);
            Auto bind = get_block_reg_bind(ra, block);

            array_iter (succ, &block->succs) {
                U32 count = succ->live_in.count;

                if (count) {
                    Auto b   = &bind->end[ARRAY_IDX];
                    b->count = count;
                    b->data  = mem_alloc(ra->mem, SirReg*, .size=count*sizeof(SirReg*));
                    array_iter (op, &succ->live_in) array_set(b, ARRAY_IDX, reg_of(ra, op));
                }
            }
        }
    }

    ra->assigning_regs = false;
}

// Suppose we have the following CFG:
//
//     b0:
//         bind V to a register
//         branch b1 b2
//     b1:
//         spill V
//     b2:
//         read V
//
// Note that V is bound to a register at the bottom of b0 and
// to a stack slot (spilled) at the top of b2 yet there is no
// spill instruction along the b0->b2 edge. That's due to the
// algorithm working on a flattened CFG (linear-scan).
//
// This function examines all edges for these mismatches. To
// fix them it will emit store, load or move instructions and
// split edges to insert them.
static Void fix_bind_mismatch_between_edges (RegAlloc *ra) {
    tmem_new(tm);

    ArraySirOp moves_ordered; array_init(&moves_ordered, tm);
    ArraySirOp moves;         array_init(&moves, tm);
    ArraySirOp loads;         array_init(&loads, tm);
    ArraySirOp stores;        array_init(&stores, tm);

    U32 edge_id = 0;

    array_iter (block, &ra->public->fn->blocks) {
        if (block->tag == SIR_BLOCK_REG_SPLIT) continue;

        array_iter (succ, &block->succs) {
            if (succ->tag == SIR_BLOCK_REG_SPLIT) continue;
            edge_id++;

            { // 1. Create necessary stores, loads, moves:

                stores.count        = 0;
                loads.count         = 0;
                moves.count         = 0;
                moves_ordered.count = 0;

                Auto from_map = get_block_reg_bind(ra, block)->end[ARRAY_IDX];
                Auto to_map   = get_block_reg_bind(ra, succ)->start;

                array_iter (it, &succ->live_in) {
                    Auto from = array_get(&from_map, ARRAY_IDX);
                    Auto to   = array_get(&to_map, ARRAY_IDX);

                    if (to) to->alive_at_end_of_edge = edge_id;

                    if (!from && to) {
                        Auto load = alloc_op(ra, SIR_OP_REG_LOAD, it->type);
                        array_push(&loads, load);
                        add_spill_link(ra, load, it);
                        Auto b = get_op_reg_bind(ra, load);
                        array_set(&b->inputs, 0, to);
                    } else if (from && !to) {
                        Auto store = alloc_op(ra, SIR_OP_REG_STORE, it->type);
                        array_push(&stores, store);
                        add_spill_link(ra, store, it);
                        Auto b = get_op_reg_bind(ra, store);
                        array_set(&b->inputs, 0, from);
                    } else if (from != to) {
                        Auto move = alloc_op(ra, SIR_OP_REG_MOVE, it->type);
                        array_push(&moves, move);
                        Auto b = get_op_reg_bind(ra, move);
                        array_set(&b->outputs, 0, to);
                        array_set(&b->inputs, 0, from);
                        from->flags |= REG_IS_MOVE_SRC;
                    }
                }
            }

            { // 2. Order the moves correctly:

                // Sometimes it will be necessary to use a temporary register to resolve
                // moves that were inserted in step 1. For example:
                //
                //      B <- A          TMP <- A
                //      A <- B    ->    A   <- B
                //                      B   <- TMP
                //
                // The target of a load or a register that is not used at the start of the
                // target block can be used as a temporary. That's because such a register
                // can only be the source of a move but not a target, and any such move will
                // already be scheduled by the time we have to use the temporary because we
                // make sure to only use it when all remaining unscheduled moves form cycles.
                //
                // The target of a store can also be used as a temporary, but if there is a
                // move targeting that register, that move must be scheduled last. We don't
                // bother with this.
                //
                // In the worst case, we will convert a single unscheduled move into a store
                // and load pair in order to obtain the temporary.

                SirReg *tmp = 0;
                SirOp *store_emitted_to_obtain_tmp = 0;

                if (loads.count) {
                    Auto load = array_get(&loads, 0);
                    Auto bind = get_op_reg_bind(ra, load);
                    tmp = array_get(&bind->inputs, 0);
                } else {
                    array_iter (reg, &ra->public->registers) if (reg->alive_at_end_of_edge != edge_id) { tmp = reg; break; }
                }

                while (moves.count) {
                    Bool scheduled_a_move = false;

                    array_iter (move, &moves) {
                        Auto bind = get_op_reg_bind(ra, move);
                        Auto dst  = array_get(&bind->outputs, 0);
                        Auto src  = array_get(&bind->inputs, 0);

                        if (! (dst->flags & REG_IS_MOVE_SRC)) {
                            src->flags &= ~REG_IS_MOVE_SRC;
                            scheduled_a_move = true;
                            array_push(&moves_ordered, move);
                            array_remove_fast(&moves, ARRAY_IDX);
                            break;
                        }
                    }

                    if (! scheduled_a_move) { // All the moves form cycles.
                        Auto move        = array_get_last(&moves);
                        Auto move_bind   = get_op_reg_bind(ra, move);
                        Auto move_dst    = array_get(&move_bind->outputs, 0);
                        Auto move_src    = array_get(&move_bind->inputs, 0);
                        move_src->flags &= ~REG_IS_MOVE_SRC;

                        if (tmp) {
                            Auto op = alloc_op(ra, SIR_OP_REG_MOVE, move->type);
                            array_push(&moves_ordered, op);
                            Auto b = get_op_reg_bind(ra, op);
                            array_set(&b->inputs, 0, move_src);
                            array_set(&b->outputs, 0, tmp);
                            array_set(&move_bind->inputs, 0, tmp);
                        } else {
                            tmp = move_dst;
                            moves.count--;
                            store_emitted_to_obtain_tmp = alloc_op(ra, SIR_OP_REG_STORE, move->type);
                            array_push(&stores, store_emitted_to_obtain_tmp);
                            Auto b = get_op_reg_bind(ra, store_emitted_to_obtain_tmp);
                            array_set(&b->inputs, 0, move_src);
                        }
                    }
                }

                if (store_emitted_to_obtain_tmp) {
                    Auto type = store_emitted_to_obtain_tmp->type;
                    Auto load = alloc_op(ra, SIR_OP_REG_LOAD, type);
                    Auto bind = get_op_reg_bind(ra, load);
                    array_push(&loads, load);
                    array_set(&bind->inputs, 0, tmp);
                    array_push(&load->args, store_emitted_to_obtain_tmp); // The special link arg.
                }
            }

            // 3. Insert the ops into the CFG (stores go first, then moves, then loads):
            if (stores.count || moves_ordered.count || loads.count) {
                Auto dst = sir_edge_split(ra->public->fn, block, succ, SIR_BLOCK_REG_SPLIT);
                array_iter (store, &stores)       sir_op_add_to_block(dst, store);
                array_iter (move, &moves_ordered) sir_op_add_to_block(dst, move);
                array_iter (load, &loads)         sir_op_add_to_block(dst, load);
            }
        }
    }
}

static Void init_live_ranges (RegAlloc *ra) {
    array_iter (block, &ra->public->fn->blocks) {
        Auto prev = ra->last_pos;
        ra->last_pos += block->ops.count;
        assert_always(prev <= ra->last_pos);
    }

    Auto pos = ra->last_pos;
    assert_dbg(pos != UINT32_MAX); // This algorithm requires that 1 pos bigger than all others is reserved.

    #define get_current_live_range(INFO, POS) ({\
        def1(info, INFO);\
        if (info->ranges.count == 0) { LiveRange r = {POS,POS}; array_push(&info->ranges, r); }\
        array_ref_last(&info->ranges);\
    })

    #define push_live_range(INFO, START, END) ({\
        def1(info, INFO);\
        Auto current = get_current_live_range(info, END);\
        if (END < (current->start - 1))  { LiveRange r = {START,END}; array_push(&info->ranges, r); }\
        else if (START < current->start) { current->start = START; }\
    })

    array_iter_back (block, &ra->public->fn->blocks) {
        U32 block_start = pos - block->ops.count + 1;

        array_iter (op, &block->live_out) push_live_range(get_info(ra, op), block_start, pos);

        array_iter_back (op, &block->ops) {
            Auto info        = get_info(ra, op);
            Auto inputs      = sir_op_get_inputs(op);
            Auto outputs     = sir_op_get_outputs(op);
            Auto constraints = get_constraints(ra, op);

            if (op->flags & SIR_OP_SELF_IS_REG) {
                Auto range = get_current_live_range(info, pos);
                range->start = pos + 1;
                Auto c = &constraints->self;
                if (c->tag == SIR_RC_ONLY && c->reg->last_preferrer_pos == 0) c->reg->last_preferrer_pos = pos;
            }

            array_iter (it, &outputs) {
                Auto range = get_current_live_range(get_info(ra, it), pos);
                range->start = pos + 1;
                Auto c = array_ref(&constraints->outputs, ARRAY_IDX);
                if (c->tag == SIR_RC_ONLY && c->reg->last_preferrer_pos == 0) c->reg->last_preferrer_pos = pos;
            }

            array_iter (it, &inputs) {
                push_live_range(get_info(ra, it), block_start, pos);
                Auto c = array_ref(&constraints->inputs, ARRAY_IDX);
                if (c->tag == SIR_RC_ONLY && c->reg->last_preferrer_pos == 0) c->reg->last_preferrer_pos = pos;
            }

            info->pos = pos--;
        }
    }

    assert_dbg(pos == 0); // This algorithm requires that 1 pos smaller than all others is reserved.
}

static Void init_reg_constraints (RegAlloc *ra) {
    array_increase_count(&ra->constraints, ra->public->fn->next_op_id, true);

    array_iter (block, &ra->public->fn->blocks) {
        array_iter (op, &block->ops) {
            Auto inputs      = sir_op_get_inputs(op).count;
            Auto outputs     = sir_op_get_outputs(op).count;
            Auto constraints = array_ref(&ra->constraints, op->id);

            if (inputs + outputs) {
                SirRegConstraint *buf      = mem_alloc(ra->mem, SirRegConstraint, .zeroed=true, .size=(inputs + outputs)*sizeof(SirRegConstraint));
                constraints->outputs.data  = buf;
                constraints->outputs.count = outputs;
                constraints->inputs.data   = buf+outputs;
                constraints->inputs.count  = inputs;
            }

            ra->public->init_constraints(ra->public, op, constraints);
        }
    }
}

SirReg *sir_make_reg (SirRegAlloc *ra, Mem *mem, SirRegId id, String name, Bool is_callee_saved) {
    Auto reg = mem_new(mem, SirReg);
    reg->id = id;
    reg->name = name;
    array_init(&reg->ops, mem);
    array_init(&reg->clobbers, mem);
    if (is_callee_saved) reg->flags |= REG_IS_CALLEE_SAVED;
    return reg;
}

Void sir_reg_add_clobber (SirReg *reg, SirOp *op) {
    array_push(&reg->clobbers, op);
}

SirRegId sir_reg_id (SirReg *reg) {
    return reg->id;
}

String sir_reg_name (SirReg *reg) {
    return reg->name;
}

Void sir_alloc_regs (SirRegAlloc *public) {
    assert_static(SIR_RC_ANY == 0);
    assert_dbg(public->registers.count > 2);
    assert_dbg(public->tmp_reg0 != public->tmp_reg1);
    assert_dbg(array_has(&public->registers, public->tmp_reg0));
    assert_dbg(array_has(&public->registers, public->tmp_reg1));
    assert_dbg(public->dummy_reg && !array_has(&public->registers, public->dummy_reg));

    Auto ra = mem_new(public->fn->mem, RegAlloc);
    ra->pos = 1;
    ra->mem = public->fn->mem;
    ra->public = public;
    array_init(&ra->infos, ra->mem);
    array_init(&ra->tmp_op_buf, ra->mem);
    array_init(&ra->constraints, ra->mem);
    array_init(&ra->block_reg_binds, ra->mem);
    array_init(&ra->public->used_callee_saved_regs, public->fn->mem);
    array_init(&public->bindings, public->fn->mem);
    array_init(&public->used_callee_saved_regs, public->fn->mem);

    array_increase_count(&ra->block_reg_binds, public->fn->next_block_id, true);
    array_increase_count(&ra->infos, public->fn->next_op_id, true);
    array_iter (info, &ra->infos, *) array_init(&info->ranges, ra->mem);

    {
        Auto n = public->fn->next_op_id;
        SirOpRegBind *binds = mem_alloc(public->fn->mem, SirOpRegBind, .zeroed=true, .size=(n * sizeof(SirOpRegBind)));
        array_increase_count(&ra->public->bindings, n, false);
        array_iter (it, &ra->public->bindings, *) *it = &binds[ARRAY_IDX];
    }

    init_reg_constraints(ra);
    sir_do_liveness_analysis(public->fn);
    init_live_ranges(ra);
    allocate_registers(ra);
    fix_bind_mismatch_between_edges(ra);

    array_iter (reg, &public->registers) {
        if ((reg->flags & REG_IS_CALLEE_SAVED) && (reg->flags & REG_WAS_USED)) {
            array_push(&public->used_callee_saved_regs, reg);
        }
    }
}
