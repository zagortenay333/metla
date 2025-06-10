#if 1
#include "compiler/abi.h"
#include "compiler/sir_frame.h"

istruct (SirStackFrame) {
    Abi *abi;
    SirFn *fn;
    SirRegAlloc *ra;
    U32 frame_size;
    U32 arg_area_size;
    U32 main_area_size;
    Array(SirOp*) fn_args;
    Map(SirOpId, U32) spill_slots;
    Map(SirOpId, U32) object_slots;
    Array(SirOpId) spill_slot_patch_list;
    Array(SirOpId) object_slot_patch_list;
};

// We don't try to reuse stack slots, we just bump allocate.
static U32 alloc_slot (SirStackFrame *frame, Type *type) {
    Auto abi = abi_of_obj(frame->abi, type);
    frame->main_area_size += padding_to_align(frame->main_area_size, abi.align);
    Auto slot = frame->main_area_size;
    frame->main_area_size += abi.size;
    return slot;
}

static Void assign_object_slot (SirStackFrame *frame, SirOp *op, U32 slot) {
    map_add(&frame->object_slots, op->id, slot);
}

static Void assign_spill_slot_and_patch (SirStackFrame *frame, SirOp *op, U32 slot) {
    op->flags |= SIR_OP_SELF_WAS_SPILLED;
    map_add(&frame->spill_slots, op->id, slot);
    array_push(&frame->spill_slot_patch_list, op->id);
}

static Void assign_object_slot_and_patch (SirStackFrame *frame, SirOp *op, U32 slot) {
    map_add(&frame->object_slots, op->id, slot);
    array_push(&frame->object_slot_patch_list, op->id);
}

static Void try_assign_slot (SirStackFrame *frame, SirOp *op) {
    if (op->flags & SIR_OP_IS_STACK_OBJECT) {
        assert_dbg(op->type->tag == TYPE_POINTER);
        Auto t = ((TypePointer*)op->type)->pointee;
        Auto slot = alloc_slot(frame, t);
        assign_object_slot_and_patch(frame, op, slot);
    }

    switch (op->tag) {
    case SIR_OP_CALL: {
        // We must calculate the arg area size necessary for this call.

        Auto ast = sir_op_get_value(frame->fn, op).ast;
        Auto type = (TypeFn*)sem_get_type(frame->fn->sem, ast);
        Auto fn_abi = abi_of_fn(frame->abi, frame->fn->mem, type);

        U32 arg_area_size = 0;
        Auto inputs = sir_op_get_inputs(op);
        if (! (op->flags & SIR_OP_IS_DIRECT_CALL)) inputs.count--; // Skip the last arg (the fn pointer) in the loop below.

        array_iter (arg, &inputs) {
            Auto r = array_get(&fn_abi->inputs, ARRAY_IDX);
            Auto t = abi_can_be_in_reg(frame->abi, arg->type) ? arg->type : ((TypePointer*)arg->type)->pointee;

            if (r == ABI_REG_MEM) {
                Auto obj_abi   = abi_of_obj(frame->abi, t);
                obj_abi.align  = max(frame->abi->stack_arg_min_align, obj_abi.align);
                arg_area_size += padding_to_align(arg_area_size, obj_abi.align);
                arg_area_size += max(frame->abi->stack_arg_min_size, obj_abi.size);
            }
        }

        frame->arg_area_size = max(arg_area_size, frame->arg_area_size);
    } break;

    case SIR_OP_REG_LOAD:
    case SIR_OP_REG_STORE: {
        // Make sure you read the description of these instructions
        // in the sir_ops.h file to understand what this code does.

        if (op->flags & SIR_OP_SELF_WAS_SPILLED) break; // Already assigned a slot to this group.

        Auto arg = array_get(&op->args, 0);

        if (!arg || (arg->tag != SIR_OP_REG_STORE && arg->tag != SIR_OP_REG_LOAD)) {
            // The current op is the group link.
            Auto slot = alloc_slot(frame, op->type);
            assign_spill_slot_and_patch(frame, op, slot);
            if (arg) assign_spill_slot_and_patch(frame, arg, slot);
        } else if (arg->flags & SIR_OP_SELF_WAS_SPILLED) {
            Auto slot = sir_get_spill_stack_slot(frame, arg);
            assign_spill_slot_and_patch(frame, op, slot);
        } else {
            Auto slot = alloc_slot(frame, op->type);
            Auto a = array_get(&arg->args, 0);
            assign_spill_slot_and_patch(frame, op, slot);
            assign_spill_slot_and_patch(frame, arg, slot);
            if (a) assign_spill_slot_and_patch(frame, a, slot);
        }
    } break;

    default: break;
    }
}

static Void assign_slots (SirStackFrame *frame) {
    //
    // Allocate main area:
    //
    array_iter (block, &frame->fn->blocks) {
        array_iter (op, &block->ops) {
            if (op->tag == SIR_OP_FN_ARG) array_push(&frame->fn_args, op);
            try_assign_slot(frame, op);
        }
    }

    U8 pointer_size = frame->abi->pointer_size;
    U8 frame_align  = frame->abi->stack_frame_align;

    frame->main_area_size += frame->ra->used_callee_saved_regs.count * frame->abi->register_size;
    frame->main_area_size += padding_to_align(pointer_size + frame->main_area_size, frame_align); // padding1
    frame->frame_size      = frame->arg_area_size + frame->main_area_size;

    U32 padding2 = padding_to_align(pointer_size + frame->frame_size, frame_align);
    frame->frame_size += padding2;
    assert_dbg(((frame->frame_size + pointer_size) % frame_align) == 0);

    //
    // Patch the slot positions:
    //
    array_iter (id, &frame->spill_slot_patch_list) {
        Bool found; Auto slot = map_uadd(&frame->spill_slots, id, &found);
        *slot += padding2 + frame->arg_area_size;
    }

    array_iter (id, &frame->object_slot_patch_list) {
        Bool found; Auto slot = map_uadd(&frame->object_slots, id, &found);
        *slot += padding2 + frame->arg_area_size;
    }

    //
    // Allocate arguments area:
    //
    U32 arg_area_size = 0;

    array_iter (arg, &frame->fn_args) {
        assert_dbg(arg->tag == SIR_OP_FN_ARG);

        Auto idx = sir_op_get_value(frame->fn, arg).u32;
        Auto reg = array_get(&frame->fn->abi->inputs, idx);

        if (reg == ABI_REG_MEM) {
            Type *t  = abi_can_be_in_reg(frame->abi, arg->type) ? arg->type : ((TypePointer*)arg->type)->pointee;
            Auto abi = abi_of_obj(frame->abi, t);

            abi.size  = max(frame->abi->stack_arg_min_size, abi.size);
            abi.align = max(frame->abi->stack_arg_min_align, abi.align);

            arg_area_size += padding_to_align(arg_area_size, abi.align);
            assign_object_slot(frame, arg, frame->frame_size + pointer_size + arg_area_size);
            arg_area_size += abi.size;
        }
    }
}

SirStackFrame *sir_stack_frame_new (SirFn *fn, SirRegAlloc *ra) {
    Auto frame = mem_new(fn->mem, SirStackFrame);
    frame->ra = ra;
    frame->fn = fn;
    frame->abi = fn->abi->abi;
    array_init(&frame->fn_args, fn->mem);
    array_init(&frame->spill_slot_patch_list, fn->mem);
    array_init(&frame->object_slot_patch_list, fn->mem);
    map_init(&frame->spill_slots, fn->mem);
    map_init(&frame->object_slots, fn->mem);
    assign_slots(frame);
    return frame;
}

U32 sir_get_frame_size (SirStackFrame *frame) {
    return frame->frame_size;
}

U32 sir_get_object_stack_slot (SirStackFrame *frame, SirOp *op) {
    U32 slot; Bool found = map_get(&frame->object_slots, op->id, &slot);
    return found ? slot : SIR_NO_STACK_SLOT;
}

U32 sir_get_spill_stack_slot (SirStackFrame *frame, SirOp *op) {
    U32 slot; Bool found = map_get(&frame->spill_slots, op->id, &slot);
    return found ? slot : SIR_NO_STACK_SLOT;
}
#endif
