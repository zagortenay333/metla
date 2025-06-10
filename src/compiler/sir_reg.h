#pragma once

// =============================================================================
// Overview:
// ---------
//
// This module is responsible for performing register allocation. It
// requires that the input IR is not in SSA form.
//
// The register allocator might have to insert SIR_OP_[LOAD|STORE|MOVE]
// instructions into the control flow graph and it might have to split
// basic block edges to insert these instructions.
//
// Usage example:
// --------------
//
// Allocate a SirRegAlloc struct and init it's input fields. After that
// call sir_alloc_regs() on this struct which allocates the registers
// and stores the result into the output fields of SirRegAlloc.
//
//     Auto ra = mem_new(mem, SirRegAlloc);
//     ra->fn = fn;
//     ra->is_compatible = reg_is_compatible;
//     ra->init_constraints = init_reg_constraints;
//
//     array_push(&ra->registers, sir_make_reg(ra, mem, RAX, str("rax"), false));
//     array_push(&ra->registers, sir_make_reg(ra, mem, RDI, str("rdi"), false));
//     ...
//
//     ra->tmp_reg0  = R[TMP0]; // R maps tags to SirReg*. Implement yourself.
//     ra->tmp_reg1  = R[TMP1];
//     ra->dummy_reg = sir_make_reg(ra, mem, NIL, str("nil"), false);
//
//     sir_alloc_regs(ra);
//
//     Auto binds = array_get(&ra->bindings, op->id);
//
// See also the comments on the SirRegAlloc struct below.
// =============================================================================

#include "compiler/sir.h"

typedef U32 SirRegId;

istruct (SirReg);
istruct (SirRegAlloc);

istruct (SirOpRegBind) {
    SirReg *self;           // 0 if SIR_OP_SELF_IS_REG not set.
    Slice(SirReg*) inputs;  // Parallel to sir_op_get_inputs().
    Slice(SirReg*) outputs; // Parallel to sir_op_get_outputs().
};

ienum (SirRegConstraintTag, U8) {
    SIR_RC_ANY,          // Use any register.
    SIR_RC_SKIP,         // Use the dummy register.
    SIR_RC_ONLY,         // Use only the given register.
    SIR_RC_ANY_EXCEPT,   // Use any register except the given one.
    SIR_RC_SAME_AS_ARG0, // Use register bound to first arg. Only for SirOpRegConstraints.self.
};

istruct (SirRegConstraint) {
    SirRegConstraintTag tag;
    SirReg *reg;
};

istruct (SirOpRegConstraints) {
    SirRegConstraint self;
    Slice(SirRegConstraint) inputs;  // Parallel to sir_op_get_inputs().
    Slice(SirRegConstraint) outputs; // Parallel to sir_op_get_outputs().
};

istruct (SirRegAlloc) {
    SirFn *fn;

    // User provided context pointer.
    Void *data;

    // Use sir_make_reg() to allocate the registers and insert
    // them yourself into this array. Any register in here can
    // can be used by the allocator.
    Array(SirReg*) registers;

    // The tmp_regs must appear in the above registers array.
    // You use these by setting the SIR_OP_USES_TMP_REG flags
    // on ops inside the init_reg_constraints() function.
    //
    // When the register allocator encounters an op with that
    // flag it will make sure the op doesn't read or write to
    // the register. This enables you to use that register as
    // a temporary later on when generating code for this op.
    SirReg *tmp_reg0;
    SirReg *tmp_reg1;

    // This register should not appear in the above registers
    // array. It's used in situations where no register can be
    // bound. For example, the dummy register will be bound to
    // arguments which have a SIR_RC_SKIP constraint.
    SirReg *dummy_reg;

    // This function indicates whether the register can be bound
    // to the op. Maybe the type of the op is float, and you only
    // want to use float registers.
    Bool (*is_compatible) (SirRegAlloc *, SirOp *, SirReg *);

    // The purpose of this function is to:
    //
    //     1. Potentially modify the SirOpRegConstraints struct
    //        that is passed to it. Note that the allocator has
    //        set all constraints to SIR_RC_ANY before calling
    //        this function.
    //
    //     2. Potentially set the SIR_OP_USES_TMP_REG flags on
    //        the given op. See comment about tmp_regs above.
    //
    //     3. Call the sir_reg_add_clobber() function to mark
    //        which registers the op clobbers if any.
    //
    Void (*init_constraints) (SirRegAlloc *, SirOp *, SirOpRegConstraints *);

    // This array is initted and filled by sir_alloc_regs().
    //
    // The register allocator does not emit spills and loads of
    // used callee saved registers at function start or end. It
    // only lists them in this array.
    Array(SirReg*) used_callee_saved_regs;

    // This array is initted and filled by sir_alloc_regs().
    //
    // Index into this array with SirOpId to see which registers
    // were assigned to the arguments of the SirOp. The arrays in
    // SirOpRegBind are parallel to arrays you obtain by calling
    // the sir_op_get_(inputs|outputs) functions.
    //
    // The instructions emitted by the register allocator itself
    // SIR_OP_(REG_STORE|REG_LOAD|REG_MOVE) also have entries in
    // here but since they don't have virtual register arguments,
    // the arrays in their SirOpRegBind are not parallel to them.
    //
    // If a SirOp has more arguments than there are registers, the
    // register allocator will bind arguments to the dummy register
    // once it runs out of registers. This dummy binding indicates
    // the argument is on the stack at that point.
    Array(SirOpRegBind*) bindings;
};

SirReg     *sir_make_reg        (SirRegAlloc *, Mem *, SirRegId, String name, Bool is_callee_saved);
Void        sir_alloc_regs      (SirRegAlloc *);
Void        sir_reg_add_clobber (SirReg *, SirOp *);
SirRegId    sir_reg_id          (SirReg *);
String      sir_reg_name        (SirReg *);
