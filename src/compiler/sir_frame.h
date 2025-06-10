#pragma once

// =============================================================================
// Overview:
// ---------
//
// This module determines the low-level layout of stack frames. It
// assigns stack slots to values that are spilled by the register
// allocator and to those that must be on the stack. It will also
// reserve space for callee saved register that have been used.
//
// Stack slots:
// ------------
//
// Stack slots are just offsets into the stack frame from lower
// addresses. On x64 this means that RSP + stack_slot = address.
//
// We differentiate between "spill" and "object" slots:
//
//     1. Object slots are assigned to values that are on the stack
//        inherently. That is, ops with the SIR_OP_IS_STACK_OBJECT
//        flag set and any SIR_OP_FN_ARG that is passed in memory.
//
//     2. Spill slots are assigned to SirOps that represent virtual
//        registers (those with SIR_OP_SELF_IS_REG flag set) which
//        got spilled by the register allocator.
//
// Some SirOps can have an object and spill slot assigned to them at
// the same time. For example, SIR_OP_STACK_OBJECT represents both a
// stack object and a virtual register that contains the address of
// that object. It will have an object slot assigned for the stack
// object it represents, and it might have a spill slot assigned for
// the virtual register it represents in case that one got spilled
// by the register allocator.
//
// Frame layout:
// -------------
//
// The layout of a stack frame looks like this:
//
//     +----------------+
//     | return address |
//     |----------------| Below callee frame, above caller frame.
//     | padding1       |
//     |----------------|
//     | main area      |
//     |----------------|
//     | padding2       |
//     |----------------|
//     | argN           |
//     | ...            |
//     | arg0           |
//     +----------------+
//
// =============================================================================
#include "compiler/sir.h"
#include "compiler/sir_reg.h"

istruct (SirStackFrame);

#define SIR_NO_STACK_SLOT UINT32_MAX // Returned if a SirOp wasn't assigned any slot.

SirStackFrame *sir_stack_frame_new       (SirFn *, SirRegAlloc *);
U32            sir_get_spill_stack_slot  (SirStackFrame *, SirOp *);
U32            sir_get_object_stack_slot (SirStackFrame *, SirOp *);
U32            sir_get_frame_size        (SirStackFrame *);
