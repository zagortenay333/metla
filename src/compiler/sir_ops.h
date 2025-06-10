// =============================================================================
// Overview:
// ---------
//
// This whole file is an X list. Use it as follows:
//
//     #define X(tag, ...) foo(tag)
//     #include "sir_ops.h"
//
// The X macro is undefined by this file and it's signature is:
//
// X(
//     tag:            SirOpTag,
//     n_special_args: U16, // Use -1 to indicate variable length.
//     n_output_args:  U16, // Use -1 to indicate variable length.
//     n_input_args:   U16, // Use -1 to indicate variable length.
//     default_flags:  SirOpFlags
// )
//
// Nomenclature in comments describing ops:
// ----------------------------------------
//
// - a0..N  refers to arguments
// - "self" refers to the virtual register that is the SirOp itself.
// - "mem"  refers to the register modeling memory. See top comment in sir.c.
// - Value  refers to a const value attached to the op. See sir_op_get_value().
// =============================================================================
#define R SIR_OP_SELF_IS_REG
#define D SIR_OP_DEAD_IF_UNUSED
#define S SIR_OP_IS_STACK_OBJECT

// =============================================================================
// Generic SirOps:
// =============================================================================
X(SIR_OP_ADD, 0, 0, 2, R|D) // self=(a0 + a1)
X(SIR_OP_BITWISE_AND, 0, 0, 2, R|D) // self=(a0 & a1)
X(SIR_OP_BITWISE_NOT, 0, 0, 1, R|D) // self=(~ a0)
X(SIR_OP_BITWISE_OR, 0, 0, 2, R|D) // self=(a0 | a1)
X(SIR_OP_BITWISE_XOR, 0, 0, 2, R|D) // self=(a0 ~ a1)
X(SIR_OP_BRANCH, 0, 0, 1, 0) // If a0 is true, jump to first successor, else to second.
X(SIR_OP_CALL, 1, 0, -1, 0) // self=(mem; if fn returns, then self is also a new reg holding the returned value or the address of returned stack object)
                            // a0=mem a1..N=inputs
                            // Value.ast=(ast of called fn in case of direct call, else AstCall.lhs and aN+1=fn_address)
X(SIR_OP_CAST, 0, 0, 1, R|D) // self=cast(a0, self.type)
X(SIR_OP_CONST, 0, 0, 0, R|D) // self=Value
X(SIR_OP_DECREMENT, 0, 0, 1, R|D) // self=(a0 - 1)
X(SIR_OP_DIV, 0, 0, 2, R|D) // self=(a0 / a1)
X(SIR_OP_EQUAL, 0, 0, 2, R|D) // self=(a0 == a1)
X(SIR_OP_FN_ADDRESS, 0, 0, 0, R|D) // self=(address of a function) Value.ast=AstFn*
X(SIR_OP_FN_ARG, 0, 0, 0, R) // Value.u32=(arg index)
X(SIR_OP_GLOBAL_OBJECT, 0, 0, 0, R|D) // self=(address of a global data object) Value.ast=(ast of global)
X(SIR_OP_GREATER, 0, 0, 2, R|D) // self=(a0 > a1)
X(SIR_OP_GREATER_EQUAL, 0, 0, 2, R|D) // self=(a0 >= a1)
X(SIR_OP_INCREMENT, 0, 0, 1, R|D) // self=(a0 + 1)
X(SIR_OP_INDEX, 0, 0, 2, R|D) // self=(a0[a1]) The a1 reg contains a 64-bit value.
X(SIR_OP_LESS, 0, 0, 2, R|D) // self=(a0 < a1)
X(SIR_OP_LESS_EQUAL, 0, 0, 2, R|D) // self=(a0 <= a1)
X(SIR_OP_LOAD, 1, 0, 1, R|D) // self=(new reg holding loaded value) a0=mem a1=from
X(SIR_OP_MEMCPY, 1, 0, 2, 0) // self=mem a0=mem a1=to a2=from Copy from memory at address a2 to memory at address a1.
X(SIR_OP_MEMORY, 0, 0, 0, D) // The initial memory token at the start of a function.
X(SIR_OP_MOD, 0, 0, 2, R|D) // self=(a0 % a1)
X(SIR_OP_MUL, 0, 0, 2, R|D) // self=(a0 * a1)
X(SIR_OP_NEGATE, 0, 0, 1, R|D) // self=(-a0)
X(SIR_OP_NOP, 0, 0, 0, 0) // Mostly used for quick deletion.
X(SIR_OP_NOT, 0, 0, 1, R|D) // self=(! a0)
X(SIR_OP_NOT_EQUAL, 0, 0, 2, R|D) // self=(a0 != a1)
X(SIR_OP_OFFSET, 0, 0, 1, R|D) // self=(address: a0 + offset) Value.u32=offset
X(SIR_OP_PHI, -1, 0, 0, R|D) // Value.u32=SirVar a0..N=(special arguments)
X(SIR_OP_PHI_MEM, -1, 0, 0, D) // Value.u32=SirVar a0..N=(reaching mem versions)
X(SIR_OP_RETURN, 0, 0, -1, 0) // a0=(optional result) a1=(optional return address SIR_OP_FN_ARG)
X(SIR_OP_SHIFT_LEFT, 0, 0, 2, R|D) // self=(a0 >> a1)
X(SIR_OP_SHIFT_RIGHT, 0, 0, 2, R|D) // self=(a0 << a1)
X(SIR_OP_STACK_OBJECT, 0, 0, 0, R|D|S) // self=(address of new stack object) Value.ptr=(set if also SIR_OP_INIT_BY_MEMCPY is set)
X(SIR_OP_STORE, 1, 0, 2, 0) // self=mem a0=mem a1=to a2=from Copy from a2 to memory at address a1 + Value.u32.
X(SIR_OP_STRING_LITERAL, 0, 0, 0, R|D) // self=(address of a string literal object) Value.str=(the literal string)
X(SIR_OP_SUB, 0, 0, 2, R|D) // self=(a0 - a1)
X(SIR_OP_VALUE_ADDRESS, 0, 0, 1, R|D|S) // self=(address of new stack object holding the value in a0)

// =============================================================================
// We emit direct linux syscalls in the backend.
// =============================================================================
X(SIR_OP_LINUX_SYSCALL, 1, 0, -1, R) // self=result a0=mem Value.ast=AstFnLinux

// =============================================================================
// These ops are emitted when leaving SSA.
// =============================================================================
X(SIR_OP_COPY, 0, 0, 1, R|D) // self=(new reg holding same val as a0)
X(SIR_OP_MOVE, 0, 1, 1, 0) // a0=to a1=from Not emitted while in SSA since it overwrites the contents of a0.

// =============================================================================
// These SirOps are emitted by the register allocator only.
//
// They do not appear in the SirOp.users list.
//
// These ops do not have virtual registers as input or output arguments,
// only "physical" registers assigned by the register allocator. We use
// orN and irN below to refer to these physical register arguments.
//
// The set of REG_LOAD and REG_STORE SirOps applied to the same register
// are linked via their first special argument which is a REG_STORE or
// REG_LOAD from that set (called "link"). The first special arg of the
// link is either the the SirOp (virtual register) being spilled or 0
// in case it's not a virtual register that's being spilled but just a
// physical register.
// =============================================================================
X(SIR_OP_REG_MOVE, 0, 0, 0, 0) // or0=to ir0=from
X(SIR_OP_REG_LOAD, 1, 0, 0, 0) // a0=(SirOp being loaded or link or 0) ir0=(reg to load into)
X(SIR_OP_REG_STORE, 1, 0, 0, 0) // a0=(SirOp being loaded or link or 0) ir0=(reg to spill)

// =============================================================================
// These ops are x64 specific:
// =============================================================================
X(SIR_OP_X64_JCC, 0, 0, 0, 0) // Conditional jump. Value.U8=(condition code)
X(SIR_OP_X64_CMP, 0, 0, 2, 0) // "cmp a0 a1"
X(SIR_OP_X64_CMP_0, 0, 0, 1, 0) // "cmp a0"
X(SIR_OP_X64_CMP_0_JE, 0, 0, 1, 0) // "cmp a0 0; je"
X(SIR_OP_X64_CMP_0_JNE, 0, 0, 1, 0) // "cmp a0 0; je"

#undef R
#undef D
#undef S
#undef X
