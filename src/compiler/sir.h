#pragma once

// =============================================================================
// Overview:
// ---------
//
// Sir is a classical IR made up of a control flow graph (SirFn)
// whose nodes are basic blocks (SirBlock) where blocks contain
// instructions (SirOp) in three-address form. The instructions
// use virtual registers.
//
// SirOps:
// -------
//
// In Sir we don't have separate data structures for virtual registers
// and instructions. A given SirOp can represent a virtual register, an
// instruction, both, neither or some combo of these. For example:
//
//     SIR_OP_JUMP   is just an instruction.
//     SIR_OP_FN_ARG is just a virtual register containing a fn argument.
//     SIR_OP_ADD    is an add instruction and register holding the result.
//     SIR_OP_PHI    is a virtual instruction used when Sir is in SSA form.
//     SIR_OP_STORE  is an instruction and special register modeling memory.
//
// SirOps can have 3 kinds of arguments: special, input, output. Input
// and output arguments refer to virtual registers that an instruction
// is reading and/or writing. Special args are used to create ad hoc
// data structures within the IR such as the memory dependency graph.
//
// All 3 kinds of arguments appear in the same array SirOp.args in the
// order specials, outputs, inputs. For more info about the SirOp.args
// array check out the two functions sir_op_get_inputs/outputs.
//
// Memory dependency modeling:
// ---------------------------
//
// We want to know whether two given instructions are touching the
// same memory. In order to do that we have to create some kind of
// a data structure that tracks which ops have these dependencies
// between them.
//
// In this IR we use a trick to implement this dependency system.
// We pretend that all memory fits into a single virtual register.
// The variable this virtual register is bound to during a scope
// lookup is SIR_VAR_MEMORY.
//
// The virtual register that will represent memory at the start of
// a procedure is introduced with the SIR_OP_MEMORY.
//
// Any SirOp that touches memory is treated like it's reading this
// memory register, and it will have as it's first special argument
// that memory register.
//
// Any SirOp that modifies memory is treated like it's writing to
// that register, and thus just like with regular SSA variables we
// rebind the SIR_VAR_MEMORY variable to this new SirOp. That is,
// now there will be a new current version of memory represented
// by this memory register.
//
// Also, just like with SSA variables, it's possible that during a
// scope lookup we introduces a phi op into a block. Specifically,
// this will be a SIR_OP_PHI_MEM. This phi represents multiple
// versions of memory converging on a basic block.
//
// The initial construction of Sir creates a pessimistic dependency
// graph. Each instruction that touches memory will depend on the
// previous instruction (up the control flow graph) that touches
// memory. The function relax_memory_dependencies() defined in the
// sir_optimizer.h module is used to fix this.
// =============================================================================
#include "compiler/interns.h"
#include "compiler/abi.h"
#include "compiler/sem.h"
#include "compiler/ast.h"
#include "compiler/vm.h"

typedef U32 SirOpId;
typedef U32 SirBlockId;

istruct (Compiler);
istruct (SirRegAlloc);

istruct (SirOp);
istruct (SirFn);
istruct (SirBlock);

array_typedef(SirOp*, SirOp);
array_typedef(SirBlock*, SirBlock);
array_typedef(SirFn*, SirFn);

// A SirVar connects virtual register which represent different
// versions of it. It is used during Sir construction and later
// by sir_update_phi(), so it's mostly an internal thing.
typedef U32 SirVar;
typedef Array(struct { SirVar var; SirOp *val; }) SirSsaScope;

istruct (SirFn) {
    Mem *mem;
    Sem *sem;
    AbiFn *abi;
    AstFn *ast;
    Compiler *cc;
    Interns *interns;
    Bool in_ssa_form;
    SirOpId next_op_id;
    SirBlockId next_block_id;
    SirBlock *entry_block;
    SirBlock *exit_block;
    ArraySirBlock blocks;
    SirSsaScope ssa_scope;
    Map(SirOpId, Value) op_data;
};

#define EACH_SIR_BLOCK(X)\
    X(SIR_BLOCK_NORMAL)\
    X(SIR_BLOCK_THEN)\
    X(SIR_BLOCK_ELSE)\
    X(SIR_BLOCK_JOIN)\
    X(SIR_BLOCK_EXIT)\
    X(SIR_BLOCK_ENTRY)\
    X(SIR_BLOCK_SSA_SPLIT)\
    X(SIR_BLOCK_REG_SPLIT)\
    X(SIR_BLOCK_LOOP_START)\
    X(SIR_BLOCK_LOOP_BREAK)\
    X(SIR_BLOCK_UNREACHABLE)\
    X(SIR_BLOCK_LOOP_CONTINUE)

fenum (SirBlockFlags, U16) {
    SIR_BLOCK_IS_DEAD           = flag(0), // Block can be deleted.
    SIR_BLOCK_IS_VISITED        = flag(1), // A generic flag that can be used by any algorithm.
    SIR_BLOCK_DEFINES_OP        = flag(2), // Only used by liveness analysis.
    SIR_BLOCK_IS_REACHABLE      = flag(3), // Only used by dead code elimination.
    SIR_BLOCK_ALL_PREDS_KNOWN   = flag(4), // Only used during Sir construction. Means that all predecessors are known.
    SIR_BLOCK_WAS_SCCP_EVALED   = flag(5), // Only used by the sccp algorithm.
    SIR_BLOCK_PHIS_NEED_UPDATE  = flag(6), // The sir_update_phi() must be called on all phis in this block.
    SIR_BLOCK_UPWARD_EXPOSES_OP = flag(7), // Only used by liveness analysis.
};

ienum (SirBlockTag, U32) {
    #define X(tag) tag,
        EACH_SIR_BLOCK(X)
    #undef X
};

istruct (SirBlock) {
    SirBlockId id;
    SirBlockTag tag;
    SirBlockFlags flags;
    U32 scratch;
    SirFn *fn;
    SirBlock *idom;
    ArraySirOp ops;
    ArraySirBlock preds;
    ArraySirBlock succs;
    ArraySirOp live_in;
    ArraySirOp live_out;

    // SSA specific stuff:
    SirOp *mem_phi;
    ArraySirOp phis;
    SirSsaScope scope;
    ArraySirOp phi_scratch_buf;
    SirOp *phi_inserted_recursively;
};

fenum (SirOpFlags, U16) {
    SIR_OP_0                   = flag(0),  // A temporary flag to be used by any algorithm.
    SIR_OP_1                   = flag(1),  // A temporary flag to be used by any algorithm.
    SIR_OP_SELF_IS_REG         = flag(2),  // Op itself represents a virtual reg.
    SIR_OP_USES_TMP_REG0       = flag(3),  // Only used by reg allocator. Reserves register "tmp0" for this op.
    SIR_OP_USES_TMP_REG1       = flag(4),  // Only used by reg allocator. Reserves register "tmp1" for this op.
    SIR_OP_DEAD_IF_UNUSED      = flag(5),  // If not set, sir_try_delete_op() must handle this op specially.
    SIR_OP_TOUCHES_MEMORY      = flag(6),  // Op reads and/or writes to memory.
    SIR_OP_IS_DIRECT_CALL      = flag(7),  // Only for SIR_OP_CALL.
    SIR_OP_IS_STACK_OBJECT     = flag(8),  // Op represents a new stack object. For example: SIR_OP_STACK_OBJECT, SIR_OP_CALL_OUTPUT_MEM, ...
    SIR_OP_MODIFIES_MEMORY     = flag(9),  // Op writes to memory.
    SIR_OP_SELF_WAS_SPILLED    = flag(10), // Only used by stack slot allocator.
    SIR_OP_LIVENESS_COMPUTED   = flag(11), // Only used by liveness analysis.
    SIR_OP_DEFAULT_INITIALIZED = flag(12), // A SIR_OP_CONST or SIR_OP_STACK_OBJECT that must be initted with the default value of it's type.
    SIR_OP_INIT_BY_MEMCPY      = flag(13), // A SIR_OP_STACK_OBJECT to be initted with the object in Value.ptr.
};

ienum (SirOpTag, U32) {
    #define X(tag, ...) tag,
    #include "sir_ops.h"
    SIR_OP_TAG_COUNT
};

istruct (SirOp) {
    Type *type;
    SirOpId id;
    SirOpTag tag;
    SirOpFlags flags;
    SirBlock *block;
    ArraySirOp args;
    ArraySirOp users;
};

extern Char      *sir_op_tag_to_str        [SIR_OP_TAG_COUNT];
extern Char      *sir_block_tag_to_str     [];
extern SirOpFlags sir_op_get_default_flags [SIR_OP_TAG_COUNT];

SirFn      *sir_fn_new               (Mem *, Interns *, Sem *, AstFn *, Abi *);
Void        sir_check_integrity      (SirFn *);
SliceSirOp  sir_op_get_inputs        (SirOp *);
SliceSirOp  sir_op_get_outputs       (SirOp *);
Void        sir_op_add_to_block      (SirBlock *, SirOp *);
SirOp      *sir_op_alloc             (SirFn *, SirOpTag, Type *);
SirOp      *sir_op_emit              (SirFn *, SirBlock *, SirOpTag, Type *);
Void        sir_op_set_value         (SirFn *, SirOp *, Value);
Value       sir_op_get_value         (SirFn *, SirOp *);
Void        sir_op_set_arg           (SirOp *, U32 arg_idx, SirOp *new_arg);
Void        sir_op_remove_args       (SirOp *);
Void        sir_op_delete            (SirFn *, SirOp *);
Bool        sir_op_try_delete        (SirFn *, SirOp *);
SirBlock   *sir_edge_split           (SirFn *, SirBlock *from, SirBlock *to, SirBlockTag);
Void        sir_update_idom          (SirBlock *);
SirBlock   *sir_get_block            (SirFn *, SirBlockId);
Bool        sir_update_phi           (SirFn *, SirOp *phi);
Void        sir_update_phis          (SirFn *, SirBlock *);
Void        sir_do_liveness_analysis (SirFn *);
Void        sir_leave_ssa_form       (SirFn *);
Void        sir_reverse_postorder    (SirFn *);
Void        sir_to_dot               (SirFn *, Mem *, String filepath, SirRegAlloc *);
Void        sir_to_dot_if_marked     (SirFn *, Mem *, String filepath, SirRegAlloc *);
