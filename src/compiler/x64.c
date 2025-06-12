#include "compiler/x64.h"
#include "compiler/elf.h"
#include "base/string.h"
#include "sir_reg.h"
#include "sir_frame.h"

istruct (X64Abi) {
    Abi pub;
    Compiler *cc;
    Map(TypeId, AbiFn*) fn_abis;
    Map(TypeId, AbiObj) obj_abis;
    Map(AstId, U32) field_offsets;
};

istruct (SirX64) {
    Mem *mem;
    Abi *abi;
    Elf elf;
    SirFn *fn;
    SirRegAlloc *ra;
    SemProgram program;
    SirStackFrame *frame;
    Map(IString*, U8) string_literals;
};

#define GPR_COUNT 15

// This array maps RegTag to SirReg*.
// It's initialized by allocate_registers().
SirReg *R[GPR_COUNT + 2];

// X(RegTag, is_callee_saved, name, x64_reg_number)
//
// This is the list of general purpose registers.
//
// Note we don't include the RSP register here in order
// to prevent the register allocator from being able to
// use it. The RSP register is only used as a base when
// addressing the stack, so it only appears at the last
// minute when emitting machine code.
#define EACH_GP_REGISTER(X)\
    X(RAX, false, "rax", 0)\
    X(RCX, false, "rcx", 1)\
    X(RDX, false, "rdx", 2)\
    X(RBX, true,  "rbx", 3)\
    X(RBP, true,  "rbp", 5)\
    X(RSI, false, "rsi", 6)\
    X(RDI, false, "rdi", 7)\
    X(R08, false, "r08", 8)\
    X(R09, false, "r09", 9)\
    X(R10, false, "r10", 10)\
    X(R11, false, "r11", 11)\
    X(R12, true,  "r12", 12)\
    X(R13, true,  "r13", 13)\
    X(R14, true,  "r14", 14)\
    X(R15, true,  "r15", 15)

ienum (RegTag, U8) {
    RSP = 4, // Stack pointer.

    #define ADD_GPR_TAG(tag, _, __, n) tag = n,
    EACH_GP_REGISTER(ADD_GPR_TAG)

    NIL, // Dummy value indicating missing register.
    RIP, // Dummy value refering to instruction pointer.

    // Read the explanation in sir_reg_alloc.h about
    // temporary registers and what they are used for.
    TMP0 = R10,
    TMP1 = R11,
};

ienum (RegWidth, U8) {
    W8  = 8,
    W16 = 16,
    W32 = 32,
    W64 = 64,
};

ienum (SibScale, U8) {
    S1,
    S2,
    S4,
    S8,
};

ienum (RexBit, U8) {
    REX   = 0x40,
    REX_W = 0x48,
    REX_R = 0x44,
    REX_X = 0x42,
    REX_B = 0x41,
};

ienum (ConditionCode, U8) {
    CC_O   = 0x0,    // overflow
    CC_NO  = 0x1,    // no overflow
    CC_B   = 0x2,    // below
    CC_NAE = CC_B,   // neither above nor equal
    CC_NB  = 0x3,    // not below
    CC_AE  = CC_NB,  // above or equal
    CC_E   = 0x4,    // equal
    CC_Z   = CC_E,   // zero
    CC_NE  = 0x5,    // not equal
    CC_NZ  = CC_NE,  // not zero
    CC_BE  = 0x6,    // below or equal
    CC_NA  = CC_BE,  // not above
    CC_NBE = 0x7,    // neither below nor equal
    CC_A   = CC_NBE, // above
    CC_S   = 0x8,    // sign
    CC_NS  = 0x9,    // no sign
    CC_P   = 0xa,    // parity
    CC_PE  = CC_P,   // parity even
    CC_NP  = 0xb,    // no parity
    CC_PO  = CC_NP,  // parity odd
    CC_L   = 0xc,    // less
    CC_NGE = CC_L,   // neither greater nor equal
    CC_NL  = 0xd,    // not less
    CC_GE  = CC_NL,  // greater or equal
    CC_LE  = 0xe,    // less or equal
    CC_NG  = CC_LE,  // not greater
    CC_NLE = 0xf,    // neither less nor equal
    CC_G   = CC_NLE, // greater
};

fenum (OpBufFlags, U8) {
    ENSURE_SIB             = flag(0), // If the SIB field in ob is 0, add a 0 SIB.
    ENSURE_MODRM           = flag(1), // If the MODRM field in ob is 0, add a 0 MODRM.
    ENSURE_1B_DISPLACEMENT = flag(2), // If the displacement field in ob is 0, add a 1 byte 0 displacement.
    ENSURE_4B_DISPLACEMENT = flag(3), // If the displacement field in ob is 0, add a 4 byte 0 displacement.
};

// You can use this to encode most parts of an
// instruction out of order. Later you can emit
// the instruction by passing the OpBuf and an
// opcode to functions like emit_instruction().
istruct (OpBuf) {
    U8 rex;
    U8 sib;
    U8 modrm;
    OpBufFlags flags;
    U32 displacement;
};

#define ob_set_reg_op(ob, byte, offset_within_byte, reg, rex_bit) ({\
    if (is_extended(reg)) {\
        ob.rex |= (U8)(rex_bit);\
        ob.byte |= (U8)(((reg) & 0x7) << (offset_within_byte));\
    } else {\
        ob.byte |= (U8)((reg) << (offset_within_byte));\
    }\
})

#define ob_set_modrm_reg(ob, reg) ob_set_reg_op(ob, modrm, 3, reg, REX_R)
#define ob_set_modrm_rm(ob, reg)  ob_set_reg_op(ob, modrm, 0, reg, REX_B)
#define ob_set_sib_idx(ob, reg)   ob_set_reg_op(ob, sib, 3, reg, REX_X)
#define ob_set_sib_base(ob, reg)  ob_set_reg_op(ob, sib, 0, reg, REX_B)

// This function takes a 2-bit, 3-bit and 3-bit value
// and packs them into a byte in that order. You can
// use it to create a modrm or sib byte.
inl U8 pack_modrm (U8 mod, RegTag reg, RegTag rm) {
    return (U8)((mod << 6) | (((U8)reg & 0x7) << 3) | ((U8)rm & 0x7));
}

inl U8       pack_reg_into_op   (U8 op, RegTag reg) { return (U8)(op | ((U8)reg & 0x7)); }
inl U32      pack_2b            (U8 a, U8 b)        { return (U32)((b << 8) | a); }
inl Bool     is_extended        (RegTag reg)        { return reg >= 8; }
inl Bool     is_valid_sib_scale (U32 n)             { return n == 8 || n == 4 || n == 2 || n == 1 || n == 0; }
inl SibScale to_sib_scale       (U32 n)             { assert_dbg(is_valid_sib_scale(n)); return n == 8 ? S8 : n == 4 ? S4 : n == 2 ? S2 : S1; }

// Returns an OpBuf with r0 encoded into MODRM:reg and r1 into MODRM:rm.
static OpBuf regops (RegTag r0, RegTag r1) {
    OpBuf ob = {};
    ob.modrm |= pack_modrm(3, r0, r1);
    if (is_extended(r0)) ob.rex |= REX_R;
    if (is_extended(r1)) ob.rex |= REX_B;
    return ob;
}

// Returns an ob with the memory operand encoded into it.
// Use NIL to indicate that base or idx is not given.
// Use base=RIP and idx=NIL for a RIP-relative memory operand.
// Note that the displacement is actually an I32, but we leave it
// as a U32 for the sake of avoiding a bunch of annoying casts.
static OpBuf memop (RegTag base, RegTag idx, SibScale scale, U32 displacement) {
    OpBuf ob = {};
    ob.flags |= ENSURE_MODRM;

    if (idx == NIL) {
        if (displacement) {
            ob.displacement = displacement;

            switch (base) {
            case NIL: ob.modrm |= 0x4; ob.sib |= 0x25; break;
            case RIP: ob.modrm |= 0x5; break;
            case RSP: ob.modrm |= 0x84; ob.sib |= 0x24; break;
            case R12: ob.modrm |= 0x84; ob.sib |= 0x24; ob.rex |= REX_B; break;
            case RBP: ob.modrm |= 0x85; break;
            case R13: ob.modrm |= 0x85; ob.rex |= REX_B; break;
            default:  ob.modrm |= 0x80; ob_set_modrm_rm(ob, base); break;
            }
        } else {
            switch (base) {
            case NIL: badpath;
            case RIP: ob.modrm |= 0x5; ob.flags |= ENSURE_4B_DISPLACEMENT; break;
            case RSP: ob.modrm |= 0x4; ob.sib |= 0x24; break;
            case R12: ob.modrm |= 0x4; ob.sib |= 0x24; ob.rex |= REX_B; break;
            case RBP: ob.modrm |= 0x45; ob.flags |= ENSURE_1B_DISPLACEMENT; break;
            case R13: ob.modrm |= 0x45; ob.rex |= REX_B; ob.flags |= ENSURE_1B_DISPLACEMENT; break;
            default:  ob_set_modrm_rm(ob, base); break;
            }
        }
    } else {
        assert_dbg(idx != RSP);
        assert_dbg(base != RIP);

        if (displacement) {
            if (base == NIL) {
                base = RBP;
                ob.modrm |= 0x04;
            } else {
                ob.modrm |= 0x80;
            }

            ob.displacement = displacement;
        } else if (base == RBP || base == R13) {
            ob.modrm |= 0x40;
            ob.flags |= ENSURE_1B_DISPLACEMENT;
        } else if (base == NIL) {
            base = RBP;
            ob.modrm |= 0x04;
            ob.flags |= ENSURE_4B_DISPLACEMENT;
        }

        ob.modrm |= 0x4;
        ob.sib |= ((U8)scale) << 6;
        ob_set_sib_idx(ob, idx);
        ob_set_sib_base(ob, base);
        ob.flags |= ENSURE_SIB;
    }

    return ob;
}

// Convert the ob and opcode into an actual instruction.
static Void emit_instruction (AString *astr, OpBuf ob, U32 op_len, U32 op) {
    assert_dbg(op_len > 0 && op_len < 4);

    if (ob.rex) astr_push_u8(astr, ob.rex);
    astr_push_u8(astr, op & 0xff);
    if (op_len > 1) astr_push_u8(astr, (U8)((op >> 8) & 0xff));
    if (op_len > 2) astr_push_u8(astr, (U8)((op >> 16) & 0xff));
    if (ob.modrm || (ob.flags & ENSURE_MODRM)) astr_push_u8(astr, ob.modrm);
    if (ob.sib || (ob.flags & ENSURE_SIB)) astr_push_u8(astr, ob.sib);

    if (ob.displacement) {
        astr_push_u32(astr, ob.displacement);
    } else if (ob.flags & ENSURE_1B_DISPLACEMENT) {
        astr_push_u8(astr, 0);
    } else if (ob.flags & ENSURE_4B_DISPLACEMENT) {
        astr_push_u32(astr, 0);
    }
}

// Many instructions without immediate operands follow this pattern:
//
//   - If 64-bit operands, use op1 with REX.W
//   - If 32-bit operands, use op1
//   - If 16-bit operands, use op1 with 0x66 prefix
//   - If 8-bit  operands, use op2
//
// Emitters of those instructions can use this function for convenience.
//
// We assume that op1 and op2 have the same number of bytes, and the bytes are
// serialized in little-endian order. Use the pack_Nb() macros to make the ops.
//
// Note this function might emit a redundant REX byte when operands are 8-bit.
// It's because we always emit a rex byte when the operands are 8-bit to ensure
// that we use the lower byte of the registers RAX, RCX, RDX and RBX. However,
// if the operands are one of RSI, RDI, RBP, RSP, then the rex byte is redundant.
static Void emit_instruction1 (AString *astr, OpBuf ob, RegWidth w, U32 op_len, U32 op1, U32 op2) {
    switch (w) {
    case W64:
        ob.rex |= REX_W;
        emit_instruction(astr, ob, op_len, op1);
        break;
    case W32:
        emit_instruction(astr, ob, op_len, op1);
        break;
    case W16:
        astr_push_u8(astr, 0x66);
        emit_instruction(astr, ob, op_len, op1);
        break;
    case W8:
        ob.rex |= REX;
        emit_instruction(astr, ob, op_len, op2);
        break;
    }
}

// Many instructions with immediate operands follow a similar pattern to the one
// shown in emit_instruction1(). Emmitters of those instructions can use this for convenience.
static Void emit_instruction2 (AString *astr, OpBuf ob, RegWidth w, U32 op_len, U32 op1, U32 op2, Bool imm_is_64bit, U64 imm) {
    switch (w) {
    case W64:
        ob.rex |= REX_W;
        emit_instruction(astr, ob, op_len, op1);
        if (imm_is_64bit) astr_push_u64(astr, imm);
        else              astr_push_u32(astr, (U32)imm);
        break;
    case W32:
        emit_instruction(astr, ob, op_len, op1);
        astr_push_u32(astr, (U32)imm);
        break;
    case W16:
        astr_push_u8(astr, 0x66);
        emit_instruction(astr, ob, op_len, op1);
        astr_push_u16(astr, (U16)imm);
        break;
    case W8:
        ob.rex |= REX;
        emit_instruction(astr, ob, op_len, op2);
        astr_push_u8(astr, (U8)imm);
        break;
    }
}

static Void emit_add_ri   (AString *astr, RegWidth w, RegTag r0, U32 imm)            { emit_instruction2(astr, regops(0, r0), w, 1, 0x81, 0x80, false, imm); }
static Void emit_add_rm   (AString *astr, RegWidth w, RegTag r, OpBuf m)             { ob_set_modrm_reg(m, r); emit_instruction1(astr, m, w, 1, 0x03, 0x02); }
static Void emit_add_rr   (AString *astr, RegWidth w, RegTag r0, RegTag r1)          { emit_instruction1(astr, regops(r0, r1), w, 1, 0x03, 0x02); }
static Void emit_and_rr   (AString *astr, RegWidth w, RegTag r0, RegTag r1)          { emit_instruction1(astr, regops(r0, r1), w, 1, 0x23, 0x22); }
static Void emit_call     (AString *astr, RegTag r)                                  { if (is_extended(r)) astr_push_u8(astr, REX_B); astr_push_u8(astr, 0xff); astr_push_u8(astr, pack_modrm(3, 2, r)); }
static Void emit_call_rel (AString *astr, U32 rel)                                   { astr_push_u8(astr, 0xe8); astr_push_u32(astr, rel); }
static Void emit_cdq      (AString *astr)                                            { astr_push_u8(astr, 0x99); }
static Void emit_cmp_rm   (AString *astr, RegWidth w, RegTag r, OpBuf m)             { ob_set_modrm_reg(m, r); emit_instruction1(astr, m, w, 1, 0x3b, 0x3a); }
static Void emit_cmp_rr   (AString *astr, RegWidth w, RegTag r0, RegTag r1)          { emit_instruction1(astr, regops(r0, r1), w, 1, 0x3b, 0x3a); }
static Void emit_cqo      (AString *astr)                                            { astr_push_2u8(astr, 0x48, 0x99); }
static Void emit_cwd      (AString *astr)                                            { astr_push_2u8(astr, 0x66, 0x99); }
static Void emit_dec      (AString *astr, RegWidth w, RegTag r)                      { emit_instruction1(astr, regops(1, r), w, 1, 0xff, 0xfe); }
static Void emit_div      (AString *astr, RegWidth w, RegTag r)                      { emit_instruction1(astr, regops(6, r), w, 1, 0xf7, 0xf6); }
static Void emit_hlt      (AString *astr)                                            { astr_push_u8(astr, 0xf4); }
static Void emit_idiv     (AString *astr, RegWidth w, RegTag r)                      { emit_instruction1(astr, regops(7, r), w, 1, 0xf7, 0xf6); }
static Void emit_imul_r   (AString *astr, RegWidth w, RegTag r)                      { emit_instruction1(astr, regops(5, r), w, 1, 0xf7, 0xf6); }
static Void emit_imul_rr  (AString *astr, RegWidth w, RegTag r0, RegTag r1)          { assert_dbg(w != W8); emit_instruction1(astr, regops(r0, r1), w, 2, pack_2b(0x0f, 0xaf), 0); }
static Void emit_imul_rri (AString *astr, RegWidth w, RegTag r0, RegTag r1, U32 imm) { assert_dbg(w != W8); emit_instruction2(astr, regops(r0, r1), w, 1, 0x69, 0x00, false, imm); }
static Void emit_inc      (AString *astr, RegWidth w, RegTag r)                      { emit_instruction1(astr, regops(0, r), w, 1, 0xff, 0xfe); }
static Void emit_jcc      (AString *astr, ConditionCode cc, U32 rel)                 { astr_push_2u8(astr, 0x0f, (U8)(0x80 | cc)); astr_push_u32(astr, rel); }
static Void emit_jmp      (AString *astr, RegTag r)                                  { if (is_extended(r)) astr_push_u8(astr, REX_B); astr_push_u8(astr, 0xff); astr_push_u8(astr, pack_modrm(3, 4, r)); }
static Void emit_jmp_rel  (AString *astr, U32 rel)                                   { astr_push_u8(astr, 0xe9); astr_push_u32(astr, rel); }
static Void emit_lea      (AString *astr, RegTag r, OpBuf ob)                        { ob.rex |= REX_W; ob_set_modrm_reg(ob, r); emit_instruction(astr, ob, 1, 0x8d); }
static Void emit_mov_mi   (AString *astr, RegWidth w, OpBuf dst, U32 imm)            { emit_instruction2(astr, dst, w, 1, 0xc7, 0xc6, false, imm); }
static Void emit_mov_mr   (AString *astr, RegWidth w, OpBuf m, RegTag r)             { ob_set_modrm_reg(m, r); emit_instruction1(astr, m, w, 1, 0x89, 0x88); }
static Void emit_mov_rm   (AString *astr, RegWidth w, RegTag r, OpBuf m)             { ob_set_modrm_reg(m, r); emit_instruction1(astr, m, w, 1, 0x8b, 0x8a); }
static Void emit_mov_rr   (AString *astr, RegWidth w, RegTag r0, RegTag r1)          { if (r0 != r1) emit_instruction1(astr, regops(r0, r1), w, 1, 0x8b, 0x8a); }
static Void emit_neg_r    (AString *astr, RegWidth w, RegTag r)                      { emit_instruction1(astr, regops(3, r), w, 1, 0xf7, 0xf6); }
static Void emit_nop      (AString *astr)                                            { astr_push_u8(astr, 0x90); }
static Void emit_not_r    (AString *astr, RegWidth w, RegTag r)                      { emit_instruction1(astr, regops(2, r), w, 1, 0xf7, 0xf6); }
static Void emit_or_rr    (AString *astr, RegWidth w, RegTag r0, RegTag r1)          { emit_instruction1(astr, regops(r0, r1), w, 1, 0x0b, 0x0a); }
static Void emit_pop      (AString *astr, RegTag r)                                  { if (is_extended(r)) astr_push_u8(astr, REX_B); astr_push_u8(astr, pack_reg_into_op(0x58, r)); }
static Void emit_push     (AString *astr, RegTag r)                                  { if (is_extended(r)) astr_push_u8(astr, REX_B); astr_push_u8(astr, pack_reg_into_op(0x50, r)); }
static Void emit_ret      (AString *astr)                                            { astr_push_u8(astr, 0xc3); }
static Void emit_shl      (AString *astr, RegWidth w, RegTag r)                      { emit_instruction1(astr, regops(4, r), w, 1, 0xd3, 0xd2); }
static Void emit_shr      (AString *astr, RegWidth w, RegTag r)                      { emit_instruction1(astr, regops(5, r), w, 1, 0xd3, 0xd2); }
static Void emit_sub_ri   (AString *astr, RegWidth w, RegTag r0, U32 imm)            { emit_instruction2(astr, regops(5, r0), w, 1, 0x81, 0x80, false, imm); }
static Void emit_sub_rr   (AString *astr, RegWidth w, RegTag r0, RegTag r1)          { emit_instruction1(astr, regops(r0, r1), w, 1, 0x2b, 0x2a); }
static Void emit_syscall  (AString *astr)                                            { astr_push_2u8(astr, 0x0f, 0x05); }
static Void emit_xor_rr   (AString *astr, RegWidth w, RegTag r0, RegTag r1)          { emit_instruction1(astr, regops(r0, r1), w, 1, 0x33, 0x31); }

static Void emit_mov_ri (AString *astr, RegWidth w, RegTag r, U64 imm) {
    if (imm == 0) {
        emit_xor_rr(astr, W32, r, r);
    } else {
        OpBuf ob = {};
        if (is_extended(r)) ob.rex |= REX_B;
        emit_instruction2(astr, ob, w, 1, pack_reg_into_op(0xb8, r), pack_reg_into_op(0xb0, r), true, imm);
    }
}

static Void emit_movzx_rr (AString *astr, RegWidth w0, RegWidth w1, RegTag r0, RegTag r1) {
    assert_dbg(w0 > w1);
    OpBuf ob = regops(r0, r1);
    switch (w1) {
    case W16: emit_instruction1(astr, ob, w0, 2, pack_2b(0x0f, 0xb7), 0); break;
    case W8:  ob.rex |= REX; emit_instruction1(astr, ob, w0, 2, pack_2b(0x0f, 0xb6), 0); break;
    default:  badpath;
    }
}

static Void emit_movsx_rr (AString *astr, RegWidth w0, RegWidth w1, RegTag r0, RegTag r1) {
    assert_dbg(w0 > w1);
    OpBuf ob = regops(r0, r1);
    switch (w1) {
    case W32: emit_instruction1(astr, ob, w0, 1, 0x63, 0); break;
    case W16: emit_instruction1(astr, ob, w0, 2, pack_2b(0x0f, 0xbf), 0); break;
    case W8:  ob.rex |= REX; emit_instruction1(astr, ob, w0, 2, pack_2b(0x0f, 0xbe), 0); break;
    default:  badpath;
    }
}

static Void emit_cmp_r0 (AString *astr, RegWidth w, RegTag r) {
    OpBuf ob = regops(7, r);
    ob.flags |= ENSURE_1B_DISPLACEMENT;
    emit_instruction1(astr, ob, w, 1, 0x83, 0x80);
}

static Void emit_set (AString *astr, ConditionCode cc, RegTag r) {
    if      (r >= R08) astr_push_u8(astr, REX_B);
    else if (r >= RSP) astr_push_u8(astr, REX);
    astr_push_3u8(astr, 0x0f, (U8)(0x90 | cc), pack_modrm(3, 0, r));
}

static U64 imm (SirFn *fn, SirOp *op) {
    assert_dbg(op->tag == SIR_OP_CONST);

    Auto t = op->type;
    Auto v = sir_op_get_value(fn, op);

    switch (t->tag) {
    case TYPE_ENUM:
        t = ((TypeEnum*)t)->raw;
        assert_dbg(t->tag == TYPE_INT);
        through;
    case TYPE_INT:
        switch (((TypeInt*)t)->bitwidth) {
        case 8:  return ((TypeInt*)t)->is_signed ? (U64)v.i8  : v.u8;
        case 16: return ((TypeInt*)t)->is_signed ? (U64)v.i16 : v.u16;
        case 32: return ((TypeInt*)t)->is_signed ? (U64)v.i32 : v.u32;
        case 64: return ((TypeInt*)t)->is_signed ? (U64)v.i64 : v.u64;
        default: badpath;
        }
    case TYPE_BOOL:
        return v.u8;
    default: badpath;
    }
}

static Void emit_memcpy (Elf *elf, AString *astr, RegTag tmp, RegTag to, RegTag from, U32 to_offset, U32 from_offset, U32 n_bytes, Ast *from_patch) {
    #define copy(astr, width, offset, offset_increment) {\
        if (from_patch) {\
            emit_mov_rm(astr, width, tmp, memop(from, NIL, 1, 1));\
            elf_add_reloc(elf, true, from_patch, &elf->text_section, astr->count, 4, offset);\
        } else {\
            emit_mov_rm(astr, width, tmp, memop(from, NIL, 1, from_offset + offset));\
        }\
        emit_mov_mr(astr, width, memop(to, NIL, 1, to_offset + offset), tmp);\
        offset += offset_increment;\
    }

    U32 byte_offset = 0;

    for (U32 i=0; i < n_bytes/8; i++) copy(astr, W64, byte_offset, 8);
    if (n_bytes - byte_offset >= 4)   copy(astr, W32, byte_offset, 4);
    if (n_bytes - byte_offset >= 2)   copy(astr, W16, byte_offset, 2);
    if (n_bytes - byte_offset == 1)   copy(astr, W8,  byte_offset, 1);

    #undef copy
}

static Void emit_memset_zero (AString *astr, RegTag at, U32 n_bytes) {
    #define clear(astr, width, offset, offset_increment) {\
        emit_mov_mi(astr, width, memop(at, NIL, 1, offset), 0);\
        offset += offset_increment;\
    }

    U32 byte_offset = 0;

    for (U32 i=0; i < n_bytes/8; i++) clear(astr, W64, byte_offset, 8);
    if (n_bytes - byte_offset >= 4)   clear(astr, W32, byte_offset, 4);
    if (n_bytes - byte_offset >= 2)   clear(astr, W16, byte_offset, 2);
    if (n_bytes - byte_offset == 1)   clear(astr, W8,  byte_offset, 1);

    #undef clear
}

static AbiObj get_obj_abi (Abi *abi, Type *type) {
    switch (type->tag) {
    case TYPE_BOOL:    return (AbiObj){ .align=1, .size=1 };
    case TYPE_FN:      return (AbiObj){ .align=8, .size=8 };
    case TYPE_POINTER: return (AbiObj){ .align=8, .size=8 };
    case TYPE_ENUM:    return get_obj_abi(abi, ((TypeEnum*)type)->raw);

    case TYPE_FLOAT: {
        Auto t = (TypeFloat*)type;
        Auto n = t->bitwidth / 8;
        return (AbiObj){ .align=n, .size=n };
    }

    case TYPE_INT: {
        Auto t = (TypeInt*)type;
        Auto n = t->bitwidth / 8;
        return (AbiObj){ .align=n, .size=n };
    }

    case TYPE_ARRAY: {
        Auto t  = (TypeArray*)type;
        Auto r  = get_obj_abi(abi, t->element);
        r.size *= t->length;
        return r;
    }

    case TYPE_TUPLE: {
        Auto a = (X64Abi*)abi;

        AbiObj r = {};
        Auto found = map_get(&a->obj_abis, type->id, &r);
        if (found) return r;

        Auto n = ((TypeTuple*)type)->node;

        array_iter (field_ast, &n->fields) {
            Auto field_type = sem_get_type(abi->sem, field_ast);
            Auto field_abi  = get_obj_abi(abi, field_type);

            r.size += padding_to_align(r.size, field_abi.align);
            map_add(&a->field_offsets, field_ast->id, r.size);

            r.size += field_abi.size;
            if (field_abi.align > r.align) r.align = field_abi.align;
        }

        r.size += padding_to_align(r.size, r.align);
        map_add(&a->obj_abis, type->id, r);
        return r;
    }

    case TYPE_STRUCT: {
        tmem_new(tm);

        Auto a = (X64Abi*)abi;
        AbiObj r = {};
        Auto found = map_get(&a->obj_abis, type->id, &r);
        if (found) return r;

        Auto t = (TypeStruct*)type;
        Auto i = sem_iter_new(tm, abi->sem, &t->node->members);

        if (((Ast*)t->node)->flags & AST_IS_UNION) {
            while (sem_iter_next(i)) {
                Auto field_type = sem_get_type(abi->sem, i->node);
                Auto field_abi  = get_obj_abi(abi, field_type);
                if (field_abi.size > r.size) r.size = field_abi.size;
                if (field_abi.align > r.align) r.align = field_abi.align;
                map_add(&a->field_offsets, i->node->id, 0);
            }
        } else {
            while (sem_iter_next(i)) {
                Auto field_type = sem_get_type(abi->sem, i->node);
                Auto field_abi  = get_obj_abi(abi, field_type);

                r.size += padding_to_align(r.size, field_abi.align);
                map_add(&a->field_offsets, i->node->id, r.size);

                r.size += field_abi.size;
                if (field_abi.align > r.align) r.align = field_abi.align;
            }
        }

        r.size += padding_to_align(r.size, r.align);
        map_add(&a->obj_abis, type->id, r);

        return r;
    }

    case TYPE_VAR:
    case TYPE_VOID:
    case TYPE_MISC:
        badpath;
    }

    badpath;
}

static U32 get_offset (Abi *abi, Ast *field) {
    return map_get_assert(&((X64Abi*)abi)->field_offsets, field->id);
}

static RegWidth reg_size_of (Abi *abi, Type *type) {
    Auto s = get_obj_abi(abi, type).size;
    assert_dbg(s <= 8);
    return (s <= 1) ? W8 : (s <= 2) ? W16 : (s <= 4) ? W32 : W64;
}

static Bool can_be_in_reg (Abi *abi, Type *type) {
    switch (type->tag) {
    case TYPE_FN:
    case TYPE_INT:
    case TYPE_BOOL:
    case TYPE_ENUM:
    case TYPE_FLOAT:
    case TYPE_POINTER:
        return true;

    case TYPE_ARRAY:
    case TYPE_TUPLE:
    case TYPE_STRUCT:
        return false;

    case TYPE_VAR:
    case TYPE_MISC:
    case TYPE_VOID:
        badpath;
    }

    badpath;
}

static AbiFn *get_fn_abi (Abi *abi, Mem *mem, TypeFn *type) {
    Auto a = (X64Abi*)abi;
    Auto type_id = ((Type*)type)->id;

    Auto fn_abi = map_get_ptr(&a->fn_abis, type_id);
    if (fn_abi) return fn_abi;

    fn_abi = mem_new(mem, AbiFn);
    fn_abi->abi = abi;
    array_init(&fn_abi->inputs, mem);
    map_add(&a->fn_abis, type_id, fn_abi);

    U8 next_reg = 0;
    constexpr U8 n_regs = 6;
    static U8 regs[n_regs] = { RDI, RSI, RDX, RCX, R08, R09 };

    if (type->node->output) {
        if (can_be_in_reg(abi, sem_get_type(abi->sem, type->node->output))) {
            fn_abi->output = RAX;
        } else {
            // First argument reserved for the return address.
            array_push(&fn_abi->inputs, regs[next_reg++]);
            fn_abi->output = ABI_REG_MEM;
        }
    }

    array_iter (input, &type->node->inputs) {
        Auto t = sem_get_type(abi->sem, input);
        Auto r = (can_be_in_reg(abi, t) && next_reg < n_regs) ? regs[next_reg++] : ABI_REG_MEM;
        array_push(&fn_abi->inputs, r);
    }

    return fn_abi;
}

Abi *x64_abi_new (Mem *mem, Sem *sem) {
    Auto abi = mem_new(mem, X64Abi);

    abi->pub.sem = sem;
    map_init(&abi->fn_abis, mem);
    map_init(&abi->obj_abis, mem);
    map_init(&abi->field_offsets, mem);

    abi->pub.pointer_size        = 8;
    abi->pub.register_size       = 8;
    abi->pub.stack_frame_align   = 16;
    abi->pub.stack_arg_min_size  = 8;
    abi->pub.stack_arg_min_align = 8;

    abi->pub.any_id_offset      = 0;
    abi->pub.any_value_offset   = 8;
    abi->pub.any_value_size     = 8;
    abi->pub.slice_data_offset  = 8;
    abi->pub.slice_count_offset = 0;

    abi->pub.get_fn_abi    = get_fn_abi;
    abi->pub.get_obj_abi   = get_obj_abi;
    abi->pub.get_offset    = get_offset;
    abi->pub.can_be_in_reg = can_be_in_reg;

    return (Abi*)abi;
}

// This function replaces all SIR_OP_BRANCH instructions with
// a CMP and JCC pair. This is the only form of "lowering" we
// do in this IR right now.
//
// We assume that the blocks array is sorted in such a way
// that one of 2 successors of a block must follow it.
static Void rewrite_branch_ops (SirX64 *x64) {
    array_iter (block, &x64->fn->blocks) {
        if (block->succs.count != 2) continue;

        Auto branch     = array_get_last(&block->ops);
        Auto next_block = array_get(ARRAY, ARRAY_IDX + 1);

        assert_dbg(branch->tag == SIR_OP_BRANCH);

        if (next_block == array_get(&block->succs, 0)) {
            branch->tag = SIR_OP_X64_CMP_0_JE;
        } else {
            assert_dbg(next_block == array_get(&block->succs, 1));
            branch->tag = SIR_OP_X64_CMP_0_JNE;
        }
    }
}

static Bool reg_is_compatible (SirRegAlloc *, SirOp *, SirReg *) {
    return true;
}

static Void init_reg_constraints (SirRegAlloc *ra, SirOp *op, SirOpRegConstraints *constraints) {
    Auto x64 = cast(SirX64*, ra->data);

    #define ONLY(REG)       ((SirRegConstraint){ .tag=SIR_RC_ONLY, .reg=(REG) })
    #define SAME_AS_ARG0()  ((SirRegConstraint){ .tag=SIR_RC_SAME_AS_ARG0 })
    #define ANY_EXCEPT(REG) ((SirRegConstraint){ .tag=SIR_RC_ANY_EXCEPT, .reg=(REG) })

    switch (op->tag) {
    case SIR_OP_CALL: {
        Auto inputs      = sir_op_get_inputs(op);
        Auto callee_ast  = sir_op_get_value(ra->fn, op).ast;
        Auto callee_type = sem_get_type(ra->fn->sem, callee_ast);
        Auto callee_abi  = get_fn_abi(x64->abi, x64->mem, (TypeFn*)callee_type);

        if (! (op->flags & SIR_OP_IS_DIRECT_CALL)) {
            inputs.count--; // Skip last argument in loop below.

            // We set an only constraint on the last argument
            // (the return address) to make sure the register
            // allocator doesn't spill this one onto the stack.
            // It could spill it because the call op can have
            // arbitrary many inputs. This simplifies codegen.
            array_set_last(&constraints->inputs, ONLY(R[R12]));
        }

        array_iter (_, &inputs) {
            _;
            Auto reg = array_get(&callee_abi->inputs, ARRAY_IDX);

            if (reg == ABI_REG_MEM) {
                // Argument is passed on the stack, so we reserve
                // temporary registers for the memcpy we emit later.
                op->flags |= SIR_OP_USES_TMP_REG0 | SIR_OP_USES_TMP_REG1;
            } else {
                array_set(&constraints->inputs, ARRAY_IDX, ONLY(R[reg]));
            }
        }

        if (op->flags & SIR_OP_SELF_IS_REG) constraints->self = ONLY(R[RAX]);

        #define X(TAG, CALLEE_SAVED, ...) if (! CALLEE_SAVED) sir_reg_add_clobber(R[TAG], op);
        EACH_GP_REGISTER(X);
        #undef X
    } break;

    case SIR_OP_RETURN: {
        Auto args = sir_op_get_inputs(op);

        if (args.count == 1) {
            // We are returning a value by register.
            array_set(&constraints->inputs, 0, ONLY(R[RAX]));
        } else if (args.count == 2) {
            // We are returning a value on the stack, so we reserve
            // the temporary registers for the memcpy we emit later.
            op->flags |= SIR_OP_USES_TMP_REG0;
        }
    } break;

    case SIR_OP_LINUX_SYSCALL: {
        SirReg *map[] = { R[RDI], R[RSI], R[RDX], R[R10], R[R08], R[R09] };

        constraints->self = ONLY(R[RAX]);
        array_iter (c, &constraints->inputs, *) *c = ONLY(map[ARRAY_IDX]);

        sir_reg_add_clobber(R[RAX], op);
        sir_reg_add_clobber(R[RCX], op);
        sir_reg_add_clobber(R[R11], op);
    } break;

    case SIR_OP_FN_ARG: {
        Auto idx = sir_op_get_value(ra->fn, op).u32;
        Auto reg = array_get(&ra->fn->abi->inputs, idx);
        if (reg != ABI_REG_MEM) constraints->self = ONLY(R[reg]);
    } break;

    case SIR_OP_CAST: {
        constraints->self = SAME_AS_ARG0();
    } break;

    case SIR_OP_STRING_LITERAL: {
        op->flags |= SIR_OP_USES_TMP_REG0;
    } break;

    case SIR_OP_INDEX: {
        Auto t = ((TypePointer*)op->type)->pointee;
        Auto s = abi_of_obj(x64->abi, t).size;
        if (! is_valid_sib_scale(s)) op->flags |= SIR_OP_USES_TMP_REG1;
    } break;

    case SIR_OP_MUL: {
        constraints->self = SAME_AS_ARG0();
        if (reg_size_of(x64->abi, op->type) == W8) array_set(&constraints->inputs, 0, ONLY(R[RAX]));
    } break;

    case SIR_OP_DIV: {
        constraints->self = ONLY(R[RAX]);
        array_set(&constraints->inputs, 0, ONLY(R[RAX]));
        array_set(&constraints->inputs, 1, ANY_EXCEPT(R[RDX]));
        sir_reg_add_clobber(R[RDX], op);
    } break;

    case SIR_OP_MOD: {
        constraints->self = ONLY(R[RDX]);
        array_set(&constraints->inputs, 0, ONLY(R[RAX]));
        array_set(&constraints->inputs, 1, ANY_EXCEPT(R[RDX]));
        sir_reg_add_clobber(R[RAX], op);
    } break;

    case SIR_OP_SHIFT_LEFT:
    case SIR_OP_SHIFT_RIGHT: {
        constraints->self = SAME_AS_ARG0();
        array_set(&constraints->inputs, 1, ONLY(R[RCX]));
    } break;

    case SIR_OP_MEMCPY: {
        op->flags |= SIR_OP_USES_TMP_REG0;
    } break;

    case SIR_OP_ADD:
    case SIR_OP_SUB:
    case SIR_OP_NEGATE:
    case SIR_OP_INCREMENT:
    case SIR_OP_DECREMENT:
    case SIR_OP_BITWISE_NOT:
    case SIR_OP_BITWISE_OR:
    case SIR_OP_BITWISE_XOR:
    case SIR_OP_BITWISE_AND: {
        constraints->self = SAME_AS_ARG0();
    } break;

    default: break;
    }

    #undef ONLY
    #undef ANY_EXCEPT
    #undef SAME_AS_ARG0
}

static SirRegAlloc *allocate_registers (SirX64 *x64) {
    Auto ra = mem_new(x64->mem, SirRegAlloc);
    ra->data = x64;
    ra->fn = x64->fn;
    ra->is_compatible = reg_is_compatible;
    ra->init_constraints = init_reg_constraints;
    array_init(&ra->registers, x64->mem);

    #define MAKE_REG(TAG, CALLEE_SAVED, NAME, ...) ({\
        Auto reg = sir_make_reg(ra, x64->mem, TAG, str(NAME), CALLEE_SAVED);\
        array_push(&ra->registers, reg);\
        R[TAG] = reg;\
    });

    EACH_GP_REGISTER(MAKE_REG)

    ra->tmp_reg0  = R[TMP0];
    ra->tmp_reg1  = R[TMP1];
    ra->dummy_reg = sir_make_reg(ra, x64->mem, NIL, str("nil"), false);
    R[NIL]        = ra->dummy_reg;

    sir_alloc_regs(ra);

    return ra;
}

static Void emit_op (SirX64 *x64, SirOp *op, SirBlock *next_block) {
    Auto abi    = x64->abi;
    Auto astr   = &x64->elf.text_section.astr;
    Auto regs   = array_get(&x64->ra->bindings, op->id);
    RegTag self = regs->self             ? sir_reg_id(regs->self)                   : NIL;
    RegTag out  = regs->outputs.count    ? sir_reg_id(array_get(&regs->outputs, 0)) : NIL;
    RegTag in0  = regs->inputs.count     ? sir_reg_id(array_get(&regs->inputs, 0))  : NIL;
    RegTag in1  = regs->inputs.count > 1 ? sir_reg_id(array_get(&regs->inputs, 1))  : NIL;

    #define ADD_RELOC(TAG, IS_TEXT) elf_add_reloc(&x64->elf, IS_TEXT, TAG, &x64->elf.text_section, astr->count, 4, 0);

    switch (op->tag) {
    case SIR_OP_RETURN: {
        Auto args = sir_op_get_inputs(op);

        if (args.count == 2) {
            // We are returning on the stack, so memcpy
            // the value into the caller's stack.
            Auto type = array_get(&args, 0)->type;
            assert_dbg(type->tag == TYPE_POINTER);
            Auto result_type = ((TypePointer*)type)->pointee;
            Auto result_size = abi_of_obj(abi, result_type).size;
            emit_memcpy(&x64->elf, astr, TMP0, in0, in1, 0, 0, result_size, 0);
        }

        Auto succ = array_get(&op->block->succs, 0);
        if (succ->tag != SIR_BLOCK_EXIT) {
            emit_jmp_rel(astr, 1);
            ADD_RELOC(x64->fn->exit_block, true);
        }
    } break;

    case SIR_OP_CALL: {
        U32 arg_stack_offset = 0;
        Auto args            = sir_op_get_inputs(op);
        Auto callee_ast      = sir_op_get_value(x64->fn, op).ast;
        Auto callee_type     = sem_get_type(x64->fn->sem, callee_ast);
        Auto callee_abi      = get_fn_abi(x64->abi, x64->mem, (TypeFn*)callee_type);

        if (! (op->flags & SIR_OP_IS_DIRECT_CALL)) args.count--; // To skip the last arg (the fn pointer) in the loop below.

        array_iter (arg, &args) {
            Auto reg     = array_get(&regs->inputs, ARRAY_IDX);
            Auto reg_id  = sir_reg_id(reg);
            Auto reg_abi = array_get(&callee_abi->inputs, ARRAY_IDX);

            Bool virtual_reg_is_spilled = (reg_id == NIL);
            Bool arg_is_passed_on_stack = (reg_abi == ABI_REG_MEM);

            Type *arg_type = arg->type;
            if ((arg->tag == SIR_OP_STACK_OBJECT) ||
                (arg->tag == SIR_OP_GLOBAL_OBJECT) ||
                ((arg->tag == SIR_OP_FN_ARG) && arg_is_passed_on_stack)
            ) {
                assert_dbg(arg->type->tag == TYPE_POINTER);
                arg_type = cast(TypePointer*, arg->type)->pointee;
            }

            Bool arg_is_in_virtual_reg  = can_be_in_reg(x64->abi, arg_type);

            if (arg_is_passed_on_stack) {
                Auto arg_abi = abi_of_obj(abi, arg_type);

                arg_stack_offset += padding_to_align(arg_stack_offset, max(abi->stack_arg_min_align, arg_abi.align));

                if (arg_is_in_virtual_reg) {
                    if (virtual_reg_is_spilled) {
                        emit_memcpy(&x64->elf, astr, TMP1, RSP, RSP, arg_stack_offset, sir_get_spill_stack_slot(x64->frame, arg), arg_abi.size, 0);
                    } else {
                        emit_mov_mr(astr, reg_size_of(abi, arg_type), memop(RSP, NIL, S1, arg_stack_offset), reg_id);
                    }
                } else {
                    if (virtual_reg_is_spilled) {
                        emit_mov_rm(astr, reg_size_of(abi, arg_type), TMP0, memop(RSP, NIL, S1, sir_get_spill_stack_slot(x64->frame, arg)));
                        emit_memcpy(&x64->elf, astr, TMP1, RSP, TMP0, arg_stack_offset, 0, arg_abi.size, 0);
                    } else {
                        emit_memcpy(&x64->elf, astr, TMP1, RSP, reg_id, arg_stack_offset, 0, arg_abi.size, 0);
                    }
                }

                arg_stack_offset += max(abi->stack_arg_min_size, arg_abi.size);
            }
        }

        if (op->flags & SIR_OP_IS_DIRECT_CALL) {
            Auto fn_ast = sir_op_get_value(x64->fn, op).fn;
            emit_call_rel(astr, 1);
            ADD_RELOC(fn_ast, true);
        } else {
            Auto fn_ptr_reg = array_get_last(&regs->inputs);
            emit_call(astr, sir_reg_id(fn_ptr_reg));
        }
    } break;

    case SIR_OP_INDEX: {
        Auto element_type = ((TypePointer*)op->type)->pointee;
        Auto element_size = abi_of_obj(abi, element_type).size;

        if (is_valid_sib_scale(element_size)) {
            emit_lea(astr, self, memop(in0, in1, to_sib_scale(element_size), 0));
        } else if (self == in0) {
            emit_imul_rri(astr, W64, TMP1, in1, element_size);
            emit_mov_rr(astr, W64, self, TMP1);
        } else {
            emit_imul_rri(astr, W64, self, in1, element_size);
            emit_add_rr(astr, W64, self, in0);
        }
    } break;

    case SIR_OP_STRING_LITERAL: {
        Auto str = sir_op_get_value(x64->fn, op).str;
        map_add(&x64->string_literals, str, 0);
        emit_mov_ri(astr, W64, self, 1);
        ADD_RELOC(str, false);
    } break;

    case SIR_OP_STACK_OBJECT: {
        Auto stack_slot = sir_get_object_stack_slot(x64->frame, op);
        emit_lea(astr, self, memop(RSP, NIL, S1, stack_slot));

        if (op->flags & SIR_OP_DEFAULT_INITIALIZED) {
            Auto type = ((TypePointer*)op->type)->pointee;
            Auto size = abi_of_obj(abi, type).size;
            emit_memset_zero(astr, self, size);
        }
    } break;

    case SIR_OP_CAST: {
        Auto from_type  = array_get(&op->args, 0)->type;
        Auto to_width   = reg_size_of(abi, op->type);
        Auto from_width = reg_size_of(abi, from_type);

        if (to_width <= from_width) {
            emit_mov_rr(astr, to_width, self, in0);
        } else {
            assert_dbg(op->type->tag == TYPE_INT);
            assert_dbg(from_type->tag == TYPE_INT);

            if (((TypeInt*)from_type)->is_signed) {
                emit_movsx_rr(astr, to_width, from_width, self, in0);
            } else {
                emit_movzx_rr(astr, to_width, from_width, self, in0);
            }
        }
    } break;

    case SIR_OP_FN_ARG: {
        Auto arg_idx = sir_op_get_value(x64->fn, op).u32;
        Auto reg_abi = array_get(&x64->fn->abi->inputs, arg_idx);

        if (reg_abi == ABI_REG_MEM) {
            Auto stack_slot = sir_get_object_stack_slot(x64->frame, op);
            emit_lea(astr, self, memop(RSP, NIL, S1, stack_slot));
        }
    } break;

    case SIR_OP_VALUE_ADDRESS: {
        Auto value_type = ((TypePointer*)op->type)->pointee;
        Auto stack_slot = sir_get_object_stack_slot(x64->frame, op);
        emit_lea(astr, self, memop(RSP, NIL, S1, stack_slot));
        emit_mov_mr(astr, reg_size_of(abi, value_type), memop(self, NIL, S1, 0), in0);
    } break;

    case SIR_OP_LINUX_SYSCALL: {
        Auto ast = (AstFnLinux*)sir_op_get_value(x64->fn, op).ast;
        emit_mov_ri(astr, W32, RAX, ast->num);
        emit_syscall(astr);
    } break;

    case SIR_OP_FN_ADDRESS:
    case SIR_OP_GLOBAL_OBJECT: {
        Auto ast = sir_op_get_value(x64->fn, op).ast;
        emit_lea(astr, self, memop(RIP, NIL, S1, 1));
        ADD_RELOC(ast, true);
    } break;

    case SIR_OP_CONST: {
        U64 val = (op->flags & SIR_OP_DEFAULT_INITIALIZED) ? 0 : imm(x64->fn, op);
        emit_mov_ri(astr, reg_size_of(abi, op->type), self, val);
    } break;

    case SIR_OP_MUL: {
        Auto w = reg_size_of(abi, op->type);

        if (w == W8) {
            assert_dbg(self == RAX);
            assert_dbg(out == RAX);
            emit_imul_r(astr, W8, in1);
        } else {
            emit_imul_rr(astr, w, in0, in1);
        }
    } break;

    case SIR_OP_MOD:
    case SIR_OP_DIV: {
        Auto inputs = sir_op_get_inputs(op);
        Auto t0     = array_get(&inputs, 0)->type;
        Auto t1     = array_get(&inputs, 1)->type;

        if (t0->tag == TYPE_INT && ((TypeInt*)t0)->is_signed) {
            switch (reg_size_of(abi, t0)) {
            case W8:  emit_cwd(astr); break;
            case W32: emit_cdq(astr); break;
            case W64: emit_cqo(astr); break;
            case W16:
                assert_dbg(reg_size_of(abi, t1) == W16);
                emit_movsx_rr(astr, W32, W16, in0, in0);
                emit_movsx_rr(astr, W32, W16, in1, in1);
                emit_cdq(astr);
                break;
            }

            emit_idiv(astr, reg_size_of(abi, op->type), in1);
        } else {
            emit_mov_ri(astr, W64, RDX, 0);
            emit_div(astr, reg_size_of(abi, op->type), in1);
        }
    } break;

    case SIR_OP_LESS: {
        Auto arg0 = array_get(&op->args, 0);
        assert_dbg(arg0->type->tag == TYPE_INT);
        emit_cmp_rr(astr, reg_size_of(abi, arg0->type), in0, in1);
        ConditionCode cc = ((TypeInt*)arg0->type)->is_signed ? CC_L : CC_B;
        emit_set(astr, cc, self);
    } break;

    case SIR_OP_LESS_EQUAL: {
        Auto arg0 = array_get(&op->args, 0);
        assert_dbg(arg0->type->tag == TYPE_INT);
        emit_cmp_rr(astr, reg_size_of(abi, arg0->type), in0, in1);
        ConditionCode cc = ((TypeInt*)arg0->type)->is_signed ? CC_LE : CC_BE;
        emit_set(astr, cc, self);
    } break;

    case SIR_OP_GREATER: {
        Auto arg0 = array_get(&op->args, 0);
        assert_dbg(arg0->type->tag == TYPE_INT);
        emit_cmp_rr(astr, reg_size_of(abi, arg0->type), in0, in1);
        ConditionCode cc = ((TypeInt*)arg0->type)->is_signed ? CC_G : CC_A;
        emit_set(astr, cc, self);
    } break;

    case SIR_OP_GREATER_EQUAL: {
        Auto arg0 = array_get(&op->args, 0);
        assert_dbg(arg0->type->tag == TYPE_INT);
        emit_cmp_rr(astr, reg_size_of(abi, arg0->type), in0, in1);
        ConditionCode cc = ((TypeInt*)arg0->type)->is_signed ? CC_GE : CC_AE;
        emit_set(astr, cc, self);
    } break;

    case SIR_OP_NOT: {
        Auto arg0 = array_get(&op->args, 0);
        emit_cmp_r0(astr, reg_size_of(abi, arg0->type), in0);
        emit_set(astr, CC_E, self);
    } break;

    case SIR_OP_EQUAL: {
        Auto arg0 = array_get(&op->args, 0);
        emit_cmp_rr(astr, reg_size_of(abi, arg0->type), in0, in1);
        emit_set(astr, CC_E, self);
    } break;

    case SIR_OP_NOT_EQUAL: {
        Auto arg0 = array_get(&op->args, 0);
        emit_cmp_rr(astr, reg_size_of(abi, arg0->type), in0, in1);
        emit_set(astr, CC_NE, self);
    } break;

    case SIR_OP_X64_CMP_0_JE: {
        Auto jump_target = array_find_get(&op->block->succs, IT != next_block);
        emit_cmp_r0(astr, reg_size_of(abi, op->type), in0);
        emit_jcc(astr, CC_E, 1);
        ADD_RELOC(jump_target, true);
    } break;

    case SIR_OP_X64_CMP_0_JNE: {
        Auto jump_target = array_find_get(&op->block->succs, IT != next_block);
        emit_cmp_r0(astr, reg_size_of(abi, op->type), in0);
        emit_jcc(astr, CC_NE, 1);
        ADD_RELOC(jump_target, true);
    } break;

    case SIR_OP_ADD:         emit_add_rr(astr, reg_size_of(abi, op->type), in0, in1); break;
    case SIR_OP_BITWISE_AND: emit_and_rr(astr, reg_size_of(abi, op->type), in0, in1); break;
    case SIR_OP_BITWISE_NOT: emit_not_r(astr, reg_size_of(abi, op->type), self); break;
    case SIR_OP_BITWISE_OR:  emit_or_rr(astr, reg_size_of(abi, op->type), in0, in1); break;
    case SIR_OP_BITWISE_XOR: emit_xor_rr(astr, reg_size_of(abi, op->type), in0, in1); break;
    case SIR_OP_COPY:        emit_mov_rr(astr, reg_size_of(abi, op->type), self, in0); break;
    case SIR_OP_DECREMENT:   emit_dec(astr, reg_size_of(abi, op->type), self); break;
    case SIR_OP_INCREMENT:   emit_inc(astr, reg_size_of(abi, op->type), self); break;
    case SIR_OP_LOAD:        emit_mov_rm(astr, reg_size_of(abi, op->type), self, memop(in0, NIL, S1, 0)); break;
    case SIR_OP_MEMCPY:      emit_memcpy(&x64->elf, astr, TMP0, in0, in1, 0, 0, abi_of_obj(abi, op->type).size, 0); break;
    case SIR_OP_MOVE:        emit_mov_rr(astr, reg_size_of(abi, op->type), out, in0); break;
    case SIR_OP_NEGATE:      emit_neg_r(astr, reg_size_of(abi, op->type), in0); break;
    case SIR_OP_OFFSET:      emit_lea(astr, self, memop(in0, NIL, S1, sir_op_get_value(x64->fn, op).u32)); break;
    case SIR_OP_REG_LOAD:    emit_mov_rm(astr, reg_size_of(abi, op->type), in0, memop(RSP, NIL, S1, sir_get_spill_stack_slot(x64->frame, op))); break;
    case SIR_OP_REG_MOVE:    emit_mov_rr(astr, reg_size_of(abi, op->type), out, in0); break;
    case SIR_OP_REG_STORE:   emit_mov_mr(astr, reg_size_of(abi, op->type), memop(RSP, NIL, S1, sir_get_spill_stack_slot(x64->frame, op)), in0); break;
    case SIR_OP_SHIFT_LEFT:  emit_shl(astr, reg_size_of(abi, op->type), in0); break;
    case SIR_OP_SHIFT_RIGHT: emit_shr(astr, reg_size_of(abi, op->type), in0); break;
    case SIR_OP_STORE:       emit_mov_mr(astr, reg_size_of(abi, op->type), memop(in0, NIL, S1, sir_op_get_value(x64->fn, op).u32), in1); break;
    case SIR_OP_SUB:         emit_sub_rr(astr, reg_size_of(abi, op->type), in0, in1); break;
    case SIR_OP_X64_CMP:     emit_cmp_rr(astr, reg_size_of(abi, op->type), in0, in1); break;
    case SIR_OP_X64_CMP_0:   emit_cmp_r0(astr, reg_size_of(abi, op->type), in0); break;
    default: break;
    }

    #undef ADD_RELOC
}

static Void emit_fn (SirX64 *x64) {
    Auto astr = &x64->elf.text_section.astr;
    Auto fn   = x64->fn;
    Auto elf  = &x64->elf;

    // Emit preamble:
    elf_add_symbol(elf, fn->ast, &elf->text_section, astr->count);
    array_iter (reg, &x64->ra->used_callee_saved_regs) emit_push(astr, sir_reg_id(reg));
    emit_sub_ri(astr, W64, RSP, sir_get_frame_size(x64->frame) - (8 * x64->ra->used_callee_saved_regs.count));

    // Emit instructions:
    array_iter (block, &fn->blocks) {
        elf_add_symbol(elf, block, &elf->text_section, astr->count);

        Auto next_block = array_try_get(&fn->blocks, ARRAY_IDX + 1);
        array_iter (op, &block->ops) emit_op(x64, op, next_block);

        if (block->succs.count == 1) {
            Auto succ = array_get(&block->succs, 0);
            if (succ != next_block) {
                emit_jmp_rel(astr, 1);
                elf_add_reloc(elf, true, succ, &elf->text_section, astr->count, 4, 0);
            }
        }

        if (block->tag == SIR_BLOCK_EXIT) {
            // Emit postamble:
            emit_add_ri(astr, W64, RSP, sir_get_frame_size(x64->frame) - (8 * x64->ra->used_callee_saved_regs.count));
            array_iter_back (reg, &x64->ra->used_callee_saved_regs) emit_pop(astr, sir_reg_id(reg));
            emit_ret(astr);
        }
    }
}

// This start function only works for sysV.
static Void emit_start_fn (SirX64 *x64) {
    Auto astr = &x64->elf.text_section.astr;

    // Recommended by the sysV abi:
    emit_mov_ri(astr, W32, RBP, 0);

    // Call main():
    emit_call_rel(astr, 1);
    elf_add_reloc(&x64->elf, true, x64->program.entry, &x64->elf.text_section, astr->count, 4, 0);

    // Call exit():
    emit_mov_ri(astr, W32, RAX, 60);
    emit_mov_ri(astr, W32, RDI, 0);
    emit_syscall(astr);
}

static Void emit_global (SirX64 *x64, AString *astr, ArrayAst *nested_globals, Ast *node, Bool is_top_level) {
    Auto sem     = x64->fn->sem;
    Auto abi     = x64->abi;
    Auto type    = sem_get_type(sem, node);
    Auto value   = sem_get_const(sem, node);
    Auto obj_abi = get_obj_abi(abi, type);

    if (type->flags & TYPE_IS_PRIMITIVE) {
        switch (obj_abi.size) {
        case 1:  astr_push_u8(astr, value.u8); break;
        case 2:  astr_push_u16(astr, value.u16); break;
        case 4:  astr_push_u32(astr, value.u32); break;
        case 8:  astr_push_u64(astr, value.u64); break;
        default: badpath;
        }

        return;
    }

    if (! (node->flags & AST_CAN_EVAL_WITHOUT_VM)) {
        assert_dbg(! sem_type_has_pointers(sem, type));  // TODO: Turn this into a sem error.
        astr_push_str(astr, (String){ .data=value.ptr, .count=obj_abi.size });
        return;
    }

    if ((node->tag == AST_NIL) || (node->flags & AST_IS_TYPE)) {
        astr_push_bytes(astr, 0, obj_abi.size);
        return;
    }

    switch (value.ast->tag) {
    case AST_FN: {
        assert_dbg(node->tag == AST_IDENT);
        elf_add_reloc(&x64->elf, false, value.ast, &x64->elf.data_section, astr->count, 8, 0);
        astr_push_u64(astr, 0);
    } break;

    case AST_ADDRESS_OF: {
        Auto op = ((AstBaseUnary*)value.ast)->op;
        if (op->tag == AST_IDENT) op = sem_get_const(sem, op).ast;

        elf_add_reloc(&x64->elf, false, op, &x64->elf.data_section, astr->count, 8, 0);
        astr_push_u64(astr, 0);

        if (op->tag != AST_VAR_DEF) array_push(nested_globals, op);
    } break;

    case AST_CAST: {
        Auto n = (AstCast*)value.ast;
        Auto t = sem_get_type(sem, n->expr);

        array_push(nested_globals, n->expr);

        assert_dbg(abi->any_value_offset == 8);
        assert_dbg(abi->slice_data_offset == 8);

        switch (n->tag) {
        case AST_CAST_ANY:   astr_push_u32(astr, t->id); break;
        case AST_CAST_SLICE: astr_push_u32(astr, (n->expr->tag == AST_ARRAY_LITERAL) ? ((TypeArray*)t)->length : ((AstTuple*)n->expr)->fields.count); break;
        default: badpath;
        }

        elf_add_reloc(&x64->elf, false, n->expr, &x64->elf.data_section, astr->count, 8, 0);
        astr_push_u64(astr, 0);
    } break;

    case AST_ARRAY_LITERAL: {
        Auto n = (AstArrayLiteral*)value.ast;
        if (is_top_level) array_ensure_capacity(astr, obj_abi.size);
        array_iter (init, &n->inits) emit_global(x64, astr, nested_globals, init, false);
    } break;

    case AST_STRING_LITERAL: {
        Auto n = (AstStringLiteral*)value.ast;
        map_add(&x64->string_literals, n->str, 0);
        astr_push_u64(astr, 1);
        elf_add_reloc(&x64->elf, false, n->str, &x64->elf.data_section, astr->count, 8, 0);
    } break;

    case AST_TUPLE: {
        Auto n = (AstTuple*)value.ast;

        if (is_top_level) array_increase_count(astr, obj_abi.size, true);

        Auto dummy_ds = *astr;
        dummy_ds.capacity = UINT32_MAX;

        array_iter (field, &n->fields) {
            Auto offset    = abi_offset(abi, field);
            dummy_ds.data  = astr->data + offset;
            dummy_ds.count = abi_of_obj(abi, sem_get_type(sem, field)).size;
            emit_global(x64, &dummy_ds, nested_globals, field, false);
            assert_dbg(dummy_ds.data == (astr->data + offset)); // Should not realloc.
        }
    } break;

    case AST_STRUCT_LITERAL: {
        Auto n = (AstStructLiteral*)value.ast;

        if (is_top_level) array_increase_count(astr, obj_abi.size, true);

        Auto dummy_astr = *astr;
        dummy_astr.capacity = UINT32_MAX;

        array_iter (init, &n->inits) {
            Auto target      = cast(AstStructLitInit*, init)->sem_edge;
            Auto offset      = abi_offset(abi, target);
            dummy_astr.data  = astr->data + offset;
            dummy_astr.count = abi_of_obj(abi, sem_get_type(sem, target)).size;
            emit_global(x64, &dummy_astr, nested_globals, init->val, false);
            assert_dbg(dummy_astr.data == (astr->data + offset)); // Must not realloc.
        }
    } break;

    default: badpath;
    }
}

static Void emit_globals (SirX64 *x64) {
    Auto astr = &x64->elf.data_section.astr;

    ArrayAst nested_globals;
    array_init(&nested_globals, x64->mem);

    array_iter (global, x64->program.globals) {
        Auto type  = sem_get_type(x64->fn->sem, (Ast*)global);
        Auto align = abi_of_obj(x64->abi, type).align;
        astr_push_bytes(astr, 0, padding_to_align(astr->count, align));
        elf_add_symbol(&x64->elf, global, &x64->elf.data_section, astr->count);
        emit_global(x64, astr, &nested_globals, global->init ? global->init : global->constraint, true);
    }

    array_iter (global, &nested_globals) {
        Auto type  = sem_get_type(x64->fn->sem, global);
        Auto align = abi_of_obj(x64->abi, type).align;
        astr_push_bytes(astr, 0, padding_to_align(astr->count, align));
        elf_add_symbol(&x64->elf, global, &x64->elf.data_section, astr->count);
        emit_global(x64, astr, &nested_globals, global, true);
    }

    map_iter (s, &x64->string_literals) {
        elf_add_symbol(&x64->elf, s->key, &x64->elf.data_section, astr->count);
        astr_push_str(astr, *s->key);
    }
}

Void x64_emit (String exe_file_path, Mem *mem, Abi *abi, Interns *interns, Sem *sem, SemProgram program) {
    Auto x64     = mem_new(mem, SirX64);
    x64->mem     = mem;
    x64->abi     = abi;
    x64->elf     = elf_new(mem);
    x64->program = program;
    map_init(&x64->string_literals, mem);

    emit_start_fn(x64);
    Auto ir_output = str(".ir.dot"); // TODO: Hardcoded path.

    array_iter (fn_ast, program.fns) {
        Bool print_ir_pre_regalloc  = sem_get_attribute(sem, (Ast*)fn_ast, intern_cstr(interns, "ir0"));
        Bool print_ir_post_regalloc = sem_get_attribute(sem, (Ast*)fn_ast, intern_cstr(interns, "ir1"));

        x64->fn = sir_fn_new(mem, interns, sem, fn_ast, abi);
        if (print_ir_pre_regalloc) sir_to_dot(x64->fn, mem, ir_output, 0);

        sir_leave_ssa_form(x64->fn);
        sir_reverse_postorder(x64->fn);
        rewrite_branch_ops(x64);

        Auto block_count = x64->fn->blocks.count;
        x64->ra = allocate_registers(x64);
        if (x64->fn->blocks.count != block_count) sir_reverse_postorder(x64->fn);
        if (print_ir_post_regalloc) sir_to_dot(x64->fn, mem, ir_output, x64->ra);

        x64->frame = sir_stack_frame_new(x64->fn, x64->ra);
        emit_fn(x64);
    }

    emit_globals(x64);
    elf_emit_exe(&x64->elf, exe_file_path);
}

Void x64_test (String main_file_path) {
    if (! main_file_path.data) return;
    tmem_new(tm);
    tmem_pin(tm, 1);
    Interns *interns = intern_new(tm, main_file_path);
    Sem *sem = sem_new(interns, tm);
    Abi *abi = x64_abi_new(tm, sem);
    SemProgram sem_prog = sem_check(sem, interns->main_file_path, abi);
    x64_emit(str("test.exe"), tm, abi, interns, sem, sem_prog);
}
