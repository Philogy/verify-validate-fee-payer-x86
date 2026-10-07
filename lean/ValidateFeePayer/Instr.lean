/-!
The instructions the carved code uses, as a typed syntax tree.

The constructors are the instruction *forms* that occur in the two carved
functions (see `artifacts/validate_fee_payer.intel.s` and `AUDITED_MNEMONICS`
in `carve/src/code.rs`). Operands are general enough that one constructor
covers e.g. every `cmp` the code contains; the decoder (`Decode.lean`) is
what restricts the encodings to the ones that occur.
-/

namespace ValidateFeePayer.X86

/-- General-purpose registers, in encoding order (`rax` = 0 … `r15` = 15). -/
inductive Reg where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr, Inhabited

namespace Reg

def all : List Reg :=
  [rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15]

def toFin : Reg → Fin 16
  | rax => 0 | rcx => 1 | rdx => 2 | rbx => 3 | rsp => 4 | rbp => 5 | rsi => 6 | rdi => 7
  | r8 => 8 | r9 => 9 | r10 => 10 | r11 => 11 | r12 => 12 | r13 => 13 | r14 => 14 | r15 => 15

def ofFin (i : Fin 16) : Reg := all[i]'(by simp [all])

end Reg

/-- `xmm0` … `xmm15`. -/
abbrev Xmm := Fin 16

/-- Integer operand size. 8-bit register operands always name the low byte
(`al`, `bpl`, `r11b`, …); the decoder rejects `ah`/`ch`/`dh`/`bh`. -/
inductive Size where
  | b8 | b32 | b64
  deriving DecidableEq, Repr

def Size.bits : Size → Nat
  | .b8 => 8 | .b32 => 32 | .b64 => 64

/-- A memory operand's effective address. -/
inductive Addr where
  /-- `[rip + disp]`, relative to the next instruction. -/
  | rip (disp : Int)
  /-- `[base + index * 2^scale + disp]`. -/
  | sib (base : Option Reg) (index : Option (Reg × Fin 4)) (disp : Int)
  deriving DecidableEq, Repr

/-- An integer register or memory operand (`r/m` in Intel's tables). -/
inductive RM where
  | reg (r : Reg)
  | mem (a : Addr)
  deriving DecidableEq, Repr

/-- An XMM register or memory operand (`xmm/m64`, `xmm/m128`). -/
inductive XRM where
  | reg (x : Xmm)
  | mem (a : Addr)
  deriving DecidableEq, Repr

/-- Source of a two-operand integer instruction. Immediates are stored
sign-extended to 64 bits and truncated to the operand size when used. -/
inductive Src where
  | rm (x : RM)
  | imm (v : UInt64)
  deriving DecidableEq, Repr

/-- Condition codes, in encoding order (`jcc` = `0x70 + cc`). -/
inductive Cond where
  | o | no | b | ae | e | ne | be | a | s | ns | p | np | l | ge | le | g
  deriving DecidableEq, Repr

def Cond.ofCode : Nat → Cond
  | 0 => .o | 1 => .no | 2 => .b | 3 => .ae | 4 => .e | 5 => .ne | 6 => .be | 7 => .a
  | 8 => .s | 9 => .ns | 10 => .p | 11 => .np | 12 => .l | 13 => .ge | 14 => .le | _ => .g

def Cond.name : Cond → String
  | .o => "o" | .no => "no" | .b => "b" | .ae => "ae" | .e => "e" | .ne => "ne"
  | .be => "be" | .a => "a" | .s => "s" | .ns => "ns" | .p => "p" | .np => "np"
  | .l => "l" | .ge => "ge" | .le => "le" | .g => "g"

/-- Two-operand integer ALU operations. `cmp` and `test` only write flags. -/
inductive AluOp where
  | add | or | sbb | and | sub | xor | cmp | test
  deriving DecidableEq, Repr

def AluOp.name : AluOp → String
  | .add => "add" | .or => "or" | .sbb => "sbb" | .and => "and"
  | .sub => "sub" | .xor => "xor" | .cmp => "cmp" | .test => "test"

/-- Bitwise operations on whole XMM registers. -/
inductive XBitOp where
  | pxor | por | xorpd
  deriving DecidableEq, Repr

/-- Scalar double-precision arithmetic on the low lane. -/
inductive SdOp where
  | addsd | subsd | mulsd
  deriving DecidableEq, Repr

inductive Instr where
  /-- `dst := dst op src`, flags from the result; `cmp`/`test` keep `dst`. -/
  | alu (op : AluOp) (sz : Size) (dst : RM) (src : Src)
  /-- `mov` (also `mov r32, imm32` and `mov r/m64, simm32`). -/
  | mov (sz : Size) (dst : RM) (src : Src)
  /-- `movabs r64, imm64`. -/
  | movabs (dst : Reg) (imm : UInt64)
  /-- `movzx r32/r64, r/m8`. -/
  | movzx (sz : Size) (dst : Reg) (src : RM)
  /-- `lea r64, m`: the address only, no memory access. -/
  | lea (dst : Reg) (a : Addr)
  | inc (sz : Size) (dst : RM)
  /-- `imul r64, r/m64[, simm32]`: signed, truncated to 64 bits. -/
  | imul (dst : Reg) (src : RM) (imm : Option UInt64)
  /-- `sar r/m64, imm8`. -/
  | sar (dst : RM) (count : UInt8)
  /-- `setcc r/m8`. -/
  | setcc (c : Cond) (dst : RM)
  | cmov (c : Cond) (sz : Size) (dst : Reg) (src : RM)
  | push (r : Reg)
  | pop (r : Reg)
  /-- `jcc rel`, relative to the next instruction. -/
  | jcc (c : Cond) (rel : Int)
  | jmp (rel : Int)
  /-- `call qword ptr [..]` / `call r64`: an indirect call. -/
  | call (target : RM)
  | ret
  /-- `movdqu xmm, xmm/m128` (unaligned). -/
  | movdqu (dst : Xmm) (src : XRM)
  /-- `movapd xmm, xmm/m128` (16-byte aligned). -/
  | movapd (dst : Xmm) (src : XRM)
  /-- `movq xmm, r/m64`: zero-extends to 128 bits. -/
  | movq (dst : Xmm) (src : RM)
  | xbit (op : XBitOp) (dst : Xmm) (src : XRM)
  | ptest (dst : Xmm) (src : XRM)
  /-- `punpckldq`: interleave the low two dwords. -/
  | punpckldq (dst : Xmm) (src : XRM)
  /-- `unpckhpd`: `dst := [dst.high, src.high]`. -/
  | unpckhpd (dst : Xmm) (src : XRM)
  | subpd (dst : Xmm) (src : XRM)
  | sd (op : SdOp) (dst : Xmm) (src : XRM)
  | ucomisd (dst : Xmm) (src : XRM)
  /-- `cvttsd2si r64, xmm/m64`. -/
  | cvttsd2si (dst : Reg) (src : XRM)
  deriving DecidableEq, Repr

/-- The mnemonic GNU objdump prints, to compare the decoder against the
disassembly in `Disasm.lean`. -/
def Instr.mnemonic : Instr → String
  | .alu op .. => op.name
  | .mov .. => "mov"
  | .movabs .. => "movabs"
  | .movzx .. => "movzx"
  | .lea .. => "lea"
  | .inc .. => "inc"
  | .imul .. => "imul"
  | .sar .. => "sar"
  | .setcc c _ => "set" ++ c.name
  | .cmov c .. => "cmov" ++ c.name
  | .push _ => "push"
  | .pop _ => "pop"
  | .jcc c _ => "j" ++ c.name
  | .jmp _ => "jmp"
  | .call _ => "call"
  | .ret => "ret"
  | .movdqu .. => "movdqu"
  | .movapd .. => "movapd"
  | .movq .. => "movq"
  | .xbit .pxor .. => "pxor"
  | .xbit .por .. => "por"
  | .xbit .xorpd .. => "xorpd"
  | .ptest .. => "ptest"
  | .punpckldq .. => "punpckldq"
  | .unpckhpd .. => "unpckhpd"
  | .subpd .. => "subpd"
  | .sd .addsd .. => "addsd"
  | .sd .subsd .. => "subsd"
  | .sd .mulsd .. => "mulsd"
  | .ucomisd .. => "ucomisd"
  | .cvttsd2si .. => "cvttsd2si"

end ValidateFeePayer.X86
