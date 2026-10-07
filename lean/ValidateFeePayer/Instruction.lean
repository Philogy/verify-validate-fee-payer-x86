/-!
The instructions the carved code uses, as a typed syntax tree.

The constructors are the instruction *forms* that occur in the two carved
functions (see `artifacts/validate_fee_payer.intel.s` and `AUDITED_MNEMONICS`
in `carve/src/code.rs`). Operands are general enough that one constructor
covers e.g. every compare the code contains; the decoder (`Decode.lean`) is
what restricts the encodings to the ones that occur.

Names here are descriptive; the x86 mnemonic or register name is in each
doc comment. `Print.lean` is the one place that maps them back to the names
llvm-objdump prints.
-/

namespace ValidateFeePayer.X86

/-- The 16 general-purpose 64-bit registers, in encoding order (0 … 15).
The first eight keep their historical 8086 names; the x86 names are in the
comments. -/
inductive Register where
  /-- x86: `rax`. Holds the return value. -/
  | accumulator
  /-- x86: `rcx`. -/
  | counter
  /-- x86: `rdx`. -/
  | data
  /-- x86: `rbx`. -/
  | base
  /-- x86: `rsp`. The stack pointer: the address of the top of the stack. -/
  | stackPointer
  /-- x86: `rbp`. -/
  | framePointer
  /-- x86: `rsi`. -/
  | sourceIndex
  /-- x86: `rdi`. -/
  | destinationIndex
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr, Inhabited

namespace Register

def all : List Register :=
  [accumulator, counter, data, base, stackPointer, framePointer, sourceIndex, destinationIndex,
   r8, r9, r10, r11, r12, r13, r14, r15]

/-- The register's number in instruction encodings. -/
def index : Register → Fin 16
  | accumulator => 0 | counter => 1 | data => 2 | base => 3
  | stackPointer => 4 | framePointer => 5 | sourceIndex => 6 | destinationIndex => 7
  | r8 => 8 | r9 => 9 | r10 => 10 | r11 => 11 | r12 => 12 | r13 => 13 | r14 => 14 | r15 => 15

def ofIndex (i : Fin 16) : Register := all[i]'(by simp [all])

end Register

/-- One of the 16 vector registers (x86: `xmm0` … `xmm15`, 128 bits each,
used by SSE for floating-point and bulk bitwise operations). -/
abbrev VectorRegister := Fin 16

/-- Integer operand size. 8-bit register operands always name the low byte
of the register (x86: `al`, `bpl`, `r11b`, …); the decoder rejects the
"high byte" registers (`ah`/`ch`/`dh`/`bh`). -/
inductive OperandSize where
  | bits8 | bits32 | bits64
  deriving DecidableEq, Repr

def OperandSize.bits : OperandSize → Nat
  | .bits8 => 8 | .bits32 => 32 | .bits64 => 64

/-- How a memory operand's address is computed. -/
inductive Address where
  /-- `next instruction's address + displacement` (x86: `[rip + disp]`, a
  "rip-relative" address). -/
  | relativeToNextInstruction (displacement : Int)
  /-- `base + index * 2^scale + displacement` (x86: a SIB, "scale-index-base",
  address). `index` pairs the register with the scale exponent 0–3. -/
  | baseIndex (base : Option Register) (index : Option (Register × Fin 4)) (displacement : Int)
  deriving DecidableEq, Repr

/-- An integer operand that names a register or a memory location (x86: `r/m`). -/
inductive RegisterOrMemory where
  | register (r : Register)
  | memory (a : Address)
  deriving DecidableEq, Repr

/-- A vector operand that names a vector register or a memory location
(x86: `xmm/m64`, `xmm/m128`). -/
inductive VectorOrMemory where
  | register (v : VectorRegister)
  | memory (a : Address)
  deriving DecidableEq, Repr

/-- Source of a two-operand integer instruction. Immediates (constants
encoded in the instruction) are stored sign-extended to 64 bits and
truncated to the operand size when used. -/
inductive Source where
  | operand (x : RegisterOrMemory)
  | immediate (v : UInt64)
  deriving DecidableEq, Repr

/-- The conditions of conditional jumps, sets and moves, in encoding order
(x86 "condition codes"; e.g. `jcc` is opcode `0x70 + code`). "Below/above"
compare unsigned, "less/greater" signed. The x86 suffix is in each comment. -/
inductive Condition where
  /-- `o` -/ | overflow
  /-- `no` -/ | notOverflow
  /-- `b` -/ | below
  /-- `ae` -/ | aboveOrEqual
  /-- `e` -/ | equal
  /-- `ne` -/ | notEqual
  /-- `be` -/ | belowOrEqual
  /-- `a` -/ | above
  /-- `s` -/ | negative
  /-- `ns` -/ | notNegative
  /-- `p` -/ | parityEven
  /-- `np` -/ | parityOdd
  /-- `l` -/ | less
  /-- `ge` -/ | greaterOrEqual
  /-- `le` -/ | lessOrEqual
  /-- `g` -/ | greater
  deriving DecidableEq, Repr

def Condition.ofCode : Nat → Condition
  | 0 => .overflow | 1 => .notOverflow | 2 => .below | 3 => .aboveOrEqual
  | 4 => .equal | 5 => .notEqual | 6 => .belowOrEqual | 7 => .above
  | 8 => .negative | 9 => .notNegative | 10 => .parityEven | 11 => .parityOdd
  | 12 => .less | 13 => .greaterOrEqual | 14 => .lessOrEqual | _ => .greater

/-- Two-operand integer arithmetic and logic. `compare` and `testBits` only
set the flags. -/
inductive ArithmeticOp where
  /-- x86: `add` -/ | add
  /-- x86: `or` -/ | or
  /-- `a - b - carry` (x86: `sbb`). -/ | subtractWithBorrow
  /-- x86: `and` -/ | and
  /-- x86: `sub` -/ | subtract
  /-- x86: `xor` -/ | xor
  /-- `subtract` without storing the result (x86: `cmp`). -/ | compare
  /-- `and` without storing the result (x86: `test`). -/ | testBits
  deriving DecidableEq, Repr

/-- Bitwise operations on whole vector registers. -/
inductive VectorBitwiseOp where
  /-- x86: `pxor` -/ | xor
  /-- x86: `por` -/ | or
  /-- x86: `xorpd`. Same result as `xor`; a different encoding. -/ | xorDoubles
  deriving DecidableEq, Repr

/-- Double-precision arithmetic on the low 64 bits of a vector register
(x86: the "scalar double", `sd`, instructions). -/
inductive ScalarDoubleOp where
  /-- x86: `addsd` -/ | add
  /-- x86: `subsd` -/ | subtract
  /-- x86: `mulsd` -/ | multiply
  deriving DecidableEq, Repr

inductive Instruction where
  /-- `destination := destination op source`, flags from the result;
  `compare`/`testBits` keep `destination`. -/
  | arithmetic (op : ArithmeticOp) (size : OperandSize) (destination : RegisterOrMemory) (source : Source)
  /-- x86: `mov`. -/
  | move (size : OperandSize) (destination : RegisterOrMemory) (source : Source)
  /-- Load a full 64-bit constant (x86: `movabs r64, imm64`). -/
  | moveImmediate64 (destination : Register) (immediate : UInt64)
  /-- Copy a byte, filling the upper bits with zeros (x86: `movzx`). -/
  | moveZeroExtendByte (size : OperandSize) (destination : Register) (source : RegisterOrMemory)
  /-- Compute an address without accessing memory (x86: `lea`, "load
  effective address"). -/
  | loadAddress (destination : Register) (address : Address)
  /-- x86: `inc`. -/
  | increment (size : OperandSize) (destination : RegisterOrMemory)
  /-- Signed 64-bit multiplication, truncated to 64 bits (x86: `imul r64,
  r/m64[, imm32]`). Without `immediate`, `destination` is the other factor. -/
  | multiplySigned (destination : Register) (source : RegisterOrMemory) (immediate : Option UInt64)
  /-- Shift right, copying the sign bit in (x86: `sar r/m64, imm8`). -/
  | shiftRightSigned (destination : RegisterOrMemory) (count : UInt8)
  /-- Store 1 if the condition holds, else 0, in a byte (x86: `setcc`). -/
  | setIf (condition : Condition) (destination : RegisterOrMemory)
  /-- x86: `cmovcc`. -/
  | moveIf (condition : Condition) (size : OperandSize) (destination : Register) (source : RegisterOrMemory)
  /-- x86: `push`. -/
  | push (r : Register)
  /-- x86: `pop`. -/
  | pop (r : Register)
  /-- Jump by `offset` from the next instruction if the condition holds
  (x86: `jcc`). -/
  | jumpIf (condition : Condition) (offset : Int)
  /-- x86: `jmp`. -/
  | jump (offset : Int)
  /-- Call the address held in `target` (x86: `call qword ptr [..]` /
  `call r64`, an indirect call). -/
  | call (target : RegisterOrMemory)
  /-- x86: `ret`. -/
  | returnToCaller
  /-- Copy 128 bits; a memory source need not be aligned (x86: `movdqu`). -/
  | moveVectorUnaligned (destination : VectorRegister) (source : VectorOrMemory)
  /-- Copy 128 bits; a memory source must be 16-byte aligned (x86: `movapd`). -/
  | moveVectorAligned (destination : VectorRegister) (source : VectorOrMemory)
  /-- Copy a 64-bit integer into the low half of a vector register, zeroing
  the high half (x86: `movq xmm, r/m64`). -/
  | moveIntegerToVector (destination : VectorRegister) (source : RegisterOrMemory)
  | vectorBitwise (op : VectorBitwiseOp) (destination : VectorRegister) (source : VectorOrMemory)
  /-- Set flags from bitwise tests of two vectors (x86: `ptest`). -/
  | testVectorBits (destination : VectorRegister) (source : VectorOrMemory)
  /-- Interleave the low two 32-bit lanes of both operands (x86: `punpckldq`). -/
  | interleaveLow32 (destination : VectorRegister) (source : VectorOrMemory)
  /-- `destination := [destination.high, source.high]` (x86: `unpckhpd`). -/
  | interleaveHighDoubles (destination : VectorRegister) (source : VectorOrMemory)
  /-- Subtract both 64-bit doubles lane by lane (x86: `subpd`, "packed double"). -/
  | subtractDoublePairs (destination : VectorRegister) (source : VectorOrMemory)
  | scalarDouble (op : ScalarDoubleOp) (destination : VectorRegister) (source : VectorOrMemory)
  /-- Compare two doubles and set flags (x86: `ucomisd`). -/
  | compareDoubles (destination : VectorRegister) (source : VectorOrMemory)
  /-- Convert a double to a signed 64-bit integer, rounding toward zero
  (x86: `cvttsd2si r64, xmm/m64`). -/
  | truncateDoubleToInt64 (destination : Register) (source : VectorOrMemory)
  deriving DecidableEq, Repr

end ValidateFeePayer.X86
