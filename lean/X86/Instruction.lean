import X86.OperandSize

/-!
The supported subset is chosen by instruction form, not by the instances
one program happens to contain: each constructor covers every operand size,
register and addressing mode of its form. Not supported: x87, MMX, AVX and
later, string instructions, division, rotates, bit tests and scans,
`xchg`/`cmpxchg`, `lock` and segment prefixes, system instructions,
single-precision arithmetic, and the floating-point conversions and
comparisons other than `cvttsd2si r64` and `ucomisd` (the floating-point
model, `F64`, does not cover them yet).

`Print.lean` maps the descriptive names to x86 mnemonics.
-/

namespace X86

inductive Register where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr, Inhabited

namespace Register

def all : List Register :=
  [rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi,
   r8, r9, r10, r11, r12, r13, r14, r15]

def index : Register → Fin 16
  | rax => 0 | rcx => 1 | rdx => 2 | rbx => 3
  | rsp => 4 | rbp => 5 | rsi => 6 | rdi => 7
  | r8 => 8 | r9 => 9 | r10 => 10 | r11 => 11 | r12 => 12 | r13 => 13 | r14 => 14 | r15 => 15

def ofIndex (i : Fin 16) : Register := all[i]'(by simp [all])

end Register

abbrev VectorRegister := Fin 16

-- Displacements and branch offsets are stored sign-extended to 64 bits, so
-- address arithmetic is plain wrapping `UInt64` addition, as on the CPU.
inductive Address where
  | relativeToNextInstruction (displacement : UInt64)
  | baseIndex (base : Option Register) (index : Option (Register × Fin 4)) (displacement : UInt64)
  deriving DecidableEq, Repr

inductive RegisterOrMemory where
  | register (r : Register)
  /-- Bits 8–15 of one of the first four registers. Only an 8-bit operand of
  an instruction without a REX byte can name one, so it has its own
  constructor rather than being a register-numbering quirk. -/
  | highByte (r : Register)
  | memory (a : Address)
  deriving DecidableEq, Repr

inductive VectorOrMemory where
  | register (v : VectorRegister)
  | memory (a : Address)
  deriving DecidableEq, Repr

-- Immediates are stored sign-extended to 64 bits and truncated to the operand
-- size when read, since that is what every instruction with one does.
inductive Source where
  | operand (x : RegisterOrMemory)
  | immediate (v : UInt64)
  deriving DecidableEq, Repr

-- In encoding order, so `ofCode` is the opcode's low four bits.
inductive Condition where
  | overflow | notOverflow | below | aboveOrEqual | equal | notEqual | belowOrEqual | above
  | negative | notNegative | parityEven | parityOdd | less | greaterOrEqual | lessOrEqual | greater
  deriving DecidableEq, Repr

def Condition.ofCode (code : UInt8) : Condition :=
  match code &&& 0xf with
  | 0 => .overflow | 1 => .notOverflow | 2 => .below | 3 => .aboveOrEqual
  | 4 => .equal | 5 => .notEqual | 6 => .belowOrEqual | 7 => .above
  | 8 => .negative | 9 => .notNegative | 10 => .parityEven | 11 => .parityOdd
  | 12 => .less | 13 => .greaterOrEqual | 14 => .lessOrEqual | _ => .greater

-- In encoding order, so `ofCode` is the operation field of the opcode.
inductive ArithmeticOp where
  | add | or | addWithCarry | subtractWithBorrow | and | subtract | xor | compare | testBits
  deriving DecidableEq, Repr

def ArithmeticOp.ofCode (code : UInt8) : ArithmeticOp :=
  match code &&& 7 with
  | 0 => .add | 1 => .or | 2 => .addWithCarry | 3 => .subtractWithBorrow
  | 4 => .and | 5 => .subtract | 6 => .xor | _ => .compare

inductive ShiftOp where
  | left | rightLogical | rightArithmetic
  deriving DecidableEq, Repr

inductive ShiftCount where
  | one
  | immediate (n : UInt8)
  | counter
  deriving DecidableEq, Repr

inductive VectorBitwiseOp where
  | and | andNot | or | xor
  deriving DecidableEq, Repr

/-- The data type an SSE instruction is named for. It only changes the
encoding and mnemonic, so it is kept to print the instruction faithfully. -/
inductive VectorDomain where
  | integer | double | single
  deriving DecidableEq, Repr

inductive VectorMove where
  | integerAligned | integerUnaligned | doubleAligned | doubleUnaligned | singleAligned | singleUnaligned
  deriving DecidableEq, Repr

def VectorMove.aligned : VectorMove → Bool
  | .integerAligned | .doubleAligned | .singleAligned => true
  | _ => false

inductive DoubleOp where
  | add | subtract | multiply
  deriving DecidableEq, Repr

inductive Instruction where
  | arithmetic (op : ArithmeticOp) (size : OperandSize) (destination : RegisterOrMemory) (source : Source)
  | move (size : OperandSize) (destination : RegisterOrMemory) (source : Source)
  | moveImmediate64 (destination : Register) (immediate : UInt64)
  | moveZeroExtend (size : OperandSize) (destination : Register) (sourceSize : OperandSize)
      (source : RegisterOrMemory)
  | moveSignExtend (size : OperandSize) (destination : Register) (sourceSize : OperandSize)
      (source : RegisterOrMemory)
  | loadAddress (size : OperandSize) (destination : Register) (address : Address)
  | increment (size : OperandSize) (destination : RegisterOrMemory)
  | decrement (size : OperandSize) (destination : RegisterOrMemory)
  | negate (size : OperandSize) (destination : RegisterOrMemory)
  | complement (size : OperandSize) (destination : RegisterOrMemory)
  | multiplySigned (size : OperandSize) (destination : Register) (source : RegisterOrMemory)
      (immediate : Option UInt64)
  | shift (op : ShiftOp) (size : OperandSize) (destination : RegisterOrMemory) (count : ShiftCount)
  | setIf (condition : Condition) (destination : RegisterOrMemory)
  | moveIf (condition : Condition) (size : OperandSize) (destination : Register) (source : RegisterOrMemory)
  | signExtendAccumulator (size : OperandSize)
  | signExtendIntoData (size : OperandSize)
  | push (source : Source)
  | pop (destination : RegisterOrMemory)
  | jumpIf (condition : Condition) (offset : UInt64)
  | jump (offset : UInt64)
  | jumpIndirect (target : RegisterOrMemory)
  | callRelative (offset : UInt64)
  | call (target : RegisterOrMemory)
  | returnToCaller
  | noOperation (operand : Option (OperandSize × RegisterOrMemory))
  | moveVector (kind : VectorMove) (destination : VectorOrMemory) (source : VectorOrMemory)
  | moveIntegerToVector (size : OperandSize) (destination : VectorRegister) (source : RegisterOrMemory)
  | moveVectorToInteger (size : OperandSize) (destination : RegisterOrMemory) (source : VectorRegister)
  | moveScalarDouble (destination : VectorOrMemory) (source : VectorOrMemory)
  | vectorBitwise (op : VectorBitwiseOp) (domain : VectorDomain) (destination : VectorRegister)
      (source : VectorOrMemory)
  | testVectorBits (destination : VectorRegister) (source : VectorOrMemory)
  | interleaveLow32 (destination : VectorRegister) (source : VectorOrMemory)
  | interleaveLow64 (destination : VectorRegister) (source : VectorOrMemory)
  | interleaveLowDoubles (destination : VectorRegister) (source : VectorOrMemory)
  | interleaveHighDoubles (destination : VectorRegister) (source : VectorOrMemory)
  | packedDouble (op : DoubleOp) (destination : VectorRegister) (source : VectorOrMemory)
  | scalarDouble (op : DoubleOp) (destination : VectorRegister) (source : VectorOrMemory)
  | compareDoubles (destination : VectorRegister) (source : VectorOrMemory)
  | truncateDoubleToInt64 (destination : Register) (source : VectorOrMemory)
  deriving DecidableEq, Repr

end X86
