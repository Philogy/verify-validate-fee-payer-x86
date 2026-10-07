import ValidateFeePayer.Memory
import ValidateFeePayer.Instruction

/-!
The x86-64 user-mode state the carved code can observe or change (see
`x86-state.md`), and the monad in which one instruction runs.
-/

namespace ValidateFeePayer.X86

/-- The status flags: one-bit facts about the last result, which
conditional instructions read. -/
inductive Flag where
  /-- Unsigned overflow: a carry out of, or borrow into, the top bit (x86: `CF`). -/
  | carry
  /-- The low byte of the result has an even number of set bits (x86: `PF`). -/
  | parity
  /-- A carry out of bit 3 (x86: `AF`). Nothing here reads it. -/
  | auxiliaryCarry
  /-- The result is zero (x86: `ZF`). -/
  | zero
  /-- The top bit of the result, i.e. it is negative as a signed number (x86: `SF`). -/
  | sign
  /-- Signed overflow (x86: `OF`). -/
  | overflow
  deriving DecidableEq, Repr

/-- The six status flags (x86: in `RFLAGS`). `none` means architecturally
undefined: the last instruction that wrote the flag left it undefined (e.g.
`multiplySigned` and `zero`), or nothing in the program has written it yet.
Real CPUs hold some value there, but the program must not depend on it, so
reading one stops the machine with `undefinedFlagRead` instead of guessing. -/
structure Flags where
  carry : Option Bool
  parity : Option Bool
  auxiliaryCarry : Option Bool
  zero : Option Bool
  sign : Option Bool
  overflow : Option Bool
  deriving DecidableEq, Repr

def Flags.undefined : Flags := ⟨none, none, none, none, none, none⟩

def Flags.get (f : Flags) : Flag → Option Bool
  | .carry => f.carry | .parity => f.parity | .auxiliaryCarry => f.auxiliaryCarry
  | .zero => f.zero | .sign => f.sign | .overflow => f.overflow

/-- The default floating-point control and status word (x86: `MXCSR =
0x1f80`): all exceptions masked, round to nearest, no flush-to-zero or
denormals-are-zero, no exception flags raised. -/
def defaultFloatControl : UInt32 := 0x1f80

structure State where
  /-- Address of the next instruction to execute (x86: `rip`, the
  instruction pointer). -/
  instructionPointer : UInt64
  /-- The 16 general-purpose registers, indexed by `Register.index`. -/
  registers : Vector UInt64 16
  flags : Flags
  /-- The direction flag (x86: `DF`). No carved instruction reads or writes
  it; the ABI makes it clear on entry, and the oracle checks it stays so. -/
  directionFlag : Bool
  /-- The 16 vector registers (x86: `xmm0` … `xmm15`). -/
  vectorRegisters : Vector (BitVec 128) 16
  /-- Floating-point control (rounding, masks) and sticky exception flags
  (x86: `MXCSR`). -/
  floatControl : UInt32
  memory : Memory

/-- Why the machine stopped in the middle of an instruction. The state is
the one before that instruction: a faulting instruction has no effect. -/
inductive Stop where
  /-- Page fault: the access is to an unmapped address or not permitted. -/
  | fault (f : Fault)
  /-- A misaligned 16-byte vector memory operand (x86: `#GP`, general
  protection fault). -/
  | misaligned (address : UInt64)
  /-- A read of a flag that is undefined (`Flags`). -/
  | undefinedFlagRead (f : Flag)
  /-- A setting outside what is modelled, e.g. non-default floating-point
  control bits for a floating-point instruction. -/
  | unsupported (what : String)
  deriving Repr

def OperandSize.width : OperandSize → Width
  | .bits8 => .bytes1 | .bits32 => .bytes4 | .bits64 => .bytes8

/-- One instruction's computation: reads and updates the state, or stops. -/
abbrev Exec := StateT State (Except Stop)

namespace Exec

def readRegister (r : Register) : Exec UInt64 := do return (← get).registers[r.index]

/-- Write all 64 bits of a register. -/
def writeRegister64 (r : Register) (v : UInt64) : Exec Unit :=
  modify fun s => { s with registers := s.registers.set r.index v }

/-- The low `size.bits` bits of `v`. -/
def truncate (size : OperandSize) (v : Nat) : Nat := v % 2 ^ size.bits

/-- Write a register at operand size: 32-bit writes zero the upper half,
8-bit writes keep bits 8–63. -/
def writeRegister (size : OperandSize) (r : Register) (v : Nat) : Exec Unit := do
  match size with
  | .bits64 => writeRegister64 r v.toUInt64
  | .bits32 => writeRegister64 r (truncate .bits32 v).toUInt64
  | .bits8 => writeRegister64 r (((← readRegister r) &&& ~~~0xff) ||| (truncate .bits8 v).toUInt64)

def liftFault (x : Except Fault α) : Exec α :=
  match x with
  | .ok v => pure v
  | .error f => throw (.fault f)

/-- The address a memory operand refers to (x86: its "effective address"). -/
def effectiveAddress : Address → Exec UInt64
  | .relativeToNextInstruction d => do
    return (← get).instructionPointer + (d % 2 ^ 64).toNat.toUInt64
  | .baseIndex base index d => do
    let b ← match base with | some r => readRegister r | none => pure 0
    let i ← match index with
      | some (r, scale) => do pure ((← readRegister r) <<< scale.val.toUInt64)
      | none => pure 0
    return b + i + (d % 2 ^ 64).toNat.toUInt64

def load (w : Width) (a : UInt64) : Exec Nat := do
  return (← liftFault ((← get).memory.read w a)).toNat

def store (w : Width) (a : UInt64) (v : Nat) : Exec Unit := do
  let m ← liftFault ((← get).memory.write w a (BitVec.ofNat _ v))
  modify fun s => { s with memory := m }

/-- An integer operand, zero-extended to `Nat`, below `2 ^ size.bits`. -/
def readOperand (size : OperandSize) : RegisterOrMemory → Exec Nat
  | .register r => do return truncate size (← readRegister r).toNat
  | .memory a => do load size.width (← effectiveAddress a)

def writeOperand (size : OperandSize) : RegisterOrMemory → Nat → Exec Unit
  | .register r, v => writeRegister size r v
  | .memory a, v => do store size.width (← effectiveAddress a) (truncate size v)

def readSource (size : OperandSize) : Source → Exec Nat
  | .operand x => readOperand size x
  | .immediate v => pure (truncate size v.toNat)

def readFlag (f : Flag) : Exec Bool := do
  match (← get).flags.get f with
  | some b => pure b
  | none => throw (.undefinedFlagRead f)

def writeFlags (f : Flags) : Exec Unit := modify fun s => { s with flags := f }

/-- Whether a condition holds, from the flags. -/
def holds : Condition → Exec Bool
  | .overflow => readFlag .overflow
  | .notOverflow => return !(← readFlag .overflow)
  | .below => readFlag .carry
  | .aboveOrEqual => return !(← readFlag .carry)
  | .equal => readFlag .zero
  | .notEqual => return !(← readFlag .zero)
  | .belowOrEqual => return (← readFlag .carry) || (← readFlag .zero)
  | .above => return !(← readFlag .carry) && !(← readFlag .zero)
  | .negative => readFlag .sign
  | .notNegative => return !(← readFlag .sign)
  | .parityEven => readFlag .parity
  | .parityOdd => return !(← readFlag .parity)
  | .less => return (← readFlag .sign) != (← readFlag .overflow)
  | .greaterOrEqual => return (← readFlag .sign) == (← readFlag .overflow)
  | .lessOrEqual => return (← readFlag .zero) || (← readFlag .sign) != (← readFlag .overflow)
  | .greater => return !(← readFlag .zero) && (← readFlag .sign) == (← readFlag .overflow)

def readVector (v : VectorRegister) : Exec (BitVec 128) := do return (← get).vectorRegisters[v]

def writeVector (v : VectorRegister) (x : BitVec 128) : Exec Unit :=
  modify fun s => { s with vectorRegisters := s.vectorRegisters.set v x }

/-- A 128-bit operand. A memory operand must be 16-byte aligned unless the
instruction is an unaligned one (`moveVectorUnaligned`). -/
def readVector128 (aligned : Bool) : VectorOrMemory → Exec (BitVec 128)
  | .register v => readVector v
  | .memory a => do
    let address ← effectiveAddress a
    if aligned && address % 16 != 0 then throw (.misaligned address)
    return BitVec.ofNat 128 (← load .bytes16 address)

/-- A 64-bit operand (x86: `xmm/m64`): the low half of a register. No
alignment requirement. -/
def readVector64 : VectorOrMemory → Exec UInt64
  | .register v => do return (← readVector v).toNat.toUInt64
  | .memory a => do return (← load .bytes8 (← effectiveAddress a)).toUInt64

def push (v : UInt64) : Exec Unit := do
  let sp := (← readRegister .stackPointer) - 8
  store .bytes8 sp v.toNat
  writeRegister64 .stackPointer sp

def pop : Exec UInt64 := do
  let sp ← readRegister .stackPointer
  let v ← load .bytes8 sp
  writeRegister64 .stackPointer (sp + 8)
  return v.toUInt64

end Exec

end ValidateFeePayer.X86
