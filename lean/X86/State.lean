import X86.Fault
import X86.Instruction

namespace X86

/-- `none` is a flag the SDM calls undefined after the last instruction that
wrote it (or that the entry state leaves unspecified). -/
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

def defaultFloatControl : UInt32 := 0x1f80

structure State where
  instructionPointer : UInt64
  registers : Vector UInt64 16
  flags : Flags
  vectorRegisters : Vector (BitVec 128) 16
  -- Only the control bits are modelled. The sticky exception bits (0–5) are
  -- not: no supported instruction reads them, so they cannot affect a run,
  -- and the hardware comparison masks them.
  floatControl : UInt32
  memory : Memory

def State.register (s : State) (r : Register) : UInt64 := s.registers[r.index]

def State.stackPointer (s : State) : UInt64 := s.register .stackPointer

def OperandSize.width : OperandSize → Width
  | .bits8 => .bytes1 | .bits16 => .bytes2 | .bits32 => .bytes4 | .bits64 => .bytes8

abbrev Exec := StateT State (Except Fault)

namespace Exec

def readRegister (r : Register) : Exec UInt64 := do return (← get).register r

def writeRegister64 (r : Register) (v : UInt64) : Exec Unit :=
  modify fun s => { s with registers := s.registers.set r.index v }

-- 32-bit writes zero the upper half; 8- and 16-bit writes keep the bits above.
def writeRegister (size : OperandSize) (r : Register) (v : UInt64) : Exec Unit := do
  match size with
  | .bits64 => writeRegister64 r v
  | .bits32 => writeRegister64 r (v &&& size.mask)
  | .bits16 | .bits8 => writeRegister64 r (((← readRegister r) &&& ~~~size.mask) ||| (v &&& size.mask))

def liftPageFault (x : Except PageFault α) : Exec α :=
  match x with
  | .ok v => pure v
  | .error f => throw (.pageFault f)

def effectiveAddress : Address → Exec UInt64
  | .relativeToNextInstruction d => do return (← get).instructionPointer + d
  | .baseIndex base index d => do
    let b ← match base with | some r => readRegister r | none => pure 0
    let i ← match index with
      | some (r, scale) => do pure ((← readRegister r) <<< scale.val.toUInt64)
      | none => pure 0
    return b + i + d

def load (w : Width) (a : UInt64) : Exec UInt64 := do liftPageFault ((← get).memory.read w a)

def store (w : Width) (a : UInt64) (v : UInt64) : Exec Unit := do
  let m ← liftPageFault ((← get).memory.write w a v)
  modify fun s => { s with memory := m }

def readOperand (size : OperandSize) : RegisterOrMemory → Exec UInt64
  | .register r => do return (← readRegister r) &&& size.mask
  | .highByte r => do return ((← readRegister r) >>> 8) &&& 0xff
  | .memory a => do load size.width (← effectiveAddress a)

def writeOperand (size : OperandSize) : RegisterOrMemory → UInt64 → Exec Unit
  | .register r, v => writeRegister size r v
  | .highByte r, v => do
    writeRegister64 r (((← readRegister r) &&& ~~~(0xff00 : UInt64)) ||| ((v &&& 0xff) <<< 8))
  | .memory a, v => do store size.width (← effectiveAddress a) v

def readSource (size : OperandSize) : Source → Exec UInt64
  | .operand x => readOperand size x
  | .immediate v => pure (v &&& size.mask)

def readFlag (f : Flag) : Exec Bool := do
  match (← get).flags.get f with
  | some b => pure b
  | none => throw (.undefinedFlagRead f)

def writeFlags (f : Flags) : Exec Unit := modify fun s => { s with flags := f }

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

def vectorAddress (aligned : Bool) (a : Address) : Exec UInt64 := do
  let address ← effectiveAddress a
  if aligned && address % 16 != 0 then throw (.misaligned address)
  return address

def readVector128 (aligned : Bool) : VectorOrMemory → Exec (BitVec 128)
  | .register v => readVector v
  | .memory a => do liftPageFault ((← get).memory.read128 (← vectorAddress aligned a))

def writeVector128 (aligned : Bool) : VectorOrMemory → BitVec 128 → Exec Unit
  | .register v, x => writeVector v x
  | .memory a, x => do
    let m ← liftPageFault ((← get).memory.write128 (← vectorAddress aligned a) x)
    modify fun s => { s with memory := m }

-- Scalar (64-bit) vector operands have no alignment requirement.
def readVector64 : VectorOrMemory → Exec UInt64
  | .register v => do return lowHalf (← readVector v)
  | .memory a => do load .bytes8 (← effectiveAddress a)

def push (v : UInt64) : Exec Unit := do
  let sp := (← readRegister .stackPointer) - 8
  store .bytes8 sp v
  writeRegister64 .stackPointer sp

def pop : Exec UInt64 := do
  let sp ← readRegister .stackPointer
  let v ← load .bytes8 sp
  writeRegister64 .stackPointer (sp + 8)
  return v

end Exec

end X86
