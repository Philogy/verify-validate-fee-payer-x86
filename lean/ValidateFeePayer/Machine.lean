import ValidateFeePayer.State
import ValidateFeePayer.Decode
import ValidateFeePayer.F64
import ValidateFeePayer.Stack

/-!
The semantics of one instruction (`execute`), and the machine that fetches
instructions from the predecoded code and runs them (`step`, `run`).

Flags follow the Intel SDM, vol. 2 (each instruction's "Flags Affected");
a flag the SDM calls undefined becomes `none`.
-/

namespace ValidateFeePayer.X86

namespace Arithmetic

/-- An operand read as a two's-complement signed number. -/
def toSigned (size : OperandSize) (v : Nat) : Int :=
  if v < 2 ^ (size.bits - 1) then v else (v : Int) - 2 ^ size.bits

/-- `x` is representable as a signed number of `size`. -/
def fitsSigned (size : OperandSize) (x : Int) : Bool :=
  -(2 : Int) ^ (size.bits - 1) ≤ x && x < 2 ^ (size.bits - 1)

/-- Even number of set bits in the low byte. -/
def parity (v : Nat) : Bool := ((List.range 8).countP fun i => v.testBit i) % 2 == 0

/-- `zero`, `sign`, `parity` from a result; the others as given. -/
def resultFlags (size : OperandSize) (r : Nat) (carry overflow auxiliaryCarry : Option Bool) : Flags :=
  { carry, overflow, auxiliaryCarry, zero := r == 0, sign := decide (r ≥ 2 ^ (size.bits - 1)),
    parity := parity r }

/-- The carry out of bit 3, for `auxiliaryCarry`: the same formula serves
addition and subtraction. -/
def carryOutOfBit3 (a b r : Nat) : Bool := (a ^^^ b ^^^ r) >>> 4 % 2 == 1

end Arithmetic

open Exec Arithmetic

def arithmetic (op : ArithmeticOp) (size : OperandSize) (destination : RegisterOrMemory)
    (source : Source) : Exec Unit := do
  let a ← readOperand size destination
  let b ← readSource size source
  let n := 2 ^ size.bits
  let withCarry (r : Nat) (carry : Bool) (signedResult : Int) : Exec Nat := do
    writeFlags (resultFlags size r carry (!fitsSigned size signedResult) (carryOutOfBit3 a b r))
    pure r
  let logical (r : Nat) : Exec Nat := do
    writeFlags (resultFlags size r false false none); pure r
  let r ← match op with
    | .add => withCarry ((a + b) % n) (a + b ≥ n) (toSigned size a + toSigned size b)
    | .subtract | .compare => withCarry ((a + n - b) % n) (a < b) (toSigned size a - toSigned size b)
    | .subtractWithBorrow => do
      let c := if ← readFlag .carry then 1 else 0
      withCarry ((a + 2 * n - b - c) % n) (a < b + c) (toSigned size a - toSigned size b - c)
    | .and | .testBits => logical (a &&& b)
    | .or => logical (a ||| b)
    | .xor => logical (a ^^^ b)
  unless op == .compare || op == .testBits do writeOperand size destination r

/-! A 128-bit vector register as two 64-bit halves or four 32-bit lanes. -/
namespace Lanes
def low (v : BitVec 128) : UInt64 := v.toNat.toUInt64
def high (v : BitVec 128) : UInt64 := (v.toNat >>> 64).toUInt64
def ofHalves (low high : UInt64) : BitVec 128 := BitVec.ofNat 128 (low.toNat + 2 ^ 64 * high.toNat)
def lane32 (v : BitVec 128) (i : Nat) : Nat := (v.toNat >>> (32 * i)) % 2 ^ 32
end Lanes

/-- Floating-point instructions run only under the default control bits
(see `F64`); the exception flags in bits 0–5 may be anything. -/
def requireDefaultFloatControl : Exec Unit := do
  unless (← get).floatControl &&& ~~~0x3f == defaultFloatControl do
    throw (.unsupported "MXCSR control bits")

def raiseFloatExceptions (e : F64.Exceptions) : Exec Unit :=
  modify fun s => { s with floatControl := s.floatControl ||| e.bits }

def jumpBy (offset : Int) : Exec Unit :=
  modify fun s => { s with instructionPointer := s.instructionPointer + (offset % 2 ^ 64).toNat.toUInt64 }

def jumpTo (target : UInt64) : Exec Unit :=
  modify fun s => { s with instructionPointer := target }

/-- Execute `i`; the instruction pointer already points past it. -/
def execute (i : Instruction) : Exec Unit := do
  match i with
  | .arithmetic op size destination source => arithmetic op size destination source
  | .move size destination source => writeOperand size destination (← readSource size source)
  | .moveImmediate64 destination v => writeRegister64 destination v
  | .moveZeroExtendByte size destination source =>
    writeRegister size destination (← readOperand .bits8 source)
  | .loadAddress destination a => writeRegister64 destination (← effectiveAddress a)
  | .increment size destination =>
    let a ← readOperand size destination
    let r := (a + 1) % 2 ^ size.bits
    let carry := (← get).flags.carry
    writeFlags (resultFlags size r carry (a + 1 == 2 ^ (size.bits - 1)) (a % 16 == 15))
    writeOperand size destination r
  | .multiplySigned destination source immediate =>
    let a ← readOperand .bits64 source
    let b ← match immediate with
      | some v => pure v.toNat
      | none => readOperand .bits64 (.register destination)
    let p := toSigned .bits64 a * toSigned .bits64 b
    let overflowed := !fitsSigned .bits64 p
    writeFlags { carry := overflowed, overflow := overflowed,
                 auxiliaryCarry := none, zero := none, sign := none, parity := none }
    writeRegister64 destination (p % 2 ^ 64).toNat.toUInt64
  | .shiftRightSigned destination count =>
    let c := count.toNat % 64
    unless c = 0 do
      let a ← readOperand .bits64 destination
      let r := ((toSigned .bits64 a / 2 ^ c) % 2 ^ 64).toNat
      writeFlags (resultFlags .bits64 r ((a >>> (c - 1)) % 2 == 1)
        (if c = 1 then some false else none) none)
      writeOperand .bits64 destination r
  | .setIf condition destination =>
    writeOperand .bits8 destination (if ← holds condition then 1 else 0)
  | .moveIf condition size destination source =>
    -- The source is read (and may fault) whatever the condition, and a
    -- 32-bit conditional move zeroes the upper half of `destination` even
    -- when it does not move.
    let v ← readOperand size source
    if ← holds condition then writeRegister size destination v
    else writeRegister size destination (← readOperand size (.register destination))
  | .push r => push (← readRegister r)
  | .pop r => writeRegister64 r (← pop)
  | .jumpIf condition offset => if ← holds condition then jumpBy offset
  | .jump offset => jumpBy offset
  | .call t =>
    let target ← readOperand .bits64 t
    push (← get).instructionPointer
    jumpTo target.toUInt64
  | .returnToCaller => jumpTo (← pop)
  | .moveVectorUnaligned d s => writeVector d (← readVector128 false s)
  | .moveVectorAligned d s => writeVector d (← readVector128 true s)
  | .moveIntegerToVector d s => writeVector d (BitVec.ofNat 128 (← readOperand .bits64 s))
  | .vectorBitwise op d s =>
    let a ← readVector d
    let b ← readVector128 true s
    writeVector d (match op with | .xor | .xorDoubles => a ^^^ b | .or => a ||| b)
  | .testVectorBits d s =>
    let a ← readVector d
    let b ← readVector128 true s
    writeFlags { zero := b &&& a == 0, carry := b &&& ~~~a == 0,
                 auxiliaryCarry := false, overflow := false, parity := false, sign := false }
  | .interleaveLow32 d s =>
    let a ← readVector d
    let b ← readVector128 true s
    writeVector d (BitVec.ofNat 128 (Lanes.lane32 a 0 + 2 ^ 32 * Lanes.lane32 b 0 +
      2 ^ 64 * Lanes.lane32 a 1 + 2 ^ 96 * Lanes.lane32 b 1))
  | .interleaveHighDoubles d s =>
    let a ← readVector d
    let b ← readVector128 true s
    writeVector d (Lanes.ofHalves (Lanes.high a) (Lanes.high b))
  | .subtractDoublePairs d s =>
    requireDefaultFloatControl
    let a ← readVector d
    let b ← readVector128 true s
    let (low, e₁) := F64.sub (Lanes.low a) (Lanes.low b)
    let (high, e₂) := F64.sub (Lanes.high a) (Lanes.high b)
    writeVector d (Lanes.ofHalves low high)
    raiseFloatExceptions (e₁.merge e₂)
  | .scalarDouble op d s =>
    requireDefaultFloatControl
    let a ← readVector d
    let b ← readVector64 s
    let f := match op with | .add => F64.add | .subtract => F64.sub | .multiply => F64.mul
    let (r, e) := f (Lanes.low a) b
    writeVector d (Lanes.ofHalves r (Lanes.high a))
    raiseFloatExceptions e
  | .compareDoubles d s =>
    requireDefaultFloatControl
    let a ← readVector d
    let b ← readVector64 s
    let ((zero, parity, carry), e) := F64.compareUnordered (Lanes.low a) b
    writeFlags { zero, parity, carry, overflow := false, sign := false, auxiliaryCarry := false }
    raiseFloatExceptions e
  | .truncateDoubleToInt64 destination s =>
    requireDefaultFloatControl
    let (r, e) := F64.truncateToInt64 (← readVector64 s)
    writeRegister64 destination r
    raiseFloatExceptions e

/-- How execution leaves the carved code at a known address. -/
inductive Exit where
  /-- The caller's return address: the top-level return has happened. -/
  | returned
  /-- `core::option::expect_failed`: the panic. -/
  | panicked
  deriving DecidableEq, Repr

/-- What does not change during a run. -/
structure Env where
  /-- Where the binary is loaded. -/
  loadBase : UInt64
  /-- Addresses outside the carved code where execution may legitimately
  go, and what reaching each means. -/
  exits : List (UInt64 × Exit)
  /-- Low end of the stack mapping (see `Stack`). -/
  stackLow : UInt64

def Env.exitAt (env : Env) (address : UInt64) : Option Exit := env.exits.lookup address

/-- Free stack below the stack pointer (`Stack.free`). -/
def Env.freeStack (env : Env) (stackPointer : UInt64) : Nat := Stack.free env.stackLow stackPointer

def State.stackPointer (s : State) : UInt64 := s.registers[Register.stackPointer.index]

inductive Outcome where
  /-- Ready to execute the instruction at `s.instructionPointer`. -/
  | running (s : State)
  /-- Reached an exit address; `s` is the state there (e.g. the result
  register, memory and stack pointer after the return, or the panic's
  arguments). -/
  | exited (e : Exit) (s : State)
  /-- `s.instructionPointer` is neither an instruction start of the carved
  code nor an exit. -/
  | badJump (s : State)
  /-- The instruction at `s.instructionPointer` stopped the machine without
  effect. -/
  | stopped (why : Stop) (s : State)

/-- One instruction. Execution only takes instructions from `codeTable`,
which `Checks.lean` shows is the decoding of the carved bytes; the code is
mapped read/execute, so no store can change it. -/
def step (env : Env) (s : State) : Outcome :=
  match env.exitAt s.instructionPointer with
  | some e => .exited e s
  | none =>
    match instructionAt (s.instructionPointer - env.loadBase) with
    | none => .badJump s
    | some d =>
      match (execute d.instruction).run
          { s with instructionPointer := s.instructionPointer + d.length.toUInt64 } with
      | .ok ((), s') => .running s'
      | .error why => .stopped why s

/-- At most `fuel` instructions; `running` if fuel runs out. -/
def run (env : Env) : (fuel : Nat) → State → Outcome
  | 0, s => .running s
  | fuel + 1, s =>
    match step env s with
    | .running s' => run env fuel s'
    | o => o

end ValidateFeePayer.X86
