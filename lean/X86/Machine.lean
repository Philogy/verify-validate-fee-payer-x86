import X86.State
import X86.Decode
import X86.F64

/-!
Flags follow the Intel SDM, vol. 2 ("Flags Affected" of each instruction); a
flag the SDM calls undefined becomes `none`.
-/

namespace X86

namespace Arithmetic

def parity (v : UInt64) : Bool :=
  ((List.range 8).countP fun i => (v >>> i.toUInt64) &&& 1 == 1) % 2 == 0

def resultFlags (size : OperandSize) (r : UInt64) (carry overflow auxiliaryCarry : Option Bool) : Flags :=
  { carry, overflow, auxiliaryCarry, zero := r == 0, sign := size.isNegative r, parity := parity r }

-- Bit 4 of `a ^ b ^ r` is the carry into bit 4, for addition and subtraction alike.
def carryOutOfBit3 (a b r : UInt64) : Bool := (a ^^^ b ^^^ r) &&& 0x10 != 0

end Arithmetic

open Exec Arithmetic

-- `a`, `b` and the results are below `2^size.bits`, so a carry out of the
-- top bit shows as a result below `a`, and a borrow as `a < b`.
def arithmetic (op : ArithmeticOp) (size : OperandSize) (destination : RegisterOrMemory)
    (source : Source) : Exec Unit := do
  let a ← readOperand size destination
  let b ← readSource size source
  let added (r : UInt64) (carry : Bool) : Exec UInt64 := do
    writeFlags (resultFlags size r carry (size.isNegative ((a ^^^ r) &&& (b ^^^ r))) (carryOutOfBit3 a b r))
    pure r
  let subtracted (r : UInt64) (borrow : Bool) : Exec UInt64 := do
    writeFlags (resultFlags size r borrow (size.isNegative ((a ^^^ b) &&& (a ^^^ r))) (carryOutOfBit3 a b r))
    pure r
  let logical (r : UInt64) : Exec UInt64 := do
    writeFlags (resultFlags size r false false none); pure r
  let r ← match op with
    | .add =>
      let r := (a + b) &&& size.mask
      added r (r < a)
    | .addWithCarry => do
      let c ← readFlag .carry
      let r := (a + b + (if c then 1 else 0)) &&& size.mask
      added r (r < a || (c && r == a))
    | .subtract | .compare => subtracted ((a - b) &&& size.mask) (a < b)
    | .subtractWithBorrow => do
      let c ← readFlag .carry
      subtracted ((a - b - (if c then 1 else 0)) &&& size.mask) (a < b || (c && a == b))
    | .and | .testBits => logical (a &&& b)
    | .or => logical (a ||| b)
    | .xor => logical (a ^^^ b)
  unless op == .compare || op == .testBits do writeOperand size destination r

def shift (op : ShiftOp) (size : OperandSize) (destination : RegisterOrMemory) (count : ShiftCount) :
    Exec Unit := do
  let raw : UInt64 ← match count with
    | .one => pure 1
    | .immediate n => pure n.toUInt64
    | .counter => (· &&& 0xff) <$> readRegister .rcx
  let c := raw &&& (if size = .bits64 then 63 else 31)
  let a ← readOperand size destination
  if c = 0 then
    -- The SDM does not say whether a 32-bit register destination still has
    -- its upper half cleared; rather than guess, leave it unsupported.
    if size = .bits32 && destination matches .register _ then
      throw (.unsupported "32-bit shift of a register by 0")
    return
  let w := size.bits.toUInt64
  let r := match op with
    | .left => (a <<< c) &&& size.mask
    | .rightLogical => a >>> c
    | .rightArithmetic => ((size.signExtend a).toInt64 >>> c.toInt64).toUInt64 &&& size.mask
  let bit (i : UInt64) : Bool := (a >>> i) &&& 1 == 1
  -- For 8- and 16-bit operands the masked count can reach the width; the
  -- SDM leaves the carry undefined then.
  let carry : Option Bool :=
    if c ≥ w then none
    else some (match op with
      | .left => bit (w - c)
      | .rightLogical | .rightArithmetic => bit (c - 1))
  let overflow : Option Bool :=
    if c ≠ 1 then none
    else match op with
      | .left => some (size.isNegative r != size.isNegative a)
      | .rightLogical => some (size.isNegative a)
      | .rightArithmetic => some false
  writeFlags (resultFlags size r carry overflow none)
  writeOperand size destination r

def multiplySignedOverflows (size : OperandSize) (a b : UInt64) : Bool :=
  match size with
  | .bits64 => BitVec.smulOverflow a.toBitVec b.toBitVec
  -- Narrower operands, sign-extended, multiply exactly within 64 bits.
  | _ =>
    let p := size.signExtend a * size.signExtend b
    size.signExtend p != p

def requireDefaultMxcsr : Exec Unit := do
  unless (← get).mxcsr &&& ~~~0x3f == defaultMxcsr do
    throw (.unsupported "MXCSR control bits")

def DoubleOp.eval : DoubleOp → UInt64 → UInt64 → UInt64 × F64.Exceptions
  | .add => F64.add | .subtract => F64.sub | .multiply => F64.mul

def jumpBy (offset : UInt64) : Exec Unit :=
  modify fun s => { s with rip := s.rip + offset }

def jumpTo (target : UInt64) : Exec Unit :=
  modify fun s => { s with rip := target }

def lane32 (v : BitVec 128) (i : Nat) : BitVec 32 := v.extractLsb' (32 * i) 32

/-- Execute `i`; the instruction pointer already points past it. -/
def execute (i : Instruction) : Exec Unit := do
  match i with
  | .arithmetic op size destination source => arithmetic op size destination source
  | .move size destination source => writeOperand size destination (← readSource size source)
  | .moveImmediate64 destination v => writeRegister64 destination v
  | .moveZeroExtend size destination sourceSize source =>
    writeRegister size destination (← readOperand sourceSize source)
  | .moveSignExtend size destination sourceSize source =>
    writeRegister size destination (sourceSize.signExtend (← readOperand sourceSize source))
  | .loadAddress size destination a => writeRegister size destination (← effectiveAddress a)
  | .increment size destination =>
    let a ← readOperand size destination
    let r := (a + 1) &&& size.mask
    let carry := (← get).rflags.carry
    writeFlags (resultFlags size r carry (r == size.signBit) (carryOutOfBit3 a 1 r))
    writeOperand size destination r
  | .decrement size destination =>
    let a ← readOperand size destination
    let r := (a - 1) &&& size.mask
    let carry := (← get).rflags.carry
    writeFlags (resultFlags size r carry (a == size.signBit) (carryOutOfBit3 a 1 r))
    writeOperand size destination r
  | .negate size destination =>
    let a ← readOperand size destination
    let r := (0 - a) &&& size.mask
    writeFlags (resultFlags size r (a != 0) (a == size.signBit) (carryOutOfBit3 0 a r))
    writeOperand size destination r
  | .complement size destination =>
    writeOperand size destination (~~~(← readOperand size destination))
  | .multiplySigned size destination source immediate =>
    let a ← readOperand size source
    let b ← match immediate with
      | some v => pure (v &&& size.mask)
      | none => readOperand size (.register destination)
    let overflowed := multiplySignedOverflows size a b
    writeFlags { carry := overflowed, overflow := overflowed,
                 auxiliaryCarry := none, zero := none, sign := none, parity := none }
    writeRegister size destination (a * b)
  | .shift op size destination count => shift op size destination count
  | .setIf condition destination =>
    writeOperand .bits8 destination (if ← holds condition then 1 else 0)
  | .moveIf condition size destination source =>
    -- The source is read, and may fault, whatever the condition; and a 32-bit
    -- conditional move clears the upper half of `destination` even when it
    -- does not move.
    let v ← readOperand size source
    if ← holds condition then writeRegister size destination v
    else writeRegister size destination (← readOperand size (.register destination))
  | .signExtendAccumulator size =>
    writeRegister size .rax (size.half.signExtend (← readOperand size.half (.register .rax)))
  | .signExtendIntoData size =>
    let a ← readOperand size (.register .rax)
    writeRegister size .rdx (if size.isNegative a then size.mask else 0)
  | .push source => push (← readSource .bits64 source)
  | .pop destination =>
    -- The stack pointer moves before the store, so a destination addressed
    -- through it uses the new value.
    let v ← pop
    writeOperand .bits64 destination v
  | .jumpIf condition offset => if ← holds condition then jumpBy offset
  | .jump offset => jumpBy offset
  | .jumpIndirect target => jumpTo (← readOperand .bits64 target)
  | .callRelative offset =>
    push (← get).rip
    jumpBy offset
  | .call t =>
    let target ← readOperand .bits64 t
    push (← get).rip
    jumpTo target
  | .returnToCaller => jumpTo (← pop)
  | .noOperation _ => pure ()
  | .moveVector kind d s => writeVector128 kind.aligned d (← readVector128 kind.aligned s)
  | .moveIntegerToVector size d s => writeVector d (ofHalves (← readOperand size s) 0)
  | .moveVectorToInteger size d s => writeOperand size d (lowHalf (← readVector s))
  | .moveScalarDouble d s =>
    match d, s with
    | .register d, .memory a => writeVector d (ofHalves (← load .bits64 (← effectiveAddress a)) 0)
    | .register d, .register s =>
      writeVector d (ofHalves (lowHalf (← readVector s)) (highHalf (← readVector d)))
    | .memory a, .register s => store .bits64 (← effectiveAddress a) (lowHalf (← readVector s))
    | .memory _, .memory _ => throw (.unsupported "memory-to-memory movsd")
  | .vectorBitwise op _ d s =>
    let a ← readVector d
    let b ← readVector128 true s
    writeVector d (match op with
      | .and => a &&& b | .andNot => ~~~a &&& b | .or => a ||| b | .xor => a ^^^ b)
  | .testVectorBits d s =>
    let a ← readVector d
    let b ← readVector128 true s
    writeFlags { zero := b &&& a == 0, carry := b &&& ~~~a == 0,
                 auxiliaryCarry := false, overflow := false, parity := false, sign := false }
  | .interleaveLow32 d s =>
    let a ← readVector d
    let b ← readVector128 true s
    writeVector d (lane32 b 1 ++ lane32 a 1 ++ lane32 b 0 ++ lane32 a 0)
  | .interleaveLow64 d s | .interleaveLowDoubles d s =>
    let a ← readVector d
    let b ← readVector128 true s
    writeVector d (ofHalves (lowHalf a) (lowHalf b))
  | .interleaveHighDoubles d s =>
    let a ← readVector d
    let b ← readVector128 true s
    writeVector d (ofHalves (highHalf a) (highHalf b))
  | .packedDouble op d s =>
    requireDefaultMxcsr
    let a ← readVector d
    let b ← readVector128 true s
    writeVector d (ofHalves (op.eval (lowHalf a) (lowHalf b)).1 (op.eval (highHalf a) (highHalf b)).1)
  | .scalarDouble op d s =>
    requireDefaultMxcsr
    let a ← readVector d
    let b ← readVector64 s
    writeVector d (ofHalves (op.eval (lowHalf a) b).1 (highHalf a))
  | .compareDoubles d s =>
    requireDefaultMxcsr
    let a ← readVector d
    let b ← readVector64 s
    let ((zero, parity, carry), _) := F64.compareUnordered (lowHalf a) b
    writeFlags { zero, parity, carry, overflow := false, sign := false, auxiliaryCarry := false }
  | .truncateDoubleToInt64 destination s =>
    requireDefaultMxcsr
    writeRegister64 destination (F64.truncateToInt64 (← readVector64 s)).1

/-- Where control may leave the executable code on purpose. Everything the
machine knows about the program around the code is here, so `X86/` has no
addresses of its own. -/
structure Exits where
  returnAddress : UInt64
  /-- A function that does not return (e.g. Rust's panic entry), which is
  not modelled. -/
  panicAt : UInt64

inductive Outcome where
  | running (s : State)
  | returned (s : State)
  | panicked (s : State)
  /-- Control reached an address that is neither an exit nor fetchable. -/
  | badJump (s : State)
  | faulted (why : Fault) (s : State)

-- The exits are checked before fetching: the caller's return address and the
-- panic entry are typically not mapped executable in the model at all.
def step (exits : Exits) (s : State) : Outcome := Id.run do
  let ip := s.rip
  if ip = exits.returnAddress then return .returned s
  if ip = exits.panicAt then return .panicked s
  let .ok _ := s.memory.byte .fetch ip | return .badJump s
  let executed := do
    let (i, length) ← decode s.memory ip
    (execute i).run { s with rip := ip + length.toUInt64 }
  match executed with
  | .ok ((), s') => .running s'
  | .error why => .faulted why s

def run (exits : Exits) : (fuel : Nat) → State → Outcome
  | 0, s => .running s
  | fuel + 1, s =>
    match step exits s with
    | .running s' => run exits fuel s'
    | o => o

end X86
