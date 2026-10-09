import X86Test.Harness
import X86Test.Form

/-!
The Intel SDM's "Flags Affected" for each instruction the model supports,
written from the manual rather than from `Machine.lean`, and checked against
what the model does: on every vector that completes (`x86-test behaviour`)
and on the register operands below (`#guard`). The CPU alone cannot catch a
flag the SDM leaves undefined becoming defined: it returns some value either
way, and on one vendor that value may be the "natural" one.
-/

namespace X86Test

open X86

inductive Effect where
  /-- Set according to the result. -/
  | set
  | cleared
  | undefined
  | unchanged
  deriving DecidableEq, Repr

/-- The shift count after the CPU masks it: 5 bits, 6 with REX.W. -/
def maskedShiftCount (s : State) (size : OperandSize) (count : ShiftCount) : Nat :=
  let raw := match count with
    | .one => 1
    | .immediate n => n.toNat
    | .counter => (s.register .rcx).toNat % 256
  raw % (if size = .bits64 then 64 else 32)

/-- Vol. 2, "Flags Affected" of each instruction. `s` is the state before,
which a shift needs for its count. -/
def flagsAffected (s : State) : Instruction → Flag → Effect
  | .arithmetic op .., f =>
    match op, f with
    | .and, .overflow | .or, .overflow | .xor, .overflow | .testBits, .overflow
    | .and, .carry | .or, .carry | .xor, .carry | .testBits, .carry => .cleared
    | .and, .auxiliaryCarry | .or, .auxiliaryCarry | .xor, .auxiliaryCarry | .testBits, .auxiliaryCarry => .undefined
    | _, _ => .set
  | .increment .., .carry | .decrement .., .carry => .unchanged
  | .increment .., _ | .decrement .., _ | .negate .., _ => .set
  | .multiplySigned .., .carry | .multiplySigned .., .overflow => .set
  | .multiplySigned .., _ => .undefined
  | .shift op size _ count, f =>
    let c := maskedShiftCount s size count
    if c = 0 then .unchanged else
    match f with
    | .carry => if c ≥ size.bits && op != .rightArithmetic then .undefined else .set
    | .overflow => if c != 1 then .undefined else if op == .rightArithmetic then .cleared else .set
    | .auxiliaryCarry => .undefined
    | _ => .set
  | .testVectorBits .., .zero | .testVectorBits .., .carry => .set
  | .testVectorBits .., _ => .cleared
  | .compareDoubles .., .zero | .compareDoubles .., .parity | .compareDoubles .., .carry => .set
  | .compareDoubles .., _ => .cleared
  | _, _ => .unchanged

/-- Where the model leaves undefined a flag the SDM defines. That is sound
(the model faults if the program reads it) but weaker, so each case is
listed. `sar` by at least the width of an 8- or 16-bit operand: the SDM's
exception for the carry names only `shl` and `shr`, but the model treats
all three shifts alike there. -/
def modelLeavesUndefined (s : State) : Instruction → Flag → Bool
  | .shift .rightArithmetic size _ count, .carry => maskedShiftCount s size count ≥ size.bits
  | _, _ => false

def flagViolations (i : Instruction) (before after : State) : List String :=
  flagOrder.filterMap fun f =>
    let now := after.rflags.get f
    let effect := flagsAffected before i f
    let ok := match effect with
      | .set => now.isSome || modelLeavesUndefined before i f
      | .cleared => now == some false
      | .undefined => now.isNone
      | .unchanged => now == before.rflags.get f
    if ok then none else some s!"{repr f}: the SDM says {repr effect}, the model gives {now}"

/-- The SDM table against one `step` of the model from `before`, if it completes. -/
def sdmViolations (before : State) : List String :=
  match decode before.memory before.rip, step exits before with
  | .ok (i, _), .running after => flagViolations i before after
  | _, _ => []

/-! Register operands, so nothing faults; the values include each width's
edges, and the shift counts reach and pass each width. -/

def sizes : List OperandSize := [.bits8, .bits16, .bits32, .bits64]

def sampleInstructions : List Instruction :=
  let rax := RegisterOrMemory.register .rax
  let rcx := Source.operand (.register .rcx)
  let arithmetic := [ArithmeticOp.add, .or, .addWithCarry, .subtractWithBorrow, .and, .subtract, .xor, .compare, .testBits].flatMap fun op =>
    sizes.flatMap fun size => [Instruction.arithmetic op size rax rcx, .arithmetic op size rax (.immediate 0x80)]
  let unary := sizes.flatMap fun size => [Instruction.increment size rax, .decrement size rax, .negate size rax, .complement size rax]
  let multiply := [OperandSize.bits16, .bits32, .bits64].flatMap fun size =>
    [Instruction.multiplySigned size .rax (.register .rcx) none, .multiplySigned size .rax (.register .rcx) (some 3)]
  let counts := [0, 1, 2, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 255].map fun n => ShiftCount.immediate (UInt8.ofNat n)
  let shifts := [ShiftOp.left, .rightLogical, .rightArithmetic].flatMap fun op =>
    sizes.flatMap fun size => (ShiftCount.one :: ShiftCount.counter :: counts).map (Instruction.shift op size rax ·)
  let others := [
    Instruction.move .bits64 rax rcx, .moveImmediate64 .rax 5, .moveZeroExtend .bits32 .rax .bits8 (.register .rcx),
    .moveSignExtend .bits64 .rax .bits16 (.register .rcx), .loadAddress .bits64 .rax (.baseIndex (some .rcx) none 8),
    .setIf .below rax, .moveIf .equal .bits64 .rax (.register .rcx), .signExtendAccumulator .bits64,
    .signExtendIntoData .bits64, .push rcx, .pop rax, .jumpIf .equal 4, .jump 4, .jumpIndirect (.register .rcx),
    .callRelative 4, .call (.register .rcx), .returnToCaller, .noOperation none,
    .moveVector .integerAligned (.register 0) (.register 1), .moveIntegerToVector .bits64 0 (.register .rcx),
    .moveVectorToInteger .bits64 rax 1, .moveScalarDouble (.register 0) (.register 1),
    .vectorBitwise .xor .integer 0 (.register 1), .testVectorBits 0 (.register 1), .testVectorBits 0 (.register 0),
    .interleaveLow32 0 (.register 1), .interleaveLow64 0 (.register 1), .interleaveLowDoubles 0 (.register 1),
    .interleaveHighDoubles 0 (.register 1), .packedDouble .add 0 (.register 1), .scalarDouble .multiply 0 (.register 1),
    .compareDoubles 0 (.register 1), .compareDoubles 0 (.register 0), .truncateDoubleToInt64 .rax (.register 1)]
  arithmetic ++ unary ++ multiply ++ shifts ++ others

def sampleValues : List UInt64 :=
  [0, 1, 0x7f, 0x80, 0xff, 0x8000, 0xffff, 0x7fffffff, 0x80000000, 0xffffffff,
   0x8000000000000000, 0xffffffffffffffff, 0x0123456789abcdef]

def sampleStates : List State :=
  let base := flatten (initialState [] defaultAt).memory
  [true, false].flatMap fun flag => sampleValues.flatMap fun a => [0, 8, 16, 0xffffffffffffffff].map fun c =>
    let s := initialState [] defaultAt
    { s with
      memory := base
      registers := (s.registers.set Register.rax.index a).set Register.rcx.index (if c = 0 then a else c)
      rflags := ⟨some flag, some flag, some flag, some flag, some flag, some flag⟩
      xmm := (s.xmm.set 0 (BitVec.ofNat 128 (a.toNat * 0x10001))).set 1 (BitVec.ofNat 128 a.toNat) }

def sampleViolations : List String := Id.run do
  let mut out := #[]
  for i in sampleInstructions do
    for s in sampleStates do
      if let .ok ((), after) := (execute i).run s then
        for v in flagViolations i s after do
          out := out.push s!"{reprStr i}: {v}"
  return out.toList

#guard sampleViolations == []

-- Every constructor appears in the sample.
#guard instructionConstructors.all fun c => sampleInstructions.any (constructorName · == c)

end X86Test
