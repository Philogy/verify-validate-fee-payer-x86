import X86Test.Harness

/-!
The paths on which the model refuses to go on, which no vector can reach: a
vector's `rip` is always in the executable code page, the exits are
unreachable from one step, every vector starts with the flags defined and the
default MXCSR, and no instruction the decoder accepts nears 15 bytes.
-/

namespace X86Test

open X86

def stateAt (rip : UInt64) (code : List UInt8) (flags : Flags := ⟨some false, some false, some false, some false, some false, some false⟩) : State :=
  let s := initialState [] defaultAt
  { s with rip, rflags := flags, memory := flatten (poke s.memory rip code) }

def outcomeName : Outcome → String
  | .running _ => "running" | .returned _ => "returned" | .panicked _ => "panicked"
  | .badJump _ => "badJump" | .faulted why _ => s!"faulted {reprStr why}"

def nop : List UInt8 := [0x90]

/-! Fetching only from executable memory. -/
#guard outcomeName (step exits (stateAt (codePage + defaultAt) nop)) == "running"
#guard outcomeName (step exits (stateAt dataPage nop)) == "badJump"
#guard outcomeName (step exits (stateAt readOnlyPage nop)) == "badJump"
#guard outcomeName (step exits (stateAt stackPage nop)) == "badJump"
#guard outcomeName (step exits (stateAt 0x50002000 nop)) == "badJump"
-- An instruction that runs off the executable page faults on the fetch.
#guard outcomeName (step exits (stateAt (codePage + 0xfff) [0x48])) ==
  "faulted X86.Fault.pageFault (X86.PageFault.unmapped 1073745920 (X86.Access.fetch))"

/-! The exits are checked before the fetch, so they win even over executable code. -/
def exitsInCode : Exits := { returnAddress := codePage + 0x10, panicAt := codePage + 0x20 }
#guard outcomeName (step exitsInCode (stateAt (codePage + 0x10) nop)) == "returned"
#guard outcomeName (step exitsInCode (stateAt (codePage + 0x20) nop)) == "panicked"
#guard outcomeName (step exitsInCode (stateAt (codePage + 0x18) nop)) == "running"
#guard outcomeName (step exits (stateAt exits.returnAddress [])) == "returned"
#guard outcomeName (step exits (stateAt exits.panicAt [])) == "panicked"
-- `run` stops at an exit instead of stepping on.
#guard outcomeName (X86.run exitsInCode 100 (stateAt (codePage + 0x0f) nop)) == "returned"

/-! Reading a flag the model holds undefined faults, for every condition and
for the carry `adc`/`sbb` consume; a flag the instruction does not read may
stay undefined. -/
def onlyUndefined (f : Flag) : Flags := setFlag ⟨some false, some false, some false, some false, some false, some false⟩ f none

def conditionFlags : Condition → List Flag
  | .overflow | .notOverflow => [.overflow]
  | .below | .aboveOrEqual => [.carry]
  | .equal | .notEqual => [.zero]
  | .belowOrEqual | .above => [.carry, .zero]
  | .negative | .notNegative => [.sign]
  | .parityEven | .parityOdd => [.parity]
  | .less | .greaterOrEqual => [.sign, .overflow]
  | .lessOrEqual | .greater => [.zero, .sign, .overflow]

def allConditions : List Condition :=
  (List.range 16).map fun n => Condition.ofCode n.toUInt8

def readsOf (i : Instruction) : List Flag :=
  flagOrder.filter fun f =>
    match (execute i).run (stateAt (codePage + defaultAt) [] (onlyUndefined f)) with
    | .error (.undefinedFlagRead g) => g == f
    | _ => false

#guard allConditions.length == 16 && allConditions.eraseDups.length == 16
-- `jcc`, `setcc` and `cmovcc` read exactly the flags of their condition. Flags
-- are set to false otherwise, so a short-circuiting `holds` still has to read
-- every flag of a condition before it can tell.
#guard allConditions.all fun c =>
  let want := flagOrder.filter (conditionFlags c).contains
  readsOf (.jumpIf c 4) == want && readsOf (.setIf c (.register .rax)) == want &&
    readsOf (.moveIf c .bits64 .rax (.register .rcx)) == want
#guard readsOf (.arithmetic .addWithCarry .bits64 (.register .rax) (.operand (.register .rcx))) == [.carry]
#guard readsOf (.arithmetic .subtractWithBorrow .bits8 (.register .rax) (.immediate 1)) == [.carry]
#guard readsOf (.arithmetic .add .bits64 (.register .rax) (.operand (.register .rcx))) == []
#guard readsOf (.increment .bits64 (.register .rax)) == []
-- Through `step`: the fault leaves the state as it was.
#guard match step exits (stateAt (codePage + defaultAt) [0x74, 0x02] (onlyUndefined .zero)) with
  | .faulted (.undefinedFlagRead .zero) s => s.rip == codePage + defaultAt
  | _ => false

/-! The floating-point instructions run only under the default MXCSR control
bits (sticky exception flags may be set): any rounding mode, flush-to-zero,
denormals-are-zero or unmasked exception is refused. -/
def floatInstructions : List Instruction :=
  [.packedDouble .add 0 (.register 1), .packedDouble .subtract 0 (.register 1), .packedDouble .multiply 0 (.register 1),
   .scalarDouble .add 0 (.register 1), .scalarDouble .subtract 0 (.register 1), .scalarDouble .multiply 0 (.register 1),
   .compareDoubles 0 (.register 1), .truncateDoubleToInt64 .rax (.register 1)]

def withMxcsr (m : UInt32) : State := { stateAt (codePage + defaultAt) [] with mxcsr := m }

def refusedMxcsr : List UInt32 :=
  ([0x3f80, 0x5f80, 0x7f80, 0x9f80, 0x1fc0] : List UInt32) ++ (List.range 6).map fun b => (0x1f80 : UInt32) ^^^ ((0x80 : UInt32) <<< b.toUInt32)

def acceptedMxcsr : List UInt32 := [0x1f80, 0x1f81, 0x1fbf]

#guard floatInstructions.all fun i =>
  refusedMxcsr.all (fun m => match (execute i).run (withMxcsr m) with
    | .error (.unsupported "MXCSR control bits") => true | _ => false) &&
  acceptedMxcsr.all (fun m => match (execute i).run (withMxcsr m) with
    | .ok _ => true | _ => false)
-- Instructions that do no arithmetic ignore the control bits.
#guard [Instruction.vectorBitwise .xor .integer 0 (.register 1), .moveScalarDouble (.register 0) (.register 1),
        .testVectorBits 0 (.register 1)].all fun i =>
  refusedMxcsr.all fun m => match (execute i).run (withMxcsr m) with | .ok _ => true | _ => false

/-! Fifteen bytes at most. The decoder accepts at most two prefixes, so its
longest instruction is far shorter and `tooLong` is unreachable today; these
pin the limit and the fetch for when that changes. -/
#guard maxInstructionLength == 15
#guard decodeWith.go (fun _ => .ok 0x66) 0 0 [] matches .error (.undecodable .tooLong)
#guard decodeWith (fun _ => .ok 0x66) 0 matches .error (.undecodable (.unsupported _))
end X86Test
