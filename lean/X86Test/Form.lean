import Lean
import X86.Print

/-!
An instruction's form: its mnemonic and the kind and size of each operand,
with registers, immediates and displacements abstracted away (`add r64, imm`,
`mov m32[b+i], r32`). Coverage is counted per form.
-/

namespace X86Test

open X86 Print

def addressForm : Address → String
  | .relativeToNextInstruction _ => "[rip]"
  | .baseIndex (some _) (some _) _ => "[b+i]"
  | .baseIndex (some _) none _ => "[b]"
  | .baseIndex none (some _) _ => "[i]"
  | .baseIndex none none _ => "[abs]"

def sizeBits (size : OperandSize) : String := toString size.bits

def operandForm (size : OperandSize) : RegisterOrMemory → String
  | .register _ => "r" ++ sizeBits size
  | .highByte _ => "r8h"
  | .memory a => "m" ++ sizeBits size ++ addressForm a

def sourceForm (size : OperandSize) : Source → String
  | .operand x => operandForm size x
  | .immediate _ => "imm"

def vectorForm (bits : Nat) : VectorOrMemory → String
  | .register _ => "xmm"
  | .memory a => "m" ++ toString bits ++ addressForm a

def form (i : Instruction) : String :=
  let operands := match i with
    | .arithmetic _ size d s | .move size d s => [operandForm size d, sourceForm size s]
    | .moveImmediate64 .. => ["r64", "imm64"]
    | .moveZeroExtend size _ sourceSize s | .moveSignExtend size _ sourceSize s =>
      ["r" ++ sizeBits size, operandForm sourceSize s]
    | .loadAddress size _ a => ["r" ++ sizeBits size, addressForm a]
    | .increment size d | .decrement size d | .negate size d | .complement size d => [operandForm size d]
    | .multiplySigned size _ s none => ["r" ++ sizeBits size, operandForm size s]
    | .multiplySigned size _ s (some _) => ["r" ++ sizeBits size, operandForm size s, "imm"]
    | .shift _ size d .one => [operandForm size d, "1"]
    | .shift _ size d (.immediate _) => [operandForm size d, "imm"]
    | .shift _ size d .counter => [operandForm size d, "cl"]
    | .setIf _ d => [operandForm .bits8 d]
    | .moveIf _ size _ s => ["r" ++ sizeBits size, operandForm size s]
    | .signExtendAccumulator _ | .signExtendIntoData _ | .returnToCaller | .noOperation none => []
    | .noOperation (some (size, x)) => [operandForm size x]
    | .push s => [sourceForm .bits64 s]
    | .pop d => [operandForm .bits64 d]
    | .jumpIf .. | .jump _ | .callRelative _ => ["rel"]
    | .jumpIndirect t | .call t => [operandForm .bits64 t]
    | .moveVector _ d s => [vectorForm 128 d, vectorForm 128 s]
    | .vectorBitwise _ _ _ s | .testVectorBits _ s | .interleaveLow32 _ s | .interleaveLow64 _ s
    | .interleaveLowDoubles _ s | .interleaveHighDoubles _ s | .packedDouble _ _ s =>
      ["xmm", vectorForm 128 s]
    | .moveIntegerToVector size _ s => ["xmm", operandForm size s]
    | .moveVectorToInteger size d _ => [operandForm size d, "xmm"]
    | .moveScalarDouble d s => [vectorForm 64 d, vectorForm 64 s]
    | .scalarDouble _ _ s | .compareDoubles _ s => ["xmm", vectorForm 64 s]
    | .truncateDoubleToInt64 _ s => ["r64", vectorForm 64 s]
  if operands.isEmpty then mnemonic i else mnemonic i ++ " " ++ ", ".intercalate operands

open Lean Elab Command in
run_cmd do
  let some (.inductInfo info) := (← getEnv).find? ``X86.Instruction
    | throwError "X86.Instruction is not an inductive type"
  let names := info.ctors.map fun c => c.getString!
  elabCommand (← `(def $(mkIdent `instructionConstructors) : List String := $(quote names)))

def constructorName (i : Instruction) : String :=
  (instructionConstructors[i.ctorIdx]?).getD "?"

end X86Test
