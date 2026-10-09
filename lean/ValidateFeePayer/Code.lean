import X86.Decode
import ValidateFeePayer.Image

/-!
A linear sweep of the carved functions with the generic decoder. The machine
does not use it (it decodes from memory at the instruction pointer); it
exists so `DecoderChecks/Objdump.lean` can compare the decoder with llvm-objdump and so
proofs have the instruction at each address at hand.
-/

namespace ValidateFeePayer

open X86

structure Decoded where
  address : UInt64
  instruction : Instruction
  length : Nat
  deriving DecidableEq, Repr

-- `fuel` bounds the number of instructions; each takes at least one byte.
def sweep : (fuel : Nat) → (address : UInt64) → List UInt8 →
    Except (UInt64 × DecodeError) (List Decoded)
  | _, _, [] => pure []
  | 0, address, _ => throw (address, .unsupported "out of fuel")
  | fuel + 1, address, bytes => do
    let (i, length) ← (decodeBytes (bytes.take maxInstructionLength)).mapError (address, ·)
    let rest ← sweep fuel (address + length.toUInt64) (bytes.drop length)
    pure (⟨address, i, length⟩ :: rest)

def sweepRegion (r : Region) : Except (UInt64 × DecodeError) (List Decoded) :=
  match r.contents with
  | .code bytes => sweep bytes.size r.address.off bytes.toList
  | _ => throw (r.address.off, .unsupported "not a code region")

def sweepImage : Except (UInt64 × DecodeError) (List Decoded) := do
  return (← Image.functions.mapM sweepRegion).flatten

/-- `DecoderChecks/Sweep.lean` proves `sweepImage = .ok listing`, so the fallback is never taken. -/
def listing : List Decoded :=
  match sweepImage with
  | .ok t => t
  | .error _ => []

def instructionAt (address : UInt64) : Option Decoded := listing.find? (·.address == address)

/-- Image bytes at load base 0, as a fetch function for `decodeWith`. -/
def codeByte (address : UInt64) : Except PageFault UInt8 :=
  match Image.functions.find? (fun r => decide (r.Contains address)) with
  | some { address := start, contents := .code bytes, .. } =>
    match bytes[address.toNat - start.off.toNat]? with
    | some b => .ok b
    | none => .error (.unmapped address .fetch)
  | _ => .error (.unmapped address .fetch)

end ValidateFeePayer
