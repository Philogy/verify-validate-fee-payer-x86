import ValidateFeePayer.Code
import ValidateFeePayer.Disasm
import X86.Print

-- Separate from `Checks.lean`: the proof does not use these, and checking
-- them takes the kernel ~30s.

namespace ValidateFeePayer
open Image X86

/-! ## The decoder -/

theorem sweepImage_ok : sweepImage.toOption = some listing := by
  set_option maxRecDepth 100000 in decide +kernel

def Decoded.text (e : Decoded) : UInt64 × Nat × String :=
  (e.address, e.length, Print.instruction (e.address + e.length.toUInt64) e.instruction)

/-- The generic decoder agrees with llvm-objdump (`Disasm.lean`), an
independent disassembler, on every instruction's address, length, mnemonic
and operands. -/
theorem listing_eq_objdump : listing.map Decoded.text = Disasm.listing := by
  set_option maxRecDepth 100000 in decide +kernel

theorem branch_targets :
    listing.all (fun e => match e.instruction with
      | .jumpIf _ offset | .jump offset =>
        (instructionAt (e.address + e.length.toUInt64 + offset)).isSome
      | _ => true) := by
  set_option maxRecDepth 100000 in decide +kernel

end ValidateFeePayer
