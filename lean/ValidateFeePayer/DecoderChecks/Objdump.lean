import ValidateFeePayer.Code
import ValidateFeePayer.Disasm
import X86.Print

namespace ValidateFeePayer
open X86

def Decoded.text (e : Decoded) : UInt64 × Nat × String :=
  (e.address, e.length, Print.instruction (e.address + e.length.toUInt64) e.instruction)

/-- The generic decoder agrees with llvm-objdump (`Disasm.lean`), an
independent disassembler, on every instruction's address, length, mnemonic
and operands. -/
theorem listing_eq_objdump : listing.map Decoded.text = Disasm.listing := by
  set_option maxRecDepth 100000 in decide +kernel

end ValidateFeePayer
