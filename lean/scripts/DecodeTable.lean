import ValidateFeePayer.Code

/-! Writes `ValidateFeePayer/Proof/DecodeTable.lean`:
`lake env lean --run scripts/DecodeTable.lean > ValidateFeePayer/Proof/DecodeTable.lean` -/

open ValidateFeePayer

def hexDigits (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def lemma (d : Decoded) : String :=
  let i := ((repr d.instruction).pretty 100000).replace "X86." ""
  s!"@[decode_table] theorem decode_{hexDigits d.address.toNat} :
    decodeWith codeByte 0x{hexDigits d.address.toNat} = .ok ({i}, {d.length}) := by
  decide +kernel
"

def main : IO Unit := do
  IO.print "import ValidateFeePayer.Code
import ValidateFeePayer.Proof.Attr

/-! Generated from `listing`: the instruction at each address, decoded from the image at load base 0. -/

namespace ValidateFeePayer.Proof

open X86

deriving instance DecidableEq for Except

"
  IO.print ("\n".intercalate (listing.map lemma))
  IO.print "\nend ValidateFeePayer.Proof\n"
