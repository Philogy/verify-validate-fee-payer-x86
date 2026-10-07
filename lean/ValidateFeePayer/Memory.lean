import ValidateFeePayer.Image

/-!
The fixed part of the initial memory: the carved regions at load base `B`.
Every other address is unmapped (`none`). The argument structs and the stack
are not part of this; a precondition will supply them.
-/

namespace ValidateFeePayer

open Image in
def regions : List Region := functions ++ data

/-- One past the highest carved address at load base 0. -/
def imageEnd : Nat := regions.foldl (fun acc r => max acc r.endAddr) 0

/-- Load bases at which no carved address wraps around 2^64. The kernel loads
at page-aligned bases, but nothing in the carved code depends on that. -/
def ValidBase (B : UInt64) : Prop := B.toNat + imageEnd ≤ 2 ^ 64

instance : DecidablePred ValidBase := fun _B => inferInstanceAs (Decidable (_ ≤ _))

def fixedMemory (B : UInt64) (addr : UInt64) : Option UInt8 :=
  regions.findSome? fun r => (r.load B).byteAt? addr

/-- Where execution starts. -/
def entry (B : UInt64) : UInt64 := B + Image.validate_fee_payer.vaddr

/-- Reaching this address is the panicked outcome; no code is mapped there. -/
def panicEntry (B : UInt64) : UInt64 := B + Image.panicEntry

end ValidateFeePayer
