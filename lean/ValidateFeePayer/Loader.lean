import X86.Memory
import ValidateFeePayer.Image

/-!
The carved image as the loader maps it at `loadBase`: the carved regions,
inside the span the source binary's segments reserve. The rest of that span
is left unmapped, so the code touching anything that was not carved faults
instead of reading made-up bytes.
-/

namespace ValidateFeePayer

open X86 Image

/-- No reserved address wraps around `2^64`. Nothing in the code depends on
the base being page-aligned, so that is not required. -/
def ValidLoadBase (loadBase : UInt64) : Prop := loadBase.toNat + reservedEnd ≤ 2 ^ 64

instance : DecidablePred ValidLoadBase := fun _ => inferInstanceAs (Decidable (_ ≤ _))

def reservedSpan (loadBase : UInt64) : Nat × Nat :=
  (loadBase.toNat + reservedStart.toNat, loadBase.toNat + reservedEnd)

-- The GOT slots are read-only, as after RELRO.
def Region.mapping (loadBase : UInt64) (r : Region) : Mapping :=
  { base := loadBase + r.address, bytes := r.contents.bytesAt loadBase,
    permissions := if r.contents.isCode then .readExecute else .readOnly }

def imageMappings (loadBase : UInt64) : List Mapping := regions.map (·.mapping loadBase)

def entryAddress (loadBase : UInt64) : UInt64 := loadBase + validate_fee_payer.address

def panicAddress (loadBase : UInt64) : UInt64 := loadBase + panicEntry

end ValidateFeePayer
