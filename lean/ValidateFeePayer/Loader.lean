import X86.Machine
import Abi.Block
import ValidateFeePayer.Image

/-!
The carved image as the loader maps it at `loadBase`: the carved regions,
inside the span the source binary's segments reserve. The rest of that span
is left unmapped, so the code touching anything that was not carved faults
instead of reading made-up bytes.
-/

namespace ValidateFeePayer

open X86 Abi Image

/-- No reserved address wraps around `2^64`. Nothing in the code depends on
the base being page-aligned, so that is not required. -/
def ValidLoadBase (loadBase : UInt64) : Prop := loadBase.toNat + reservedEnd ≤ 2 ^ 64

instance : DecidablePred ValidLoadBase := fun _ => inferInstanceAs (Decidable (_ ≤ _))

def reservedSpan (loadBase : UInt64) : Block :=
  ⟨reservedStart.at loadBase, reservedEnd - reservedStart.off.toNat⟩

-- The GOT slots are read-only, as after RELRO.
def Region.mapping (loadBase : UInt64) (r : Region) : Mapping :=
  { base := r.address.at loadBase, bytes := r.contents.bytesAt loadBase,
    permissions := if r.contents.isCode then .readExecute else .readOnly }

def imageMappings (loadBase : UInt64) : List Mapping := regions.map (·.mapping loadBase)

/-- `m` holds the image loaded at `loadBase`, and nothing else is mapped in
its reserved span. -/
structure Loaded (loadBase : UInt64) (m : Memory) : Prop where
  validBase : ValidLoadBase loadBase
  image : ∃ rest, m = ⟨imageMappings loadBase ++ rest⟩ ∧
    ∀ mp ∈ rest, Block.Apart ⟨mp.base, mp.bytes.size⟩ (reservedSpan loadBase)

def entryAddress (loadBase : UInt64) : UInt64 := validate_fee_payer.address.at loadBase

def panicAddress (loadBase : UInt64) : UInt64 := panicEntry.at loadBase

/-- Running the code: it ends when control reaches the caller's return
address or the (uncarved) panic entry. -/
def exits (loadBase returnAddress : UInt64) : Exits := { returnAddress, panicAt := panicAddress loadBase }

end ValidateFeePayer
