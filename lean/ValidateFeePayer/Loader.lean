import X86.Machine
import Abi.Block
import ValidateFeePayer.Image

/-!
The carved image in memory at `loadBase`: what it means for it to be there
(`Loaded`), and one memory where it is (`load`). The carved regions sit
inside the span the source binary's segments reserve; nothing is assumed
about the rest of that span, so the code touching anything that was not
carved makes the proof fail rather than read made-up bytes.
-/

namespace ValidateFeePayer

open Image

/-- No reserved address wraps around `2^64`. Nothing in the code depends on
the base being page-aligned, so that is not required. -/
def ValidLoadBase (loadBase : UInt64) : Prop := loadBase.toNat + reservedEnd ≤ 2 ^ 64

instance : DecidablePred ValidLoadBase := fun _ => inferInstanceAs (Decidable (_ ≤ _))

def reservedSpan (loadBase : UInt64) : Abi.Block :=
  ⟨reservedStart.at loadBase, reservedEnd - reservedStart.off.toNat⟩

-- The GOT slots are read-only, as after RELRO.
def Region.permissions (r : Region) : X86.Permissions :=
  if r.contents.isCode then .readExecute else .readOnly

def Region.block (loadBase : UInt64) (r : Region) : Abi.Block := ⟨r.address.at loadBase, r.size⟩

/-- Every carved byte is in `m` at `loadBase`, with its region's permissions. -/
structure Loaded (loadBase : UInt64) (m : X86.Memory) : Prop where
  validBase : ValidLoadBase loadBase
  bytes : ∀ r ∈ regions, ∀ (i : Nat) (h : i < (r.contents.bytesAt loadBase).size),
    m.cell (r.address.at loadBase + i.toUInt64) = some ⟨r.permissions, (r.contents.bytesAt loadBase)[i]⟩

/-- `m` with the carved regions mapped in at `loadBase`. -/
def load (loadBase : UInt64) (m : X86.Memory) : X86.Memory :=
  regions.foldr (fun r m => m.map (r.address.at loadBase) (r.contents.bytesAt loadBase) r.permissions) m

def entryAddress (loadBase : UInt64) : UInt64 := validate_fee_payer.address.at loadBase

def panicAddress (loadBase : UInt64) : UInt64 := panicEntry.at loadBase

/-- Running the code: it ends when control reaches the caller's return
address or the (uncarved) panic entry. -/
def exits (loadBase returnAddress : UInt64) : X86.Exits := { returnAddress, panicAt := panicAddress loadBase }

end ValidateFeePayer
