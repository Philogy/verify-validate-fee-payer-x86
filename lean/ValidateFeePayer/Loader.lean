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

open Image

/-- No reserved address wraps around `2^64`. Nothing in the code depends on
the base being page-aligned, so that is not required. -/
def ValidLoadBase (loadBase : UInt64) : Prop := loadBase.toNat + reservedEnd ≤ 2 ^ 64

instance : DecidablePred ValidLoadBase := fun _ => inferInstanceAs (Decidable (_ ≤ _))

def reservedSpan (loadBase : UInt64) : Abi.Block :=
  ⟨reservedStart.at loadBase, reservedEnd - reservedStart.off.toNat⟩

-- The GOT slots are read-only, as after RELRO.
def Region.mapping (loadBase : UInt64) (r : Region) : X86.Mapping :=
  { base := r.address.at loadBase, bytes := r.contents.bytesAt loadBase,
    permissions := if r.contents.isCode then .readExecute else .readOnly }

def imageMappings (loadBase : UInt64) : List X86.Mapping := regions.map (·.mapping loadBase)

/-- Nothing in `m` is mapped in the span the image reserves at `loadBase`. -/
def SpanFree (loadBase : UInt64) (m : X86.Memory) : Prop :=
  ∀ mp ∈ m.mappings, Abi.Block.Apart ⟨mp.base, mp.bytes.size⟩ (reservedSpan loadBase)

/-- `m` with the image mapped in at `loadBase`. -/
def load (loadBase : UInt64) (m : X86.Memory) : X86.Memory := ⟨imageMappings loadBase ++ m.mappings⟩

def entryAddress (loadBase : UInt64) : UInt64 := validate_fee_payer.address.at loadBase

def panicAddress (loadBase : UInt64) : UInt64 := panicEntry.at loadBase

/-- The caller's state `s` with the image loaded at `loadBase` and control
at its entry. -/
-- Irreducible: unfolding it would unfold the whole image wherever a proof
-- compares an entry state with the caller's.
@[irreducible] def enter (loadBase : UInt64) (s : X86.State) : X86.State :=
  { s with instructionPointer := entryAddress loadBase, memory := load loadBase s.memory }

/-- Running the code: it ends when control reaches the caller's return
address or the (uncarved) panic entry. -/
def exits (loadBase returnAddress : UInt64) : X86.Exits := { returnAddress, panicAt := panicAddress loadBase }

end ValidateFeePayer
