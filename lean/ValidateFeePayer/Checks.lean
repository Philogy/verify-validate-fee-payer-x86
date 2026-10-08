import ValidateFeePayer.Loader
import ValidateFeePayer.Code
import ValidateFeePayer.Disasm
import X86.Print

-- A regenerated `Image.lean` that breaks one of these fails the build here.

namespace ValidateFeePayer
open Image X86

theorem regions_disjoint : regions.Pairwise Disjoint := by
  set_option maxRecDepth 5000 in decide

theorem got_targets :
    got_check_static_account_rent_state_transition.contents
      = .pointer check_static_account_rent_state_transition.address ∧
    got_expect_failed.contents = .pointer Image.panicEntry := ⟨rfl, rfl⟩

theorem functions_are_code : functions.all (·.contents.isCode) := by decide

theorem panic_unmapped : regions.all fun r => !decide (r.Contains Image.panicEntry) := by decide

theorem regions_nonempty : regions.all (0 < ·.size) := by
  set_option maxRecDepth 5000 in decide

theorem regions_within_image : regions.all (·.endAddress ≤ imageEnd) := by
  set_option maxRecDepth 5000 in decide

theorem Region.mapping_bounds {loadBase : UInt64} (hBase : ValidLoadBase loadBase) {r : Region}
    (hr : r ∈ regions)
    {m : Mapping} (hm : r.mapping loadBase = some m) :
    m.base.toNat = loadBase.toNat + r.address.toNat ∧ m.endAddress = loadBase.toNat + r.endAddress := by
  have hne := List.all_eq_true.1 regions_nonempty r hr
  have hle := List.all_eq_true.1 regions_within_image r hr
  simp only [decide_eq_true_eq] at hne hle
  simp only [Region.mapping, Option.map_eq_some_iff] at hm
  obtain ⟨bytes, hb, rfl⟩ := hm
  have hs := Contents.size_bytesAt hb
  unfold ValidLoadBase at hBase
  unfold Region.endAddress Region.size at *
  have : loadBase.toNat + r.address.toNat < 2 ^ 64 := by omega
  simp only [Mapping.endAddress, UInt64.toNat_add, Nat.mod_eq_of_lt this]
  exact ⟨trivial, by omega⟩

theorem imageMappings_disjoint {loadBase : UInt64} (hBase : ValidLoadBase loadBase) :
    (imageMappings loadBase).Pairwise Mapping.Disjoint := by
  unfold imageMappings
  rw [List.pairwise_filterMap]
  refine regions_disjoint.imp_of_mem ?_
  intro r₁ r₂ h₁ h₂ hd m₁ hm₁ m₂ hm₂
  obtain ⟨b₁, e₁⟩ := Region.mapping_bounds hBase h₁ hm₁
  obtain ⟨b₂, e₂⟩ := Region.mapping_bounds hBase h₂ hm₂
  unfold Disjoint at hd
  unfold Mapping.Disjoint
  omega

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

def decodesAt (d : Decoded) : Bool :=
  match decodeWith codeByte d.address with
  | .ok (i, length) => i == d.instruction && length == d.length
  | .error _ => false

/-- Fetching from the image byte by byte, as the machine does, gives the
same instructions as the sweep. -/
theorem decodeWith_codeByte : listing.all decodesAt := by
  set_option maxRecDepth 100000 in decide +kernel

theorem branch_targets :
    listing.all (fun e => match e.instruction with
      | .jumpIf _ offset | .jump offset =>
        (instructionAt (e.address + e.length.toUInt64 + offset)).isSome
      | _ => true) := by
  set_option maxRecDepth 100000 in decide +kernel

end ValidateFeePayer
