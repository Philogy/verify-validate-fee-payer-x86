import ValidateFeePayer.Memory
import ValidateFeePayer.Print
import ValidateFeePayer.Disasm

/-!
Facts about the generated image that later proofs rely on, checked by the
kernel. A regenerated `Image.lean` that breaks one fails the build here.
-/

namespace ValidateFeePayer
open Image

theorem regions_disjoint : regions.Pairwise Disjoint := by
  set_option maxRecDepth 5000 in decide

/-- The two pointer slots the code calls through hold, after loading, the
callee's entry point and the panic entry. -/
theorem got_targets :
    got_check_static_account_rent_state_transition.contents
      = .pointer check_static_account_rent_state_transition.address ∧
    got_expect_failed.contents = .pointer Image.panicEntry := ⟨rfl, rfl⟩

/-- Functions are code regions, whose bytes are the same at every base. -/
theorem functions_are_code : functions.all (·.contents.isCode) := by decide

/-- The panic entry is not inside any carved region. -/
theorem panic_unmapped : regions.all fun r => !decide (r.Contains Image.panicEntry) := by decide

theorem regions_nonempty : regions.all (0 < ·.size) := by
  set_option maxRecDepth 5000 in decide

theorem regions_within_image : regions.all (·.endAddress ≤ imageEnd) := by
  set_option maxRecDepth 5000 in decide

/-- A region mapped at a valid base sits at `loadBase + address` without wrapping. -/
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

/-- At a valid base the carved image's mappings do not overlap. -/
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

namespace X86

/-- The strict decoder accepts every instruction of the carved code, so
`codeTable` is the real sweep, not its fallback. -/
theorem decodeImage_ok : decodeImage.toOption = some codeTable := by
  set_option maxRecDepth 100000 in decide +kernel

/-- The decoder agrees with llvm-objdump (`Disasm.lean`) on every
instruction's address, length, mnemonic and operands. -/
theorem codeTable_eq_objdump : codeTable.map Print.entry = Disasm.listing := by
  set_option maxRecDepth 100000 in decide +kernel

/-- Every relative branch lands on a decoded instruction. -/
theorem branch_targets :
    codeTable.all (fun e => match e.instruction with
      | .jumpIf _ offset | .jump offset =>
        (instructionAt ((e.address.toNat + e.length + offset) % 2 ^ 64).toNat.toUInt64).isSome
      | _ => true) := by
  set_option maxRecDepth 100000 in decide +kernel

end X86

end ValidateFeePayer
