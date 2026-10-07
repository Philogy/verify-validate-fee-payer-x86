import ValidateFeePayer.Memory

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
      = .pointer check_static_account_rent_state_transition.vaddr ∧
    got_expect_failed.contents = .pointer Image.panicEntry := ⟨rfl, rfl⟩

/-- Functions are code regions, whose bytes are the same at every base. -/
theorem functions_are_code : functions.all (·.contents.isCode) := by decide

/-- The panic entry is not inside any carved region. -/
theorem panic_unmapped : regions.all fun r => !decide (r.Contains Image.panicEntry) := by decide

theorem regions_nonempty : regions.all (0 < ·.size) := by
  set_option maxRecDepth 5000 in decide

theorem regions_within_image : regions.all (·.endAddr ≤ imageEnd) := by
  set_option maxRecDepth 5000 in decide

/-- A region mapped at a valid base sits at `B + vaddr` without wrapping. -/
theorem Region.mapping_bounds {B : UInt64} (hB : ValidBase B) {r : Region} (hr : r ∈ regions)
    {m : Mapping} (hm : r.mapping B = some m) :
    m.base.toNat = B.toNat + r.vaddr.toNat ∧ m.endAddr = B.toNat + r.endAddr := by
  have hne := List.all_eq_true.1 regions_nonempty r hr
  have hle := List.all_eq_true.1 regions_within_image r hr
  simp only [decide_eq_true_eq] at hne hle
  simp only [Region.mapping, Option.map_eq_some_iff] at hm
  obtain ⟨bytes, hb, rfl⟩ := hm
  have hs := Contents.size_bytesAt hb
  unfold ValidBase at hB
  unfold Region.endAddr Region.size at *
  have : B.toNat + r.vaddr.toNat < 2 ^ 64 := by omega
  simp only [Mapping.endAddr, UInt64.toNat_add, Nat.mod_eq_of_lt this]
  exact ⟨trivial, by omega⟩

/-- At a valid base the carved image's mappings do not overlap. -/
theorem imageMappings_disjoint {B : UInt64} (hB : ValidBase B) :
    (imageMappings B).Pairwise Mapping.Disjoint := by
  unfold imageMappings
  rw [List.pairwise_filterMap]
  refine regions_disjoint.imp_of_mem ?_
  intro r₁ r₂ h₁ h₂ hd m₁ hm₁ m₂ hm₂
  obtain ⟨b₁, e₁⟩ := Region.mapping_bounds hB h₁ hm₁
  obtain ⟨b₂, e₂⟩ := Region.mapping_bounds hB h₂ hm₂
  unfold Disjoint at hd
  unfold Mapping.Disjoint
  omega

end ValidateFeePayer
