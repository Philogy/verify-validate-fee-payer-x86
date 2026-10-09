import ValidateFeePayer.Loader
import ValidateFeePayer.Code

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

theorem panic_objects_unmapped :
    [panic_msg, panic_location, panic_location_file].all fun a =>
      decide (reservedStart ≤ a ∧ a.toNat < reservedEnd) && regions.all fun r => !decide (r.Contains a) := by
  set_option maxRecDepth 5000 in decide

theorem regions_nonempty : regions.all (0 < ·.size) := by
  set_option maxRecDepth 5000 in decide

theorem regions_within_reserved : regions.all fun r => reservedStart ≤ r.address ∧ r.endAddress ≤ reservedEnd := by
  set_option maxRecDepth 5000 in decide

theorem Region.mapping_bounds {loadBase : UInt64} (hBase : ValidLoadBase loadBase) {r : Region}
    (hr : r ∈ regions) :
    (r.mapping loadBase).base.toNat = loadBase.toNat + r.address.toNat ∧
      (r.mapping loadBase).endAddress = loadBase.toNat + r.endAddress := by
  have hne := List.all_eq_true.1 regions_nonempty r hr
  have hle := List.all_eq_true.1 regions_within_reserved r hr
  simp only [decide_eq_true_eq] at hne hle
  have hs := Contents.size_bytesAt (c := r.contents) (loadBase := loadBase) rfl
  unfold ValidLoadBase at hBase
  unfold Region.endAddress Region.size at *
  have : loadBase.toNat + r.address.toNat < 2 ^ 64 := by omega
  simp only [Region.mapping, Mapping.endAddress, UInt64.toNat_add, Nat.mod_eq_of_lt this]
  exact ⟨trivial, by omega⟩

theorem imageMappings_disjoint {loadBase : UInt64} (hBase : ValidLoadBase loadBase) :
    (imageMappings loadBase).Pairwise Mapping.Disjoint := by
  unfold imageMappings
  rw [List.pairwise_map]
  refine regions_disjoint.imp_of_mem ?_
  intro r₁ r₂ h₁ h₂ hd
  obtain ⟨b₁, e₁⟩ := Region.mapping_bounds hBase h₁
  obtain ⟨b₂, e₂⟩ := Region.mapping_bounds hBase h₂
  unfold Disjoint at hd
  unfold Mapping.Disjoint
  omega

end ValidateFeePayer
