import ValidateFeePayer.Loader
import ValidateFeePayer.Code
import X86.MemoryFacts

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

theorem panic_unmapped : regions.all fun r => !decide (r.Contains Image.panicEntry.off) := by decide

theorem panic_objects_unmapped :
    [panic_msg, panic_location, panic_location_file].all fun a =>
      decide (reservedStart.off ≤ a.off ∧ a.off.toNat < reservedEnd) && regions.all fun r => !decide (r.Contains a.off) := by
  set_option maxRecDepth 5000 in decide

theorem regions_nonempty : regions.all (0 < ·.size) := by
  set_option maxRecDepth 5000 in decide

theorem regions_within_reserved : regions.all fun r => reservedStart.off ≤ r.address.off ∧ r.endAddress ≤ reservedEnd := by
  set_option maxRecDepth 5000 in decide

theorem Region.toNat_at {loadBase : UInt64} (hBase : ValidLoadBase loadBase) {r : Region} (hr : r ∈ regions)
    {i : Nat} (hi : i < r.size) :
    (r.address.at loadBase + i.toUInt64).toNat = loadBase.toNat + r.address.off.toNat + i := by
  have hle := List.all_eq_true.1 regions_within_reserved r hr
  simp only [decide_eq_true_eq] at hle
  have hne := List.all_eq_true.1 regions_nonempty r hr
  simp only [decide_eq_true_eq] at hne
  have : reservedEnd = 0x3a423d4 := rfl
  unfold ValidLoadBase at hBase
  unfold Region.endAddress at hle
  simp only [ImageOffset.at, UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (a := loadBase.toNat + r.address.off.toNat) (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- The image can be loaded at any valid base: `Loaded` is satisfiable. -/
theorem loaded_load {loadBase : UInt64} (hBase : ValidLoadBase loadBase) (m : X86.Memory) :
    Loaded loadBase (load loadBase m) := by
  refine ⟨hBase, fun r hr i hi => ?_⟩
  have hs := Contents.size_bytesAt (c := r.contents) (loadBase := loadBase) rfl
  suffices ∀ L : List Region, L.Pairwise Disjoint → (∀ r' ∈ L, r' ∈ regions) → r ∈ L →
      (L.foldr (fun r m => m.map (r.address.at loadBase) (r.contents.bytesAt loadBase) r.permissions) m).cell
        (r.address.at loadBase + i.toUInt64) = some ⟨r.permissions, (r.contents.bytesAt loadBase)[i]⟩ from
    this regions regions_disjoint (fun _ h => h) hr
  intro L
  induction L with
  | nil => intro _ _ h; simp at h
  | cons r' L ih =>
    intro hd hsub hmem
    simp only [List.foldr_cons]
    have hr' := hsub r' (List.mem_cons_self ..)
    have hs' := Contents.size_bytesAt (c := r'.contents) (loadBase := loadBase) rfl
    have hat := Region.toNat_at hBase hr (i := i) (by unfold Region.size; omega)
    have hat' := Region.toNat_at hBase hr' (i := 0)
      (by have := List.all_eq_true.1 regions_nonempty r' hr'; simpa using this)
    simp only [Nat.toUInt64_eq, UInt64.reduceOfNat, UInt64.add_zero, Nat.add_zero] at hat'
    rcases List.mem_cons.1 hmem with rfl | hmem
    · have hw : (r.address.at loadBase).toNat + (r.contents.bytesAt loadBase).size ≤ 2 ^ 64 := by
        have hle := List.all_eq_true.1 regions_within_reserved r hr
        simp only [decide_eq_true_eq] at hle
        unfold ValidLoadBase at hBase; unfold Region.endAddress Region.size at hle
        omega
      exact X86.Memory.cell_map_inside hi hw
    · have hdis := (List.pairwise_cons.1 hd).1 r hmem
      rw [X86.Memory.cell_map_outside]
      · exact ih (List.pairwise_cons.1 hd).2 (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hmem
      · unfold Disjoint Region.endAddress Region.size at hdis
        rw [hat, hat', hs']
        unfold Region.size at hi; omega

end ValidateFeePayer
