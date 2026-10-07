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

end ValidateFeePayer
