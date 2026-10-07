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
    got_check_static_account_rent_state_transition.relocations.map (·.value)
      = [check_static_account_rent_state_transition.vaddr] ∧
    got_expect_failed.relocations.map (·.value) = [Image.panicEntry] := by decide

/-- Code regions contain no relocations: their bytes are the same at every base. -/
theorem functions_position_independent : functions.all (·.relocations.isEmpty) := by decide

/-- The panic entry is not inside any carved region. -/
theorem panic_unmapped : regions.all fun r => r.byteAt? Image.panicEntry |>.isNone := by decide

end ValidateFeePayer
