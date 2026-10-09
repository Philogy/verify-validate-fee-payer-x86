import ValidateFeePayer.Proof.Entry
import ValidateFeePayer.Proof.Outcome

/-!
The proof of `validateFeePayer_correct`.

The entry conditions of `Pre` are discharged here with the symbolic-execution
framework (`codeExits_of_pre`, `codeAt_of_pre`): control starts in the carved
code and neither exit points into it. What remains is the symbolic walk of the
239 instructions, isolated in `symbolicRun`.
-/

namespace ValidateFeePayer

open X86 ValidateFeePayer.Proof

/-- The remaining obligation: from an entry state the machine finishes within
`fuel` steps in an outcome described by `Spec.Outcome`. Proving it is the
symbolic walk of the code against the spec; the surrounding packaging
(entry conditions, exit decoding, this reduction) is done. -/
theorem symbolicRun (c : Call) (account : Spec.Account) (metrics : Spec.ErrorMetrics) (rent : Spec.Rent)
    (relax : Bool) (s : State) (pre : Pre c account metrics rent relax s)
    (hx : CodeExits c.loadBase c.exits) (hc : CodeAt c.loadBase s.memory) :
    Proof.Finishes c.exits fuel s (Spec.Outcome c account metrics rent relax s) := by
  sorry

theorem correct (c : Call) (account : Spec.Account) (metrics : Spec.ErrorMetrics) (rent : Spec.Rent)
    (relax : Bool) (s : State) (pre : Pre c account metrics rent relax s) :
    match Spec.validateFeePayer account c.payerIndex rent c.fee relax metrics with
    | (.error (.panic _), _) => ∃ s', run c.exits fuel s = .panicked s'
    | (.error (.tx e), metrics') => ∃ s', run c.exits fuel s = .returned s' ∧ Post c s metrics' (.error e) s'
    | (.ok account', metrics') => ∃ s', run c.exits fuel s = .returned s' ∧ Post c s metrics' (.ok account') s' := by
  have hfin := (symbolicRun c account metrics rent relax s pre (codeExits_of_pre pre)
    (codeAt_of_pre pre)).run_eq (Nat.le_refl fuel)
  unfold Spec.Outcome at hfin
  split
  all_goals rename_i h; rw [h] at hfin; split at hfin <;> simp_all
