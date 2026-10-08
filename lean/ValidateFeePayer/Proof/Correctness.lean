import ValidateFeePayer.Proof.Entry

/-!
The proof of `validateFeePayer_correct`.

The entry conditions of `Pre` are discharged here with the symbolic-execution
framework (`codeExits_of_pre`, `codeAt_of_pre`): control starts in the carved
code and neither exit points into it. What remains is the symbolic walk of the
239 instructions — including the SSE path that computes `Rent::minimum_balance`
and must match `F64` bit for bit — which is isolated in `symbolicRun`.
-/

namespace ValidateFeePayer

open X86 ValidateFeePayer.Proof

/-- What a finished run must look like: it panics exactly when the spec
panics, and otherwise returns in a state satisfying `Post`. This is the body
of `validateFeePayer_correct` as a predicate on the outcome. -/
def Spec.Outcome (c : Call) (refs : Spec.MutRefs) (rent : Spec.Rent) (relax : Bool) (s : State) :
    X86.Outcome → Prop
  | .returned s' => ∃ result refs', (Spec.validateFeePayer c.payerIndex rent c.fee relax).run refs
        = .ok (result, refs') ∧ Post c s result refs' s'
  | .panicked _ => (Spec.validateFeePayer c.payerIndex rent c.fee relax).run refs
      = .error .maximumPermittedDataLengthExceeded
  | _ => False

/-- The remaining obligation: from an entry state the machine finishes within
`fuel` steps in an outcome described by `Spec.Outcome`. Proving it is the
symbolic walk of the code against the spec; the surrounding packaging
(entry conditions, exit decoding, this reduction) is done. -/
theorem symbolicRun (c : Call) (refs : Spec.MutRefs) (rent : Spec.Rent) (relax : Bool)
    (s : State) (pre : Pre c refs rent relax s)
    (hx : CodeExits c.loadBase c.exits) (hc : CodeAt c.loadBase s.memory) :
    Proof.Finishes c.exits fuel s (Spec.Outcome c refs rent relax s) := by
  sorry

theorem correct (c : Call) (refs : Spec.MutRefs) (rent : Spec.Rent) (relax : Bool)
    (s : State) (pre : Pre c refs rent relax s) :
    match (Spec.validateFeePayer c.payerIndex rent c.fee relax).run refs with
    | .error .maximumPermittedDataLengthExceeded => ∃ s', run c.exits fuel s = .panicked s'
    | .ok (result, refs') => ∃ s', run c.exits fuel s = .returned s' ∧ Post c s result refs' s' := by
  have hfin := (symbolicRun c refs rent relax s pre (codeExits_of_pre pre) (codeAt_of_pre pre)).run_eq
    (Nat.le_refl fuel)
  -- `hfin : Spec.Outcome … (run c.exits fuel s)`; read off the two live cases.
  cases hrun : run c.exits fuel s with
  | returned s' =>
    simp only [hrun, Spec.Outcome] at hfin
    obtain ⟨result, refs', hspec, hpost⟩ := hfin
    rw [hspec]
    cases result with
    | ok => exact ⟨s', rfl, hpost⟩
    | error e => cases e <;> exact ⟨s', rfl, hpost⟩
  | panicked s' =>
    simp only [hrun, Spec.Outcome] at hfin
    rw [hfin]; exact ⟨s', rfl⟩
  | running s' => simp only [hrun, Spec.Outcome] at hfin
  | badJump t s' => simp only [hrun, Spec.Outcome] at hfin
  | undecodable w s' => simp only [hrun, Spec.Outcome] at hfin
  | stopped w s' => simp only [hrun, Spec.Outcome] at hfin

end ValidateFeePayer
