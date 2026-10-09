import ValidateFeePayer.Proof.Entry

/-!
The proof of `validateFeePayer_correct`.

The entry conditions of `Pre` are discharged here with the symbolic-execution
framework (`codeExits_of_pre`, `codeAt_of_pre`): control starts in the carved
code and neither exit points into it. What remains is the symbolic walk of the
239 instructions, isolated in `symbolicRun`.
-/

namespace ValidateFeePayer

open X86 ValidateFeePayer.Proof

/-- `checked_sub_lamports(fee)` cannot fail once the balance covers the fee
and the minimum balance, so `Spec.validateFeePayer`'s second
`insufficientFundsForFee` is dead. -/
theorem checkedSubLamports_ok {lamports fee minBalance : UInt64}
    (h : ¬ lamports.toNat < fee.toNat + minBalance.toNat) : ¬ lamports < fee := by
  rw [UInt64.lt_iff_toNat_lt]; omega

/-- What a finished run must look like: it panics exactly when the spec
panics, and otherwise returns in a state satisfying `Post`. -/
def Spec.Outcome (c : Call) (account : Spec.Account) (metrics : Spec.ErrorMetrics) (rent : Spec.Rent)
    (relax : Bool) (s : State) (o : X86.Outcome) : Prop :=
  match (Spec.validateFeePayer account c.payerIndex rent c.fee relax).run.run metrics, o with
  | (.error (.panic _), _), .panicked _ => True
  | (.error (.tx e), metrics'), .returned s' => Post c s metrics' (.error e) s'
  | (.ok account', metrics'), .returned s' => Post c s metrics' (.ok account') s'
  | _, _ => False

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
    match (Spec.validateFeePayer account c.payerIndex rent c.fee relax).run.run metrics with
    | (.error (.panic _), _) => ∃ s', run c.exits fuel s = .panicked s'
    | (.error (.tx e), metrics') => ∃ s', run c.exits fuel s = .returned s' ∧ Post c s metrics' (.error e) s'
    | (.ok account', metrics') => ∃ s', run c.exits fuel s = .returned s' ∧ Post c s metrics' (.ok account') s' := by
  have hfin := (symbolicRun c account metrics rent relax s pre (codeExits_of_pre pre)
    (codeAt_of_pre pre)).run_eq (Nat.le_refl fuel)
  unfold Spec.Outcome at hfin
  split
  all_goals rename_i h; rw [h] at hfin; split at hfin <;> simp_all
