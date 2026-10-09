import ValidateFeePayer.Proof.Entry2
import ValidateFeePayer.Proof.PathsCurrent
import ValidateFeePayer.Proof.PathsSimd0194

/-!
The proof of `validateFeePayer_correct`: `Pre` gives the walk's `Entry` facts
and the entry state in the explicit form the walk starts from, and each
integer exemption threshold has its walk of every path.
-/

namespace ValidateFeePayer

open X86 ValidateFeePayer.Proof

theorem entryState_of_pre {c : Call} {account metrics rent relax s} (pre : Pre c account metrics rent relax s) :
    s = entryState c.loadBase (s.stackPointer - 96) c.account.account c.result c.errorMetrics c.rent c.fee
      (s.register .accumulator) (s.register .data) (s.register .base) (s.register .framePointer)
      (s.register .r10) (s.register .r11) (s.register .r12) (s.register .r13) (s.register .r14)
      (s.register .r15) s.vectorRegisters[0] s.vectorRegisters[1] s.vectorRegisters[2] s.vectorRegisters[3]
      s.vectorRegisters[4] s.vectorRegisters[5] s.vectorRegisters[6] s.vectorRegisters[7]
      s.vectorRegisters[8] s.vectorRegisters[9] s.vectorRegisters[10] s.vectorRegisters[11]
      s.vectorRegisters[12] s.vectorRegisters[13] s.vectorRegisters[14] s.vectorRegisters[15]
      s.floatControl s.memory := by
  refine (entry_state pre).trans ?_
  simp only [entryState, UInt64.sub_add_cancel]
  rw [← vector16_eta]

theorem Finishes.of_eq {exits : Exits} {n : Nat} {s t : State} {P : Outcome → Prop} (h : s = t)
    (k : Finishes exits n t P) : Finishes exits n s P := h ▸ k

theorem symbolicRun (c : Call) (account : Spec.Account) (metrics : Spec.ErrorMetrics) (rent : Spec.Rent)
    (relax : Bool) (s : State) (pre : Pre c account metrics rent relax s) :
    Proof.Finishes c.exits fuel s (Spec.Outcome c account metrics rent relax s) := by
  refine Finishes.of_eq (entryState_of_pre pre) ?_
  rcases pre.integerThreshold with h | h
  · exact walk_simd0194 (entry_of_pre pre pre.returnNotPanic) h
  · exact walk_current (entry_of_pre pre pre.returnNotPanic) h

theorem correct (c : Call) (account : Spec.Account) (metrics : Spec.ErrorMetrics) (rent : Spec.Rent)
    (relax : Bool) (s : State) (pre : Pre c account metrics rent relax s) :
    ∀ n ≥ fuel, match Spec.validateFeePayer account c.payerIndex rent c.fee relax metrics with
    | (.error (.panic _), _) => ∃ s', run c.exits n s = .panicked s' ∧ c.Frame s s'
    | (.error (.tx e), metrics') => ∃ s', run c.exits n s = .returned s' ∧ Post c s metrics' (.error e) s'
    | (.ok account', metrics') => ∃ s', run c.exits n s = .returned s' ∧ Post c s metrics' (.ok account') s' := by
  intro n hn
  have hfin := (symbolicRun c account metrics rent relax s pre).run_eq hn
  unfold Spec.Outcome at hfin
  split
  all_goals rename_i h; rw [h] at hfin; split at hfin <;> simp_all

end ValidateFeePayer
