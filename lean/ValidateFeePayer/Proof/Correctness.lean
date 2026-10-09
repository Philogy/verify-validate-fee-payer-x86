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
  · exact walk_simd0194 (entry_of_pre pre pre.called.returnNotPanic) h
  · exact walk_current (entry_of_pre pre pre.called.returnNotPanic) h

theorem frame_of_call {c : Call} {account metrics rent relax s} (pre : Pre c account metrics rent relax s)
    {s' : State} (h : c.Frame s s') : Frame s s' := by
  intro access a ha
  apply h
  simp only [writes, List.mem_cons, forall_eq_or_imp] at ha
  obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := ha
  rw [← pre.ofState]
  rintro (hw | hw | hw | hw | hw | hw)
  · exact h0 hw
  · exact h1 hw
  · exact h2 hw
  · exact h3 hw
  · exact h4 hw
  · exact h5 hw

theorem post_of_call {c : Call} {account metrics rent relax s} (pre : Pre c account metrics rent relax s)
    {metrics' : Spec.ErrorMetrics} {r : Except Spec.TransactionError Spec.Account} {s' : State}
    (h : CallPost c s metrics' r s') : Post s c.heap metrics' r s' where
  returned := ⟨h.stackPopped, h.calleeSavedKept, h.floatControlKept⟩
  returnsResultPointer := by
    show _ = (args s).result
    rw [pre.result]; exact h.returnsResultPointer
  frame := frame_of_call pre h.frame
  resultEncoded := by rw [pre.result]; exact h.resultEncoded
  accountEncoded := by rw [pre.accountAt_eq]; exact h.accountEncoded
  metricsEncoded := by rw [pre.errorMetrics]; exact h.metricsEncoded

theorem correctCall (c : Call) (account : Spec.Account) (metrics : Spec.ErrorMetrics) (rent : Spec.Rent)
    (relax : Bool) (s : State) (pre : Pre c account metrics rent relax s) :
    ∀ n ≥ fuel, match Spec.validateFeePayer account c.payerIndex rent c.fee relax metrics with
    | (.error (.panic _), _) => ∃ s', run c.exits n s = .panicked s' ∧ c.Frame s s'
    | (.error (.tx e), metrics') => ∃ s', run c.exits n s = .returned s' ∧ CallPost c s metrics' (.error e) s'
    | (.ok account', metrics') => ∃ s', run c.exits n s = .returned s' ∧ CallPost c s metrics' (.ok account') s' := by
  intro n hn
  have hfin := (symbolicRun c account metrics rent relax s pre).run_eq hn
  unfold Spec.Outcome at hfin
  split
  all_goals rename_i h; rw [h] at hfin; split at hfin <;> simp_all

theorem correct (c : Call) (account : Spec.Account) (metrics : Spec.ErrorMetrics) (rent : Spec.Rent)
    (relax : Bool) (s : State) (pre : Pre c account metrics rent relax s) :
    ∀ n ≥ fuel, match Spec.validateFeePayer account c.payerIndex rent c.fee relax metrics with
    | (.error (.panic _), _) => ∃ s', run c.exits n s = .panicked s' ∧ Frame s s'
    | (.error (.tx e), metrics') => ∃ s', run c.exits n s = .returned s' ∧ Post s c.heap metrics' (.error e) s'
    | (.ok account', metrics') => ∃ s', run c.exits n s = .returned s' ∧ Post s c.heap metrics' (.ok account') s' := by
  intro n hn
  have h := correctCall c account metrics rent relax s pre n hn
  generalize Spec.validateFeePayer account c.payerIndex rent c.fee relax metrics = r at h ⊢
  obtain ⟨(e | a), m⟩ := r
  · cases e with
    | panic p =>
      obtain ⟨s', hr, hf⟩ := h
      exact ⟨s', hr, frame_of_call pre hf⟩
    | tx e =>
      obtain ⟨s', hr, hp⟩ := h
      exact ⟨s', hr, post_of_call pre hp⟩
  · obtain ⟨s', hr, hp⟩ := h
    exact ⟨s', hr, post_of_call pre hp⟩

end ValidateFeePayer
