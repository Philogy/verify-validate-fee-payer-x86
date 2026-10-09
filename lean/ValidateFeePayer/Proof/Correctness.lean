import ValidateFeePayer.Proof.Entry2
import ValidateFeePayer.Proof.PathsCurrent
import ValidateFeePayer.Proof.PathsSimd0194
import ValidateFeePayer.Proof.Load

/-!
The proof of `validateFeePayer_correct`: the caller's state's hypotheses
become `Pre` at the entry state (`pre_of_called`), `Pre` gives the walk's
`Entry` facts and the entry state in the explicit form the walk starts from,
and each integer exemption threshold has its walk of every path.
-/

namespace ValidateFeePayer

open X86 ValidateFeePayer.Proof

theorem entryState_of_pre {c : Call} {account metrics rent relax s} (pre : Pre c account metrics rent relax s) :
    s = entryState c.loadBase (s.rsp - 96) c.account.account c.result c.errorMetrics c.rent c.fee
      (s.register .rax) (s.register .rdx) (s.register .rbx) (s.register .rbp)
      (s.register .r10) (s.register .r11) (s.register .r12) (s.register .r13) (s.register .r14)
      (s.register .r15) s.xmm[0] s.xmm[1] s.xmm[2] s.xmm[3]
      s.xmm[4] s.xmm[5] s.xmm[6] s.xmm[7]
      s.xmm[8] s.xmm[9] s.xmm[10] s.xmm[11]
      s.xmm[12] s.xmm[13] s.xmm[14] s.xmm[15]
      s.mxcsr s.memory := by
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
  · exact walk_simd0194 (entry_of_pre pre pre.entered.returnNotPanic) h
  · exact walk_current (entry_of_pre pre pre.entered.returnNotPanic) h

theorem frame_of_call {c : Call} {account metrics rent relax s}
    (pre : Pre c account metrics rent relax (enter c.loadBase s)) {s' : State}
    (h : c.Frame (enter c.loadBase s) s') : Frame c.loadBase s s' := by
  have hres : c.result = (args s).result := by rw [← pre.result, args_enter]
  have hacc : c.account.account = (args s).account := by rw [← pre.accountPtr, args_enter]
  have hmet : c.errorMetrics = (args s).errorMetrics := by rw [← pre.errorMetrics, args_enter]
  intro access a ha
  rw [← enter_memory]
  apply h
  simp only [writes, List.mem_cons, forall_eq_or_imp] at ha
  obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := ha
  simp only [Call.Written, hres, hacc, hmet, enter_stackPointer]
  rintro (hw | hw | hw | hw | hw | hw)
  · exact h0 hw
  · exact h1 hw
  · exact h2 hw
  · exact h3 hw
  · exact h4 hw
  · exact h5 hw

theorem post_of_call {c : Call} {account metrics rent relax s}
    (pre : Pre c account metrics rent relax (enter c.loadBase s))
    {metrics' : Spec.ErrorMetrics} {r : Except Spec.TransactionError Spec.Account} {s' : State}
    (h : CallPost c (enter c.loadBase s) metrics' r s') : Post c.loadBase s c.heap metrics' r s' := by
  have hres : (args s).result = c.result := by rw [← pre.result, args_enter]
  have hacc : accountAt s c.heap = c.account := by rw [← accountAt_enter (lb := c.loadBase), pre.accountAt_eq]
  have hmet : (args s).errorMetrics = c.errorMetrics := by rw [← pre.errorMetrics, args_enter]
  have hsp := h.stackPopped
  have hcs := h.calleeSavedKept
  have hfc := h.mxcsrKept
  rw [enter_stackPointer] at hsp
  rw [enter_floatControl] at hfc
  simp only [enter_register] at hcs
  exact {
    returned := ⟨hsp, hcs, hfc⟩
    returnsResultPointer := by
      show _ = (args s).result
      rw [hres]; exact h.returnsResultPointer
    frame := frame_of_call pre h.frame
    resultEncoded := by rw [hres]; exact h.resultEncoded
    accountEncoded := by rw [hacc]; exact h.accountEncoded
    metricsEncoded := by rw [hmet]; exact h.metricsEncoded }

theorem Spec.Account.Encodes.extend {m m' : Memory} (h : Extends m m') {p : AccountAt} {x : Spec.Account}
    (e : x.Encodes m p) : x.Encodes m' p :=
  let ⟨h1, h2, h3, h4, h5, h6⟩ := e
  ⟨h.holds h1, h.holds h2, h.holdsBytes h3, h.holds h4, h.holds h5, h.holdsBytes h6⟩

theorem Spec.ErrorMetrics.Encodes.extend {m m' : Memory} (h : Extends m m') {p : UInt64}
    {x : Spec.ErrorMetrics} (e : x.Encodes m p) : x.Encodes m' p :=
  let ⟨h1, h2, h3⟩ := e
  ⟨h.holds h1, h.holds h2, h.holds h3⟩

/-- The bridge: the hypotheses on the caller's state `s` are `Pre` at the
state `invoke` starts from. -/
theorem pre_of_called {loadBase returnAddress : UInt64} {s : State} {heap : AccountHeap}
    {account : Spec.Account} {metrics : Spec.ErrorMetrics} {rent : Spec.Rent} {payerIndex : UInt16}
    {fee : UInt64} {relax : Bool}
    (called : Called loadBase returnAddress s)
    (footprint : Footprint loadBase s heap account.data.length)
    (encoded : Encoded s heap account metrics rent payerIndex fee relax)
    (integerThreshold : IntegerThreshold rent) :
    Pre (.of loadBase returnAddress (enter loadBase s) heap payerIndex fee) account metrics rent relax
      (enter loadBase s) := by
  have hx := extends_load called.validBase called.spanFree
  exact {
    ofState := rfl
    entered := ⟨called.validBase, ⟨s.memory, enter_memory, called.spanFree⟩, enter_instructionPointer,
      called.returnOutsideImage, called.returnNotPanic⟩
    abi := by
      show Abi.SysV.Entry (enter loadBase s) returnAddress
      refine ⟨?_, ?_, ?_⟩
      · rw [enter_memory, enter_stackPointer]; exact hx.holds called.abi.returnAddress
      · rw [enter_stackPointer]; exact called.abi.stackAligned
      · rw [enter_rflags]; exact called.abi.rflags
    footprint := by
      show Footprint loadBase (enter loadBase s) heap account.data.length
      refine ⟨?_, ?_, ?_⟩
      · rw [objects_enter]; exact footprint.separate
      · rw [objects_enter]; exact footprint.noWrap
      · rw [writes_enter, enter_memory]; exact fun b hb => hx.writable (footprint.writable b hb)
    encoded := by
      show Encoded (enter loadBase s) heap account metrics rent payerIndex fee relax
      have hr := encoded.rent
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [args_enter, accountAt_enter, enter_memory]
      · exact encoded.account.extend hx
      · exact encoded.payerIndex
      · exact ⟨hx.holds hr.1, hx.holds hr.2⟩
      · exact encoded.fee
      · exact hx.holds encoded.relax
      · exact encoded.metrics.extend hx
    integerThreshold }

theorem invoke_behaves {loadBase returnAddress : UInt64} {s : State} {heap : AccountHeap}
    {account : Spec.Account} {metrics : Spec.ErrorMetrics} {rent : Spec.Rent} {payerIndex : UInt16}
    {fee : UInt64} {relax : Bool}
    (called : Called loadBase returnAddress s)
    (footprint : Footprint loadBase s heap account.data.length)
    (encoded : Encoded s heap account metrics rent payerIndex fee relax)
    (integerThreshold : IntegerThreshold rent) :
    Behaves loadBase s heap (Spec.validateFeePayer account payerIndex rent fee relax metrics)
      (invoke loadBase returnAddress s) := by
  have pre := pre_of_called called footprint encoded integerThreshold
  have h := (symbolicRun _ account metrics rent relax _ pre).run_eq (Nat.le_refl fuel)
  unfold Spec.Outcome at h
  change Behaves _ _ _ _ (run (Call.exits (.of loadBase returnAddress (enter loadBase s) heap payerIndex fee)) fuel _)
  generalize run _ fuel _ = o at h ⊢
  rw [show (Call.of loadBase returnAddress (enter loadBase s) heap payerIndex fee).payerIndex = payerIndex from rfl,
    show (Call.of loadBase returnAddress (enter loadBase s) heap payerIndex fee).fee = fee from rfl] at h
  generalize Spec.validateFeePayer account payerIndex rent fee relax metrics = r at h ⊢
  obtain ⟨(e | a), m⟩ := r
  · cases e with
    | panic p =>
      cases o
      all_goals first | exact h.elim | exact ⟨⟨p, rfl⟩, frame_of_call pre h⟩
    | tx e =>
      cases o
      all_goals first | exact h.elim | exact ⟨.error e, rfl, post_of_call pre h⟩
  · cases o
    all_goals first | exact h.elim | exact ⟨.ok a, rfl, post_of_call pre h⟩

theorem run_add_of_stopped {exits : Exits} :
    ∀ (n k : Nat) (s : State), (∀ s', run exits n s ≠ .running s') → run exits (n + k) s = run exits n s
  | 0, _, s, h => absurd rfl (h s)
  | n + 1, k, s, h => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [run] at h ⊢
    split
    · rename_i s' hs
      rw [hs] at h
      exact run_add_of_stopped n k s' h
    · rfl

theorem run_of_behaves {loadBase returnAddress : UInt64} {s : State} {heap : AccountHeap}
    {spec : Except Spec.Error Spec.Account × Spec.ErrorMetrics}
    (h : Behaves loadBase s heap spec (invoke loadBase returnAddress s)) {n : Nat} (hn : fuel ≤ n) :
    run (exits loadBase returnAddress) n (enter loadBase s) = invoke loadBase returnAddress s := by
  unfold invoke at h ⊢
  rw [show n = fuel + (n - fuel) by omega]
  refine run_add_of_stopped _ _ _ fun s' hs => ?_
  rw [hs] at h
  exact h

end ValidateFeePayer
