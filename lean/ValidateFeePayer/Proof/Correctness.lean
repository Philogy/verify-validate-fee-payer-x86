import ValidateFeePayer.Proof.Entry2
import ValidateFeePayer.Proof.PathsCurrent
import ValidateFeePayer.Proof.PathsSimd0194

/-!
The proofs of the correctness theorems. The hypotheses become `Pre`
(`pre_of`), `Pre` gives the walk's `Entry` facts and the state in the
explicit form the walk starts from, and each integer exemption threshold has
its walk of every path. Without `Encoded`, the values the walk needs are
read off the memory `Footprint` describes (`encoded_of_footprint`).
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
      s.rflags s.mxcsr s.memory := by
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

theorem step_returned {exits : Exits} {s s' : State} (h : step exits s = .returned s') :
    s'.rip = exits.returnAddress := by
  by_cases hr : s.rip = exits.returnAddress
  · simp only [step, hr, ↓reduceIte, Id.run, pure, Outcome.returned.injEq] at h
    subst h; exact hr
  · exfalso
    by_cases hp : s.rip = exits.panicAt
    · have hne : exits.panicAt ≠ exits.returnAddress := hp ▸ hr
      simp [step, hp, hne, Id.run] at h
    · simp only [step, hr, hp, ↓reduceIte, Id.run] at h
      split at h
      · split at h <;> exact Outcome.noConfusion h
      · exact Outcome.noConfusion h

theorem run_returned {exits : Exits} :
    ∀ {n : Nat} {s s' : State}, run exits n s = .returned s' → s'.rip = exits.returnAddress
  | 0, _, _, h => by cases h
  | n + 1, s, s', h => by
    simp only [run] at h
    split at h
    · exact run_returned h
    · exact step_returned h

theorem untouched_of_frame {c : Call} {account metrics rent relax s} (pre : Pre c account metrics rent relax s)
    {s' : State} (h : c.Frame s s') : CallerMemoryUntouched s s' := by
  intro access a ha
  apply h
  simp only [writes, List.mem_cons, forall_eq_or_imp] at ha
  obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := ha
  simp only [Call.Written, ← pre.result, ← pre.accountPtr, ← pre.errorMetrics]
  rintro (hw | hw | hw | hw | hw | hw)
  · exact h0 hw
  · exact h1 hw
  · exact h2 hw
  · exact h3 hw
  · exact h4 hw
  · exact h5 hw

theorem returned_of_callPost {c : Call} {account metrics rent relax s} (pre : Pre c account metrics rent relax s)
    {metrics' : Spec.ErrorMetrics} {r : Except Spec.TransactionError Spec.Account} {s' : State}
    (h : CallPost c s metrics' r s') (hrip : s'.rip = c.returnAddress) :
    PanicsOrReturns c.returnAddress s (.returned s') ∧ ResultEncoded s c.heap metrics' r s' := by
  have hres : (args s).result = c.result := pre.result
  have hacc : accountAt s c.heap = c.account := pre.accountAt_eq
  have hmet : (args s).errorMetrics = c.errorMetrics := pre.errorMetrics
  refine ⟨⟨⟨hrip, h.stackPopped, h.calleeSavedKept, h.mxcsrKept⟩, ?_, untouched_of_frame pre h.frame⟩, ?_⟩
  · show _ = (args s).result
    rw [hres]; exact h.returnsResultPointer
  · exact {
      resultEncoded := by rw [hres]; exact h.resultEncoded
      accountEncoded := by rw [hacc]; exact h.accountEncoded
      metricsEncoded := by rw [hmet]; exact h.metricsEncoded }

theorem integerThreshold_of_read {s : State} {p : UInt64} {rent : Spec.Rent} (e : rent.Encodes s.memory p)
    (h : s.memory.read .bits64 (off p Image.Layout.rent.exemption_threshold) ∈
      [.ok Spec.simd0194ExemptionThreshold, .ok Spec.currentExemptionThreshold]) :
    IntegerThreshold rent := by
  have := e.2
  unfold Memory.Holds at this
  rw [this] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Except.ok.injEq] at h
  exact h

theorem pre_of {loadBase returnAddress : UInt64} {s : State} {heap : AccountHeap} {x : Args}
    (loaded : Loaded loadBase s.memory) (called : Called loadBase returnAddress s)
    (footprint : Footprint loadBase s heap x.account.data.length) (encoded : Encoded s heap x)
    (integerThreshold : IntegerThreshold x.rent) :
    Pre (.of loadBase returnAddress s heap x.payerIndex x.fee) x.account x.metrics x.rent x.relax s :=
  { ofState := rfl, loaded, called, footprint, encoded, integerThreshold }

theorem invoke_matchesSpec {loadBase returnAddress : UInt64} {s : State} {heap : AccountHeap} {x : Args}
    (loaded : Loaded loadBase s.memory) (called : Called loadBase returnAddress s)
    (footprint : Footprint loadBase s heap x.account.data.length) (encoded : Encoded s heap x)
    (integerThreshold : s.memory.read .bits64 (exemptionThresholdAddress s) ∈
      [.ok Spec.simd0194ExemptionThreshold, .ok Spec.currentExemptionThreshold]) :
    PanicsOrReturns returnAddress s (invoke loadBase returnAddress s) ∧
      MatchesSpec s heap x.spec (invoke loadBase returnAddress s) := by
  have pre := pre_of loaded called footprint encoded (integerThreshold_of_read encoded.rent integerThreshold)
  have h : Spec.Outcome _ x.account x.metrics x.rent x.relax s (run (exits loadBase returnAddress) fuel s) :=
    (symbolicRun _ x.account x.metrics x.rent x.relax _ pre).run_eq (Nat.le_refl fuel)
  have hrip : ∀ s', run (exits loadBase returnAddress) fuel s = .returned s' → s'.rip = returnAddress :=
    fun _ hr => run_returned hr
  unfold Spec.Outcome at h
  unfold invoke Args.spec
  rw [show (Call.of loadBase returnAddress s heap x.payerIndex x.fee).payerIndex = x.payerIndex from rfl,
    show (Call.of loadBase returnAddress s heap x.payerIndex x.fee).fee = x.fee from rfl] at h
  generalize run (exits loadBase returnAddress) fuel s = o at h hrip ⊢
  generalize Spec.validateFeePayer x.account x.payerIndex x.rent x.fee x.relax x.metrics = r at h ⊢
  obtain ⟨(e | a), m⟩ := r
  · cases e with
    | panic p =>
      cases o
      all_goals first | exact h.elim | exact ⟨untouched_of_frame pre h, ⟨p, rfl⟩⟩
    | tx e =>
      cases o with
      | returned s' =>
        obtain ⟨hp, he⟩ := returned_of_callPost pre h (hrip s' rfl)
        exact ⟨hp, .error e, rfl, he⟩
      | _ => exact h.elim
  · cases o with
    | returned s' =>
      obtain ⟨hp, he⟩ := returned_of_callPost pre h (hrip s' rfl)
      exact ⟨hp, .ok a, rfl, he⟩
    | _ => exact h.elim

/-! ## The values in the footprint -/

theorem readable_of_writable {m : Memory} {a : UInt64} {n : Nat} (h : m.Writable a n) : m.Readable a n := by
  intro i hi
  obtain ⟨b, hb⟩ := h i hi
  unfold Memory.byte at hb ⊢
  split at hb
  · cases hb
  · rename_i c _
    exact ⟨c.byte, by simp [Permissions.allows]⟩

theorem bytes_of_readable {m : Memory} {a : UInt64} {n : Nat} (h : m.Readable a n) :
    ∃ bs, bs.length = n ∧ m.bytes .read a n = .ok bs := by
  obtain ⟨bs, hbs⟩ := bytes_ok h
  exact ⟨bs, by simpa using length_of_mapM_ok hbs, hbs⟩

theorem holds_of_readable {m : Memory} {w : OperandSize} {a : UInt64} (h : m.Readable a w.byteCount) :
    ∃ v, m.Holds w a v := by
  obtain ⟨bs, -, hbs⟩ := bytes_of_readable h
  exact ⟨_, read_of_bytes hbs⟩

theorem toUInt16_toUInt64 (v : UInt64) : v.toUInt16.toUInt64 = v &&& 0xffff := by
  apply UInt64.toNat_inj.1
  simp only [UInt16.toNat_toUInt64, UInt64.toNat_toUInt16, UInt64.toNat_and]
  exact (Nat.and_two_pow_sub_one_eq_mod v.toNat 16).symm

/-- Whatever the memory `Footprint` describes holds, it encodes some `Args`. -/
theorem encoded_of_footprint {loadBase : UInt64} {s : State} {heap : AccountHeap} {n : Nat}
    (fp : Footprint loadBase s heap n) : ∃ x : Args, x.account.data.length = n ∧ Encoded s heap x := by
  have rd (b : Abi.Block) (hb : b ∈ reads s heap n) : s.memory.Readable b.base b.size := fp.readable b hb
  have wr (b : Abi.Block) (hb : b ∈ writes s) : s.memory.Readable b.base b.size :=
    readable_of_writable (fp.writable b hb)
  obtain ⟨owner, howner, hown⟩ :=
    bytes_of_readable (rd ⟨off (args s).account Image.Layout.account_shared_data.owner, 32⟩ (by simp [reads]))
  obtain ⟨data, hdata, hdat⟩ := bytes_of_readable (rd ⟨heap.data, n⟩ (by simp [reads]))
  obtain ⟨lamports, hlam⟩ := holds_of_readable (w := .bits64)
    (wr ⟨off (args s).account Image.Layout.account_shared_data.lamports, 8⟩ (by simp [writes]))
  obtain ⟨lpb, hlpb⟩ := holds_of_readable (w := .bits64)
    (rd ⟨off (args s).rent Image.Layout.rent.lamports_per_byte, 8⟩ (by simp [reads]))
  obtain ⟨thr, hthr⟩ := holds_of_readable (w := .bits64)
    (rd ⟨off (args s).rent Image.Layout.rent.exemption_threshold, 8⟩ (by simp [reads]))
  obtain ⟨c1, hc1⟩ := holds_of_readable (w := .bits64)
    (wr ⟨off (args s).errorMetrics Image.Layout.transaction_error_metrics.account_not_found, 8⟩ (by simp [writes]))
  obtain ⟨c2, hc2⟩ := holds_of_readable (w := .bits64)
    (wr ⟨off (args s).errorMetrics Image.Layout.transaction_error_metrics.invalid_account_for_fee, 8⟩
      (by simp [writes]))
  obtain ⟨c3, hc3⟩ := holds_of_readable (w := .bits64)
    (wr ⟨off (args s).errorMetrics Image.Layout.transaction_error_metrics.insufficient_funds, 8⟩ (by simp [writes]))
  have hrelax : ∃ relax, BoolEncodes s.memory (args s).relax relax := by
    rcases fp.relaxIsBool with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  obtain ⟨relax, hrel⟩ := hrelax
  let account : Spec.Account := ⟨lamports, ⟨⟨owner⟩, howner⟩, data⟩
  refine ⟨⟨account, (args s).payerIndex.toUInt16, ⟨lpb, thr⟩, (args s).fee, relax, ⟨c1, c2, c3⟩⟩, hdata,
    ⟨?_, (toUInt16_toUInt64 _).symm, ⟨hlpb, hthr⟩, rfl, hrel, ⟨hc1, hc2, hc3⟩⟩⟩
  refine ⟨fp.arcInner, hlam, ?_, fp.data, ?_, ?_⟩
  · show s.memory.bytes .read _ owner.length = .ok owner
    rw [howner]; exact hown
  · show s.memory.Holds _ _ data.length.toUInt64
    rw [hdata]; exact fp.length
  · show s.memory.bytes .read _ data.length = .ok data
    rw [hdata]; exact hdat

theorem invoke_panicsOrReturns {loadBase returnAddress : UInt64} {s : State} {heap : AccountHeap} {n : Nat}
    (loaded : Loaded loadBase s.memory) (called : Called loadBase returnAddress s)
    (footprint : Footprint loadBase s heap n)
    (integerThreshold : s.memory.read .bits64 (exemptionThresholdAddress s) ∈
      [.ok Spec.simd0194ExemptionThreshold, .ok Spec.currentExemptionThreshold]) :
    PanicsOrReturns returnAddress s (invoke loadBase returnAddress s) := by
  obtain ⟨x, rfl, encoded⟩ := encoded_of_footprint footprint
  exact (invoke_matchesSpec loaded called footprint encoded integerThreshold).1

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

theorem run_of_panicsOrReturns {loadBase returnAddress : UInt64} {s : State}
    (h : PanicsOrReturns returnAddress s (invoke loadBase returnAddress s)) {n : Nat} (hn : fuel ≤ n) :
    run (exits loadBase returnAddress) n s = invoke loadBase returnAddress s := by
  unfold invoke at h ⊢
  rw [show n = fuel + (n - fuel) by omega]
  refine run_add_of_stopped _ _ _ fun s' hs => ?_
  rw [hs] at h
  exact h

end ValidateFeePayer
