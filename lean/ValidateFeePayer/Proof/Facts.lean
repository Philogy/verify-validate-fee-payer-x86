import ValidateFeePayer.Proof.Walk

/-!
`Pre` restated as the facts the walk uses: each field the code loads as a
`read` of the entry memory, and the footprint's disjointness as `Separate`
hypotheses for `apart`.
-/

namespace ValidateFeePayer.Proof

open X86 Memory Image.Layout

theorem bytes_drop {m : Memory} {acc : Access} {a : UInt64} {n k : Nat} {bs : List UInt8}
    (h : m.bytes acc a (n + k) = .ok bs) : m.bytes acc (a + n.toUInt64) k = .ok (bs.drop n) := by
  simp only [bytes, List.range_add, List.mapM_append, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i l hl
    split at h
    · cases h
    · rename_i l' hl'
      cases h
      have : l.length = n := by simpa using length_of_mapM_ok hl
      subst this
      simp only [List.drop_left]
      rw [List.mapM_map] at hl'
      simp only [bytes]
      rw [← hl']
      congr 1; funext i
      simp only [Function.comp, Nat.toUInt64_eq, UInt64.ofNat_add, UInt64.add_assoc]

theorem read128_of_bytes {m : Memory} {a : UInt64} {bs : List UInt8} (h : m.bytes .read a 16 = .ok bs) :
    m.read128 a = .ok (ofHalves (ofLittleEndian (bs.take 8)) (ofLittleEndian (bs.drop 8))) := by
  simp [Memory.read128, h, bind, Except.bind, pure, Except.pure]

theorem read_of_bytes {m : Memory} {w : Width} {a : UInt64} {bs : List UInt8}
    (h : m.bytes .read a w.size = .ok bs) : m.read w a = .ok (ofLittleEndian bs) := by
  simp [Memory.read, h, bind, Except.bind, pure, Except.pure]

/-- The owner's two 16-byte halves, as the code loads them, are zero exactly
for the system program. -/
theorem ownerHalves_eq_zero (v : Spec.Pubkey) :
    (ofHalves (ofLittleEndian ((v.toList.drop 16).take 8)) (ofLittleEndian ((v.toList.drop 16).drop 8)) |||
      ofHalves (ofLittleEndian ((v.toList.take 16).take 8)) (ofLittleEndian ((v.toList.take 16).drop 8))) = 0 ↔
    v = Spec.systemProgramId := by
  obtain ⟨⟨l⟩, hl⟩ := v
  simp only [List.size_toArray] at hl
  match l, hl with
  | [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
     b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31], _ =>
    simp only [Spec.systemProgramId, Vector.toList, Vector.replicate, Vector.mk.injEq, Array.replicate,
      List.replicate, Array.mk.injEq, List.cons.injEq, List.drop, List.take, ofLittleEndian, ofHalves, and_true]
    bv_decide

theorem off_eq (a : UInt64) (n : Nat) : off a n = a + n.toUInt64 := rfl

theorem Spec.Account.reads {m : Memory} {p : AccountAt} {x : Spec.Account} (h : x.Encodes m p) :
    m.read .bytes8 p.account = .ok p.arcInner ∧
    m.read .bytes8 (p.account + 8) = .ok x.lamports ∧
    m.read128 (p.account + 16) = .ok (ofHalves (ofLittleEndian ((x.owner.toList.take 16).take 8))
      (ofLittleEndian ((x.owner.toList.take 16).drop 8))) ∧
    m.read128 (p.account + 32) = .ok (ofHalves (ofLittleEndian ((x.owner.toList.drop 16).take 8))
      (ofLittleEndian ((x.owner.toList.drop 16).drop 8))) ∧
    m.read .bytes8 (p.arcInner + 24) = .ok p.data ∧
    m.read .bytes8 (p.arcInner + 32) = .ok x.data.length.toUInt64 ∧
    (x.data.length = 80 →
      m.read .bytes4 p.data = .ok (ofLittleEndian (x.data.take 4)) ∧
      m.read .bytes4 (p.data + 4) = .ok (ofLittleEndian ((x.data.drop 4).take 4))) := by
  obtain ⟨harc, hlam, hown, hdat, hlen, hbytes⟩ := h
  simp only [Memory.Holds, Memory.HoldsBytes, off_eq, account_shared_data.data_arc,
    account_shared_data.lamports, account_shared_data.owner, account_shared_data.arc_inner.data_ptr,
    account_shared_data.arc_inner.data_len, Nat.toUInt64_eq, UInt64.reduceOfNat, UInt64.add_zero] at *
  have hown32 : m.bytes .read (p.account + 16) (16 + 16) = .ok x.owner.toList := by simpa using hown
  refine ⟨harc, hlam, read128_of_bytes (by simpa using bytes_take hown32 (k := 16) (by omega)), ?_,
    hdat, hlen, fun h80 => ⟨?_, ?_⟩⟩
  · have := read128_of_bytes (bytes_drop hown32)
    simpa [UInt64.add_assoc] using this
  · rw [h80] at hbytes
    exact read_of_bytes (bytes_take hbytes (by decide))
  · rw [h80] at hbytes
    have h76 : m.bytes .read p.data (4 + 76) = .ok x.data := hbytes
    have := bytes_take (bytes_drop h76) (k := Width.bytes4.size) (by decide)
    simp only [Nat.toUInt64_eq, UInt64.reduceOfNat] at this
    exact read_of_bytes this

/-- The objects' addresses as `Nat` intervals: none wraps around, and no two
overlap. `S` is the lowest stack address the code uses. -/
structure Separation (c : Call) (S : UInt64) (n : Nat) : Prop where
  stack : S.toNat + 112 ≤ 2 ^ 64
  result : c.result.toNat + 12 ≤ 2 ^ 64
  account : c.account.account.toNat + 64 ≤ 2 ^ 64
  arcInner : c.account.arcInner.toNat + 40 ≤ 2 ^ 64
  data : c.account.data.toNat + n ≤ 2 ^ 64
  metrics : c.errorMetrics.toNat + 192 ≤ 2 ^ 64
  rent : c.rent.toNat + 24 ≤ 2 ^ 64
  result_account : Separate c.result 12 c.account.account 64
  result_arcInner : Separate c.result 12 c.account.arcInner 40
  result_data : Separate c.result 12 c.account.data n
  result_metrics : Separate c.result 12 c.errorMetrics 192
  result_rent : Separate c.result 12 c.rent 24
  result_stack : Separate c.result 12 S 112
  account_arcInner : Separate c.account.account 64 c.account.arcInner 40
  account_data : Separate c.account.account 64 c.account.data n
  account_metrics : Separate c.account.account 64 c.errorMetrics 192
  account_rent : Separate c.account.account 64 c.rent 24
  account_stack : Separate c.account.account 64 S 112
  arcInner_data : Separate c.account.arcInner 40 c.account.data n
  arcInner_metrics : Separate c.account.arcInner 40 c.errorMetrics 192
  arcInner_rent : Separate c.account.arcInner 40 c.rent 24
  arcInner_stack : Separate c.account.arcInner 40 S 112
  data_metrics : Separate c.account.data n c.errorMetrics 192
  data_rent : Separate c.account.data n c.rent 24
  data_stack : Separate c.account.data n S 112
  metrics_rent : Separate c.errorMetrics 192 c.rent 24
  metrics_stack : Separate c.errorMetrics 192 S 112
  rent_stack : Separate c.rent 24 S 112

theorem separation_of_pre {c : Call} {account metrics rent relax s} (pre : Pre c account metrics rent relax s) :
    Separation c (s.stackPointer - 96) account.data.length := by
  have hdis := pre.disjoint
  have hnw := pre.noWrap
  simp only [IntervalsDisjoint, Call.footprint, interval, List.pairwise_append, List.pairwise_cons,
    List.mem_cons, List.mem_map, List.not_mem_nil, forall_eq_or_imp, forall_eq, List.cons_append,
    List.nil_append, forall_exists_index, and_imp, result.size, account_shared_data.size,
    account_shared_data.arc_inner.data_len, transaction_error_metrics.size, Image.Layout.rent.size, stackUse,
    List.Pairwise.nil, true_and, and_true, false_or, or_false, imp_false, Nat.toUInt64_eq,
    UInt64.reduceOfNat, Nat.reduceAdd] at hdis hnw
  obtain ⟨⟨h01, h02, h03, h04, h05, h06, -⟩, ⟨h12, h13, h14, h15, h16, -⟩, ⟨h23, h24, h25, h26, -⟩,
    ⟨h34, h35, h36, -⟩, ⟨h45, h46, -⟩, ⟨h56, -⟩, -⟩ := hdis
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, -⟩ := hnw
  exact ⟨n6, n0, n1, n2, n3, n4, n5, h01, h02, h03, h04, h05, h06, h12, h13, h14, h15, h16, h23, h24, h25,
    h26, h34, h35, h36, h45, h46, h56⟩

end ValidateFeePayer.Proof
