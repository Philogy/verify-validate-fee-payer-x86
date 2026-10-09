import ValidateFeePayer.Proof.Leaf

/-! `walk_simd0194` for accounts whose data is not nonce-sized. -/

namespace ValidateFeePayer.Proof
open X86

set_option maxHeartbeats 0 in
theorem walk_simd0194_other {c : Call} {account : Spec.Account} {metrics : Spec.ErrorMetrics} {rent : Spec.Rent}
    {relax : Bool} {s : State} {lb S acct arc dat res met rnt fee ra r0 r2 r3 r5 r10 r11 r12 r13 r14 r15 : UInt64}
    {o1 o2 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : BitVec 128} {fc : UInt32} {m : Memory}
    (e : Entry c account metrics rent relax s lb S acct arc dat res met rnt fee ra r2 r3 r5 r12 r13 r14 r15 o1 o2 fc m)
    (hthr : rent.exemptionThreshold = Spec.simd0194ExemptionThreshold) (path : ¬ account.data.length.toUInt64 = 80) :
    Finishes c.exits 240 (entryState lb S acct res met rnt fee r0 r2 r3 r5 r10 r11 r12 r13 r14 r15
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 fc m)
      (Spec.Outcome c account metrics rent relax s) := by
  vpaths e, account, hthr, Spec.simd0194ExemptionThreshold, minimumBalance_simd0194 hthr
end ValidateFeePayer.Proof
