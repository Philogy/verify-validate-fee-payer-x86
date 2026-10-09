import ValidateFeePayer.Proof.PathsSimd0194.Other
import ValidateFeePayer.Proof.PathsSimd0194.NonceStrict
import ValidateFeePayer.Proof.PathsSimd0194.NonceRelaxed

/-!
Every path of the code from the entry state, for the exemption threshold
`1.0` (SIMD-0194), ends as `Spec.Outcome` says. The cases are separate modules so that
they check in parallel.
-/
namespace ValidateFeePayer.Proof
open X86

theorem walk_simd0194 {c : Call} {account : Spec.Account} {metrics : Spec.ErrorMetrics} {rent : Spec.Rent}
    {relax : Bool} {s : State} {lb S acct arc dat res met rnt fee ra r0 r2 r3 r5 r10 r11 r12 r13 r14 r15 : UInt64}
    {o1 o2 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : BitVec 128} {fl : Flags} {fc : UInt32} {m : Memory}
    (e : Entry c account metrics rent relax s lb S acct arc dat res met rnt fee ra r2 r3 r5 r12 r13 r14 r15 o1 o2 fc m)
    (hthr : rent.exemptionThreshold = Spec.simd0194ExemptionThreshold) :
    Finishes c.exits 240 (entryState lb S acct res met rnt fee r0 r2 r3 r5 r10 r11 r12 r13 r14 r15
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 fl fc m)
      (Spec.Outcome c account metrics rent relax s) := by
  by_cases h80 : account.data.length.toUInt64 = 80
  · cases relax
    · exact walk_simd0194_nonceStrict e hthr h80 rfl
    · exact walk_simd0194_nonceRelaxed e hthr h80 rfl
  · exact walk_simd0194_other e hthr h80
end ValidateFeePayer.Proof
