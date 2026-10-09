import ValidateFeePayer.Proof.Leaf

/-!
Every path of the code from the entry state, for the exemption threshold
`1.0` (SIMD-0194), ends as `Spec.Outcome` says.
-/
namespace ValidateFeePayer.Proof
open X86

set_option maxHeartbeats 0 in
theorem walk_simd0194 {c : Call} {account : Spec.Account} {metrics : Spec.ErrorMetrics} {rent : Spec.Rent}
    {relax : Bool} {s : State} {lb S acct arc dat res met rnt fee ra r0 r2 r3 r5 r10 r11 r12 r13 r14 r15 : UInt64}
    {o1 o2 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : BitVec 128} {fc : UInt32} {m : Memory}
    (e : Entry c account metrics rent relax s lb S acct arc dat res met rnt fee ra r2 r3 r5 r12 r13 r14 r15 o1 o2 fc m)
    (hthr : rent.exemptionThreshold = Spec.simd0194ExemptionThreshold) :
    Finishes c.exits 240 (entryState lb S acct res met rnt fee r0 r2 r3 r5 r10 r11 r12 r13 r14 r15
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 fc m)
      (Spec.Outcome c account metrics rent relax s) := by
  have hx := e.codeExits
  have hc := e.code
  have hd := e.data
  have hw := e.stackFree
  have hwr := e.resultWritable
  have hwm1 := e.accountNotFoundWritable
  have hwm2 := e.insufficientFundsWritable
  have hwm3 := e.invalidAccountForFeeWritable
  have hwl := e.lamportsWritable
  have hSt := e.stackBound
  have hR := e.resultBound
  have hA := e.accountBound
  have hArc := e.arcBound
  have hM := e.metricsBound
  have hRnt := e.rentBound
  have s01 := e.result_account
  have s02 := e.result_arcInner
  have s04 := e.result_metrics
  have s05 := e.result_rent
  have s06 := e.result_stack
  have s12 := e.account_arcInner
  have s14 := e.account_metrics
  have s15 := e.account_rent
  have s16 := e.account_stack
  have s24 := e.arcInner_metrics
  have s25 := e.arcInner_rent
  have s26 := e.arcInner_stack
  have s45 := e.metrics_rent
  have s46 := e.metrics_stack
  have s56 := e.rent_stack
  have hs36 := e.nonceData_stack
  have hDat80 := e.nonceDataBound
  have hthrM := e.readThreshold
  rw [hthr, Spec.simd0194ExemptionThreshold] at hthrM
  simp only [entryState]
  vwalk [e.readReturn, e.readRelax, e.readArc, e.readLamports, e.readOwnerLow, e.readOwnerHigh, e.readData,
    e.readLength, e.readVersions, e.readState, e.readLamportsPerByte, hthrM, e.readAccountNotFound,
    e.readInvalidAccountForFee, e.readInsufficientFunds]
  without_info all_goals vleaf e, account, minimumBalance_simd0194 hthr
end ValidateFeePayer.Proof
