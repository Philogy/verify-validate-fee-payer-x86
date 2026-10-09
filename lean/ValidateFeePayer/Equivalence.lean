import ValidateFeePayer.Proof.RustShaped

/-!
`Spec.validateFeePayer` against `Spec.RustShaped.validateFeePayer`, the
statement-by-statement transcription. The proof is in
`ValidateFeePayer/Proof/RustShaped.lean`.
-/

namespace ValidateFeePayer.Spec.RustShaped

/-- Both panic alike; both return the same error, with the metrics
`ErrorMetrics.record` gives; or both succeed with the same account and the
metrics unchanged. -/
theorem validateFeePayer_agrees (account : Account) (metrics : ErrorMetrics) (payerIndex : UInt16)
    (rent : Rent) (fee : UInt64) (relax : Bool) :
    Agrees metrics (Spec.validateFeePayer account payerIndex rent fee relax)
      ((validateFeePayer payerIndex rent fee relax).run ⟨account, metrics⟩) :=
  agrees account metrics payerIndex rent fee relax

end ValidateFeePayer.Spec.RustShaped
