import ValidateFeePayer.Contract

namespace ValidateFeePayer

open X86

/-- `checked_sub_lamports(fee)` cannot fail once the balance covers the fee
and the minimum balance, so the code's branch for it is dead and
`Spec.chargeFeePayer` subtracts unchecked. -/
theorem checkedSubLamports_ok {lamports fee minBalance : UInt64}
    (h : ¬ lamports.toNat < fee.toNat + minBalance.toNat) : ¬ lamports < fee := by
  rw [UInt64.lt_iff_toNat_lt]; omega

/-- What a finished run must look like: it panics exactly when the spec
panics, and otherwise returns in a state satisfying `Post`. -/
def Spec.Outcome (c : Call) (account : Spec.Account) (metrics : Spec.ErrorMetrics) (rent : Spec.Rent)
    (relax : Bool) (s : State) (o : X86.Outcome) : Prop :=
  match Spec.validateFeePayer account c.payerIndex rent c.fee relax metrics, o with
  | (.error (.panic _), _), .panicked _ => True
  | (.error (.tx e), metrics'), .returned s' => Post c s metrics' (.error e) s'
  | (.ok account', metrics'), .returned s' => Post c s metrics' (.ok account') s'
  | _, _ => False

end ValidateFeePayer
