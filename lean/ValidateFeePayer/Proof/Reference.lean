import ValidateFeePayer.Reference

/-! The proof that `Spec.chargeFeePayer` agrees with `Reference.chargeFeePayer`. -/

namespace ValidateFeePayer.Reference

open Spec

theorem getPreExecAccountRentState_eq (lamports dataSize minBalance : UInt64) (relax : Bool) :
    getPreExecAccountRentState lamports dataSize minBalance relax =
      if lamports = 0 then .uninitialized
      else if lamports ≥ minBalance ∨ relax then .rentExempt
      else .rentPaying lamports dataSize := by
  unfold getPreExecAccountRentState getAccountRentState
  by_cases h0 : lamports = 0 <;> by_cases h1 : lamports ≥ minBalance <;> cases relax <;> simp [h0, h1]

theorem getPostExecAccountRentState_eq (lamports dataSize minBalance : UInt64) (pre : RentState)
    (preBalance : UInt64) (relax : Bool) :
    getPostExecAccountRentState lamports dataSize minBalance pre preBalance relax =
      if lamports = 0 then .uninitialized
      else if lamports ≥ minBalance then .rentExempt
      else if relax ∧ pre = .rentExempt ∧ lamports ≥ preBalance then .rentExempt
      else .rentPaying lamports dataSize := by
  unfold getPostExecAccountRentState getAccountRentState
  cases relax <;> simp <;> rfl

/-- The rent-state transition fails exactly when the simplified condition of
`Spec.chargeFeePayer` holds, given what the earlier checks establish. -/
theorem transitionAllowed_iff {lamports fee dataSize minBalance : UInt64} {relax : Bool}
    (hl : lamports ≠ 0) (hf : fee ≤ lamports) :
    let pre := getPreExecAccountRentState lamports dataSize minBalance relax
    transitionAllowed pre
        (getPostExecAccountRentState (lamports - fee) dataSize minBalance pre lamports relax) =
      !decide (0 < lamports - fee ∧ lamports - fee < minBalance ∧
        (minBalance ≤ lamports ∨ relax ∧ fee ≠ 0)) := by
  have hsub : (lamports - fee).toNat = lamports.toNat - fee.toNat := UInt64.toNat_sub_of_le _ _ hf
  simp only [getPreExecAccountRentState_eq, getPostExecAccountRentState_eq]
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, UInt64.toNat_zero] at *
  simp only [transitionAllowed,
    UInt64.le_iff_toNat_le, ← UInt64.toNat_inj, UInt64.toNat_zero, hsub, hl]
  have hl' : lamports.toNat ≠ 0 := fun h => hl (UInt64.toNat_inj.mp h)
  have hfee : fee = 0 ↔ fee.toNat = 0 := by simp [← UInt64.toNat_inj]
  by_cases h0 : lamports.toNat - fee.toNat = 0 <;>
  by_cases h1 : minBalance.toNat ≤ lamports.toNat - fee.toNat <;>
  by_cases h2 : minBalance.toNat ≤ lamports.toNat <;>
  by_cases h3 : lamports.toNat ≤ lamports.toNat - fee.toNat <;>
  cases relax <;> simp [h0, h1, h2, h3, hsub, hfee] <;> omega

theorem chargeFeePayer_eq' (account : Account) (payerIndex : UInt16) (rent : Rent) (fee : UInt64)
    (relax : Bool) :
    Spec.chargeFeePayer account payerIndex rent fee relax =
      Reference.chargeFeePayer account payerIndex rent fee relax := by
  simp only [Spec.chargeFeePayer, Reference.chargeFeePayer, checkStaticAccountRentStateTransition]
  by_cases hl : account.lamports = 0
  · simp only [hl, ite_true]; rfl
  simp only [hl, ite_false]
  rcases hk : systemAccountKind account with _ | _ | _
  · rfl
  all_goals
    simp only
    congr 1; funext minBalance
    by_cases hf : account.lamports < fee
    · simp only [hf, ite_true]; rfl
    have hf' : fee ≤ account.lamports := UInt64.not_lt.mp hf
    by_cases hm : account.lamports - fee < minBalance
    · simp only [hf, hm, ite_true, ite_false]; rfl
    simp only [hf, hm, ite_false]
    cases minimumBalance rent account.data.length.toUInt64
    · rfl
    rename_i r
    simp only [transitionAllowed_iff hl hf']
    by_cases hc : 0 < account.lamports - fee ∧ account.lamports - fee < r ∧
        (r ≤ account.lamports ∨ relax = true ∧ fee ≠ 0)
    all_goals
      simp only [liftM, monadLift, MonadLift.monadLift, Except.mapError, bind, Except.bind]
      simp [hc] <;> rfl

end ValidateFeePayer.Reference
