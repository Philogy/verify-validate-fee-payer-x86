import ValidateFeePayer.Spec.RustShaped

/-! The proof of `Spec.RustShaped.validateFeePayer_agrees`: a case split on
every branch of both definitions. -/

namespace ValidateFeePayer.Spec.RustShaped

/-- `checked_sub_lamports(fee)` cannot fail once the balance covers the fee
and the minimum balance. -/
theorem checkedSubLamports_ok {lamports fee minBalance : UInt64}
    (h : ¬ lamports.toNat < fee.toNat + minBalance.toNat) : ¬ lamports < fee := by
  rw [UInt64.lt_iff_toNat_lt]; omega

private theorem ite_apply' {α β : Type} (c : Prop) [Decidable c] (f g : α → β) (a : α) :
    (if c then f else g) a = if c then f a else g a := by split <;> rfl

local macro "unfold_monads" : tactic => `(tactic| simp [*, Agrees, ErrorMetrics.record,
  TransactionError.metric?, ErrorMetrics.increment, bind, Except.bind, throw, throwThe,
  MonadExceptOf.throw, StateT.run, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, modify,
  modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, Except.pure, StateT.pure, liftM, monadLift,
  MonadLift.monadLift, Except.mapError, StateT.lift, set, StateT.set, MonadStateOf.set, ite_apply'])

set_option hygiene false in
/-- From the fee check on, given the minimum balance `m` of the payer's kind. -/
local macro "rentPath" m:term : tactic => `(tactic| (
  by_cases hc : account.lamports.toNat < fee.toNat + ($m : UInt64).toNat
  · try simp only [UInt64.toNat_zero, Nat.add_zero] at hc
    unfold_monads
  · have hs : ¬ account.lamports < fee := hsub hc
    try simp only [UInt64.toNat_zero, Nat.add_zero] at hc
    cases hr : minimumBalance rent (UInt64.ofNat account.data.length) with
    | error => unfold_monads
    | ok v =>
      cases ht : transitionAllowed
          (preExecAccountRentState account.lamports (UInt64.ofNat account.data.length) v relax)
          (postExecAccountRentState (account.lamports - fee) (UInt64.ofNat account.data.length) v
            (preExecAccountRentState account.lamports (UInt64.ofNat account.data.length) v relax)
            account.lamports relax) <;>
      unfold_monads))

theorem agrees (account : Account) (metrics : ErrorMetrics) (payerIndex : UInt16)
    (rent : Rent) (fee : UInt64) (relax : Bool) :
    Agrees metrics (Spec.validateFeePayer account payerIndex rent fee relax)
      ((validateFeePayer payerIndex rent fee relax).run ⟨account, metrics⟩) := by
  have hsub := @checkedSubLamports_ok account.lamports fee
  simp only [Spec.validateFeePayer, validateFeePayer, getAccount, modifyMetrics,
    Spec.checkStaticAccountRentStateTransition, checkStaticAccountRentStateTransition]
  by_cases h0 : account.lamports = 0
  · unfold_monads
  rcases hk : systemAccountKind account with _ | _ | _
  · unfold_monads
  · rentPath 0
  · cases hm : minimumBalance rent nonceStateSize.toUInt64 with
    | error => unfold_monads
    | ok m => rentPath m

end ValidateFeePayer.Spec.RustShaped
