import ValidateFeePayer.Spec

/-!
The rent-state check of `svm/src/rent_calculator.rs` written as in Rust
(pre-exec state, post-exec state, allowed transition), and `chargeFeePayer`
calling it. `Spec.chargeFeePayer` folds this into one condition; the theorem
in `ValidateFeePayer/ReferenceAgrees.lean` says the two agree.
-/

namespace ValidateFeePayer.Reference

open Spec

inductive RentState where
  | uninitialized
  | rentPaying (lamports : UInt64) (dataSize : UInt64)
  | rentExempt
  deriving DecidableEq, Repr

def preExecAccountRentState (lamports dataSize minBalance : UInt64) (relax : Bool) :
    RentState :=
  if lamports = 0 then .uninitialized
  else if lamports ≥ minBalance ∨ relax then .rentExempt
  else .rentPaying lamports dataSize

def postExecAccountRentState (lamports dataSize minBalance : UInt64) (preState : RentState) (preBalance : UInt64) : RentState :=
  if lamports = 0 then .uninitialized
  else if lamports ≥ minBalance then .rentExempt
  else if preState = .rentExempt ∧ lamports ≥ preBalance then .rentExempt
  else .rentPaying lamports dataSize

def transitionAllowed (pre post : RentState) : Bool :=
  match post with
  | .uninitialized | .rentExempt => true
  | .rentPaying postLamports postDataSize =>
    match pre with
    | .rentPaying preLamports preDataSize => postDataSize == preDataSize && postLamports ≤ preLamports
    | _ => false

def checkStaticAccountRentStateTransition (preBalance postBalance dataSize : UInt64) (rent : Rent)
    (accountIndex : UInt16) (relax : Bool) : Except Error Unit := do
  let minBalance ← minimumBalance rent dataSize
  let preState := preExecAccountRentState preBalance dataSize minBalance relax
  let postState := postExecAccountRentState postBalance dataSize minBalance preState preBalance
  unless transitionAllowed preState postState do
    throw (.tx (.insufficientFundsForRent accountIndex.toUInt8))

def chargeFeePayer (account : Account) (payerIndex : UInt16) (rent : Rent) (fee : UInt64)
    (relax : Bool) : Except Error Account := do
  if account.lamports = 0 then throw (.tx .accountNotFound)
  let some kind := systemAccountKind account | throw (.tx .invalidAccountForFee)
  let minBalance ← match kind with
    | .system => pure 0
    | .nonce => minimumBalance rent nonceStateSize.toUInt64
  if account.lamports < fee then throw (.tx .insufficientFundsForFee)
  let postBalance := account.lamports - fee
  if postBalance < minBalance then throw (.tx .insufficientFundsForFee)
  checkStaticAccountRentStateTransition account.lamports postBalance account.data.length.toUInt64
    rent payerIndex relax
  return { account with lamports := postBalance }

end ValidateFeePayer.Reference
