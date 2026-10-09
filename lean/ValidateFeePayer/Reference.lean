import ValidateFeePayer.Spec

/-!
The rent-state check of `svm/src/rent_calculator.rs` function by function as
in Rust, and `chargeFeePayer` calling it. `Spec.chargeFeePayer` folds this
into one condition; the theorem in `ValidateFeePayer/ReferenceAgrees.lean`
says the two agree.
-/

namespace ValidateFeePayer.Reference

open Spec

inductive RentState where
  | uninitialized
  | rentPaying (lamports : UInt64) (dataSize : UInt64)
  | rentExempt
  deriving DecidableEq, Repr

def getAccountRentState (accountLamports accountSize minBalance : UInt64) : RentState :=
  if accountLamports = 0 then .uninitialized
  else if accountLamports ≥ minBalance then .rentExempt
  else .rentPaying accountLamports accountSize

def getPreExecAccountRentState (accountLamports accountSize minBalance : UInt64)
    (disallowRentPaying : Bool) : RentState :=
  match getAccountRentState accountLamports accountSize minBalance, disallowRentPaying with
  | .rentPaying .., true => .rentExempt
  | rentState, _ => rentState

def getPostExecAccountRentState (accountLamports accountSize minBalance : UInt64)
    (preRentState : RentState) (preExecBalance : UInt64) (relaxRentExemptCriteria : Bool) :
    RentState := Id.run do
  if !relaxRentExemptCriteria then
    return getAccountRentState accountLamports accountSize minBalance
  if accountLamports = 0 then .uninitialized
  else if accountLamports ≥ minBalance then .rentExempt
  else if preRentState = .rentExempt ∧ accountLamports ≥ preExecBalance then .rentExempt
  else .rentPaying accountLamports accountSize

def transitionAllowed (preRentState postRentState : RentState) : Bool :=
  match postRentState with
  | .uninitialized | .rentExempt => true
  | .rentPaying postLamports postDataSize =>
    match preRentState with
    | .uninitialized | .rentExempt => false
    | .rentPaying preLamports preDataSize => postDataSize == preDataSize && postLamports ≤ preLamports

def checkStaticAccountRentStateTransition (preExecBalance postExecBalance dataSize : UInt64)
    (rent : Rent) (accountIndex : UInt16) (relaxPostExecMinBalanceCheck : Bool) :
    Except Error Unit := do
  let rentMinBalance ← minimumBalance rent dataSize
  let preState := getPreExecAccountRentState preExecBalance dataSize rentMinBalance
    relaxPostExecMinBalanceCheck
  let postState := getPostExecAccountRentState postExecBalance dataSize rentMinBalance preState
    preExecBalance relaxPostExecMinBalanceCheck
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
