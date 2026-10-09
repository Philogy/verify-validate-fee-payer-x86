import ValidateFeePayer.Spec

/-!
`validate_fee_payer` statement by statement: the `&mut` arguments are the
state of `SpecM`, a returned `TransactionError` is the result, and only a
panic is an error. Includes the `checked_sub_lamports(fee)` branch
(`account_loader.rs:407-409`) that `Spec.validateFeePayer` drops because the
check before it already rules it out.
-/

namespace ValidateFeePayer.Spec.RustShaped

/-- The values behind the `&mut` arguments of `validate_fee_payer`. -/
structure MutRefs where
  account : Account
  metrics : ErrorMetrics

abbrev SpecM := StateT MutRefs (Except Panic)

def checkStaticAccountRentStateTransition (preBalance postBalance dataSize : UInt64) (rent : Rent)
    (accountIndex : UInt16) (relax : Bool) : Except Panic (Except TransactionError Unit) := do
  let minBalance ← minimumBalance rent dataSize
  let preState := preExecAccountRentState preBalance dataSize minBalance relax
  let postState := postExecAccountRentState postBalance dataSize minBalance preState preBalance relax
  if transitionAllowed preState postState then return .ok ()
  return .error (.insufficientFundsForRent accountIndex.toUInt8)

def modifyMetrics (f : ErrorMetrics → ErrorMetrics) : SpecM Unit :=
  modify fun s => { s with metrics := f s.metrics }

def getAccount : SpecM Account := do return (← get).account

def validateFeePayer (payerIndex : UInt16) (rent : Rent) (fee : UInt64) (relax : Bool) :
    SpecM (Except TransactionError Unit) := do
  if (← getAccount).lamports = 0 then
    modifyMetrics fun m => { m with accountNotFound := saturatingIncrement m.accountNotFound }
    return .error .accountNotFound
  let some kind := systemAccountKind (← getAccount)
    | modifyMetrics fun m => { m with invalidAccountForFee := saturatingIncrement m.invalidAccountForFee }
      return .error .invalidAccountForFee
  let minBalance ← match kind with
    | .system => pure 0
    | .nonce => minimumBalance rent nonceStateSize.toUInt64
  if (← getAccount).lamports.toNat < fee.toNat + minBalance.toNat then
    modifyMetrics fun m => { m with insufficientFunds := saturatingIncrement m.insufficientFunds }
    return .error .insufficientFundsForFee
  let preBalance := (← getAccount).lamports
  if preBalance < fee then return .error .insufficientFundsForFee
  let postBalance := preBalance - fee
  modify ({ · with account.lamports := postBalance })
  checkStaticAccountRentStateTransition preBalance postBalance (← getAccount).data.length.toUInt64 rent
    payerIndex relax

/-- How a run of the Rust-shaped spec from `⟨account, metrics⟩` matches the
result of `Spec.validateFeePayer`: the same panic, or the same error with the
metrics `ErrorMetrics.record` gives, or success with the new account. -/
def Agrees (metrics : ErrorMetrics) :
    Except Error Account → Except Panic (Except TransactionError Unit × MutRefs) → Prop
  | .ok account, r => r = .ok (.ok (), ⟨account, metrics⟩)
  | .error (.panic p), r => r = .error p
  | .error (.tx e), r => ∃ account, r = .ok (.error e, ⟨account, metrics.record e⟩)

end ValidateFeePayer.Spec.RustShaped
