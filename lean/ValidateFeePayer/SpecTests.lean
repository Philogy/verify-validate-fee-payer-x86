import ValidateFeePayer.Reference

/-!
Agave's `test_validate_fee_payer` and
`test_validate_nonce_fee_payer_with_checked_arithmetic`
(`svm/src/account_loader.rs`), run on `Spec.validateFeePayer` and on
`Reference.chargeFeePayer`.
-/

namespace ValidateFeePayer.SpecTests

open Spec

/-- `Rent::default()`. -/
def defaultRent : Rent := ⟨6960, simd0194ExemptionThreshold⟩

/-- `NonceVersions::new(NonceState::Initialized(..))`: version `Current` (1),
state `Initialized` (1). -/
def nonceAccount (lamports : UInt64) : Account :=
  { lamports, owner := systemProgramId, data := [1, 0, 0, 0, 1, 0, 0, 0] ++ List.replicate 72 0 }

def systemAccount (lamports : UInt64) : Account := { lamports, owner := systemProgramId, data := [] }

abbrev ChargeFeePayer := Account → UInt16 → Rent → UInt64 → Bool → Except Error Account

def viaSpec : ChargeFeePayer := fun a i r f x => (validateFeePayer a i r f x ⟨0, 0, 0⟩).1

/-- `validate_fee_payer_account`: the result, and the balance after a success. -/
def check (charge : ChargeFeePayer) (rent : Rent) (isNonce : Bool) (initBalance fee : UInt64)
    (relax : Bool) (expected : Except TransactionError Unit) (postBalance : UInt64) : Bool :=
  let account := if isNonce then nonceAccount initBalance else systemAccount initBalance
  match charge account 0 rent fee relax, expected with
  | .ok a, .ok () => a.lamports == postBalance
  | .error (.tx e), .error e' => e == e'
  | _, _ => false

def nonceMinBalance : UInt64 := (accountStorageOverhead + 80) * 6960
def systemMinBalance : UInt64 := accountStorageOverhead * 6960
def fee : UInt64 := 5000

def testValidateFeePayer (charge : ChargeFeePayer) : Bool :=
  let check := check charge defaultRent
  [false, true].all fun relax =>
    [(true, nonceMinBalance), (false, systemMinBalance), (false, 0)].all
      (fun (isNonce, minBalance) => check isNonce (minBalance + fee) fee relax (.ok ()) minBalance) &&
    [true, false].all (fun isNonce => check isNonce 0 fee relax (.error .accountNotFound) 0) &&
    [(true, nonceMinBalance + fee - 1, .error .insufficientFundsForFee),
     (true, nonceMinBalance - 1, .error .insufficientFundsForFee),
     (false, fee - 1, .error .insufficientFundsForFee),
     (false, systemMinBalance - 1,
       if relax then .error (.insufficientFundsForRent 0) else .ok ()),
     (false, systemMinBalance + fee - 1, .error (.insufficientFundsForRent 0))].all
      (fun (isNonce, initBalance, expected) => check isNonce initBalance fee relax expected (initBalance - fee)) &&
    check true nonceMinBalance nonceMinBalance relax (.error .insufficientFundsForFee) nonceMinBalance &&
    check false 0xffffffffffffffff 0xffffffffffffffff relax (.ok ()) 0

def testValidateNonceFeePayerWithCheckedArithmetic (charge : ChargeFeePayer) : Bool :=
  [false, true].all fun relax =>
    check charge { defaultRent with lamportsPerByte := 1 } true 0xffffffffffffffff 0xffffffffffffffff
      relax (.error .insufficientFundsForFee) 0xffffffffffffffff

#guard testValidateFeePayer viaSpec
#guard testValidateFeePayer Reference.chargeFeePayer
#guard testValidateNonceFeePayerWithCheckedArithmetic viaSpec
#guard testValidateNonceFeePayerWithCheckedArithmetic Reference.chargeFeePayer

end ValidateFeePayer.SpecTests
