import X86.F64
import X86.Bytes

/-!
`validate_fee_payer` (`svm/src/account_loader.rs` at the pinned Agave commit)
and what it calls, as pure Lean functions over the values its arguments
point to. Names follow the Rust source; `Option` is Rust's `Option`. The
`&mut` arguments are the state of `SpecM`, and a Rust panic is a `Panic`
error, so a panicking run has no final state.

Arithmetic is on `UInt64` with wrapping, as in a release build (no overflow
checks); the Rust source uses `checked_sub` where it needs checking.
-/

namespace ValidateFeePayer.Spec

open X86

abbrev Pubkey := Vector UInt8 32

/-- `solana_sdk_ids::system_program::ID`. -/
def systemProgramId : Pubkey := Vector.replicate 32 0

/-- The parts of `AccountSharedData` the function reads or writes. The rest
(`rent_epoch`, `executable`, the `Arc` counts, the `Vec` capacity) is left
alone, which the frame condition of the theorem states. -/
structure Account where
  lamports : UInt64
  owner : Pubkey
  data : List UInt8

structure Rent where
  lamportsPerByte : UInt64
  /-- An `f64` stored as bytes, compared bytewise; so its bits, not its value. -/
  exemptionThreshold : UInt64

/-- The three counters of `TransactionErrorMetrics` the function may
increment; it leaves the other 21 alone. -/
structure ErrorMetrics where
  accountNotFound : UInt64
  invalidAccountForFee : UInt64
  insufficientFunds : UInt64

inductive TransactionError where
  | accountNotFound
  | invalidAccountForFee
  | insufficientFundsForFee
  | insufficientFundsForRent (accountIndex : UInt8)
  deriving DecidableEq, Repr

/-- The panics reachable from `validate_fee_payer`, named by their message. -/
inductive Panic where
  | maximumPermittedDataLengthExceeded
  deriving DecidableEq, Repr

/-- The values behind the `&mut` arguments of `validate_fee_payer`. -/
structure MutRefs where
  account : Account
  metrics : ErrorMetrics

abbrev SpecM := StateT MutRefs (Except Panic)

def UInt64.MIN : UInt64 := 0
def UInt64.MAX : UInt64 := 0xffffffffffffffff
theorem UInt64.MIN_is_min : ∀ (x : UInt64), UInt64.MIN ≤ x := by grind [MIN]
theorem UInt64.MAX_is_max : ∀ (x : UInt64), x ≤ UInt64.MAX := by grind [MAX]

/-- `+= 1` on a `Saturating<usize>`. -/
def saturatingIncrement (c : UInt64) : UInt64 := if c = UInt64.MAX then c else c + 1

/-! ## `solana-rent` 4.5.0 -/

def accountStorageOverhead : UInt64 := 128
def maxPermittedDataLength : UInt64 := 10 * 1024 * 1024
def simd0194ExemptionThreshold : UInt64 := 0x3ff0000000000000
def currentExemptionThreshold : UInt64 := 0x4000000000000000
def simd0194MaxLamportsPerByte : UInt64 := 1759197129867
def currentMaxLamportsPerByte : UInt64 := 879598564933

/-- Rust's `u64 as f64`: rounded to nearest, ties to even. -/
def u64ToF64 (v : UInt64) : UInt64 := (F64.ofScaled v.toNat 0 false).1


/-- Rust's `f64 as u64`: truncated toward zero and saturating, with NaN as 0. -/
def f64ToU64 (x : UInt64) : UInt64 :=
  if F64.isNaN x then 0
  else if F64.isInfinite x then (if F64.sign x then UInt64.MIN else UInt64.MAX)
  else
    let t := (F64.scaled x).toNat / 2 ^ 1074
    if t ≥ UInt64.size then UInt64.MAX else t.toUInt64

def minimumBalanceUnchecked (rent : Rent) (dataLength : UInt64) : UInt64 :=
  let bytes := accountStorageOverhead + dataLength
  if rent.exemptionThreshold = simd0194ExemptionThreshold then bytes * rent.lamportsPerByte
  else if rent.exemptionThreshold = currentExemptionThreshold then 2 * bytes * rent.lamportsPerByte
  else f64ToU64 (F64.mul (u64ToF64 (bytes * rent.lamportsPerByte)) rent.exemptionThreshold).1

def tryMinimumBalance (rent : Rent) (dataLength : UInt64) : Option UInt64 :=
  if dataLength > maxPermittedDataLength then none
  else if (rent.lamportsPerByte > currentMaxLamportsPerByte ∧
      rent.exemptionThreshold = currentExemptionThreshold) ∨
    (rent.lamportsPerByte > simd0194MaxLamportsPerByte ∧
      rent.exemptionThreshold = simd0194ExemptionThreshold) then none
  else some (minimumBalanceUnchecked rent dataLength)

/-- `Rent::minimum_balance`: the `expect` on `try_minimum_balance`. -/
def minimumBalance (rent : Rent) (dataLength : UInt64) : Except Panic UInt64 :=
  match tryMinimumBalance rent dataLength with
  | some v => .ok v
  | none => .error .maximumPermittedDataLengthExceeded

/-! ## `solana-nonce-account` 5.0.0 -/

inductive SystemAccountKind where
  | system | nonce
  deriving DecidableEq, Repr

/-- `nonce::state::State::size()`. -/
def nonceStateSize : Nat := 80

def systemAccountKind (account : Account) : Option SystemAccountKind :=
  if account.owner ≠ systemProgramId then none
  else if account.data = [] then some .system
  else if account.data.length = nonceStateSize then
    let versionsTag := ofLittleEndian (account.data.take 4)
    let stateTag := ofLittleEndian ((account.data.drop 4).take 4)
    if (versionsTag = 0 ∨ versionsTag = 1) ∧ stateTag = 1 then some .nonce else none
  else none

/-! ## `svm/src/rent_calculator.rs` -/

inductive RentState where
  | uninitialized
  | rentPaying (lamports : UInt64) (dataSize : UInt64)
  | rentExempt
  deriving DecidableEq, Repr

def accountRentState (lamports dataSize minBalance : UInt64) : RentState :=
  if lamports = 0 then .uninitialized
  else if lamports ≥ minBalance then .rentExempt
  else .rentPaying lamports dataSize

def preExecAccountRentState (lamports dataSize minBalance : UInt64) (disallowRentPaying : Bool) :
    RentState :=
  match accountRentState lamports dataSize minBalance with
  | .rentPaying .. => if disallowRentPaying then .rentExempt else .rentPaying lamports dataSize
  | state => state

def postExecAccountRentState (lamports dataSize minBalance : UInt64) (preState : RentState)
    (preBalance : UInt64) (relax : Bool) : RentState :=
  if !relax then accountRentState lamports dataSize minBalance
  else if lamports = 0 then .uninitialized
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
    (accountIndex : UInt16) (relax : Bool) : Except Panic (Except TransactionError Unit) := do
  let minBalance ← minimumBalance rent dataSize
  let preState := preExecAccountRentState preBalance dataSize minBalance relax
  let postState := postExecAccountRentState postBalance dataSize minBalance preState preBalance relax
  if transitionAllowed preState postState then return .ok ()
  return .error (.insufficientFundsForRent accountIndex.toUInt8)

/-! ## `svm/src/account_loader.rs` -/

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
  let postBalance := preBalance - fee
  modify ({ · with account.lamports := postBalance })
  checkStaticAccountRentStateTransition preBalance postBalance (← getAccount).data.length.toUInt64 rent
    payerIndex relax

end ValidateFeePayer.Spec
