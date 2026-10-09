import X86.F64
import X86.Bytes

/-!
`validate_fee_payer` (`svm/src/account_loader.rs` at the pinned Agave commit)
and what it calls, as Lean functions over the values its arguments point to.
Names follow the Rust source; `Option` is Rust's `Option`. A Rust panic and a
returned `TransactionError` are the two kinds of `Error`. `chargeFeePayer` is
the function without its error metrics, which `validateFeePayer` updates from
the error; the `&mut` account is returned on success only, since after an
error the caller drops it.

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

inductive Error where
  | panic (p : Panic)
  | tx (e : TransactionError)
  deriving DecidableEq, Repr

instance : MonadLift (Except Panic) (Except Error) := ⟨Except.mapError .panic⟩

instance : Alternative (Except Panic) where
  failure := .error .maximumPermittedDataLengthExceeded
  orElse
    | .ok x, _ => .ok x
    | .error _, y => y ()

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

/-- `Rent::minimum_balance`: `try_minimum_balance` and its `expect`.

`exemption_threshold` is a deprecated field ("empty space"), kept only for
the 17-byte `Rent` layout: SIMD-0194 (feature `rent6iVy6PDoViPBeJ6k5EJQrkj62h7DPyLbWGHwjrC`)
folded it into `lamports_per_byte` (3480 × 2.0 → 6960 × 1.0; Agave
`runtime/src/rent_collector.rs:49`, `bank.rs:6337`, `bank.rs:6412`). Per SIMD-0607 it
is 1.0 on mainnet-beta since epoch 943 and was 2.0 before, so in production
only the integer paths run; the `f64` path needs a non-standard genesis, the
`[0; 8]` snapshot default, or a malformed sysvar. -/
def minimumBalance (rent : Rent) (dataLength : UInt64) : Except Panic UInt64 := do
  guard (dataLength ≤ maxPermittedDataLength)
  let bytes := accountStorageOverhead + dataLength
  if rent.exemptionThreshold = simd0194ExemptionThreshold then
    guard (rent.lamportsPerByte ≤ simd0194MaxLamportsPerByte)
    return bytes * rent.lamportsPerByte
  else if rent.exemptionThreshold = currentExemptionThreshold then
    guard (rent.lamportsPerByte ≤ currentMaxLamportsPerByte)
    return 2 * bytes * rent.lamportsPerByte
  return f64ToU64 (F64.mul (u64ToF64 (bytes * rent.lamportsPerByte)) rent.exemptionThreshold).1

/-! ## `solana-nonce-account` 5.0.0 -/

inductive SystemAccountKind where
  | system | nonce
  deriving DecidableEq, Repr

/-- `nonce::state::State::size()`. -/
def nonceStateSize : Nat := 80

def systemAccountKind (account : Account) : Option SystemAccountKind := do
  guard (account.owner = systemProgramId)
  if account.data = [] then return .system
  guard (account.data.length = nonceStateSize)
  let versionsTag := ofLittleEndian (account.data.take 4)
  let stateTag := ofLittleEndian ((account.data.drop 4).take 4)
  guard ((versionsTag = 0 ∨ versionsTag = 1) ∧ stateTag = 1)
  return .nonce

/-! ## `svm/src/account_loader.rs` -/

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
  let rentExemptBalance ← minimumBalance rent account.data.length.toUInt64
  -- `check_static_account_rent_state_transition` (`svm/src/rent_calculator.rs`) with its
  -- rent states unfolded: the payer only loses lamports, so it may end rent-paying only if it
  -- started so, which `relax` rules out for any nonzero balance; an unchanged balance passes.
  -- `chargeFeePayer_eq_reference` proves this matches the Rust-shaped `Reference`.
  if 0 < postBalance ∧ postBalance < rentExemptBalance ∧
      (rentExemptBalance ≤ account.lamports ∨ relax ∧ fee ≠ 0) then
    throw (.tx (.insufficientFundsForRent payerIndex.toUInt8))
  return { account with lamports := postBalance }

def validateFeePayer (account : Account) (payerIndex : UInt16) (rent : Rent) (fee : UInt64)
    (relax : Bool) (metrics : ErrorMetrics) : Except Error Account × ErrorMetrics :=
  let result := chargeFeePayer account payerIndex rent fee relax
  let metrics' := match result with
    | .error (.tx .accountNotFound) =>
      { metrics with accountNotFound := saturatingIncrement metrics.accountNotFound }
    | .error (.tx .invalidAccountForFee) =>
      { metrics with invalidAccountForFee := saturatingIncrement metrics.invalidAccountForFee }
    | .error (.tx .insufficientFundsForFee) =>
      { metrics with insufficientFunds := saturatingIncrement metrics.insufficientFunds }
    | _ => metrics
  (result, metrics')

end ValidateFeePayer.Spec
