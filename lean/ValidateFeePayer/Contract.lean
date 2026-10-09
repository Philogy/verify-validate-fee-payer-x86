import Abi
import ValidateFeePayer.Loader
import ValidateFeePayer.Spec

/-!
The contract of the machine code, in three layers:

1. `Called`: the image is loaded (`Loaded`) and the state is a call into it.
2. `Footprint`: the memory the code touches is mapped as it needs, no two
   objects overlap and none wraps around; `Frame` says it leaves the rest alone.
3. `Encoded`: the bytes at those places are the Rust values `Spec` takes;
   `Post` says they are the values it gives back.

Where the arguments are comes from the ABI: `Abi.SysV` for what every call
shares, `Abi.ValidateFeePayerEntry` for this function's observed layout.
-/

namespace ValidateFeePayer

open X86 Abi Image.Layout

def off (a : UInt64) (offset : Nat) : UInt64 := a + offset.toUInt64

/-- The argument locations at entry state `s`. -/
abbrev args (s : State) : ValidateFeePayerEntry := .of s

/-! ## Layer 1: a call into the loaded image -/

/-- `s` calls the image loaded at `loadBase`, to return to `returnAddress`. -/
structure Called (loadBase returnAddress : UInt64) (s : State) : Prop where
  loaded : Loaded loadBase s.memory
  atEntry : s.instructionPointer = entryAddress loadBase
  -- Otherwise the code could "return" by jumping into itself.
  returnOutsideImage : ∀ mp ∈ imageMappings loadBase, ¬ mp.Contains returnAddress
  -- Reaching the panic entry would count as a return; a caller's return
  -- address is in its own code, never at `expect_failed`.
  returnNotPanic : returnAddress ≠ panicAddress loadBase

/-! ## Layer 2: the footprint -/

/-- The deepest the code goes below the entry stack pointer: five pushes,
`sub rsp, 0x10`, the call into the rent check, its three pushes and the call
into the panic (`Tests.lean` checks one byte less faults). -/
def stackUse : Nat := 96

/-- The two heap allocations behind `&mut AccountSharedData`: the `Arc`'s
block holding the data `Vec`, and the `Vec`'s buffer. Their addresses are
pointers stored in memory (`Spec.Account.Encodes` follows them). -/
structure AccountHeap where
  arcInner : UInt64
  data : UInt64

/-- Every object the code touches, and the image's reserved span. -/
def objects (loadBase : UInt64) (s : State) (heap : AccountHeap) (dataLength : Nat) : List Block :=
  let a := args s
  [⟨a.result, result.size⟩,
   ⟨a.account, account_shared_data.size⟩,
   ⟨heap.arcInner, account_shared_data.arc_inner.data_len + 8⟩,
   ⟨heap.data, dataLength⟩,
   ⟨a.errorMetrics, transaction_error_metrics.size⟩,
   ⟨a.rent, rent.size⟩,
   -- The code's frame, the return address and the stack argument's slot.
   ⟨s.stackPointer - stackUse.toUInt64, stackUse + 16⟩,
   reservedSpan loadBase]

/-- The bytes the code may change: the result, the account's lamports, the
three counters it may increment, and its frame. -/
def writes (s : State) : List Block :=
  let a := args s
  [⟨a.result, result.size⟩,
   ⟨off a.account account_shared_data.lamports, 8⟩,
   ⟨off a.errorMetrics transaction_error_metrics.account_not_found, 8⟩,
   ⟨off a.errorMetrics transaction_error_metrics.invalid_account_for_fee, 8⟩,
   ⟨off a.errorMetrics transaction_error_metrics.insufficient_funds, 8⟩,
   ⟨s.stackPointer - stackUse.toUInt64, stackUse⟩]

structure Footprint (loadBase : UInt64) (s : State) (heap : AccountHeap) (dataLength : Nat) : Prop where
  -- `&mut` arguments do not alias in Rust; this is that, plus no overlap
  -- with the stack or the binary.
  separate : Block.Separate (objects loadBase s heap dataLength)
  noWrap : ∀ b ∈ objects loadBase s heap dataLength, b.NoWrap
  writable : ∀ b ∈ writes s, b.Writable s.memory

/-- `s'` differs from the entry state `s` only in bytes the code may write. -/
def Frame (s s' : State) : Prop := UnchangedOutside (writes s) s.memory s'.memory

/-! ## Layer 3: the Rust values

`Encodes m p x` says the bytes at `p` in memory `m` are the in-memory
representation of the Lean value `x`, with the layouts measured from the
build (`Image.Layout`). Each covers exactly the bytes the code reads or
writes; the rest of each object is in the frame. -/

/-- The three allocations behind `&mut AccountSharedData`. -/
structure AccountAt where
  account : UInt64
  arcInner : UInt64
  data : UInt64

def accountAt (s : State) (heap : AccountHeap) : AccountAt := ⟨(args s).account, heap.arcInner, heap.data⟩

def Spec.Account.Encodes (m : Memory) (p : AccountAt) (x : Spec.Account) : Prop :=
  PtrAt m p.account account_shared_data.data_arc p.arcInner ∧
  m.Holds .bits64 (off p.account account_shared_data.lamports) x.lamports ∧
  m.HoldsBytes (off p.account account_shared_data.owner) x.owner.toList ∧
  PtrAt m p.arcInner account_shared_data.arc_inner.data_ptr p.data ∧
  m.Holds .bits64 (off p.arcInner account_shared_data.arc_inner.data_len) x.data.length.toUInt64 ∧
  m.HoldsBytes p.data x.data

def Spec.Rent.Encodes (m : Memory) (p : UInt64) (x : Spec.Rent) : Prop :=
  m.Holds .bits64 (off p rent.lamports_per_byte) x.lamportsPerByte ∧
  m.Holds .bits64 (off p rent.exemption_threshold) x.exemptionThreshold

def Spec.ErrorMetrics.Encodes (m : Memory) (p : UInt64) (x : Spec.ErrorMetrics) : Prop :=
  m.Holds .bits64 (off p transaction_error_metrics.account_not_found) x.accountNotFound ∧
  m.Holds .bits64 (off p transaction_error_metrics.invalid_account_for_fee) x.invalidAccountForFee ∧
  m.Holds .bits64 (off p transaction_error_metrics.insufficient_funds) x.insufficientFunds

def resultTag : Except Spec.TransactionError Unit → Nat
  | .ok () => result.tags.Ok
  | .error .accountNotFound => result.tags.AccountNotFound
  | .error .invalidAccountForFee => result.tags.InvalidAccountForFee
  | .error .insufficientFundsForFee => result.tags.InsufficientFundsForFee
  | .error (.insufficientFundsForRent _) => result.tags.InsufficientFundsForRent

/-- `Result<(), TransactionError>` is 12 bytes, but only the 4-byte tag and,
for `InsufficientFundsForRent`, its `u8` account index are defined: Rust
promises nothing about the other bytes (padding and other variants'
payloads), and the code does not write them. -/
def ResultEncodes (m : Memory) (p : UInt64) (x : Except Spec.TransactionError Unit) : Prop :=
  m.Holds .bits32 p (resultTag x).toUInt64 ∧
  match x with
  | .error (.insufficientFundsForRent i) => m.Holds .bits8 (off p result.account_index) i.toUInt64
  | _ => True

/-- A `bool` must be 0 or 1 (Rust's validity invariant); the code relies on it. -/
def BoolEncodes (m : Memory) (p : UInt64) (x : Bool) : Prop :=
  m.Holds .bits8 p (if x then 1 else 0)

/-- The entry state `s` holds the arguments `account`, `payerIndex`, `rent`,
`fee`, `relax` and `metrics` where the ABI puts them. -/
structure Encoded (s : State) (heap : AccountHeap) (account : Spec.Account) (metrics : Spec.ErrorMetrics)
    (rent : Spec.Rent) (payerIndex : UInt16) (fee : UInt64) (relax : Bool) : Prop where
  account : account.Encodes s.memory (accountAt s heap)
  -- Only the low 16 bits are the `u16`; the rest is whatever the caller left.
  payerIndex : (args s).payerIndex &&& 0xffff = payerIndex.toUInt64
  rent : rent.Encodes s.memory (args s).rent
  fee : (args s).fee = fee
  relax : BoolEncodes s.memory (args s).relax relax
  metrics : metrics.Encodes s.memory (args s).errorMetrics

/-- Only the two exemption thresholds that take an integer path in
`Rent::minimum_balance` are covered; the `f64`/`cvttsd2si` path (the SSE
blocks at `0x27f369b` and `0x27f384b`) is excluded, so the `F64` model is
not exercised. `0x3ff0…` is `1.0`, `0x4000…` is `2.0`. -/
def IntegerThreshold (rent : Spec.Rent) : Prop :=
  rent.exemptionThreshold = Spec.simd0194ExemptionThreshold ∨
    rent.exemptionThreshold = Spec.currentExemptionThreshold

/-- The state `s'` after a normal return from entry state `s`, for which the
spec gave `result` and left `metrics`. After an error the account is only
bound by the frame: the code may have written the lamports already. -/
structure Post (s : State) (heap : AccountHeap) (metrics : Spec.ErrorMetrics)
    (result : Except Spec.TransactionError Spec.Account) (s' : State) : Prop where
  returned : SysV.Returned s s'
  -- The hidden result pointer comes back in `rax`.
  returnsResultPointer : s'.register .accumulator = (args s).result
  frame : Frame s s'
  resultEncoded : ResultEncodes s'.memory (args s).result (result.map fun _ => ())
  accountEncoded : ∀ account, result = .ok account → account.Encodes s'.memory (accountAt s heap)
  metricsEncoded : metrics.Encodes s'.memory (args s).errorMetrics

/-- The control-flow graph is acyclic, so each of the 239 instructions runs
at most once; one more step reaches the exit. -/
def fuel : Nat := 240

end ValidateFeePayer
