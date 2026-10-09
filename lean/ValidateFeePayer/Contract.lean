import Abi
import ValidateFeePayer.Loader
import ValidateFeePayer.Spec

/-!
The contract of the machine code, over the machine state `s` at the moment
of the call. What the run may assume comes in layers:

1. `Loaded` (in `Loader.lean`): the carved image is in memory. That it can
   be, and that the image itself is sound, is proved apart (`Checks.lean`,
   `DecoderChecks/`).
2. `Called`: control is at the entry, and the stack holds a return address
   outside the image.
3. `Footprint`: the argument registers point at memory the code may read and
   write, no two objects overlap, and none overlaps the image's reserved span.

`PanicsOrReturns` is what the run then does, whatever the values in that
memory. `Encoded` adds which Rust values those are; `MatchesSpec` says the
run does with them what `Spec` does. Names from `X86` (the machine) and
`Abi` (calling conventions, memory blocks) are written qualified; the rest is
this function's.
-/

namespace ValidateFeePayer

open Image.Layout

def off (a : UInt64) (offset : Nat) : UInt64 := a + offset.toUInt64

/-- The argument locations of the call made in `s`. -/
abbrev args (s : X86.State) : Abi.ValidateFeePayerEntry := .of s

/-- The control-flow graph is acyclic, so each of the 239 instructions runs
at most once; one more step reaches the exit. -/
def fuel : Nat := 240

/-- Run the code from the state `s` of the call, until it returns to
`returnAddress` or panics. -/
def invoke (loadBase returnAddress : UInt64) (s : X86.State) : X86.Outcome :=
  X86.run (exits loadBase returnAddress) fuel s

/-! ## Layer 2: the call -/

/-- `s` is the state right after a `call` into the image at `loadBase` that
will return to `returnAddress`. -/
structure Called (loadBase returnAddress : UInt64) (s : X86.State) : Prop where
  atEntry : s.rip = entryAddress loadBase
  abi : Abi.SysV.Entry s returnAddress
  -- Otherwise the code could "return" by jumping into itself.
  returnOutsideImage : ∀ r ∈ Image.regions, ¬ (r.block loadBase).Contains returnAddress
  -- Reaching the panic entry would count as a return; a caller's return
  -- address is in its own code, never at `expect_failed`.
  returnNotPanic : returnAddress ≠ panicAddress loadBase

/-! ## Layer 3: the footprint -/

/-- The deepest the code goes below the entry stack pointer: five pushes,
`sub rsp, 0x10`, the call into the rent check, its three pushes and the call
into the panic (`Tests.lean` checks one byte less faults). -/
def stackUse : Nat := 96

/-- The two heap allocations behind `&mut AccountSharedData`: the `Arc`'s
block holding the data `Vec`, and the `Vec`'s buffer. Their addresses are
pointers stored in memory, which `Footprint` pins down. -/
structure AccountHeap where
  arcInner : UInt64
  data : UInt64

/-- Every object the code touches, and the image's reserved span. -/
def objects (loadBase : UInt64) (s : X86.State) (heap : AccountHeap) (dataLength : Nat) : List Abi.Block :=
  let a := args s
  [⟨a.result, result.size⟩,
   ⟨a.account, account_shared_data.size⟩,
   ⟨heap.arcInner, account_shared_data.arc_inner.data_len + 8⟩,
   ⟨heap.data, dataLength⟩,
   ⟨a.errorMetrics, transaction_error_metrics.size⟩,
   ⟨a.rent, rent.size⟩,
   -- The code's frame, the return address and the stack argument's slot.
   ⟨s.rsp - stackUse.toUInt64, stackUse + 16⟩,
   reservedSpan loadBase]

/-- The bytes the code may change: the result, the account's lamports, the
three counters it may increment, and its frame. -/
def writes (s : X86.State) : List Abi.Block :=
  let a := args s
  [⟨a.result, result.size⟩,
   ⟨off a.account account_shared_data.lamports, 8⟩,
   ⟨off a.errorMetrics transaction_error_metrics.account_not_found, 8⟩,
   ⟨off a.errorMetrics transaction_error_metrics.invalid_account_for_fee, 8⟩,
   ⟨off a.errorMetrics transaction_error_metrics.insufficient_funds, 8⟩,
   ⟨s.rsp - stackUse.toUInt64, stackUse⟩]

/-- The bytes the code reads and does not write, other than the pointers
and the length `Footprint` names. -/
def reads (s : X86.State) (heap : AccountHeap) (dataLength : Nat) : List Abi.Block :=
  let a := args s
  [⟨off a.account account_shared_data.owner, 32⟩,
   ⟨heap.data, dataLength⟩,
   ⟨off a.rent rent.lamports_per_byte, 8⟩,
   ⟨off a.rent rent.exemption_threshold, 8⟩]

/-- What the code needs of the memory it is called on to run without
faulting. `heap` and `dataLength` are the account's pointers and data length
as stored in memory. -/
structure Footprint (loadBase : UInt64) (s : X86.State) (heap : AccountHeap) (dataLength : Nat) : Prop where
  arcInner : Abi.PtrAt s.memory (args s).account account_shared_data.data_arc heap.arcInner
  data : Abi.PtrAt s.memory heap.arcInner account_shared_data.arc_inner.data_ptr heap.data
  length : s.memory.Holds .bits64 (off heap.arcInner account_shared_data.arc_inner.data_len)
    dataLength.toUInt64
  readable : ∀ b ∈ reads s heap dataLength, b.Readable s.memory
  writable : ∀ b ∈ writes s, b.Writable s.memory
  -- Rust's validity invariant for `bool`; a caller in Rust cannot break it.
  relaxIsBool : s.memory.Holds .bits8 (args s).relax 0 ∨ s.memory.Holds .bits8 (args s).relax 1
  -- `&mut` arguments do not alias in Rust; this is that, plus no overlap
  -- with the stack or the binary.
  separate : Abi.Block.Separate (objects loadBase s heap dataLength)
  noWrap : ∀ b ∈ objects loadBase s heap dataLength, b.NoWrap

/-- `s'` differs from the state `s` of the call only in bytes the code may write. -/
def CallerMemoryUntouched (s s' : X86.State) : Prop :=
  Abi.UnchangedOutside (writes s) s.memory s'.memory

/-- The address of the rent's exemption threshold, an `f64`. -/
def exemptionThresholdAddress (s : X86.State) : UInt64 := off (args s).rent rent.exemption_threshold

/-- What the run from the call made in `s` does: it panics, or it returns to
`returnAddress` as the ABI requires, with the result pointer in `rax`. It
never faults, jumps outside the code or runs out of fuel. Either way memory
outside what the code may write is untouched. -/
def PanicsOrReturns (returnAddress : UInt64) (s : X86.State) : X86.Outcome → Prop
  | .panicked s' => CallerMemoryUntouched s s'
  | .returned s' =>
    Abi.SysV.Returned s returnAddress s' ∧ Abi.SysV.ReturnsIndirectly s s' ∧ CallerMemoryUntouched s s'
  | _ => False

/-! ## The Rust values

`Encodes m p x` says the bytes at `p` in memory `m` are the in-memory
representation of the Lean value `x`, with the layouts measured from the
build (`Image.Layout`). Each covers exactly the bytes the code reads or
writes; the rest of each object is in the frame. -/

/-- The three allocations behind `&mut AccountSharedData`. -/
structure AccountAt where
  account : UInt64
  arcInner : UInt64
  data : UInt64

def accountAt (s : X86.State) (heap : AccountHeap) : AccountAt := ⟨(args s).account, heap.arcInner, heap.data⟩

def Spec.Account.Encodes (m : X86.Memory) (p : AccountAt) (x : Spec.Account) : Prop :=
  Abi.PtrAt m p.account account_shared_data.data_arc p.arcInner ∧
  m.Holds .bits64 (off p.account account_shared_data.lamports) x.lamports ∧
  m.HoldsBytes (off p.account account_shared_data.owner) x.owner.toList ∧
  Abi.PtrAt m p.arcInner account_shared_data.arc_inner.data_ptr p.data ∧
  m.Holds .bits64 (off p.arcInner account_shared_data.arc_inner.data_len) x.data.length.toUInt64 ∧
  m.HoldsBytes p.data x.data

def Spec.Rent.Encodes (m : X86.Memory) (p : UInt64) (x : Spec.Rent) : Prop :=
  m.Holds .bits64 (off p rent.lamports_per_byte) x.lamportsPerByte ∧
  m.Holds .bits64 (off p rent.exemption_threshold) x.exemptionThreshold

def Spec.ErrorMetrics.Encodes (m : X86.Memory) (p : UInt64) (x : Spec.ErrorMetrics) : Prop :=
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
def ResultEncodes (m : X86.Memory) (p : UInt64) (x : Except Spec.TransactionError Unit) : Prop :=
  m.Holds .bits32 p (resultTag x).toUInt64 ∧
  match x with
  | .error (.insufficientFundsForRent i) => m.Holds .bits8 (off p result.account_index) i.toUInt64
  | _ => True

/-- A `bool` must be 0 or 1 (Rust's validity invariant); the code relies on it. -/
def BoolEncodes (m : X86.Memory) (p : UInt64) (x : Bool) : Prop :=
  m.Holds .bits8 p (if x then 1 else 0)

/-- The arguments of `validate_fee_payer`, as Lean values. -/
structure Args where
  account : Spec.Account
  payerIndex : UInt16
  rent : Spec.Rent
  fee : UInt64
  relax : Bool
  metrics : Spec.ErrorMetrics

def Args.spec (x : Args) : Except Spec.Error Spec.Account × Spec.ErrorMetrics :=
  Spec.validateFeePayer x.account x.payerIndex x.rent x.fee x.relax x.metrics

/-- The state `s` of the call holds the arguments `x` where the ABI puts them. -/
structure Encoded (s : X86.State) (heap : AccountHeap) (x : Args) : Prop where
  account : x.account.Encodes s.memory (accountAt s heap)
  -- Only the low 16 bits are the `u16`; the rest is whatever the caller left.
  payerIndex : (args s).payerIndex &&& 0xffff = x.payerIndex.toUInt64
  rent : x.rent.Encodes s.memory (args s).rent
  fee : (args s).fee = x.fee
  relax : BoolEncodes s.memory (args s).relax x.relax
  metrics : x.metrics.Encodes s.memory (args s).errorMetrics

/-- After a normal return to `s'` from the call made in `s`, for which the
spec gave `result` and left `metrics`, memory holds them. After an error the
account is only bound by `CallerMemoryUntouched`: the code may have written
the lamports already. -/
structure ResultEncoded (s : X86.State) (heap : AccountHeap) (metrics : Spec.ErrorMetrics)
    (result : Except Spec.TransactionError Spec.Account) (s' : X86.State) : Prop where
  resultEncoded : ResultEncodes s'.memory (args s).result (result.map fun _ => ())
  accountEncoded : ∀ account, result = .ok account → account.Encodes s'.memory (accountAt s heap)
  metricsEncoded : metrics.Encodes s'.memory (args s).errorMetrics

/-- The run from the call made in `s` does what the spec answered (`spec`):
it panics exactly when the spec panics, and otherwise returns what the spec
returns. -/
def MatchesSpec (s : X86.State) (heap : AccountHeap)
    (spec : Except Spec.Error Spec.Account × Spec.ErrorMetrics) : X86.Outcome → Prop
  | .panicked _ => ∃ p, spec.1 = .error (.panic p)
  | .returned s' => ∃ result, spec.1 = result.mapError .tx ∧ ResultEncoded s heap spec.2 result s'
  | _ => False

end ValidateFeePayer
