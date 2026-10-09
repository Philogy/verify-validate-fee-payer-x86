import X86.Machine
import ValidateFeePayer.Loader
import ValidateFeePayer.Spec

/-!
The contract of the machine code: which states it starts in (`Pre`), and what
it must leave behind (`Post`), stated against the pure functions of `Spec`.

`Encodes m p x` says the bytes at `p` in memory `m` are the in-memory
representation of the Lean value `x`, with the layouts measured from the
build (`Image.Layout`). Each covers exactly the bytes the code reads or
writes; the rest of each object is in the frame.
-/

namespace ValidateFeePayer

open X86 Image.Layout

def _root_.X86.Memory.Holds (m : Memory) (w : Width) (a v : UInt64) : Prop := m.read w a = .ok v

def _root_.X86.Memory.HoldsBytes (m : Memory) (a : UInt64) (bs : List UInt8) : Prop :=
  m.bytes .read a bs.length = .ok bs

def _root_.X86.Memory.Writable (m : Memory) (a : UInt64) (n : Nat) : Prop := ∃ bs, m.bytes .write a n = .ok bs

def off (a : UInt64) (offset : Nat) : UInt64 := a + offset.toUInt64

/-- The three allocations behind `&mut AccountSharedData`: the struct, the
`Arc`'s heap block holding the data `Vec`, and the `Vec`'s buffer. -/
structure AccountAt where
  account : UInt64
  arcInner : UInt64
  data : UInt64

def Spec.Account.Encodes (m : Memory) (p : AccountAt) (x : Spec.Account) : Prop :=
  m.Holds .bytes8 (off p.account account_shared_data.data_arc) p.arcInner ∧
  m.Holds .bytes8 (off p.account account_shared_data.lamports) x.lamports ∧
  m.HoldsBytes (off p.account account_shared_data.owner) x.owner.toList ∧
  m.Holds .bytes8 (off p.arcInner account_shared_data.arc_inner.data_ptr) p.data ∧
  m.Holds .bytes8 (off p.arcInner account_shared_data.arc_inner.data_len) x.data.length.toUInt64 ∧
  m.HoldsBytes p.data x.data

def Spec.Rent.Encodes (m : Memory) (p : UInt64) (x : Spec.Rent) : Prop :=
  m.Holds .bytes8 (off p rent.lamports_per_byte) x.lamportsPerByte ∧
  m.Holds .bytes8 (off p rent.exemption_threshold) x.exemptionThreshold

def Spec.ErrorMetrics.Encodes (m : Memory) (p : UInt64) (x : Spec.ErrorMetrics) : Prop :=
  m.Holds .bytes8 (off p transaction_error_metrics.account_not_found) x.accountNotFound ∧
  m.Holds .bytes8 (off p transaction_error_metrics.invalid_account_for_fee) x.invalidAccountForFee ∧
  m.Holds .bytes8 (off p transaction_error_metrics.insufficient_funds) x.insufficientFunds

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
  m.Holds .bytes4 p (resultTag x).toUInt64 ∧
  match x with
  | .error (.insufficientFundsForRent i) => m.Holds .bytes1 (off p result.account_index) i.toUInt64
  | _ => True

/-- A `bool` must be 0 or 1 (Rust's validity invariant); the code relies on it. -/
def BoolEncodes (m : Memory) (p : UInt64) (x : Bool) : Prop :=
  m.Holds .bytes1 p (if x then 1 else 0)

/-- Everything about one call that is not a Lean value of the Rust program:
where things are. -/
structure Call where
  loadBase : UInt64
  result : UInt64
  account : AccountAt
  errorMetrics : UInt64
  rent : UInt64
  payerIndex : UInt16
  fee : UInt64
  returnAddress : UInt64

def Spec.MutRefs.Encodes (m : Memory) (c : Call) (x : Spec.MutRefs) : Prop :=
  x.account.Encodes m c.account ∧ x.metrics.Encodes m c.errorMetrics

def Call.exits (c : Call) : Exits :=
  { returnAddress := c.returnAddress, panicAt := panicAddress c.loadBase }

/-- The deepest the code goes below the entry stack pointer: five pushes,
`sub rsp, 0x10`, the call into the rent check, its three pushes and the call
into the panic (`Tests.lean` checks one byte less faults). -/
def stackUse : Nat := 96

def interval (a : UInt64) (n : Nat) : Nat × Nat := (a.toNat, a.toNat + n)

def IntervalsDisjoint (l : List (Nat × Nat)) : Prop :=
  l.Pairwise fun (a, b) (c, d) => b ≤ c ∨ d ≤ a

/-- Every object the code touches, as `[start, end)`. -/
def Call.footprint (c : Call) (sp : UInt64) (dataLength : Nat) : List (Nat × Nat) :=
  [interval c.result result.size,
   interval c.account.account account_shared_data.size,
   interval c.account.arcInner (account_shared_data.arc_inner.data_len + 8),
   interval c.account.data dataLength,
   interval c.errorMetrics transaction_error_metrics.size,
   interval c.rent rent.size,
   interval (sp - stackUse.toUInt64) (stackUse + 16)] ++
  (imageMappings c.loadBase).map fun mp => (mp.base.toNat, mp.endAddress)

/-- The entry state of a call `c` with argument values `refs`, `rent` and
`relax`, as the System V ABI passes them: the result pointer in
`rdi`, then `rsi rdx rcx r8 r9`, the `bool` above the return address. -/
structure Pre (c : Call) (refs : Spec.MutRefs) (rent : Spec.Rent) (relax : Bool) (s : State) :
    Prop where
  image : ∃ rest, s.memory = ⟨imageMappings c.loadBase ++ rest⟩
  validBase : ValidLoadBase c.loadBase
  -- The `f64` constants are read with SSE instructions that need 16-byte
  -- alignment; the loader's bases are page-aligned anyway.
  alignedBase : c.loadBase % 16 = 0
  -- Otherwise the code could "return" by jumping into itself.
  returnOutsideImage : ∀ mp ∈ imageMappings c.loadBase, ¬ mp.Contains c.returnAddress
  entry : s.instructionPointer = entryAddress c.loadBase
  resultRegister : s.register .destinationIndex = c.result
  accountRegister : s.register .sourceIndex = c.account.account
  -- Only the low 16 bits of `rdx` are the `u16`; the rest is whatever the caller left.
  payerIndexRegister : s.register .data &&& 0xffff = c.payerIndex.toUInt64
  metricsRegister : s.register .counter = c.errorMetrics
  rentRegister : s.register .r8 = c.rent
  feeRegister : s.register .r9 = c.fee
  returnAddress : s.memory.Holds .bytes8 s.stackPointer c.returnAddress
  relaxArgument : BoolEncodes s.memory (s.stackPointer + 8) relax
  -- SysV: `rsp ≡ 0 (mod 16)` before the `call`, which pushed 8 bytes.
  stackAligned : s.stackPointer % 16 = 8
  stackFree : s.memory.Writable (s.stackPointer - stackUse.toUInt64) stackUse
  flags : s.flags = .undefined
  floatControl : s.floatControl &&& ~~~0x3f = defaultFloatControl
  -- Only the two exemption thresholds that take an integer path in
  -- `Rent::minimum_balance` are covered; the `f64`/`cvttsd2si` path (the SSE
  -- blocks at `0x27f369b` and `0x27f384b`) is excluded, so the `F64` model is
  -- not exercised. `0x3ff0…` is `1.0`, `0x4000…` is `2.0`.
  integerThreshold : rent.exemptionThreshold = Spec.simd0194ExemptionThreshold ∨
    rent.exemptionThreshold = Spec.currentExemptionThreshold
  refsEncoded : refs.Encodes s.memory c
  rentEncoded : rent.Encodes s.memory c.rent
  resultWritable : s.memory.Writable c.result result.size
  lamportsWritable : s.memory.Writable (off c.account.account account_shared_data.lamports) 8
  metricsWritable : s.memory.Writable c.errorMetrics transaction_error_metrics.size
  -- `&mut` arguments do not alias in Rust; this is that, plus no overlap
  -- with the stack or the code.
  disjoint : IntervalsDisjoint (c.footprint s.stackPointer refs.account.data.length)
  noWrap : ∀ i ∈ c.footprint s.stackPointer refs.account.data.length, i.2 ≤ 2 ^ 64

def calleeSaved : List Register :=
  [.base, .framePointer, .r12, .r13, .r14, .r15]

/-- The bytes a call may change: the result, the account's lamports, the
three counters, and the stack below the entry stack pointer. -/
def Call.Written (c : Call) (sp a : UInt64) : Prop :=
  let inside (start : UInt64) (n : Nat) := start.toNat ≤ a.toNat ∧ a.toNat < start.toNat + n
  inside c.result result.size ∨
  inside (off c.account.account account_shared_data.lamports) 8 ∨
  inside (off c.errorMetrics transaction_error_metrics.account_not_found) 8 ∨
  inside (off c.errorMetrics transaction_error_metrics.invalid_account_for_fee) 8 ∨
  inside (off c.errorMetrics transaction_error_metrics.insufficient_funds) 8 ∨
  inside (sp - stackUse.toUInt64) stackUse

/-- The state `s'` after a normal return from entry state `s`. -/
structure Post (c : Call) (s : State) (result : Except Spec.TransactionError Unit)
    (refs : Spec.MutRefs) (s' : State) : Prop where
  resultEncoded : ResultEncodes s'.memory c.result result
  refsEncoded : refs.Encodes s'.memory c
  returnsResultPointer : s'.register .accumulator = c.result
  stackPopped : s'.stackPointer = s.stackPointer + 8
  calleeSavedKept : ∀ r ∈ calleeSaved, s'.register r = s.register r
  frame : ∀ access a, ¬ c.Written s.stackPointer a → s'.memory.byte access a = s.memory.byte access a

/-- The code has no loops (its only backward branch goes to the epilogue), so
each of its 239 instructions runs at most once; one more step reaches the
exit. -/
def fuel : Nat := 240

end ValidateFeePayer
