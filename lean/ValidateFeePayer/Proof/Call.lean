import ValidateFeePayer.Contract

/-!
The walk's view of one call: every location and argument as a plain field,
so the walk can name them by variables. `Pre` bundles the theorem's
hypotheses about such a call; `CallPost` and `Call.Frame` are `Post` and
`Frame` over the fields, which `Correctness.lean` turns back into the
contract's form.
-/

namespace ValidateFeePayer.Proof

open X86 Abi Image.Layout

structure Call where
  loadBase : UInt64
  result : UInt64
  account : AccountAt
  errorMetrics : UInt64
  rent : UInt64
  payerIndex : UInt16
  fee : UInt64
  returnAddress : UInt64

def Call.heap (c : Call) : AccountHeap := ⟨c.account.arcInner, c.account.data⟩

def Call.of (loadBase returnAddress : UInt64) (s : State) (heap : AccountHeap) (payerIndex : UInt16)
    (fee : UInt64) : Call :=
  { loadBase, result := (args s).result, account := accountAt s heap, errorMetrics := (args s).errorMetrics,
    rent := (args s).rent, payerIndex, fee, returnAddress }

def Call.exits (c : Call) : Exits := ValidateFeePayer.exits c.loadBase c.returnAddress

/-- The theorem's hypotheses, for the call `c` made in state `s`. -/
structure Pre (c : Call) (account : Spec.Account) (metrics : Spec.ErrorMetrics) (rent : Spec.Rent)
    (relax : Bool) (s : State) : Prop where
  ofState : Call.of c.loadBase c.returnAddress s c.heap c.payerIndex c.fee = c
  called : Called c.loadBase c.returnAddress s
  abi : SysV.Entry s c.returnAddress
  footprint : Footprint c.loadBase s c.heap account.data.length
  encoded : Encoded s c.heap account metrics rent c.payerIndex c.fee relax
  integerThreshold : IntegerThreshold rent

def calleeSaved : List Register :=
  [.base, .framePointer, .r12, .r13, .r14, .r15]

/-- The bytes a call may change, as `writes`. -/
def Call.Written (c : Call) (sp a : UInt64) : Prop :=
  let inside (start : UInt64) (n : Nat) := start.toNat ≤ a.toNat ∧ a.toNat < start.toNat + n
  inside c.result result.size ∨
  inside (off c.account.account account_shared_data.lamports) 8 ∨
  inside (off c.errorMetrics transaction_error_metrics.account_not_found) 8 ∨
  inside (off c.errorMetrics transaction_error_metrics.invalid_account_for_fee) 8 ∨
  inside (off c.errorMetrics transaction_error_metrics.insufficient_funds) 8 ∨
  inside (sp - stackUse.toUInt64) stackUse

def Call.Frame (c : Call) (s s' : State) : Prop :=
  ∀ access a, ¬ c.Written s.stackPointer a → s'.memory.byte access a = s.memory.byte access a

structure CallPost (c : Call) (s : State) (metrics : Spec.ErrorMetrics)
    (result : Except Spec.TransactionError Spec.Account) (s' : State) : Prop where
  resultEncoded : ResultEncodes s'.memory c.result (result.map fun _ => ())
  accountEncoded : ∀ account, result = .ok account → account.Encodes s'.memory c.account
  metricsEncoded : metrics.Encodes s'.memory c.errorMetrics
  returnsResultPointer : s'.register .accumulator = c.result
  stackPopped : s'.stackPointer = s.stackPointer + 8
  calleeSavedKept : ∀ r ∈ calleeSaved, s'.register r = s.register r
  floatControlKept : s'.floatControl &&& ~~~0x3f = s.floatControl &&& ~~~0x3f
  frame : c.Frame s s'

namespace Pre

variable {c : Call} {account : Spec.Account} {metrics : Spec.ErrorMetrics} {rent : Spec.Rent} {relax : Bool}
  {s : State} (pre : Pre c account metrics rent relax s)
include pre

theorem result : (args s).result = c.result := by rw [← pre.ofState]; rfl
theorem accountPtr : (args s).account = c.account.account := by rw [← pre.ofState]; rfl
theorem accountAt_eq : accountAt s c.heap = c.account := by
  conv => rhs; rw [← pre.ofState]
  rfl
theorem errorMetrics : (args s).errorMetrics = c.errorMetrics := by rw [← pre.ofState]; rfl
theorem rentPtr : (args s).rent = c.rent := by rw [← pre.ofState]; rfl

theorem resultRegister : s.register .destinationIndex = c.result := pre.result
theorem accountRegister : s.register .sourceIndex = c.account.account := pre.accountPtr
theorem metricsRegister : s.register .counter = c.errorMetrics := pre.errorMetrics
theorem rentRegister : s.register .r8 = c.rent := pre.rentPtr
theorem feeRegister : s.register .r9 = c.fee := pre.encoded.fee
theorem payerIndexRegister : s.register .data &&& 0xffff = c.payerIndex.toUInt64 := pre.encoded.payerIndex

theorem accountEncoded : account.Encodes s.memory c.account := pre.accountAt_eq ▸ pre.encoded.account
theorem metricsEncoded : metrics.Encodes s.memory c.errorMetrics := pre.errorMetrics ▸ pre.encoded.metrics
theorem rentEncoded : rent.Encodes s.memory c.rent := pre.rentPtr ▸ pre.encoded.rent

end Pre

end ValidateFeePayer.Proof
