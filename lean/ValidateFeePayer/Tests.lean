import ValidateFeePayer.Contract
import ValidateFeePayer.Checks
import X86.MemoryFacts

/-!
Runs of the machine on concrete inputs, checked at build time. Each case
runs the code and `Spec.validateFeePayer` on the same values and compares
the outcome, the result, the account and the counters. These test the model
and the spec against each other; they are not proofs.
-/

namespace ValidateFeePayer.Tests

open X86 Abi Image.Layout

def obj (base : UInt64) (size : Nat) (fields : List (Nat × List UInt8)) (m : Memory) : Memory :=
  let bytes := fields.foldl (fun (bs : Array UInt8) (offset, v) =>
    v.zipIdx.foldl (fun bs (b, i) => bs.set! (offset + i) b) bs) (Array.replicate size 0)
  m.map base ⟨bytes⟩ .readWrite

def u64 (v : UInt64) : List UInt8 := littleEndianBytes 8 v
def u32 (v : UInt64) : List UInt8 := littleEndianBytes 4 v

structure Case where
  lamports : UInt64
  owner : List UInt8 := List.replicate 32 0
  data : List UInt8 := []
  lamportsPerByte : UInt64 := 3480
  /-- The `f64`'s bits. -/
  threshold : UInt64 := Spec.currentExemptionThreshold
  fee : UInt64
  relax : Bool := false
  loadBase : UInt64 := 0x555555554000
  free : Nat := 4096
  counters : UInt64 := 0
  returnAddress : UInt64 := 0x400000

def resultPtr : UInt64 := 0x10000
def accountPtr : UInt64 := 0x20000
def heap : AccountHeap := ⟨0x30000, 0x40000⟩
def metricsPtr : UInt64 := 0x50000
def rentPtr : UInt64 := 0x60000
def payerIndex : UInt16 := 7

def Case.exits (c : Case) : Exits := ValidateFeePayer.exits c.loadBase c.returnAddress

def stackTop : UInt64 := 0x7ffffff00000

/-- The state right after the caller's `call` into the image. -/
def Case.state (c : Case) : State :=
  -- SysV: 16-byte aligned before the `call` pushed the return address.
  let sp := stackTop - 72
  let stack (m : Memory) := m.map (sp - c.free.toUInt64)
    ⟨(List.replicate c.free 0xaa ++ u64 c.returnAddress ++ [if c.relax then 1 else 0] ++
      List.replicate 55 0xbb).toArray⟩ .readWrite
  let ctr (offset : Nat) := (offset, u64 c.counters)
  let objects := [
    obj resultPtr 16 [],
    obj accountPtr account_shared_data.size
      [(account_shared_data.data_arc, u64 heap.arcInner),
       (account_shared_data.lamports, u64 c.lamports),
       (account_shared_data.owner, c.owner)],
    obj heap.arcInner 0x28
      [(account_shared_data.arc_inner.data_ptr, u64 heap.data),
       (account_shared_data.arc_inner.data_len, u64 c.data.length.toUInt64)],
    obj heap.data (max c.data.length 1) [(0, c.data)],
    obj metricsPtr transaction_error_metrics.size
      [ctr transaction_error_metrics.account_not_found,
       ctr transaction_error_metrics.invalid_account_for_fee,
       ctr transaction_error_metrics.insufficient_funds],
    obj rentPtr rent.size
      [(rent.lamports_per_byte, u64 c.lamportsPerByte),
       (rent.exemption_threshold, u64 c.threshold)]]
  let registers := (Vector.replicate 16 (0x1234567890abcdef : UInt64))
    |>.set Register.rdi.index resultPtr
    |>.set Register.rsi.index accountPtr
    |>.set Register.rdx.index (0x1234567890ab0000 ||| payerIndex.toUInt64)
    |>.set Register.rcx.index metricsPtr
    |>.set Register.r8.index rentPtr
    |>.set Register.r9.index c.fee
    |>.set Register.rsp.index sp
  -- Defined flags, as on a real CPU: the code writes every flag it reads.
  { rip := entryAddress c.loadBase, registers, rflags := ⟨some true, some false, some true, some false, some true, some false⟩,
    xmm := Vector.replicate 16 0, mxcsr := defaultMxcsr,
    memory := load c.loadBase (stack (objects.foldl (fun m o => o m) .empty)) }

def Case.account (c : Case) : Spec.Account :=
  { lamports := c.lamports, owner := Vector.ofFn fun i => c.owner.getD i 0, data := c.data }

def Case.run (c : Case) : Outcome := invoke c.loadBase c.returnAddress c.state

def Case.steps (c : Case) : Nat := go fuel c.state 0
where
  go : Nat → State → Nat → Nat
    | 0, _, n => n
    | k + 1, s, n => match step c.exits s with
      | .running s' => go k s' (n + 1)
      | _ => n + 1

def read (s : State) (w : OperandSize) (a : UInt64) : Option UInt64 := (s.memory.read w a).toOption

def Case.metrics (c : Case) : Spec.ErrorMetrics := ⟨c.counters, c.counters, c.counters⟩

def Case.rent (c : Case) : Spec.Rent := ⟨c.lamportsPerByte, c.threshold⟩

def Case.expected (c : Case) : Except Spec.Error Spec.Account × Spec.ErrorMetrics :=
  Spec.validateFeePayer c.account payerIndex c.rent c.fee c.relax c.metrics

/-- The machine and the spec agree on the outcome and on everything `Post` names. -/
def Case.agrees (c : Case) : Bool :=
  let returned (s : State) (r : Except Spec.TransactionError Spec.Account) (metrics : Spec.ErrorMetrics) :=
    let counter (offset : Nat) := read s .bits64 (off metricsPtr offset)
    read s .bits32 resultPtr == some (resultTag (r.map fun _ => ())).toUInt64 &&
    (match r with
     | .error (.insufficientFundsForRent i) => read s .bits8 (off resultPtr result.account_index) == some i.toUInt64
     | _ => true) &&
    (match r with
     | .ok account => read s .bits64 (off accountPtr account_shared_data.lamports) == some account.lamports
     | .error _ => true) &&
    counter transaction_error_metrics.account_not_found == some metrics.accountNotFound &&
    counter transaction_error_metrics.invalid_account_for_fee == some metrics.invalidAccountForFee &&
    counter transaction_error_metrics.insufficient_funds == some metrics.insufficientFunds &&
    s.register .rax == resultPtr && s.rsp == c.state.rsp + 8 &&
    SysV.calleeSaved.all fun r => s.register r == c.state.register r
  match c.expected, c.run with
  | (.error (.panic _), _), .panicked _ => true
  | (.error (.tx e), metrics), .returned s => returned s (.error e) metrics
  | (.ok account, metrics), .returned s => returned s (.ok account) metrics
  | _, _ => false

def Case.outcome (c : Case) : String :=
  match c.run with
  | .running _ => "running" | .returned _ => "returned" | .panicked _ => "panicked"
  | .badJump s => s!"badJump {s.rip}" | .faulted why _ => s!"faulted {repr why}"

def nonceData : List UInt8 := u32 1 ++ u32 1 ++ List.replicate 72 0
def minBalance (lpb : Nat) (threshold : Float) : UInt64 := (Float.ofNat (208 * lpb) * threshold).toUInt64

def cases : List Case := [
  { lamports := 0, fee := 5 },
  { lamports := 10, fee := 5, owner := List.replicate 32 1 },
  { lamports := 1000, fee := 100 },
  { lamports := 99, fee := 100 },
  { lamports := 1000, fee := 100, counters := 0xffffffffffffffff },
  { lamports := 99, fee := 100, counters := 0xffffffffffffffff },
  { lamports := 10, fee := 5, data := [1, 2, 3] },
  { lamports := 10, fee := 5, data := u32 2 ++ u32 1 ++ List.replicate 72 0 },
  { lamports := 208 * 3480 * 2 + 5000, fee := 5000, data := nonceData },
  { lamports := 208 * 3480 * 2 + 4999, fee := 5000, data := nonceData },
  { lamports := 208 * 3480 + 5000, fee := 5000, data := nonceData, threshold := Spec.simd0194ExemptionThreshold },
  { lamports := minBalance 3480 3.3 + 5000, fee := 5000, data := nonceData, threshold := (3.3 : Float).toBits },
  { lamports := minBalance 3480 3.3 + 4999, fee := 5000, data := nonceData, threshold := (3.3 : Float).toBits },
  { lamports := 900000, fee := 10000 },
  { lamports := 900000, fee := 10000, relax := true },
  { lamports := 900000, fee := 900000 },
  { lamports := 1000, fee := 100, lamportsPerByte := 0xcccc28f646 },
  { lamports := 1000, fee := 100, lamportsPerByte := 1759197129868, threshold := Spec.simd0194ExemptionThreshold },
  { lamports := 10 ^ 18, fee := 100, data := nonceData, lamportsPerByte := 0xcccc28f646 },
  { lamports := 1000, fee := 100, lamportsPerByte := 0xcccc28f646, threshold := (3.3 : Float).toBits }]

#guard cases.all Case.agrees
#guard (cases.map Case.outcome).count "panicked" == 3
#guard cases.all fun c => c.steps < fuel

/-! The stack: 88 bytes below the entry stack pointer on the deepest normal
path, 96 to the panic from the callee (`stackUse`). One byte less faults. -/
#guard ({ lamports := 1000, fee := 100, free := 88 } : Case).agrees
#guard (({ lamports := 1000, fee := 100, free := 87 } : Case).outcome).startsWith "faulted X86.Fault.pageFault (X86.PageFault.unmapped"
#guard ({ lamports := 1000, fee := 100, lamportsPerByte := 0xcccc28f646, free := stackUse } : Case).agrees
#guard (({ lamports := 1000, fee := 100, lamportsPerByte := 0xcccc28f646, free := stackUse - 1 } : Case).outcome).startsWith "faulted X86.Fault.pageFault"

/-! At a base that is only 8-aligned the f64 constants are misaligned for
`interleaveLow32` (x86: `punpckldq`). The theorem excludes the `f64` path, so
it does not need an aligned base. -/
def floatPathAt (loadBase : UInt64) : Case :=
  { lamports := 10 ^ 9, fee := 5000, data := nonceData, threshold := (3.3 : Float).toBits, loadBase }
#guard ((floatPathAt 0x555555554008).outcome).startsWith "faulted X86.Fault.misaligned"
#guard (floatPathAt 0x555555554000).agrees

/-! A return to an address that is neither exit is `badJump`: unmapped, or
mapped but not executable. -/
def returnsTo (returnAddress : UInt64) : Case := { lamports := 1000, fee := 100, returnAddress }

def runWithReturnExit (c : Case) (exit : UInt64) : Outcome :=
  X86.run { c.exits with returnAddress := exit } fuel c.state

#guard match runWithReturnExit (returnsTo 0x400000) 0x500000 with
  | .badJump s => s.rip == 0x400000 | _ => false
#guard
  let lb : UInt64 := 0x555555554000
  let data := ((Image.data.head?).map (·.address.at lb)).getD 0
  match runWithReturnExit (returnsTo data) 0x400000 with
  | .badJump s => s.rip == data | _ => false

/-! What was not carved is unmapped, though the code takes its address. -/
#guard match (({ lamports := 1, fee := 1 } : Case).state.memory.byte .read (Image.panic_msg.at 0x555555554000)) with
  | .error (.unmapped _ _) => true | _ => false

/-! The theorems' hypotheses are satisfiable: they hold of a concrete state. -/
deriving instance DecidableEq for Except

theorem writable_of_ok {m : Memory} {a : UInt64} {n : Nat} (h : (m.bytes .write a n).toBool = true) :
    m.Writable a n := by
  cases hb : m.bytes .write a n with
  | ok bs => exact fun i hi => Memory.ok_of_mapM_ok hb i (List.mem_range.2 hi)
  | error e => simp [hb, Except.toBool] at h

def example1 : Case := { lamports := 1000, fee := 100, free := stackUse }

theorem writable_of_mem {m : Memory} {bs : List Block} (h : (bs.all fun b => (m.bytes .write b.base b.size).toBool) = true) :
    ∀ b ∈ bs, b.Writable m := fun b hb => writable_of_ok (List.all_eq_true.1 h b hb)

example : Loaded example1.loadBase example1.state.memory := loaded_load (by decide +kernel) _

example : Called example1.loadBase example1.returnAddress example1.state where
  atEntry := rfl
  abi := { returnAddress := by unfold Memory.Holds; decide +kernel }
  returnOutsideImage := by unfold Region.block Block.Contains Block.endAddress; decide +kernel
  returnNotPanic := by decide +kernel

theorem readable_of_ok {m : Memory} {a : UInt64} {n : Nat} (h : (m.bytes .read a n).toBool = true) :
    m.Readable a n := by
  cases hb : m.bytes .read a n with
  | ok bs => exact fun i hi => Memory.ok_of_mapM_ok hb i (List.mem_range.2 hi)
  | error e => simp [hb, Except.toBool] at h

theorem readable_of_mem {m : Memory} {bs : List Block} (h : (bs.all fun b => (m.bytes .read b.base b.size).toBool) = true) :
    ∀ b ∈ bs, b.Readable m := fun b hb => readable_of_ok (List.all_eq_true.1 h b hb)

example : Footprint example1.loadBase example1.state heap example1.account.data.length where
  arcInner := by unfold PtrAt Memory.Holds; decide +kernel
  data := by unfold PtrAt Memory.Holds; decide +kernel
  length := by unfold Memory.Holds; decide +kernel
  readable := readable_of_mem (by decide +kernel)
  writable := writable_of_mem (by decide +kernel)
  relaxIsBool := by unfold Memory.Holds; decide +kernel
  separate := by unfold Block.Separate Block.Apart Block.endAddress; decide +kernel
  noWrap := by unfold Block.NoWrap Block.endAddress; decide +kernel

example : example1.state.memory.read .bits64 (exemptionThresholdAddress example1.state) ∈
    [.ok Spec.simd0194ExemptionThreshold, .ok Spec.currentExemptionThreshold] := by decide +kernel

example : Encoded example1.state heap
    ⟨example1.account, payerIndex, example1.rent, example1.fee, false, example1.metrics⟩ where
  account := by unfold Spec.Account.Encodes PtrAt Memory.Holds Memory.HoldsBytes; decide +kernel
  payerIndex := by decide +kernel
  rent := by unfold Spec.Rent.Encodes Memory.Holds; decide +kernel
  fee := by decide +kernel
  relax := by unfold BoolEncodes Memory.Holds; decide +kernel
  metrics := by unfold Spec.ErrorMetrics.Encodes Memory.Holds; decide +kernel

/-! A branch on a flag nobody wrote faults. -/
#guard match ((execute (.jumpIf .equal 0)).run { ({ lamports := 1, fee := 1 } : Case).state with rflags := .undefined }) with
  | .error (.undefinedFlagRead .zero) => true | _ => false

/-! F64 against the host's `Float` on random operands, bit-exact, NaN payloads
compared only as NaN: more operands than `tests/x86/` runs on the CPU. -/
def xorshift (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13); let x := x ^^^ (x >>> 7); x ^^^ (x <<< 17)

/-- Random doubles biased toward denormals, tiny normals, huge values and
values near one. -/
def interesting (r : UInt64) : UInt64 :=
  match r % 8 with
  | 0 => r &&& 0x800fffffffffffff
  | 1 => (r &&& 0x800fffffffffffff) ||| 0x0010000000000000
  | 2 => (r &&& 0x803fffffffffffff) ||| 0x7fc0000000000000
  | 3 => (r &&& 0x800fffffffffffff) ||| 0x3ff0000000000000
  | 4 => (r &&& 0x81ffffffffffffff) ||| 0x3c00000000000000
  | _ => r

def f64Mismatches (n : Nat) : Nat := Id.run do
  let mut x : UInt64 := 0x9e3779b97f4a7c15
  let mut bad := 0
  for _ in [0:n] do
    x := xorshift x
    let a := interesting x
    x := xorshift x
    let b := if x % 5 == 0 then a ^^^ (x >>> 60) else interesting x
    let fa := Float.ofBits a
    let fb := Float.ofBits b
    for (mine, hw) in [((F64.add a b).1, (fa + fb).toBits), ((F64.sub a b).1, (fa - fb).toBits),
                       ((F64.mul a b).1, (fa * fb).toBits)] do
      unless mine == hw || (F64.isNaN mine && F64.isNaN hw) do bad := bad + 1
    let ((zero, parity, carry), _) := F64.compareUnordered a b
    let hw := if F64.isNaN a || F64.isNaN b then (true, true, true)
      else if fa < fb then (false, false, true) else if fa == fb then (true, false, false)
      else (false, false, false)
    unless (zero, parity, carry) == hw do bad := bad + 1
    if !F64.isNaN a && fa.abs < 9.0e18 && (F64.truncateToInt64 a).1 != fa.toInt64.toUInt64 then bad := bad + 1
  return bad

#guard f64Mismatches 20000 == 0

end ValidateFeePayer.Tests
