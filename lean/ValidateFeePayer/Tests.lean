import ValidateFeePayer.Contract

/-!
Runs of the machine on concrete inputs, checked at build time. Each case
runs the code and `Spec.validateFeePayer` on the same values and compares
the outcome, the result, the account and the counters. These test the model
and the spec against each other; they are not proofs.
-/

namespace ValidateFeePayer.Tests

open X86 Image.Layout

def obj (base : UInt64) (size : Nat) (fields : List (Nat × List UInt8)) : Mapping :=
  let bytes := fields.foldl (fun (bs : Array UInt8) (offset, v) =>
    v.zipIdx.foldl (fun bs (b, i) => bs.set! (offset + i) b) bs) (Array.replicate size 0)
  { base, bytes := ⟨bytes⟩, permissions := .readWrite }

def u64 (v : UInt64) : List UInt8 := littleEndianBytes 8 v
def u32 (v : UInt64) : List UInt8 := littleEndianBytes 4 v

structure Case where
  lamports : UInt64
  owner : List UInt8 := List.replicate 32 0
  data : List UInt8 := []
  lamportsPerByte : UInt64 := 3480
  threshold : Float := 2.0
  fee : UInt64
  relax : Bool := false
  loadBase : UInt64 := 0x555555554000
  free : Nat := 4096
  counters : UInt64 := 0

def Case.call (c : Case) : Call :=
  { loadBase := c.loadBase, result := 0x10000,
    account := { account := 0x20000, arcInner := 0x30000, data := 0x40000 },
    errorMetrics := 0x50000, rent := 0x60000, payerIndex := 7, fee := c.fee, returnAddress := 0x400000 }

def stackTop : UInt64 := 0x7ffffff00000

def Case.state (c : Case) : State :=
  let call := c.call
  let sp := stackTop - 64
  let stack : Mapping :=
    { base := sp - c.free.toUInt64,
      bytes := ⟨(List.replicate c.free 0xaa ++ u64 call.returnAddress ++ [if c.relax then 1 else 0] ++
        List.replicate 55 0xbb).toArray⟩,
      permissions := .readWrite }
  let ctr (offset : Nat) := (offset, u64 c.counters)
  let objects := [
    obj call.result 16 [],
    obj call.account.account account_shared_data.size
      [(account_shared_data.data_arc, u64 call.account.arcInner),
       (account_shared_data.lamports, u64 c.lamports),
       (account_shared_data.owner, c.owner)],
    obj call.account.arcInner 0x28
      [(account_shared_data.arc_inner.data_ptr, u64 call.account.data),
       (account_shared_data.arc_inner.data_len, u64 c.data.length.toUInt64)],
    obj call.account.data (max c.data.length 1) [(0, c.data)],
    obj call.errorMetrics transaction_error_metrics.size
      [ctr transaction_error_metrics.account_not_found,
       ctr transaction_error_metrics.invalid_account_for_fee,
       ctr transaction_error_metrics.insufficient_funds],
    obj call.rent rent.size
      [(rent.lamports_per_byte, u64 c.lamportsPerByte),
       (rent.exemption_threshold, u64 c.threshold.toBits)]]
  let registers := (Vector.replicate 16 (0x1234567890abcdef : UInt64))
    |>.set Register.destinationIndex.index call.result
    |>.set Register.sourceIndex.index call.account.account
    |>.set Register.data.index (0x1234567890ab0000 ||| call.payerIndex.toUInt64)
    |>.set Register.counter.index call.errorMetrics
    |>.set Register.r8.index call.rent
    |>.set Register.r9.index call.fee
    |>.set Register.stackPointer.index sp
  { instructionPointer := entryAddress c.loadBase, registers, flags := .undefined,
    vectorRegisters := Vector.replicate 16 0, floatControl := defaultFloatControl,
    memory := ⟨imageMappings c.loadBase ++ stack :: objects⟩ }

def Case.account (c : Case) : Spec.Account :=
  { lamports := c.lamports, owner := Vector.ofFn fun i => c.owner.getD i 0, data := c.data }

def Case.run (c : Case) : Outcome := X86.run c.call.exits fuel c.state

def Case.steps (c : Case) : Nat := go fuel c.state 0
where
  go : Nat → State → Nat → Nat
    | 0, _, n => n
    | k + 1, s, n => match step c.call.exits s with
      | .running s' => go k s' (n + 1)
      | _ => n + 1

def read (s : State) (w : Width) (a : UInt64) : Option UInt64 := (s.memory.read w a).toOption

def Case.expected (c : Case) : Except Spec.Panic (Except Spec.TransactionError Unit × Spec.MutRefs) :=
  (Spec.validateFeePayer 7 ⟨c.lamportsPerByte, c.threshold.toBits⟩ c.fee c.relax).run
    ⟨c.account, ⟨c.counters, c.counters, c.counters⟩⟩

/-- The machine and the spec agree on the outcome and on everything `Post` names. -/
def Case.agrees (c : Case) : Bool :=
  let call := c.call
  match c.expected, c.run with
  | .error _, .panicked _ => true
  | .ok (r, ⟨account, metrics⟩), .returned s =>
    let counter (offset : Nat) := read s .bytes8 (off call.errorMetrics offset)
    read s .bytes4 call.result == some (resultTag r).toUInt64 &&
    (match r with
     | .error (.insufficientFundsForRent i) => read s .bytes1 (off call.result result.account_index) == some i.toUInt64
     | _ => true) &&
    read s .bytes8 (off call.account.account account_shared_data.lamports) == some account.lamports &&
    counter transaction_error_metrics.account_not_found == some metrics.accountNotFound &&
    counter transaction_error_metrics.invalid_account_for_fee == some metrics.invalidAccountForFee &&
    counter transaction_error_metrics.insufficient_funds == some metrics.insufficientFunds &&
    s.register .accumulator == call.result && s.stackPointer == c.state.stackPointer + 8 &&
    calleeSaved.all fun r => s.register r == c.state.register r
  | _, _ => false

def Case.outcome (c : Case) : String :=
  match c.run with
  | .running _ => "running" | .returned _ => "returned" | .panicked _ => "panicked"
  | .badJump t _ => s!"badJump {t}" | .undecodable why _ => s!"undecodable {repr why}"
  | .stopped why _ => s!"stopped {repr why}"

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
  { lamports := 208 * 3480 + 5000, fee := 5000, data := nonceData, threshold := 1.0 },
  { lamports := minBalance 3480 3.3 + 5000, fee := 5000, data := nonceData, threshold := 3.3 },
  { lamports := minBalance 3480 3.3 + 4999, fee := 5000, data := nonceData, threshold := 3.3 },
  { lamports := 900000, fee := 10000 },
  { lamports := 900000, fee := 10000, relax := true },
  { lamports := 900000, fee := 900000 },
  { lamports := 1000, fee := 100, lamportsPerByte := 0xcccc28f646 },
  { lamports := 1000, fee := 100, lamportsPerByte := 1759197129868, threshold := 1.0 },
  { lamports := 10 ^ 18, fee := 100, data := nonceData, lamportsPerByte := 0xcccc28f646 },
  { lamports := 1000, fee := 100, lamportsPerByte := 0xcccc28f646, threshold := 3.3 }]

#guard cases.all Case.agrees
#guard (cases.map Case.outcome).count "panicked" == 3
#guard cases.all fun c => c.steps < fuel

/-! The stack: 88 bytes below the entry stack pointer on the deepest normal
path, 96 to the panic from the callee (`stackUse`). One byte less faults. -/
#guard ({ lamports := 1000, fee := 100, free := 88 } : Case).agrees
#guard (({ lamports := 1000, fee := 100, free := 87 } : Case).outcome).startsWith "stopped X86.Stop.pageFault (X86.PageFault.unmapped"
#guard ({ lamports := 1000, fee := 100, lamportsPerByte := 0xcccc28f646, free := stackUse } : Case).agrees
#guard (({ lamports := 1000, fee := 100, lamportsPerByte := 0xcccc28f646, free := stackUse - 1 } : Case).outcome).startsWith "stopped X86.Stop.pageFault"

/-! At a base that is only 8-aligned the f64 constants are misaligned for
`interleaveLow32` (x86: `punpckldq`), hence `Pre.alignedBase`. -/
def floatPathAt (loadBase : UInt64) : Case :=
  { lamports := 10 ^ 9, fee := 5000, data := nonceData, threshold := 3.3, loadBase }
#guard ((floatPathAt 0x555555554008).outcome).startsWith "stopped X86.Stop.misaligned"
#guard (floatPathAt 0x555555554000).agrees

/-! A branch on a flag nobody wrote stops the machine. -/
#guard match ((execute (.jumpIf .equal 0)).run ({ lamports := 1, fee := 1 } : Case).state) with
  | .error (.undefinedFlagRead .zero) => true | _ => false

/-! F64 against the host's `Float` on random operands (a stand-in until the
per-instruction hardware harness exists : bit-exact, NaN payloads compared
only as NaN). -/
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
