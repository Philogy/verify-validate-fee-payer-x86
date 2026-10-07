import ValidateFeePayer.Entry

/-!
Runs of the model on concrete inputs, checked when the file is built. They
exercise every exit of `validate_fee_payer` against what the Rust source
says, the floating-point path against the host CPU's `Float`, and the
machine's stops (stack overflow, misalignment, undefined flags). They are
tests of the model, not proofs about the code.
-/

namespace ValidateFeePayer.X86.Tests

open Image.Layout

/-- A read/write object of `size` zero bytes with `fields` (offset, value
bytes) written in. -/
def obj (base : UInt64) (size : Nat) (fields : List (Nat × List UInt8)) : Mapping :=
  let bytes := fields.foldl (fun (bs : Array UInt8) (off, v) =>
    v.zipIdx.foldl (fun bs (b, i) => bs.set! (off + i) b) bs) (Array.replicate size 0)
  { base, bytes := ⟨bytes⟩, permissions := .readWrite }

def u64 (v : Nat) : List UInt8 := leBytes 8 v
def u32 (v : Nat) : List UInt8 := leBytes 4 v

def systemProgramId : List UInt8 := List.replicate 32 0

/-- Addresses of the argument objects. -/
def resultAt : UInt64 := 0x10000
def accountAt : UInt64 := 0x20000
def arcAt : UInt64 := 0x30000
def dataAt : UInt64 := 0x40000
def metricsAt : UInt64 := 0x50000
def rentAt : UInt64 := 0x60000

structure Case where
  lamports : Nat
  owner : List UInt8 := systemProgramId
  /-- Account data; a nonce account's is 80 bytes starting with
  `(version, state)` = `(1, 1)`. -/
  data : List UInt8 := []
  lamportsPerByte : Nat := 3480
  /-- `Rent::exemption_threshold`, as f64 bits. -/
  threshold : Float := 2.0
  fee : Nat
  relax : Bool := false
  loadBase : UInt64 := 0x555555554000
  /-- Free stack at entry. -/
  free : Nat := 4096

def nonceData : List UInt8 := u32 1 ++ u32 1 ++ List.replicate 72 0

def Case.entry (c : Case) : Entry :=
  { loadBase := c.loadBase
    args := { result := resultAt, payerAccount := accountAt, payerIndex := 7,
              errorMetrics := metricsAt, rent := rentAt, fee := c.fee.toUInt64, relaxMinBalanceCheck := c.relax }
    stackLow := 0x7ffffff00000 - 8 - c.free.toUInt64
    freeStackBytes := ⟨Array.replicate c.free 0xaa⟩
    returnAddress := 0x400000
    callerStack := ⟨Array.replicate 55 0xbb⟩
    otherRegisters := Vector.replicate 16 0x1234567890abcdef
    vectorRegisters := Vector.replicate 16 0
    floatControl := defaultFloatControl
    objects := [
      obj resultAt 16 [],
      obj accountAt account_shared_data.size
        [(account_shared_data.data_arc, u64 arcAt.toNat),
         (account_shared_data.lamports, u64 c.lamports),
         (account_shared_data.owner, c.owner)],
      obj arcAt 0x28
        [(account_shared_data.arc_inner.data_ptr, u64 dataAt.toNat),
         (account_shared_data.arc_inner.data_len, u64 c.data.length)],
      obj dataAt (max c.data.length 1) [(0, c.data)],
      obj metricsAt transaction_error_metrics.size [],
      obj rentAt rent.size
        [(rent.lamports_per_byte, u64 c.lamportsPerByte),
         (rent.exemption_threshold, u64 c.threshold.toBits.toNat)]] }

def Case.run (c : Case) : Outcome := X86.run c.entry.env 1000 c.entry.state

def read (s : State) (w : Width) (a : UInt64) : Option Nat := (s.memory.read w a).toOption.map (·.toNat)

/-- Returned, with `accumulator` (x86: `rax`) pointing at the result, which has tag `tag`. -/
def returnsTag (c : Case) (tag : Nat) : Bool :=
  match c.run with
  | .exited .returned s =>
    s.registers[Register.accumulator.index] == resultAt && read s .bytes4 resultAt == some tag
      && s.stackPointer == c.entry.stackPointer + 8
  | _ => false

def metric (c : Case) (off : Nat) : Option Nat :=
  match c.run with
  | .exited .returned s => read s .bytes8 (metricsAt + off.toUInt64)
  | _ => none

def lamportsAfter (c : Case) : Option Nat :=
  match c.run with
  | .exited .returned s => read s .bytes8 (accountAt + account_shared_data.lamports.toUInt64)
  | _ => none

def stopReason (c : Case) : String :=
  match c.run with
  | .stopped why _ => reprStr why
  | .exited e _ => reprStr e
  | .badJump s => s!"badJump {s.instructionPointer}"
  | .running _ => "running"

open result.tags transaction_error_metrics

-- No lamports: `AccountNotFound`, counted.
#guard returnsTag { lamports := 0, fee := 5 } AccountNotFound
#guard metric { lamports := 0, fee := 5 } account_not_found == some 1

-- Not owned by the system program: `InvalidAccountForFee`, counted.
#guard returnsTag { lamports := 10, fee := 5, owner := List.replicate 32 1 } InvalidAccountForFee
#guard metric { lamports := 10, fee := 5, owner := List.replicate 32 1 } invalid_account_for_fee == some 1

-- System account: fee charged, then the rent-state check (rent-paying before
-- and after, same size: allowed).
#guard returnsTag { lamports := 1000, fee := 100 } Ok
#guard lamportsAfter { lamports := 1000, fee := 100 } == some 900
#guard returnsTag { lamports := 99, fee := 100 } InsufficientFundsForFee
#guard metric { lamports := 99, fee := 100 } insufficient_funds == some 1

-- Nonce account: the fee must leave the rent-exempt minimum,
-- `(128 + 80) * lamports_per_byte * threshold`. Threshold 2.0 takes the
-- integer path, 3.3 the floating-point one, compared with the host's f64.
def minBalance (lpb : Nat) (thr : Float) : Nat := (Float.ofNat (208 * lpb) * thr).toUInt64.toNat

#guard returnsTag { lamports := 208 * 3480 * 2 + 5000, fee := 5000, data := nonceData } Ok
#guard returnsTag { lamports := 208 * 3480 * 2 + 4999, fee := 5000, data := nonceData } InsufficientFundsForFee
#guard returnsTag { lamports := minBalance 3480 3.3 + 5000, fee := 5000, data := nonceData, threshold := 3.3 } Ok
#guard returnsTag { lamports := minBalance 3480 3.3 + 4999, fee := 5000, data := nonceData, threshold := 3.3 } InsufficientFundsForFee
#guard lamportsAfter { lamports := minBalance 3480 3.3 + 5000, fee := 5000, data := nonceData, threshold := 3.3 }
  == some (minBalance 3480 3.3)

-- A rent-exempt system account (minimum `128 * 3480 * 2 = 890880`) that the
-- fee would leave rent-paying: `InsufficientFundsForRent`, with the account
-- index (7) as a byte after the tag. Draining it to zero is allowed.
#guard returnsTag { lamports := 900000, fee := 10000 } InsufficientFundsForRent
#guard (match ({ lamports := 900000, fee := 10000 } : Case).run with
  | .exited .returned s => read s .bytes1 (resultAt + result.account_index.toUInt64) == some 7
  | _ => false)
#guard returnsTag { lamports := 900000, fee := 900000 } Ok

-- `lamports_per_byte` above the cap with threshold 2.0: the `expect` panics.
#guard stopReason { lamports := 1000, fee := 100, lamportsPerByte := 0xcccc28f646 } == "ValidateFeePayer.X86.Exit.panicked"
#guard stopReason { lamports := 10 ^ 18, fee := 100, data := nonceData, lamportsPerByte := 0xcccc28f646 }
  == "ValidateFeePayer.X86.Exit.panicked"

/-! The stack: the deepest normal path (into the callee) uses 88 bytes below
the entry stack pointer; the panic from the callee 96. One byte less faults on the
guard below the stack. -/
#guard returnsTag { lamports := 1000, fee := 100, free := 88 } Ok
#guard (stopReason { lamports := 1000, fee := 100, free := 87 }).startsWith "ValidateFeePayer.X86.Stop.fault (ValidateFeePayer.Fault.unmapped"
#guard stopReason { lamports := 1000, fee := 100, lamportsPerByte := 0xcccc28f646, free := 96 } == "ValidateFeePayer.X86.Exit.panicked"
#guard (stopReason { lamports := 1000, fee := 100, lamportsPerByte := 0xcccc28f646, free := 95 }).startsWith "ValidateFeePayer.X86.Stop.fault"

/-! Alignment: the f64 constants are 16-byte aligned at a page-aligned base;
at a base that is only 8-aligned, `interleaveLow32`'s (x86: `punpckldq`) memory operand is not. -/
def floatPathAt (loadBase : UInt64) : Case :=
  { lamports := 10 ^ 9, fee := 5000, data := nonceData, threshold := 3.3, loadBase }
#guard (stopReason (floatPathAt 0x555555554008)).startsWith "ValidateFeePayer.X86.Stop.misaligned"
#guard returnsTag (floatPathAt 0x555555554000) Ok
-- The integer path never touches them, so it runs at that base.
#guard returnsTag { lamports := 1000, fee := 100, loadBase := 0x555555554008 } Ok

/-! Undefined flags: a branch on a flag nobody wrote stops the machine. -/
def jumpIfEqualAtEntry (c : Case) : Except Stop Unit :=
  ((execute (.jumpIf .equal 0)).run c.entry.state).map (fun _ => ())

#guard match jumpIfEqualAtEntry { lamports := 1, fee := 1 } with
  | .error (.undefinedFlagRead .zero) => true | _ => false

-- `multiplySigned` (x86: `imul`) leaves `zero` undefined.
def jumpIfEqualAfterMultiply (c : Case) : Except Stop Unit :=
  ((do execute (.multiplySigned .accumulator (.register .accumulator) none); execute (.jumpIf .equal 0)).run c.entry.state).map (fun _ => ())

#guard match jumpIfEqualAfterMultiply { lamports := 1, fee := 1 } with
  | .error (.undefinedFlagRead .zero) => true | _ => false

/-! F64 against the host CPU on random operands (bit-exact; NaN payloads
are compared only as NaN, since hosts differ there). -/
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

end ValidateFeePayer.X86.Tests
