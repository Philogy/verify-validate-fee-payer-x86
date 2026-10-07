import ValidateFeePayer.Machine

/-!
The state at the entry of `validate_fee_payer`, built from the Rust-level
call

```rust
validate_fee_payer(payer_account: &mut AccountSharedData, payer_index: IndexOfAccount,
                   error_metrics: &mut TransactionErrorMetrics, rent: &Rent,
                   fee: u64, relax_post_exec_min_balance_check: bool) -> Result<()>
```

as the System V x86-64 ABI passes it: `Result<()>` (12 bytes) is returned
through a hidden pointer in `destinationIndex` (x86: `rdi`), the next five
arguments go in `sourceIndex`, `data`, `counter`, `r8`, `r9` (x86: `rsi`,
`rdx`, `rcx`, `r8`, `r9`), and the `bool` in the first stack slot, 8 bytes
above the return address (x86: `[rsp + 8]`). Narrow arguments only define
their low bits; the rest of the register or slot is whatever the caller
left, so it is a parameter like every other value the caller does not fix.
-/

namespace ValidateFeePayer.X86

/-- The arguments, as the machine sees them. Pointers are addresses of
objects in `Entry.objects`. -/
structure Args where
  /-- Where the `Result<()>` goes (`destinationIndex`, x86: `rdi`). -/
  result : UInt64
  /-- `&mut AccountSharedData` (`sourceIndex`, x86: `rsi`). -/
  payerAccount : UInt64
  /-- `IndexOfAccount` is `u16`: the low 16 bits of `data` (x86: `dx`). -/
  payerIndex : UInt16
  /-- `&mut TransactionErrorMetrics` (`counter`, x86: `rcx`). -/
  errorMetrics : UInt64
  /-- `&Rent` (`r8`). -/
  rent : UInt64
  /-- `r9`. -/
  fee : UInt64
  /-- `relax_post_exec_min_balance_check`: the low byte of the stack slot
  just above the return address. -/
  relaxMinBalanceCheck : Bool

/-- Everything that determines the entry state. -/
structure Entry where
  /-- Where the binary is loaded. -/
  loadBase : UInt64
  args : Args
  /-- Low end of the stack mapping. -/
  stackLow : UInt64
  /-- Leftover contents of the free stack, `[stackLow, stackPointer)`;
  their size is the free stack. -/
  freeStackBytes : ByteArray
  /-- The caller's return address, at the stack pointer. -/
  returnAddress : UInt64
  /-- From just past the `bool` argument up: the rest of its 8-byte slot
  and the caller's frames. -/
  callerStack : ByteArray
  /-- Register values the caller leaves unspecified: all but the argument
  registers and the stack pointer, plus bits 16–63 of `data` (x86: `rdx`). -/
  otherRegisters : Vector UInt64 16
  vectorRegisters : Vector (BitVec 128) 16
  floatControl : UInt32
  /-- The objects the arguments point to (account, its data, metrics, rent,
  result), each a mapping. -/
  objects : List Mapping

namespace Entry

/-- The stack pointer at entry, pointing at the return address. -/
def stackPointer (e : Entry) : UInt64 := e.stackLow + e.freeStackBytes.size.toUInt64

def stack (e : Entry) : Stack :=
  { low := e.stackLow
    bytes := e.freeStackBytes ++ UInt64.toLEBytes e.returnAddress ++
      ⟨#[if e.args.relaxMinBalanceCheck then 1 else 0]⟩ ++ e.callerStack }

def env (e : Entry) : Env :=
  { loadBase := e.loadBase
    exits := [(e.returnAddress, .returned), (panicAddress e.loadBase, .panicked)]
    stackLow := e.stackLow }

/-- The general-purpose registers at entry, with the arguments where the ABI
puts them. -/
def registers (e : Entry) : Vector UInt64 16 :=
  let a := e.args
  let set (r : Register) (v : UInt64) (g : Vector UInt64 16) := g.set r.index v
  e.otherRegisters
    |> set .destinationIndex a.result
    |> set .sourceIndex a.payerAccount
    |> set .data ((e.otherRegisters[Register.data.index] &&& ~~~0xffff) ||| a.payerIndex.toUInt64)
    |> set .counter a.errorMetrics
    |> set .r8 a.rent
    |> set .r9 a.fee
    |> set .stackPointer e.stackPointer

/-- The state at the first instruction. Flags are undefined: the caller
leaves values there, but the callee must not depend on them. -/
def state (e : Entry) : State :=
  { instructionPointer := entryAddress e.loadBase
    registers := e.registers
    flags := .undefined
    directionFlag := false
    vectorRegisters := e.vectorRegisters
    floatControl := e.floatControl
    memory := initialMemory e.loadBase e.stack.mapping e.objects }

/-- What a caller guarantees; a specification assumes these. -/
structure Assumptions (e : Entry) : Prop where
  base : ValidLoadBase e.loadBase
  /-- The stack does not wrap around `2^64`. -/
  stackFits : e.stack.high ≤ 2 ^ 64
  /-- SysV: the stack pointer is `≡ 0 (mod 16)` at the `call`, so `≡ 8`
  after it pushed the return address. -/
  aligned : e.stackPointer.toNat % 16 = 8
  /-- No two mappings overlap. -/
  wellFormed : (initialMemory e.loadBase e.stack.mapping e.objects).WellFormed
  /-- A guard page under the stack. -/
  guard : e.stack.GuardedBelow (initialMemory e.loadBase e.stack.mapping e.objects) 4096
  /-- Default floating-point control bits (callee-saved by the ABI). -/
  defaultFloatControl : e.floatControl &&& ~~~0x3f = defaultFloatControl

theorem state_stackPointer (e : Entry) : e.state.stackPointer = e.stackPointer :=
  Vector.getElem_set_self _

/-- The free stack at entry is exactly the leftover bytes below the stack
pointer: an assumption "at least `n` bytes free" is one about
`e.freeStackBytes.size`. -/
theorem freeStack_entry (e : Entry) (h : e.stack.high ≤ 2 ^ 64) :
    e.env.freeStack e.state.stackPointer = e.freeStackBytes.size := by
  have hs : e.stack.bytes.size = e.freeStackBytes.size + 8 + 1 + e.callerStack.size := by
    simp [stack, ByteArray.size_append]; rfl
  have hlt : e.stackLow.toNat + e.freeStackBytes.size < 2 ^ 64 := by
    simp only [Stack.high] at h; rw [hs] at h; simp [stack] at h; omega
  rw [state_stackPointer]
  simp only [Env.freeStack, Stack.free, env, stackPointer, UInt64.toNat_add, UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by omega : e.freeStackBytes.size < 2 ^ 64), Nat.mod_eq_of_lt hlt]
  omega

end Entry

end ValidateFeePayer.X86
