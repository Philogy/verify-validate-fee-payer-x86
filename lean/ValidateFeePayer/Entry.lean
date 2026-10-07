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
through a hidden pointer in `rdi`, the next five arguments go in `rsi`, `rdx`,
`rcx`, `r8`, `r9`, and the `bool` in the first stack slot, at `[rsp + 8]`
above the return address. Narrow arguments only define their low bits; the
rest of the register or slot is whatever the caller left, so it is a
parameter like every other value the caller does not fix.
-/

namespace ValidateFeePayer.X86

/-- The arguments, as the machine sees them. Pointers are addresses of
objects in `Entry.objects`. -/
structure Args where
  /-- `rdi`: where the `Result<()>` goes. -/
  result : UInt64
  /-- `rsi`: `&mut AccountSharedData`. -/
  payerAccount : UInt64
  /-- `dx`: `IndexOfAccount` is `u16`. -/
  payerIndex : UInt16
  /-- `rcx`: `&mut TransactionErrorMetrics`. -/
  errorMetrics : UInt64
  /-- `r8`: `&Rent`. -/
  rent : UInt64
  /-- `r9`. -/
  fee : UInt64
  /-- The low byte of the stack slot at `[rsp + 8]`. -/
  relax : Bool

/-- Everything that determines the entry state. -/
structure Entry where
  /-- Load base of the binary. -/
  loadBase : UInt64
  args : Args
  /-- Low end of the stack mapping. -/
  stackLo : UInt64
  /-- Stale contents of `[stackLo, rsp)`; their size is the free stack. -/
  stale : ByteArray
  /-- At `[rsp]`. -/
  retAddr : UInt64
  /-- `[rsp + 9, hi)`: the rest of the `bool`'s slot and the caller's frames. -/
  above : ByteArray
  /-- Register values the caller leaves unspecified: all but the argument
  registers and `rsp`, plus bits 16–63 of `rdx`. -/
  regs : Vector UInt64 16
  xmm : Vector (BitVec 128) 16
  mxcsr : UInt32
  /-- The objects the arguments point to (account, its data, metrics, rent,
  result), each a mapping. -/
  objects : List Mapping

namespace Entry

/-- `rsp` at entry, pointing at the return address. -/
def rsp (e : Entry) : UInt64 := e.stackLo + e.stale.size.toUInt64

def stack (e : Entry) : Stack :=
  { low := e.stackLo
    bytes := e.stale ++ UInt64.toLEBytes e.retAddr ++ ⟨#[if e.args.relax then 1 else 0]⟩ ++ e.above }

def env (e : Entry) : Env :=
  { loadBase := e.loadBase
    exits := [(e.retAddr, .returned), (panicAddress e.loadBase, .panicked)]
    stackLo := e.stackLo }

def gpr (e : Entry) : Vector UInt64 16 :=
  let a := e.args
  let set (r : Reg) (v : UInt64) (g : Vector UInt64 16) := g.set r.toFin v
  e.regs
    |> set .rdi a.result
    |> set .rsi a.payerAccount
    |> set .rdx ((e.regs[Reg.rdx.toFin] &&& ~~~0xffff) ||| a.payerIndex.toUInt64)
    |> set .rcx a.errorMetrics
    |> set .r8 a.rent
    |> set .r9 a.fee
    |> set .rsp e.rsp

/-- The state at the first instruction. Flags are undefined: the caller
leaves values there, but the callee must not depend on them. -/
def state (e : Entry) : State :=
  { rip := entryAddress e.loadBase
    gpr := e.gpr
    flags := .undefined
    df := false
    xmm := e.xmm
    mxcsr := e.mxcsr
    mem := initialMemory e.loadBase e.stack.mapping e.objects }

/-- What a caller guarantees; a specification assumes these. -/
structure Assumptions (e : Entry) : Prop where
  base : ValidLoadBase e.loadBase
  /-- The stack does not wrap around `2^64`. -/
  stackFits : e.stack.high ≤ 2 ^ 64
  /-- SysV: `rsp ≡ 0 (mod 16)` at the `call`, so `≡ 8` after it pushed the
  return address. -/
  aligned : e.rsp.toNat % 16 = 8
  /-- No two mappings overlap. -/
  wellFormed : (initialMemory e.loadBase e.stack.mapping e.objects).WellFormed
  /-- A guard page under the stack. -/
  guard : e.stack.GuardedBelow (initialMemory e.loadBase e.stack.mapping e.objects) 4096
  /-- Default MXCSR control bits (callee-saved by the ABI). -/
  mxcsr : e.mxcsr &&& ~~~0x3f = mxcsrDefault

theorem state_rsp (e : Entry) : e.state.rsp = e.rsp := Vector.getElem_set_self _

/-- The free stack at entry is exactly the stale bytes below `rsp`: an
assumption "at least `n` bytes free" is one about `e.stale.size`. -/
theorem stackFree_entry (e : Entry) (h : e.stack.high ≤ 2 ^ 64) :
    e.env.stackFree e.state.rsp = e.stale.size := by
  have hs : e.stack.bytes.size = e.stale.size + 8 + 1 + e.above.size := by
    simp [stack, ByteArray.size_append]; rfl
  have hlt : e.stackLo.toNat + e.stale.size < 2 ^ 64 := by
    simp only [Stack.high] at h; rw [hs] at h; simp [stack] at h; omega
  rw [state_rsp]
  simp only [Env.stackFree, Stack.free, env, rsp, UInt64.toNat_add, UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by omega : e.stale.size < 2 ^ 64), Nat.mod_eq_of_lt hlt]
  omega

end Entry

end ValidateFeePayer.X86
