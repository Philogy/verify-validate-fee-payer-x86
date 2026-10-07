import ValidateFeePayer.State
import ValidateFeePayer.Decode
import ValidateFeePayer.F64
import ValidateFeePayer.Stack

/-!
The semantics of one instruction (`exec`), and the machine that fetches
instructions from the predecoded code and runs them (`step`, `run`).

Flags follow the Intel SDM, vol. 2 (each instruction's "Flags Affected");
a flag the SDM calls undefined becomes `none`.
-/

namespace ValidateFeePayer.X86

namespace Sem

def signed (sz : Size) (v : Nat) : Int :=
  if v < 2 ^ (sz.bits - 1) then v else (v : Int) - 2 ^ sz.bits

def fits (sz : Size) (x : Int) : Bool := -(2 : Int) ^ (sz.bits - 1) ≤ x && x < 2 ^ (sz.bits - 1)

/-- Even number of set bits in the low byte. -/
def parity (v : Nat) : Bool := ((List.range 8).countP fun i => v.testBit i) % 2 == 0

/-- `ZF`, `SF`, `PF` from a result; the others as given. -/
def resultFlags (sz : Size) (r : Nat) (cf of af : Option Bool) : Flags :=
  { cf, of, af, zf := r == 0, sf := decide (r ≥ 2 ^ (sz.bits - 1)), pf := parity r }

/-- The carry out of bit 3, for `AF`: the same formula serves addition and
subtraction. -/
def auxCarry (a b r : Nat) : Bool := (a ^^^ b ^^^ r) >>> 4 % 2 == 1

end Sem

open M Sem

def alu (op : AluOp) (sz : Size) (dst : RM) (src : Src) : M Unit := do
  let a ← readRM sz dst
  let b ← readSrc sz src
  let n := 2 ^ sz.bits
  let arith (r : Nat) (cf : Bool) (sr : Int) : M Nat := do
    setFlags (resultFlags sz r cf (!fits sz sr) (auxCarry a b r)); pure r
  let logic (r : Nat) : M Nat := do
    setFlags (resultFlags sz r false false none); pure r
  let r ← match op with
    | .add => arith ((a + b) % n) (a + b ≥ n) (signed sz a + signed sz b)
    | .sub | .cmp => arith ((a + n - b) % n) (a < b) (signed sz a - signed sz b)
    | .sbb => do
      let c := if ← flag .cf then 1 else 0
      arith ((a + 2 * n - b - c) % n) (a < b + c) (signed sz a - signed sz b - c)
    | .and | .test => logic (a &&& b)
    | .or => logic (a ||| b)
    | .xor => logic (a ^^^ b)
  unless op == .cmp || op == .test do writeRM sz dst r

namespace Lanes
def lo (v : BitVec 128) : UInt64 := v.toNat.toUInt64
def hi (v : BitVec 128) : UInt64 := (v.toNat >>> 64).toUInt64
def mk (lo hi : UInt64) : BitVec 128 := BitVec.ofNat 128 (lo.toNat + 2 ^ 64 * hi.toNat)
def dword (v : BitVec 128) (i : Nat) : Nat := (v.toNat >>> (32 * i)) % 2 ^ 32
end Lanes

/-- Floating-point instructions run only under the default MXCSR control
bits (see `F64`); the exception flags in bits 0–5 may be anything. -/
def requireDefaultMxcsr : M Unit := do
  unless (← get).mxcsr &&& ~~~0x3f == mxcsrDefault do
    throw (.unsupported "MXCSR control bits")

def raise (e : F64.Exc) : M Unit := modify fun s => { s with mxcsr := s.mxcsr ||| e.bits }

/-- Execute `i`; `rip` already points past it. -/
def exec (i : Instr) : M Unit := do
  match i with
  | .alu op sz dst src => alu op sz dst src
  | .mov sz dst src => writeRM sz dst (← readSrc sz src)
  | .movabs dst v => setReg64 dst v
  | .movzx sz dst src => setReg sz dst (← readRM .b8 src)
  | .lea dst a => setReg64 dst (← ea a)
  | .inc sz dst =>
    let a ← readRM sz dst
    let r := (a + 1) % 2 ^ sz.bits
    let cf := (← get).flags.cf
    setFlags (resultFlags sz r cf (a + 1 == 2 ^ (sz.bits - 1)) (a % 16 == 15))
    writeRM sz dst r
  | .imul dst src imm =>
    let a ← readRM .b64 src
    let b ← match imm with
      | some v => pure v.toNat
      | none => readRM .b64 (.reg dst)
    let p := signed .b64 a * signed .b64 b
    let ov := !fits .b64 p
    setFlags { cf := ov, of := ov, af := none, zf := none, sf := none, pf := none }
    setReg64 dst (p % 2 ^ 64).toNat.toUInt64
  | .sar dst count =>
    let c := count.toNat % 64
    unless c = 0 do
      let a ← readRM .b64 dst
      let r := ((signed .b64 a / 2 ^ c) % 2 ^ 64).toNat
      setFlags (resultFlags .b64 r ((a >>> (c - 1)) % 2 == 1) (if c = 1 then some false else none) none)
      writeRM .b64 dst r
  | .setcc c dst => writeRM .b8 dst (if ← cond c then 1 else 0)
  | .cmov c sz dst src =>
    -- The source is read (and may fault) whatever the condition, and a
    -- 32-bit cmov zeroes the upper half of `dst` even when it does not move.
    let v ← readRM sz src
    if ← cond c then setReg sz dst v
    else setReg sz dst (← readRM sz (.reg dst))
  | .push r => push (← reg r)
  | .pop r => setReg64 r (← pop)
  | .jcc c rel =>
    if ← cond c then modify fun s => { s with rip := s.rip + (rel % 2 ^ 64).toNat.toUInt64 }
  | .jmp rel => modify fun s => { s with rip := s.rip + (rel % 2 ^ 64).toNat.toUInt64 }
  | .call t =>
    let target ← readRM .b64 t
    push (← get).rip
    modify fun s => { s with rip := target.toUInt64 }
  | .ret =>
    let target ← pop
    modify fun s => { s with rip := target }
  | .movdqu d s => setXmm d (← readX128 false s)
  | .movapd d s => setXmm d (← readX128 true s)
  | .movq d s => setXmm d (BitVec.ofNat 128 (← readRM .b64 s))
  | .xbit op d s =>
    let a ← xmm d
    let b ← readX128 true s
    setXmm d (match op with | .pxor | .xorpd => a ^^^ b | .por => a ||| b)
  | .ptest d s =>
    let a ← xmm d
    let b ← readX128 true s
    setFlags { zf := b &&& a == 0, cf := b &&& ~~~a == 0,
               af := false, of := false, pf := false, sf := false }
  | .punpckldq d s =>
    let a ← xmm d
    let b ← readX128 true s
    setXmm d (BitVec.ofNat 128 (Lanes.dword a 0 + 2 ^ 32 * Lanes.dword b 0 +
      2 ^ 64 * Lanes.dword a 1 + 2 ^ 96 * Lanes.dword b 1))
  | .unpckhpd d s =>
    let a ← xmm d
    let b ← readX128 true s
    setXmm d (Lanes.mk (Lanes.hi a) (Lanes.hi b))
  | .subpd d s =>
    requireDefaultMxcsr
    let a ← xmm d
    let b ← readX128 true s
    let (lo, e₁) := F64.sub (Lanes.lo a) (Lanes.lo b)
    let (hi, e₂) := F64.sub (Lanes.hi a) (Lanes.hi b)
    setXmm d (Lanes.mk lo hi)
    raise (e₁.or e₂)
  | .sd op d s =>
    requireDefaultMxcsr
    let a ← xmm d
    let b ← readX64 s
    let f := match op with | .addsd => F64.add | .subsd => F64.sub | .mulsd => F64.mul
    let (r, e) := f (Lanes.lo a) b
    setXmm d (Lanes.mk r (Lanes.hi a))
    raise e
  | .ucomisd d s =>
    requireDefaultMxcsr
    let a ← xmm d
    let b ← readX64 s
    let ((zf, pf, cf), e) := F64.ucomisd (Lanes.lo a) b
    setFlags { zf, pf, cf, of := false, sf := false, af := false }
    raise e
  | .cvttsd2si dst s =>
    requireDefaultMxcsr
    let (r, e) := F64.cvttsd2si (← readX64 s)
    setReg64 dst r
    raise e

/-- How execution leaves the carved code at a known address. -/
inductive Exit where
  /-- The caller's return address: the top-level `ret` has happened. -/
  | returned
  /-- `core::option::expect_failed`: the panic. -/
  | panicked
  deriving DecidableEq, Repr

/-- What does not change during a run. -/
structure Env where
  /-- Load base of the binary. -/
  B : UInt64
  /-- Addresses outside the carved code where execution may legitimately
  go, and what reaching each means. -/
  exits : List (UInt64 × Exit)
  /-- Low end of the stack mapping (see `Stack`). -/
  stackLo : UInt64

def Env.exitAt (env : Env) (rip : UInt64) : Option Exit := env.exits.lookup rip

/-- Free stack below `rsp` (`Stack.free`). -/
def Env.stackFree (env : Env) (rsp : UInt64) : Nat := Stack.free env.stackLo rsp

def State.rsp (s : State) : UInt64 := s.gpr[Reg.rsp.toFin]

inductive Outcome where
  /-- Ready to execute the instruction at `s.rip`. -/
  | running (s : State)
  /-- Reached an exit address; `s` is the state there (e.g. `rax`, memory
  and `rsp` after the return, or the panic's arguments). -/
  | exited (e : Exit) (s : State)
  /-- `s.rip` is neither an instruction start of the carved code nor an
  exit. -/
  | badJump (s : State)
  /-- The instruction at `s.rip` stopped the machine without effect. -/
  | stopped (why : Stop) (s : State)

/-- One instruction. Execution only takes instructions from `codeTable`,
which `Checks.lean` shows is the decoding of the carved bytes; the code is
mapped read/execute, so no store can change it. -/
def step (env : Env) (s : State) : Outcome :=
  match env.exitAt s.rip with
  | some e => .exited e s
  | none =>
    match instrAt (s.rip - env.B) with
    | none => .badJump s
    | some e =>
      match (exec e.instr).run { s with rip := s.rip + e.len.toUInt64 } with
      | .ok ((), s') => .running s'
      | .error why => .stopped why s

/-- At most `fuel` instructions; `running` if fuel runs out. -/
def run (env : Env) : (fuel : Nat) → State → Outcome
  | 0, s => .running s
  | fuel + 1, s =>
    match step env s with
    | .running s' => run env fuel s'
    | o => o

end ValidateFeePayer.X86
