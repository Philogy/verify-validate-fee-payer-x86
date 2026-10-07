import ValidateFeePayer.Memory
import ValidateFeePayer.Instr

/-!
The x86-64 user-mode state the carved code can observe or change (see
`x86-state.md`), and the monad in which one instruction runs.
-/

namespace ValidateFeePayer.X86

inductive Flag where
  | cf | pf | af | zf | sf | of
  deriving DecidableEq, Repr

/-- The six status flags. `none` means architecturally undefined: the last
instruction that wrote the flag left it undefined (e.g. `imul` and `ZF`), or
nothing in the program has written it yet. Real CPUs hold some value there,
but the program must not depend on it, so reading one stops the machine with
`undefinedRead` instead of guessing. -/
structure Flags where
  cf : Option Bool
  pf : Option Bool
  af : Option Bool
  zf : Option Bool
  sf : Option Bool
  of : Option Bool
  deriving DecidableEq, Repr

def Flags.undefined : Flags := ⟨none, none, none, none, none, none⟩

def Flags.get (f : Flags) : Flag → Option Bool
  | .cf => f.cf | .pf => f.pf | .af => f.af | .zf => f.zf | .sf => f.sf | .of => f.of

/-- Default MXCSR: all exceptions masked, round to nearest, no FTZ/DAZ, no
flags raised. -/
def mxcsrDefault : UInt32 := 0x1f80

structure State where
  /-- Address of the next instruction to execute. -/
  rip : UInt64
  gpr : Vector UInt64 16
  flags : Flags
  /-- The direction flag. No carved instruction reads or writes it; the ABI
  makes it clear on entry, and the oracle checks it stays so. -/
  df : Bool
  xmm : Vector (BitVec 128) 16
  mxcsr : UInt32
  mem : Memory

/-- Why the machine stopped in the middle of an instruction. The state is
the one before that instruction: a faulting instruction has no effect. -/
inductive Stop where
  /-- Page fault: the access is to an unmapped address or not permitted. -/
  | fault (f : Fault)
  /-- `#GP` from a misaligned 16-byte SSE memory operand. -/
  | misaligned (addr : UInt64)
  /-- A read of a flag that is undefined (`Flags`). -/
  | undefinedRead (f : Flag)
  /-- A setting outside what is modelled, e.g. non-default MXCSR control
  bits for a floating-point instruction. -/
  | unsupported (what : String)
  deriving Repr

def Size.width : Size → Width
  | .b8 => .w1 | .b32 => .w4 | .b64 => .w8

/-- One instruction: reads and updates the state, or stops. -/
abbrev M := StateT State (Except Stop)

namespace M

def reg (r : Reg) : M UInt64 := do return (← get).gpr[r.toFin]

/-- Write a 64-bit register. -/
def setReg64 (r : Reg) (v : UInt64) : M Unit :=
  modify fun s => { s with gpr := s.gpr.set r.toFin v }

def mask (sz : Size) (v : Nat) : Nat := v % 2 ^ sz.bits

/-- Write a register at operand size: 32-bit writes zero the upper half,
8-bit writes keep bits 8–63. -/
def setReg (sz : Size) (r : Reg) (v : Nat) : M Unit := do
  match sz with
  | .b64 => setReg64 r v.toUInt64
  | .b32 => setReg64 r (mask .b32 v).toUInt64
  | .b8 => setReg64 r (((← reg r) &&& ~~~0xff) ||| (mask .b8 v).toUInt64)

def liftFault (x : Except Fault α) : M α :=
  match x with
  | .ok v => pure v
  | .error f => throw (.fault f)

def ea : Addr → M UInt64
  | .rip d => do return (← get).rip + (d % 2 ^ 64).toNat.toUInt64
  | .sib base index d => do
    let b ← match base with | some r => reg r | none => pure 0
    let i ← match index with | some (r, s) => do pure ((← reg r) <<< s.val.toUInt64) | none => pure 0
    return b + i + (d % 2 ^ 64).toNat.toUInt64

def load (w : Width) (a : UInt64) : M Nat := do
  return (← liftFault ((← get).mem.read w a)).toNat

def store (w : Width) (a : UInt64) (v : Nat) : M Unit := do
  let m ← liftFault ((← get).mem.write w a (BitVec.ofNat _ v))
  modify fun s => { s with mem := m }

/-- An integer operand, zero-extended to `Nat`, below `2 ^ sz.bits`. -/
def readRM (sz : Size) : RM → M Nat
  | .reg r => do return mask sz (← reg r).toNat
  | .mem a => do load sz.width (← ea a)

def writeRM (sz : Size) : RM → Nat → M Unit
  | .reg r, v => setReg sz r v
  | .mem a, v => do store sz.width (← ea a) (mask sz v)

def readSrc (sz : Size) : Src → M Nat
  | .rm x => readRM sz x
  | .imm v => pure (mask sz v.toNat)

def flag (f : Flag) : M Bool := do
  match (← get).flags.get f with
  | some b => pure b
  | none => throw (.undefinedRead f)

def setFlags (f : Flags) : M Unit := modify fun s => { s with flags := f }

def cond : Cond → M Bool
  | .o => flag .of
  | .no => return !(← flag .of)
  | .b => flag .cf
  | .ae => return !(← flag .cf)
  | .e => flag .zf
  | .ne => return !(← flag .zf)
  | .be => return (← flag .cf) || (← flag .zf)
  | .a => return !(← flag .cf) && !(← flag .zf)
  | .s => flag .sf
  | .ns => return !(← flag .sf)
  | .p => flag .pf
  | .np => return !(← flag .pf)
  | .l => return (← flag .sf) != (← flag .of)
  | .ge => return (← flag .sf) == (← flag .of)
  | .le => return (← flag .zf) || (← flag .sf) != (← flag .of)
  | .g => return !(← flag .zf) && (← flag .sf) == (← flag .of)

def xmm (x : Xmm) : M (BitVec 128) := do return (← get).xmm[x]

def setXmm (x : Xmm) (v : BitVec 128) : M Unit :=
  modify fun s => { s with xmm := s.xmm.set x v }

/-- A 128-bit operand. Legacy-SSE memory operands must be 16-byte aligned
unless the instruction is an unaligned one (`movdqu`). -/
def readX128 (aligned : Bool) : XRM → M (BitVec 128)
  | .reg x => xmm x
  | .mem a => do
    let addr ← ea a
    if aligned && addr % 16 != 0 then throw (.misaligned addr)
    return BitVec.ofNat 128 (← load .w16 addr)

/-- A 64-bit operand (`xmm/m64`): the low lane of a register. No alignment
requirement. -/
def readX64 : XRM → M UInt64
  | .reg x => do return (← xmm x).toNat.toUInt64
  | .mem a => do return (← load .w8 (← ea a)).toUInt64

def push (v : UInt64) : M Unit := do
  let sp := (← reg .rsp) - 8
  store .w8 sp v.toNat
  setReg64 .rsp sp

def pop : M UInt64 := do
  let sp ← reg .rsp
  let v ← load .w8 sp
  setReg64 .rsp (sp + 8)
  return v.toUInt64

end M

end ValidateFeePayer.X86
