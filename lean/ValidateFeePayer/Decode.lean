import ValidateFeePayer.Instr
import ValidateFeePayer.Image

/-!
A strict decoder for exactly the encodings the carved code uses.

Strict means that anything this file does not list is a `DecodeError`, even
where the CPU would accept it: other opcodes, other legacy prefixes (lock,
segment overrides, `0x67`, a second prefix), `0x66` on integer instructions,
REX bits the instruction does not use (e.g. `REX.W` on `push`, `REX.B` with a
rip-relative operand, `REX.X` without a SIB index), a nonzero SIB scale
without an index, `ah`/`ch`/`dh`/`bh`, and nonzero reserved ModRM fields
(`setcc`'s `reg`). So a decoded instruction always means what `Instr` says,
with no ignored bits.

The decoder is run once over the carved code (`decodeImage`, a linear sweep
from each function's start to its end); `codeTable` is the result, and the
machine looks instructions up there. `Checks.lean` proves that the sweep
succeeds and matches GNU objdump's disassembly instruction for instruction.
-/

namespace ValidateFeePayer.X86

inductive DecodeError where
  | truncated
  | unsupported (what : String)
  deriving DecidableEq, Repr

/-- Decoding consumes bytes from the front of the list. -/
abbrev D := StateT (List UInt8) (Except DecodeError)

namespace Decode

def next : D UInt8 := do
  match ← get with
  | [] => throw .truncated
  | b :: rest => set rest; pure b

def need (ok : Bool) (what : String) : D Unit :=
  unless ok do throw (.unsupported what)

/-- `n` bytes, little-endian, unsigned. -/
def le : Nat → D Nat
  | 0 => pure 0
  | n + 1 => do
    let lo ← next
    let hi ← le n
    pure (lo.toNat + 256 * hi)

/-- `n` bytes, little-endian, two's complement. -/
def simm (n : Nat) : D Int := do
  let v ← le n
  pure (if v < 2 ^ (8 * n - 1) then v else v - 2 ^ (8 * n))

def toU64 (v : Int) : UInt64 := (v % 2 ^ 64).toNat.toUInt64

def reg (n : Nat) : Reg := Reg.ofFin ⟨n % 16, Nat.mod_lt _ (by decide)⟩

def xmm (n : Nat) : Xmm := ⟨n % 16, Nat.mod_lt _ (by decide)⟩

structure Rex where
  /-- A REX byte is present (changes the meaning of 8-bit registers 4–7). -/
  present : Bool
  w : Bool
  r : Bool
  x : Bool
  b : Bool

def Rex.none : Rex := ⟨false, false, false, false, false⟩

def Rex.ofByte (v : UInt8) : Rex :=
  ⟨true, v &&& 8 != 0, v &&& 4 != 0, v &&& 2 != 0, v &&& 1 != 0⟩

def bit (b : Bool) : Nat := if b then 8 else 0

structure ModRM where
  /-- The `reg` field, without `REX.R`; a register or an opcode extension. -/
  reg : Nat
  /-- The `r/m` operand, with `REX.B`/`REX.X` applied. -/
  rm : RM

def disp (md : Nat) : D Int :=
  match md with
  | 1 => simm 1
  | 2 => simm 4
  | _ => pure 0

/-- ModRM, then SIB and displacement if present. Rejects `REX.X` and `REX.B`
where the operand does not use them; the caller checks `REX.R`. -/
def modrm (rex : Rex) : D ModRM := do
  let m := (← next).toNat
  let md := m >>> 6
  let regField := (m >>> 3) % 8
  let rm := m % 8
  if md = 3 then
    need (!rex.x) "REX.X without a SIB index"
    return ⟨regField, .reg (reg (rm + bit rex.b))⟩
  if rm = 4 then
    let s := (← next).toNat
    let scale := s >>> 6
    let idx := (s >>> 3) % 8 + bit rex.x
    let index := if idx = 4 then none else some (reg idx, (⟨scale % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4))
    need (index.isSome || scale = 0) "SIB scale without an index"
    if s % 8 = 5 && md = 0 then
      need (!rex.b) "REX.B on a SIB without base"
      return ⟨regField, .mem (.sib none index (← simm 4))⟩
    return ⟨regField, .mem (.sib (some (reg (s % 8 + bit rex.b))) index (← disp md))⟩
  need (!rex.x) "REX.X without a SIB index"
  if md = 0 && rm = 5 then
    need (!rex.b) "REX.B on a rip-relative operand"
    return ⟨regField, .mem (.rip (← simm 4))⟩
  return ⟨regField, .mem (.sib (some (reg (rm + bit rex.b))) none (← disp md))⟩

/-- An 8-bit register operand: without REX, encodings 4–7 are `ah`…`bh`,
which the model does not have. -/
def byteRM (rex : Rex) (x : RM) : D RM := do
  if let .reg r := x then
    need (rex.present || r.toFin.val < 4) "ah/ch/dh/bh"
  pure x

def xrm : RM → XRM
  | .reg r => .reg r.toFin
  | .mem a => .mem a

def isMem : RM → Bool
  | .mem _ => true
  | .reg _ => false

/-- The ALU operation of `op r/m, r` opcodes (`0x00`…`0x3f`, `0x84`/`0x85`). -/
def aluOfOpcode : Nat → Option AluOp
  | 0x00 | 0x01 => some .add
  | 0x08 | 0x09 => some .or
  | 0x18 | 0x19 => some .sbb
  | 0x20 | 0x21 => some .and
  | 0x28 | 0x29 => some .sub
  | 0x30 | 0x31 => some .xor
  | 0x38 | 0x39 => some .cmp
  | 0x84 | 0x85 => some .test
  | _ => none

/-- The ALU operation of group 1 (`0x81`, `0x83`) by ModRM `reg`. `adc` (2)
does not occur. -/
def aluOfGroup1 : Nat → Option AluOp
  | 0 => some .add | 1 => some .or | 3 => some .sbb | 4 => some .and
  | 5 => some .sub | 6 => some .xor | 7 => some .cmp
  | _ => none

/-- Instructions without a mandatory prefix. -/
def integer (rex : Rex) (op : Nat) : D Instr := do
  let sz : Size := if rex.w then .b64 else .b32
  -- `REX.R`, `REX.X`, `REX.W` unused: opcodes with the register in the low bits.
  let opReg : D Reg := do
    need (!rex.w && !rex.r && !rex.x) "REX bits on push/pop"
    pure (reg (op % 8 + bit rex.b))
  -- Relative branches and `ret` take no REX at all.
  let noRex : D Unit := need (!rex.present) "REX on a branch"
  if 0x50 ≤ op && op ≤ 0x57 then return .push (← opReg)
  if 0x58 ≤ op && op ≤ 0x5f then return .pop (← opReg)
  if 0x70 ≤ op && op ≤ 0x7f then noRex; return .jcc (Cond.ofCode (op - 0x70)) (← simm 1)
  if 0xb8 ≤ op && op ≤ 0xbf then
    need (!rex.r && !rex.x) "REX.R/X on mov r, imm"
    let r := reg (op % 8 + bit rex.b)
    if rex.w then return .movabs r (← le 8).toUInt64
    else return .mov .b32 (.reg r) (.imm (← le 4).toUInt64)
  if let some aop := aluOfOpcode op then
    let m ← modrm rex
    let src := reg (m.reg + bit rex.r)
    if op % 2 = 0 then
      need (!rex.w) "REX.W on an 8-bit operation"
      let dst ← byteRM rex m.rm
      let src ← byteRM rex (.reg src)
      return .alu aop .b8 dst (.rm src)
    return .alu aop sz m.rm (.rm (.reg src))
  match op with
  | 0xeb => noRex; return .jmp (← simm 1)
  | 0xe9 => noRex; return .jmp (← simm 4)
  | 0xc3 => noRex; return .ret
  | 0x81 | 0x83 =>
    let m ← modrm rex
    need (!rex.r) "REX.R on an opcode extension"
    let some aop := aluOfGroup1 m.reg | throw (.unsupported "group 1 operation")
    let imm ← simm (if op = 0x83 then 1 else 4)
    return .alu aop sz m.rm (.imm (toU64 imm))
  | 0x89 =>
    let m ← modrm rex
    return .mov sz m.rm (.rm (.reg (reg (m.reg + bit rex.r))))
  | 0x8b =>
    let m ← modrm rex
    return .mov sz (.reg (reg (m.reg + bit rex.r))) (.rm m.rm)
  | 0x88 =>
    need (!rex.w) "REX.W on an 8-bit operation"
    let m ← modrm rex
    let dst ← byteRM rex m.rm
    let src ← byteRM rex (.reg (reg (m.reg + bit rex.r)))
    return .mov .b8 dst (.rm src)
  | 0xc7 =>
    let m ← modrm rex
    need (!rex.r && m.reg = 0) "c7 extension"
    return .mov sz m.rm (.imm (toU64 (← simm 4)))
  | 0x8d =>
    need rex.w "lea without REX.W"
    let m ← modrm rex
    let .mem a := m.rm | throw (.unsupported "lea of a register")
    return .lea (reg (m.reg + bit rex.r)) a
  | 0xff =>
    let m ← modrm rex
    need (!rex.r) "REX.R on an opcode extension"
    match m.reg with
    | 0 => return .inc sz m.rm
    | 2 => need (!rex.w) "REX.W on call"; return .call m.rm
    | _ => throw (.unsupported "group 5 operation")
  | 0x69 =>
    need rex.w "32-bit imul"
    let m ← modrm rex
    return .imul (reg (m.reg + bit rex.r)) m.rm (some (toU64 (← simm 4)))
  | 0xc1 =>
    need rex.w "32-bit shift"
    let m ← modrm rex
    need (!rex.r && m.reg = 7) "shift other than sar"
    return .sar m.rm (← next)
  | 0x0f =>
    let op2 := (← next).toNat
    if 0x80 ≤ op2 && op2 ≤ 0x8f then noRex; return .jcc (Cond.ofCode (op2 - 0x80)) (← simm 4)
    if 0x90 ≤ op2 && op2 ≤ 0x9f then
      need (!rex.w) "REX.W on setcc"
      let m ← modrm rex
      need (!rex.r && m.reg = 0) "setcc reg field"
      return .setcc (Cond.ofCode (op2 - 0x90)) (← byteRM rex m.rm)
    if 0x40 ≤ op2 && op2 ≤ 0x4f then
      let m ← modrm rex
      return .cmov (Cond.ofCode (op2 - 0x40)) sz (reg (m.reg + bit rex.r)) m.rm
    match op2 with
    | 0xaf =>
      need rex.w "32-bit imul"
      let m ← modrm rex
      return .imul (reg (m.reg + bit rex.r)) m.rm none
    | 0xb6 =>
      let m ← modrm rex
      return .movzx sz (reg (m.reg + bit rex.r)) (← byteRM rex m.rm)
    | _ => throw (.unsupported "0f opcode")
  | _ => throw (.unsupported "opcode")

/-- Instructions with a mandatory `0x66`, `0xf2` or `0xf3` prefix: SSE. -/
def sse (pfx : Nat) (rex : Rex) (op : Nat) : D Instr := do
  need (op = 0x0f) "prefix on a non-SSE opcode"
  let op2 := (← next).toNat
  -- `movq` and `cvttsd2si` need `REX.W` (without it they are 32-bit forms);
  -- every other one rejects it.
  need (rex.w == (pfx = 0x66 && op2 = 0x6e || pfx = 0xf2 && op2 = 0x2c)) "REX.W"
  let op2 ← if pfx = 0x66 && op2 = 0x38 then do
      need ((← next).toNat = 0x17) "0f 38 opcode"; pure 0x3817
    else pure op2
  let m ← modrm rex
  let dst := xmm (m.reg + bit rex.r)
  let src := xrm m.rm
  match pfx, op2 with
  | 0xf3, 0x6f => return .movdqu dst src
  | 0x66, 0x28 => return .movapd dst src
  | 0x66, 0x6e => return .movq dst m.rm
  | 0x66, 0xef => return .xbit .pxor dst src
  | 0x66, 0xeb => return .xbit .por dst src
  | 0x66, 0x57 => return .xbit .xorpd dst src
  | 0x66, 0x3817 => return .ptest dst src
  | 0x66, 0x62 => return .punpckldq dst src
  | 0x66, 0x15 => return .unpckhpd dst src
  | 0x66, 0x5c => return .subpd dst src
  | 0xf2, 0x58 => return .sd .addsd dst src
  | 0xf2, 0x5c => return .sd .subsd dst src
  | 0xf2, 0x59 => return .sd .mulsd dst src
  | 0x66, 0x2e => return .ucomisd dst src
  | 0xf2, 0x2c => return .cvttsd2si (reg (m.reg + bit rex.r)) src
  | _, _ => throw (.unsupported "SSE opcode")

/-- One instruction: at most one of `0x66`/`0xf2`/`0xf3`, an optional REX
byte, then the opcode. -/
def instr : D Instr := do
  let b := (← next).toNat
  let (pfx, b) ← if b = 0x66 || b = 0xf2 || b = 0xf3 then do pure (some b, (← next).toNat)
    else pure (none, b)
  let (rex, op) ← if b >>> 4 = 4 then do pure (Rex.ofByte b.toUInt8, (← next).toNat)
    else pure (Rex.none, b)
  match pfx with
  | none => integer rex op
  | some p => sse p rex op

end Decode

/-- The instruction at the start of `bytes`, and its length. -/
def decode (bytes : List UInt8) : Except DecodeError (Instr × Nat) := do
  let (i, rest) ← Decode.instr.run bytes
  let len := bytes.length - rest.length
  unless len ≤ 15 do throw (.unsupported "longer than 15 bytes")
  pure (i, len)

/-- A decoded instruction at its address (at load base 0). -/
structure Decoded where
  addr : UInt64
  instr : Instr
  len : Nat
  deriving DecidableEq, Repr

/-- Decode back to back from `addr` until the bytes run out. `fuel` bounds
the number of instructions (each is at least one byte). -/
def sweep : (fuel : Nat) → (addr : UInt64) → List UInt8 → Except (UInt64 × DecodeError) (List Decoded)
  | _, _, [] => pure []
  | 0, addr, _ => throw (addr, .unsupported "out of fuel")
  | fuel + 1, addr, bytes => do
    let (i, len) ← (decode bytes).mapError (addr, ·)
    let rest ← sweep fuel (addr + len.toUInt64) (bytes.drop len)
    pure (⟨addr, i, len⟩ :: rest)

def decodeRegion (r : Region) : Except (UInt64 × DecodeError) (List Decoded) :=
  match r.contents with
  | .code bytes => sweep bytes.size r.vaddr bytes.toList
  | _ => throw (r.vaddr, .unsupported "not a code region")

/-- Every instruction of the carved functions, in address order. -/
def decodeImage : Except (UInt64 × DecodeError) (List Decoded) := do
  let parts ← Image.functions.mapM decodeRegion
  pure parts.flatten

/-- The predecoded code. `Checks.lean` proves `decodeImage = .ok codeTable`,
so the fallback is never taken. -/
def codeTable : List Decoded :=
  match decodeImage with
  | .ok t => t
  | .error _ => []

/-- The instruction at `addr` (at load base 0), if one starts there. -/
def instrAt (addr : UInt64) : Option Decoded := codeTable.find? (·.addr == addr)

end ValidateFeePayer.X86
