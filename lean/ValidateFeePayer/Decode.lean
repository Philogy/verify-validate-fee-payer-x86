import ValidateFeePayer.Instruction
import ValidateFeePayer.Image

/-!
A strict decoder for exactly the encodings the carved code uses.

Strict means that anything this file does not list is a `DecodeError`, even
where the CPU would accept it: other opcodes, other prefixes (lock, segment
overrides, `0x67`, a second prefix), `0x66` on integer instructions,
register-extension bits the instruction does not use (e.g. `REX.W` on
`push`, `REX.B` with a rip-relative operand, `REX.X` without an index
register), a nonzero scale without an index, the high-byte registers
`ah`/`ch`/`dh`/`bh`, and nonzero reserved fields of the operand byte
(`setcc`'s middle field). So a decoded instruction always means what
`Instruction` says, with no ignored bits.

Terms, since x86 encodings are full of them: an instruction is
`[prefix] [register-extension byte (REX)] opcode [operand byte (ModRM)
[scale-index-base byte (SIB)] [displacement]] [immediate]`.

The decoder is run once over the carved code (`decodeImage`, a linear sweep
from each function's start to its end); `codeTable` is the result, and the
machine looks instructions up there. `Checks.lean` proves that the sweep
succeeds and matches llvm-objdump's disassembly instruction for instruction.
-/

namespace ValidateFeePayer.X86

inductive DecodeError where
  | truncated
  | unsupported (what : String)
  deriving DecidableEq, Repr

/-- Decoding consumes bytes from the front of the list. -/
abbrev Decoder := StateT (List UInt8) (Except DecodeError)

namespace Decode

def nextByte : Decoder UInt8 := do
  match ← get with
  | [] => throw .truncated
  | b :: rest => set rest; pure b

def require (ok : Bool) (what : String) : Decoder Unit :=
  unless ok do throw (.unsupported what)

/-- `n` bytes, little-endian, unsigned. -/
def unsignedBytes : Nat → Decoder Nat
  | 0 => pure 0
  | n + 1 => do
    let low ← nextByte
    let high ← unsignedBytes n
    pure (low.toNat + 256 * high)

/-- `n` bytes, little-endian, two's complement. -/
def signedBytes (n : Nat) : Decoder Int := do
  let v ← unsignedBytes n
  pure (if v < 2 ^ (8 * n - 1) then v else v - 2 ^ (8 * n))

/-- Two's-complement wraparound into 64 bits. -/
def wrapToUInt64 (v : Int) : UInt64 := (v % 2 ^ 64).toNat.toUInt64

def registerNumbered (n : Nat) : Register := Register.ofIndex ⟨n % 16, Nat.mod_lt _ (by decide)⟩

def vectorRegisterNumbered (n : Nat) : VectorRegister := ⟨n % 16, Nat.mod_lt _ (by decide)⟩

/-- The optional register-extension byte `0x40`–`0x4f` (x86: the REX prefix).
Each bit adds 8 to one register number, so that 16 registers can be named,
except `wide`. -/
structure RegisterExtension where
  /-- The byte is present (changes the meaning of 8-bit registers 4–7). -/
  present : Bool
  /-- 64-bit operand size (x86: `REX.W`). -/
  wide : Bool
  /-- Extends the operand byte's middle field (x86: `REX.R`). -/
  extendsMiddle : Bool
  /-- Extends the index register (x86: `REX.X`). -/
  extendsIndex : Bool
  /-- Extends the base or `r/m` register (x86: `REX.B`). -/
  extendsBase : Bool

def RegisterExtension.none : RegisterExtension := ⟨false, false, false, false, false⟩

def RegisterExtension.ofByte (v : UInt8) : RegisterExtension :=
  ⟨true, v &&& 8 != 0, v &&& 4 != 0, v &&& 2 != 0, v &&& 1 != 0⟩

/-- What an extension bit adds to a register number. -/
def extension (b : Bool) : Nat := if b then 8 else 0

/-- The operands an operand byte (x86: ModRM) and what follows it describe. -/
structure Operands where
  /-- The operand byte's middle field (x86: the `reg` field), without the
  extension bit: a register number, or for some opcodes a sub-opcode. -/
  middle : Nat
  /-- The register-or-memory operand, with the extension bits applied. -/
  operand : RegisterOrMemory

def displacement (mode : Nat) : Decoder Int :=
  match mode with
  | 1 => signedBytes 1
  | 2 => signedBytes 4
  | _ => pure 0

/-- The operand byte, then the scale-index-base byte and displacement if
present. Rejects `extendsIndex` and `extendsBase` where the operand does not
use them; the caller checks `extendsMiddle`. -/
def operands (ext : RegisterExtension) : Decoder Operands := do
  let byte := (← nextByte).toNat
  let mode := byte >>> 6
  let middle := (byte >>> 3) % 8
  let low := byte % 8
  if mode = 3 then
    require (!ext.extendsIndex) "REX.X without a SIB index"
    return ⟨middle, .register (registerNumbered (low + extension ext.extendsBase))⟩
  if low = 4 then
    let sib := (← nextByte).toNat
    let scale := sib >>> 6
    let indexNumber := (sib >>> 3) % 8 + extension ext.extendsIndex
    let index := if indexNumber = 4 then none
      else some (registerNumbered indexNumber, (⟨scale % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4))
    require (index.isSome || scale = 0) "SIB scale without an index"
    if sib % 8 = 5 && mode = 0 then
      require (!ext.extendsBase) "REX.B on a SIB without base"
      return ⟨middle, .memory (.baseIndex none index (← signedBytes 4))⟩
    return ⟨middle, .memory (.baseIndex (some (registerNumbered (sib % 8 + extension ext.extendsBase)))
      index (← displacement mode))⟩
  require (!ext.extendsIndex) "REX.X without a SIB index"
  if mode = 0 && low = 5 then
    require (!ext.extendsBase) "REX.B on a rip-relative operand"
    return ⟨middle, .memory (.relativeToNextInstruction (← signedBytes 4))⟩
  return ⟨middle, .memory (.baseIndex (some (registerNumbered (low + extension ext.extendsBase))) none
    (← displacement mode))⟩

/-- An 8-bit register operand: without the extension byte, numbers 4–7 are
the high-byte registers `ah`…`bh`, which the model does not have. -/
def byteOperand (ext : RegisterExtension) (x : RegisterOrMemory) : Decoder RegisterOrMemory := do
  if let .register r := x then
    require (ext.present || r.index.val < 4) "ah/ch/dh/bh"
  pure x

def toVectorOperand : RegisterOrMemory → VectorOrMemory
  | .register r => .register r.index
  | .memory a => .memory a

/-- The operation of `op r/m, r` opcodes (`0x00`…`0x3f`, `0x84`/`0x85`). -/
def arithmeticOfOpcode : Nat → Option ArithmeticOp
  | 0x00 | 0x01 => some .add
  | 0x08 | 0x09 => some .or
  | 0x18 | 0x19 => some .subtractWithBorrow
  | 0x20 | 0x21 => some .and
  | 0x28 | 0x29 => some .subtract
  | 0x30 | 0x31 => some .xor
  | 0x38 | 0x39 => some .compare
  | 0x84 | 0x85 => some .testBits
  | _ => none

/-- The operation of opcodes `0x81`/`0x83` (x86: "group 1") by the operand
byte's middle field. Add-with-carry (2) does not occur. -/
def arithmeticOfSubOpcode : Nat → Option ArithmeticOp
  | 0 => some .add | 1 => some .or | 3 => some .subtractWithBorrow | 4 => some .and
  | 5 => some .subtract | 6 => some .xor | 7 => some .compare
  | _ => none

/-- Instructions without a mandatory prefix. -/
def integerInstruction (ext : RegisterExtension) (opcode : Nat) : Decoder Instruction := do
  let size : OperandSize := if ext.wide then .bits64 else .bits32
  -- Opcodes with the register number in their low bits use only `extendsBase`.
  let registerInOpcode : Decoder Register := do
    require (!ext.wide && !ext.extendsMiddle && !ext.extendsIndex) "REX bits on push/pop"
    pure (registerNumbered (opcode % 8 + extension ext.extendsBase))
  -- Relative branches and `ret` take no extension byte at all.
  let noExtension : Decoder Unit := require (!ext.present) "REX on a branch"
  let middleRegister (ops : Operands) : Register :=
    registerNumbered (ops.middle + extension ext.extendsMiddle)
  if 0x50 ≤ opcode && opcode ≤ 0x57 then return .push (← registerInOpcode)
  if 0x58 ≤ opcode && opcode ≤ 0x5f then return .pop (← registerInOpcode)
  if 0x70 ≤ opcode && opcode ≤ 0x7f then
    noExtension; return .jumpIf (Condition.ofCode (opcode - 0x70)) (← signedBytes 1)
  if 0xb8 ≤ opcode && opcode ≤ 0xbf then
    require (!ext.extendsMiddle && !ext.extendsIndex) "REX.R/X on mov r, imm"
    let r := registerNumbered (opcode % 8 + extension ext.extendsBase)
    if ext.wide then return .moveImmediate64 r (← unsignedBytes 8).toUInt64
    else return .move .bits32 (.register r) (.immediate (← unsignedBytes 4).toUInt64)
  if let some op := arithmeticOfOpcode opcode then
    let ops ← operands ext
    let source := middleRegister ops
    if opcode % 2 = 0 then
      require (!ext.wide) "REX.W on an 8-bit operation"
      let destination ← byteOperand ext ops.operand
      let source ← byteOperand ext (.register source)
      return .arithmetic op .bits8 destination (.operand source)
    return .arithmetic op size ops.operand (.operand (.register source))
  match opcode with
  | 0xeb => noExtension; return .jump (← signedBytes 1)
  | 0xe9 => noExtension; return .jump (← signedBytes 4)
  | 0xc3 => noExtension; return .returnToCaller
  | 0x81 | 0x83 =>
    let ops ← operands ext
    require (!ext.extendsMiddle) "REX.R on an opcode extension"
    let some op := arithmeticOfSubOpcode ops.middle | throw (.unsupported "group 1 operation")
    let immediate ← signedBytes (if opcode = 0x83 then 1 else 4)
    return .arithmetic op size ops.operand (.immediate (wrapToUInt64 immediate))
  | 0x89 =>
    let ops ← operands ext
    return .move size ops.operand (.operand (.register (middleRegister ops)))
  | 0x8b =>
    let ops ← operands ext
    return .move size (.register (middleRegister ops)) (.operand ops.operand)
  | 0x88 =>
    require (!ext.wide) "REX.W on an 8-bit operation"
    let ops ← operands ext
    let destination ← byteOperand ext ops.operand
    let source ← byteOperand ext (.register (middleRegister ops))
    return .move .bits8 destination (.operand source)
  | 0xc7 =>
    let ops ← operands ext
    require (!ext.extendsMiddle && ops.middle = 0) "c7 extension"
    return .move size ops.operand (.immediate (wrapToUInt64 (← signedBytes 4)))
  | 0x8d =>
    require ext.wide "lea without REX.W"
    let ops ← operands ext
    let .memory a := ops.operand | throw (.unsupported "lea of a register")
    return .loadAddress (middleRegister ops) a
  | 0xff =>
    let ops ← operands ext
    require (!ext.extendsMiddle) "REX.R on an opcode extension"
    match ops.middle with
    | 0 => return .increment size ops.operand
    | 2 => require (!ext.wide) "REX.W on call"; return .call ops.operand
    | _ => throw (.unsupported "group 5 operation")
  | 0x69 =>
    require ext.wide "32-bit imul"
    let ops ← operands ext
    return .multiplySigned (middleRegister ops) ops.operand (some (wrapToUInt64 (← signedBytes 4)))
  | 0xc1 =>
    require ext.wide "32-bit shift"
    let ops ← operands ext
    require (!ext.extendsMiddle && ops.middle = 7) "shift other than sar"
    return .shiftRightSigned ops.operand (← nextByte)
  | 0x0f =>
    let opcode2 := (← nextByte).toNat
    if 0x80 ≤ opcode2 && opcode2 ≤ 0x8f then
      noExtension; return .jumpIf (Condition.ofCode (opcode2 - 0x80)) (← signedBytes 4)
    if 0x90 ≤ opcode2 && opcode2 ≤ 0x9f then
      require (!ext.wide) "REX.W on setcc"
      let ops ← operands ext
      require (!ext.extendsMiddle && ops.middle = 0) "setcc reg field"
      return .setIf (Condition.ofCode (opcode2 - 0x90)) (← byteOperand ext ops.operand)
    if 0x40 ≤ opcode2 && opcode2 ≤ 0x4f then
      let ops ← operands ext
      return .moveIf (Condition.ofCode (opcode2 - 0x40)) size (middleRegister ops) ops.operand
    match opcode2 with
    | 0xaf =>
      require ext.wide "32-bit imul"
      let ops ← operands ext
      return .multiplySigned (middleRegister ops) ops.operand none
    | 0xb6 =>
      let ops ← operands ext
      return .moveZeroExtendByte size (middleRegister ops) (← byteOperand ext ops.operand)
    | _ => throw (.unsupported "0f opcode")
  | _ => throw (.unsupported "opcode")

/-- Instructions with a mandatory `0x66`, `0xf2` or `0xf3` prefix: the vector
(x86: SSE) instructions. -/
def vectorInstruction (pfx : Nat) (ext : RegisterExtension) (opcode : Nat) : Decoder Instruction := do
  require (opcode = 0x0f) "prefix on a non-SSE opcode"
  let opcode2 := (← nextByte).toNat
  -- `movq` and `cvttsd2si` need `REX.W` (without it they are 32-bit forms);
  -- every other one rejects it.
  require (ext.wide == (pfx = 0x66 && opcode2 = 0x6e || pfx = 0xf2 && opcode2 = 0x2c)) "REX.W"
  let opcode2 ← if pfx = 0x66 && opcode2 = 0x38 then do
      require ((← nextByte).toNat = 0x17) "0f 38 opcode"; pure 0x3817
    else pure opcode2
  let ops ← operands ext
  let destination := vectorRegisterNumbered (ops.middle + extension ext.extendsMiddle)
  let source := toVectorOperand ops.operand
  match pfx, opcode2 with
  | 0xf3, 0x6f => return .moveVectorUnaligned destination source
  | 0x66, 0x28 => return .moveVectorAligned destination source
  | 0x66, 0x6e => return .moveIntegerToVector destination ops.operand
  | 0x66, 0xef => return .vectorBitwise .xor destination source
  | 0x66, 0xeb => return .vectorBitwise .or destination source
  | 0x66, 0x57 => return .vectorBitwise .xorDoubles destination source
  | 0x66, 0x3817 => return .testVectorBits destination source
  | 0x66, 0x62 => return .interleaveLow32 destination source
  | 0x66, 0x15 => return .interleaveHighDoubles destination source
  | 0x66, 0x5c => return .subtractDoublePairs destination source
  | 0xf2, 0x58 => return .scalarDouble .add destination source
  | 0xf2, 0x5c => return .scalarDouble .subtract destination source
  | 0xf2, 0x59 => return .scalarDouble .multiply destination source
  | 0x66, 0x2e => return .compareDoubles destination source
  | 0xf2, 0x2c =>
    return .truncateDoubleToInt64 (registerNumbered (ops.middle + extension ext.extendsMiddle)) source
  | _, _ => throw (.unsupported "SSE opcode")

/-- One instruction: at most one of the prefixes `0x66`/`0xf2`/`0xf3`, an
optional register-extension byte, then the opcode. -/
def instruction : Decoder Instruction := do
  let b := (← nextByte).toNat
  let (pfx, b) ← if b = 0x66 || b = 0xf2 || b = 0xf3 then do pure (some b, (← nextByte).toNat)
    else pure (none, b)
  let (ext, opcode) ← if b >>> 4 = 4 then do pure (RegisterExtension.ofByte b.toUInt8, (← nextByte).toNat)
    else pure (RegisterExtension.none, b)
  match pfx with
  | none => integerInstruction ext opcode
  | some p => vectorInstruction p ext opcode

end Decode

/-- The instruction at the start of `bytes`, and its length. -/
def decode (bytes : List UInt8) : Except DecodeError (Instruction × Nat) := do
  let (i, rest) ← Decode.instruction.run bytes
  let length := bytes.length - rest.length
  unless length ≤ 15 do throw (.unsupported "longer than 15 bytes")
  pure (i, length)

/-- A decoded instruction at its address (at load base 0). -/
structure Decoded where
  address : UInt64
  instruction : Instruction
  length : Nat
  deriving DecidableEq, Repr

/-- Decode back to back from `address` until the bytes run out. `fuel`
bounds the number of instructions (each is at least one byte). -/
def sweep : (fuel : Nat) → (address : UInt64) → List UInt8 →
    Except (UInt64 × DecodeError) (List Decoded)
  | _, _, [] => pure []
  | 0, address, _ => throw (address, .unsupported "out of fuel")
  | fuel + 1, address, bytes => do
    let (i, length) ← (decode bytes).mapError (address, ·)
    let rest ← sweep fuel (address + length.toUInt64) (bytes.drop length)
    pure (⟨address, i, length⟩ :: rest)

def decodeRegion (r : Region) : Except (UInt64 × DecodeError) (List Decoded) :=
  match r.contents with
  | .code bytes => sweep bytes.size r.address bytes.toList
  | _ => throw (r.address, .unsupported "not a code region")

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

/-- The instruction at `address` (at load base 0), if one starts there. -/
def instructionAt (address : UInt64) : Option Decoded := codeTable.find? (·.address == address)

end ValidateFeePayer.X86
