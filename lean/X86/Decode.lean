import X86.Instruction
import X86.Fault

/-!
`decodeBytes` is the encoding grammar (legacy prefixes, REX, the one-byte,
`0x0f` and `0x0f 0x38` opcode maps, ModRM, SIB, displacement, immediate) for
the forms in `Instruction`. `decode` applies it to memory at an address,
fetching one byte at a time, so it has no notion of where instructions
start: a jump into the middle of an instruction decodes whatever the bytes
from there say, as on the CPU.

The decoder is strict: it rejects encodings the CPU accepts but whose bits
it would ignore (an unused REX bit, a REX byte not right before the opcode,
a repeated prefix, `0x66` where it changes nothing, a scale without an
index, a nonzero ignored ModRM field). A decoded instruction therefore
means exactly what `Instruction` says, which a proof can rely on without
re-checking the bytes.
-/

namespace X86

abbrev Decoder := StateT (List UInt8) (Except DecodeError)

namespace Decode

def nextByte : Decoder UInt8 := do
  match ← get with
  | [] => throw .truncated
  | b :: rest => set rest; pure b

def require (ok : Bool) (what : String) : Decoder Unit :=
  unless ok do throw (.unsupported what)

def nextBytes : Nat → Decoder (List UInt8)
  | 0 => pure []
  | n + 1 => do
    let b ← nextByte
    return b :: (← nextBytes n)

def signedImmediate (size : OperandSize) : Decoder UInt64 := do
  return size.signExtend (ofLittleEndian (← nextBytes size.byteCount))

def registerNumbered (n : UInt8) : Register := Register.ofIndex (Fin.ofNat 16 (n &&& 15).toNat)

def vectorRegisterNumbered (n : UInt8) : VectorRegister := Fin.ofNat 16 (n &&& 15).toNat

structure Rex where
  present : Bool
  wide : Bool
  extendsMiddle : Bool
  extendsIndex : Bool
  extendsBase : Bool

def Rex.none : Rex := ⟨false, false, false, false, false⟩

def Rex.ofByte (v : UInt8) : Rex := ⟨true, v &&& 8 != 0, v &&& 4 != 0, v &&& 2 != 0, v &&& 1 != 0⟩

def extension (b : Bool) : UInt8 := if b then 8 else 0

structure Prefixes where
  operandSizeOverride : Bool := false
  repeatPrefix : Option UInt8 := Option.none
  rex : Rex := .none

def Prefixes.size (p : Prefixes) : OperandSize :=
  if p.rex.wide then .bits64 else if p.operandSizeOverride then .bits16 else .bits32

def isLegacyPrefix (b : UInt8) : Bool :=
  b == 0x66 || b == 0xf2 || b == 0xf3 || b == 0xf0 || b == 0x67 ||
  b == 0x2e || b == 0x36 || b == 0x3e || b == 0x26 || b == 0x64 || b == 0x65

def isRex (b : UInt8) : Bool := b >>> 4 == 4

def addPrefix (p : Prefixes) (b : UInt8) : Decoder Prefixes :=
  if b = 0x66 then do
    require (!p.operandSizeOverride) "0x66 twice"
    pure { p with operandSizeOverride := true }
  else if b = 0xf2 || b = 0xf3 then do
    require p.repeatPrefix.isNone "two of 0xf2/0xf3"
    pure { p with repeatPrefix := some b }
  else if b = 0xf0 then throw (.unsupported "lock prefix")
  else if b = 0x67 then throw (.unsupported "address-size prefix")
  else if b = 0x64 || b = 0x65 then throw (.unsupported "fs/gs segment prefix")
  else throw (.unsupported "segment prefix")

-- Each supported prefix may occur once and `0xf2`/`0xf3` exclude each other,
-- so at most two prefixes can precede the opcode.
def prefixesAndOpcode : Decoder (Prefixes × UInt8) := do
  let b ← nextByte
  let (p, b) ← if isLegacyPrefix b then do pure (← addPrefix {} b, ← nextByte) else pure ({}, b)
  let (p, b) ← if isLegacyPrefix b then do pure (← addPrefix p b, ← nextByte) else pure (p, b)
  require (!isLegacyPrefix b) "more than two prefixes"
  if isRex b then
    let opcode ← nextByte
    require (!isLegacyPrefix opcode && !isRex opcode) "REX not immediately before the opcode"
    pure ({ p with rex := .ofByte b }, opcode)
  else pure (p, b)

/-- The r/m operand before its size is known. -/
inductive RawOperand where
  | register (n : UInt8)
  | memory (a : Address)

structure ModRM where
  middle : UInt8
  operand : RawOperand

def displacement (mode : UInt8) : Decoder UInt64 :=
  match mode with
  | 1 => signedImmediate .bits8
  | 2 => signedImmediate .bits32
  | _ => pure 0

def modrm (rex : Rex) : Decoder ModRM := do
  let byte ← nextByte
  let mode := byte >>> 6
  let middle := (byte >>> 3) &&& 7
  let low := byte &&& 7
  if mode = 3 then
    require (!rex.extendsIndex) "REX.X without a SIB index"
    return ⟨middle, .register (low + extension rex.extendsBase)⟩
  if low = 4 then
    let sib ← nextByte
    let scale := sib >>> 6
    let indexNumber := ((sib >>> 3) &&& 7) + extension rex.extendsIndex
    let index := if indexNumber = 4 then none
      else some (registerNumbered indexNumber, Fin.ofNat 4 scale.toNat)
    require (index.isSome || scale = 0) "SIB scale without an index"
    if sib &&& 7 = 5 && mode = 0 then
      require (!rex.extendsBase) "REX.B on a SIB without base"
      return ⟨middle, .memory (.baseIndex none index (← signedImmediate .bits32))⟩
    return ⟨middle, .memory (.baseIndex (some (registerNumbered ((sib &&& 7) + extension rex.extendsBase)))
      index (← displacement mode))⟩
  require (!rex.extendsIndex) "REX.X without a SIB index"
  if mode = 0 && low = 5 then
    require (!rex.extendsBase) "REX.B on a rip-relative operand"
    return ⟨middle, .memory (.relativeToNextInstruction (← signedImmediate .bits32))⟩
  return ⟨middle, .memory (.baseIndex (some (registerNumbered (low + extension rex.extendsBase))) none
    (← displacement mode))⟩

def generalRegister (rex : Rex) (size : OperandSize) (n : UInt8) : RegisterOrMemory :=
  if size = .bits8 && !rex.present && 4 ≤ n && n < 8 then .highByte (registerNumbered (n - 4))
  else .register (registerNumbered n)

def ModRM.rm (o : ModRM) (rex : Rex) (size : OperandSize) : RegisterOrMemory :=
  match o.operand with
  | .register n => generalRegister rex size n
  | .memory a => .memory a

def ModRM.reg (o : ModRM) (rex : Rex) (size : OperandSize) : RegisterOrMemory :=
  generalRegister rex size (o.middle + extension rex.extendsMiddle)

def ModRM.register (o : ModRM) (rex : Rex) : Register :=
  registerNumbered (o.middle + extension rex.extendsMiddle)

def ModRM.vectorRm (o : ModRM) : VectorOrMemory :=
  match o.operand with
  | .register n => .register (vectorRegisterNumbered n)
  | .memory a => .memory a

def ModRM.vectorReg (o : ModRM) (rex : Rex) : VectorRegister :=
  vectorRegisterNumbered (o.middle + extension rex.extendsMiddle)

-- x86 has no 64-bit immediates except `movabs`; 64-bit forms take 32 bits.
def immediate (size : OperandSize) : Decoder UInt64 :=
  signedImmediate (if size = .bits64 then .bits32 else size)

def byteForm (p : Prefixes) : Decoder Unit :=
  require (!p.rex.wide && !p.operandSizeOverride) "REX.W or 0x66 on an 8-bit operation"

def subOpcode (p : Prefixes) : Decoder Unit := require (!p.rex.extendsMiddle) "REX.R on a sub-opcode"

def noModRM (p : Prefixes) : Decoder Unit :=
  require (!p.rex.extendsMiddle && !p.rex.extendsIndex) "REX.R/X without ModRM"

def accumulatorForm (p : Prefixes) : Decoder Unit := do
  noModRM p; require (!p.rex.extendsBase) "REX.B on an accumulator form"

def fixed64 (p : Prefixes) : Decoder Unit :=
  require (!p.rex.wide && !p.operandSizeOverride) "REX.W or 0x66 on a 64-bit-only operation"

def branchForm (p : Prefixes) : Decoder Unit :=
  require (!p.rex.present && !p.operandSizeOverride) "REX or 0x66 on a branch"

def shiftOp : UInt8 → Decoder ShiftOp
  | 4 => pure .left
  | 5 => pure .rightLogical
  | 7 => pure .rightArithmetic
  | _ => throw (.unsupported "rotate or sal (group 2)")

def oneByte (p : Prefixes) (opcode : UInt8) : Decoder Instruction := do
  let rex := p.rex
  let size := p.size
  if opcode < 0x40 && opcode &&& 7 < 6 then
    let op := ArithmeticOp.ofCode (opcode >>> 3)
    match opcode &&& 7 with
    | 0 | 2 =>
      byteForm p
      let o ← modrm rex
      return if opcode &&& 7 = 0 then .arithmetic op .bits8 (o.rm rex .bits8) (.operand (o.reg rex .bits8))
        else .arithmetic op .bits8 (o.reg rex .bits8) (.operand (o.rm rex .bits8))
    | 1 | 3 =>
      let o ← modrm rex
      return if opcode &&& 7 = 1 then .arithmetic op size (o.rm rex size) (.operand (o.reg rex size))
        else .arithmetic op size (o.reg rex size) (.operand (o.rm rex size))
    | 4 =>
      byteForm p; accumulatorForm p
      return .arithmetic op .bits8 (.register .accumulator) (.immediate (← immediate .bits8))
    | _ =>
      accumulatorForm p
      return .arithmetic op size (.register .accumulator) (.immediate (← immediate size))
  if 0x50 ≤ opcode && opcode ≤ 0x5f then
    fixed64 p; noModRM p
    let r := registerNumbered ((opcode &&& 7) + extension rex.extendsBase)
    return if opcode < 0x58 then .push (.operand (.register r)) else .pop (.register r)
  if 0x70 ≤ opcode && opcode ≤ 0x7f then
    branchForm p; return .jumpIf (Condition.ofCode opcode) (← signedImmediate .bits8)
  if 0xb0 ≤ opcode && opcode ≤ 0xb7 then
    byteForm p; noModRM p
    return .move .bits8 (generalRegister rex .bits8 ((opcode &&& 7) + extension rex.extendsBase))
      (.immediate (← immediate .bits8))
  if 0xb8 ≤ opcode && opcode ≤ 0xbf then
    noModRM p
    let r := registerNumbered ((opcode &&& 7) + extension rex.extendsBase)
    if rex.wide then return .moveImmediate64 r (ofLittleEndian (← nextBytes 8))
    return .move size (.register r) (.immediate (← immediate size))
  match opcode with
  | 0x63 =>
    require (rex.wide && !p.operandSizeOverride) "movsxd without REX.W"
    let o ← modrm rex
    return .moveSignExtend .bits64 (o.register rex) .bits32 (o.rm rex .bits32)
  | 0x68 | 0x6a =>
    require (!rex.present && !p.operandSizeOverride) "REX or 0x66 on push imm"
    return .push (.immediate (← signedImmediate (if opcode = 0x6a then .bits8 else .bits32)))
  | 0x69 | 0x6b =>
    let o ← modrm rex
    let v ← if opcode = 0x6b then signedImmediate .bits8 else immediate size
    return .multiplySigned size (o.register rex) (o.rm rex size) (some v)
  | 0x80 | 0x81 | 0x83 =>
    if opcode = 0x80 then byteForm p
    let size := if opcode = 0x80 then .bits8 else size
    let o ← modrm rex
    subOpcode p
    let v ← if opcode = 0x83 then signedImmediate .bits8 else immediate size
    return .arithmetic (ArithmeticOp.ofCode o.middle) size (o.rm rex size) (.immediate v)
  | 0x84 =>
    byteForm p
    let o ← modrm rex
    return .arithmetic .testBits .bits8 (o.rm rex .bits8) (.operand (o.reg rex .bits8))
  | 0x85 =>
    let o ← modrm rex
    return .arithmetic .testBits size (o.rm rex size) (.operand (o.reg rex size))
  | 0x88 =>
    byteForm p
    let o ← modrm rex
    return .move .bits8 (o.rm rex .bits8) (.operand (o.reg rex .bits8))
  | 0x89 =>
    let o ← modrm rex
    return .move size (o.rm rex size) (.operand (o.reg rex size))
  | 0x8a =>
    byteForm p
    let o ← modrm rex
    return .move .bits8 (o.reg rex .bits8) (.operand (o.rm rex .bits8))
  | 0x8b =>
    let o ← modrm rex
    return .move size (o.reg rex size) (.operand (o.rm rex size))
  | 0x8d =>
    let o ← modrm rex
    let .memory a := o.operand | throw (.unsupported "lea of a register")
    return .loadAddress size (o.register rex) a
  | 0x8f =>
    fixed64 p
    let o ← modrm rex
    subOpcode p; require (o.middle = 0) "8f sub-opcode"
    return .pop (o.rm rex .bits64)
  | 0x90 =>
    -- With REX.B this is `xchg r8, rax`, and with `0xf3` it is `pause`.
    require (!rex.present) "REX on nop"
    return .noOperation none
  | 0x98 => accumulatorForm p; return .signExtendAccumulator size
  | 0x99 => accumulatorForm p; return .signExtendIntoData size
  | 0xa8 =>
    byteForm p; accumulatorForm p
    return .arithmetic .testBits .bits8 (.register .accumulator) (.immediate (← immediate .bits8))
  | 0xa9 =>
    accumulatorForm p
    return .arithmetic .testBits size (.register .accumulator) (.immediate (← immediate size))
  | 0xc0 | 0xc1 | 0xd0 | 0xd1 | 0xd2 | 0xd3 =>
    let byteSized := opcode &&& 1 = 0
    if byteSized then byteForm p
    let size := if byteSized then .bits8 else size
    let o ← modrm rex
    subOpcode p
    let op ← shiftOp o.middle
    let count ← if opcode < 0xd0 then do pure (ShiftCount.immediate (← nextByte))
      else if opcode < 0xd2 then pure .one else pure .counter
    return .shift op size (o.rm rex size) count
  | 0xc3 => branchForm p; return .returnToCaller
  | 0xc6 | 0xc7 =>
    if opcode = 0xc6 then byteForm p
    let size := if opcode = 0xc6 then .bits8 else size
    let o ← modrm rex
    subOpcode p; require (o.middle = 0) "c6/c7 sub-opcode"
    return .move size (o.rm rex size) (.immediate (← immediate size))
  | 0xe8 => branchForm p; return .callRelative (← signedImmediate .bits32)
  | 0xe9 => branchForm p; return .jump (← signedImmediate .bits32)
  | 0xeb => branchForm p; return .jump (← signedImmediate .bits8)
  | 0xf6 | 0xf7 =>
    if opcode = 0xf6 then byteForm p
    let size := if opcode = 0xf6 then .bits8 else size
    let o ← modrm rex
    subOpcode p
    match o.middle with
    | 0 => return .arithmetic .testBits size (o.rm rex size) (.immediate (← immediate size))
    | 2 => return .complement size (o.rm rex size)
    | 3 => return .negate size (o.rm rex size)
    | _ => throw (.unsupported "multiply/divide (group 3)")
  | 0xfe =>
    byteForm p
    let o ← modrm rex
    subOpcode p
    match o.middle with
    | 0 => return .increment .bits8 (o.rm rex .bits8)
    | 1 => return .decrement .bits8 (o.rm rex .bits8)
    | _ => throw (.unsupported "fe sub-opcode")
  | 0xff =>
    let o ← modrm rex
    subOpcode p
    match o.middle with
    | 0 => return .increment size (o.rm rex size)
    | 1 => return .decrement size (o.rm rex size)
    | 2 => fixed64 p; return .call (o.rm rex .bits64)
    | 4 => fixed64 p; return .jumpIndirect (o.rm rex .bits64)
    | 6 => fixed64 p; return .push (.operand (o.rm rex .bits64))
    | _ => throw (.unsupported "far call/jmp (group 5)")
  | _ => throw (.unsupported "one-byte opcode")

def twoByteInteger (p : Prefixes) (opcode : UInt8) : Option (Decoder Instruction) :=
  let rex := p.rex
  let size := p.size
  if opcode = 0x1f then some do
    let o ← modrm rex
    subOpcode p; require (o.middle = 0) "0f 1f sub-opcode"
    return .noOperation (some (size, o.rm rex size))
  else if 0x40 ≤ opcode && opcode ≤ 0x4f then some do
    let o ← modrm rex
    return .moveIf (Condition.ofCode opcode) size (o.register rex) (o.rm rex size)
  else if 0x80 ≤ opcode && opcode ≤ 0x8f then some do
    branchForm p; return .jumpIf (Condition.ofCode opcode) (← signedImmediate .bits32)
  else if 0x90 ≤ opcode && opcode ≤ 0x9f then some do
    byteForm p
    let o ← modrm rex
    subOpcode p; require (o.middle = 0) "setcc middle field"
    return .setIf (Condition.ofCode opcode) (o.rm rex .bits8)
  else if opcode = 0xaf then some do
    let o ← modrm rex
    return .multiplySigned size (o.register rex) (o.rm rex size) none
  else if opcode = 0xb6 || opcode = 0xb7 || opcode = 0xbe || opcode = 0xbf then some do
    let o ← modrm rex
    let sourceSize := if opcode &&& 1 = 0 then .bits8 else .bits16
    let source := o.rm rex sourceSize
    return if opcode < 0xbe then .moveZeroExtend size (o.register rex) sourceSize source
      else .moveSignExtend size (o.register rex) sourceSize source
  else none

inductive MandatoryPrefix where
  | none | operandSize | f2 | f3
  deriving DecidableEq

def vector (p : Prefixes) (mandatory : MandatoryPrefix) (opcode : UInt8) : Decoder Instruction := do
  let rex := p.rex
  let integerSized := (mandatory = .operandSize && (opcode = 0x6e || opcode = 0x7e)) ||
    (mandatory = .f2 && opcode = 0x2c)
  require (integerSized || !rex.wide) "REX.W on an SSE instruction"
  let integerSize : OperandSize := if rex.wide then .bits64 else .bits32
  let load (f : VectorRegister → VectorOrMemory → Instruction) : Decoder Instruction := do
    let o ← modrm rex
    return f (o.vectorReg rex) o.vectorRm
  let move (kind : VectorMove) (store : Bool) : Decoder Instruction := do
    let o ← modrm rex
    return if store then .moveVector kind o.vectorRm (.register (o.vectorReg rex))
      else .moveVector kind (.register (o.vectorReg rex)) o.vectorRm
  let integerBitwise : Option VectorBitwiseOp :=
    match opcode with
    | 0xdb => some .and | 0xdf => some .andNot | 0xeb => some .or | 0xef => some .xor | _ => none
  let floatBitwise : Option VectorBitwiseOp :=
    match opcode with
    | 0x54 => some .and | 0x55 => some .andNot | 0x56 => some .or | 0x57 => some .xor | _ => none
  let double : Option DoubleOp :=
    match opcode with | 0x58 => some .add | 0x59 => some .multiply | 0x5c => some .subtract | _ => none
  match mandatory, opcode with
  | .none, 0x10 | .none, 0x11 => move .singleUnaligned (opcode = 0x11)
  | .none, 0x28 | .none, 0x29 => move .singleAligned (opcode = 0x29)
  | .operandSize, 0x10 | .operandSize, 0x11 => move .doubleUnaligned (opcode = 0x11)
  | .operandSize, 0x28 | .operandSize, 0x29 => move .doubleAligned (opcode = 0x29)
  | .operandSize, 0x6f | .operandSize, 0x7f => move .integerAligned (opcode = 0x7f)
  | .f3, 0x6f | .f3, 0x7f => move .integerUnaligned (opcode = 0x7f)
  | .operandSize, 0x6e =>
    let o ← modrm rex
    return .moveIntegerToVector integerSize (o.vectorReg rex) (o.rm rex integerSize)
  | .operandSize, 0x7e =>
    let o ← modrm rex
    return .moveVectorToInteger integerSize (o.rm rex integerSize) (o.vectorReg rex)
  | .f2, 0x10 => load fun d s => .moveScalarDouble (.register d) s
  | .f2, 0x11 =>
    let o ← modrm rex
    return .moveScalarDouble o.vectorRm (.register (o.vectorReg rex))
  | .operandSize, 0x62 => load .interleaveLow32
  | .operandSize, 0x6c => load .interleaveLow64
  | .operandSize, 0x14 => load .interleaveLowDoubles
  | .operandSize, 0x15 => load .interleaveHighDoubles
  | .operandSize, 0x2e => load .compareDoubles
  | .f2, 0x2c =>
    require rex.wide "cvttsd2si r32"
    let o ← modrm rex
    return .truncateDoubleToInt64 (o.register rex) o.vectorRm
  | .none, _ =>
    let some op := floatBitwise | throw (.unsupported "SSE opcode")
    load (.vectorBitwise op .single)
  | .operandSize, _ =>
    if let some op := integerBitwise then load (.vectorBitwise op .integer)
    else if let some op := floatBitwise then load (.vectorBitwise op .double)
    else if let some op := double then load (.packedDouble op)
    else throw (.unsupported "SSE opcode")
  | .f2, _ =>
    let some op := double | throw (.unsupported "SSE opcode")
    load (.scalarDouble op)
  | .f3, _ => throw (.unsupported "SSE opcode")

def twoByte (p : Prefixes) (opcode : UInt8) : Decoder Instruction := do
  if p.repeatPrefix.isNone then
    if let some d := twoByteInteger p opcode then return ← d
  require (!(p.operandSizeOverride && p.repeatPrefix.isSome)) "0x66 with 0xf2/0xf3"
  let mandatory : MandatoryPrefix := match p.repeatPrefix with
    | some 0xf2 => .f2 | some _ => .f3 | none => if p.operandSizeOverride then .operandSize else .none
  if opcode = 0x38 then
    let opcode3 ← nextByte
    require (mandatory = .operandSize && opcode3 = 0x17) "0f 38 opcode"
    require (!p.rex.wide) "REX.W on an SSE instruction"
    let o ← modrm p.rex
    return .testVectorBits (o.vectorReg p.rex) o.vectorRm
  vector p mandatory opcode

def instruction : Decoder Instruction := do
  let (p, opcode) ← prefixesAndOpcode
  if opcode = 0x0f then twoByte p (← nextByte)
  else
    require p.repeatPrefix.isNone "0xf2/0xf3 outside SSE"
    oneByte p opcode

end Decode

def decodeBytes (bytes : List UInt8) : Except DecodeError (Instruction × Nat) := do
  let (i, rest) ← Decode.instruction.run bytes
  pure (i, bytes.length - rest.length)

def maxInstructionLength : Nat := 15

-- Bytes are fetched one at a time and only as many as the instruction
-- needs: fetching past its end could fault where the CPU does not.
def decodeWith (fetch : UInt64 → Except PageFault UInt8) (address : UInt64) :
    Except Fault (Instruction × Nat) :=
  go maxInstructionLength []
where
  go : Nat → List UInt8 → Except Fault (Instruction × Nat)
    | 0, _ => .error (.undecodable .tooLong)
    | budget + 1, bytes => do
      let b ← (fetch (address + bytes.length.toUInt64)).mapError .pageFault
      let bytes := bytes ++ [b]
      match decodeBytes bytes with
      | .ok (i, length) =>
        -- Every shorter prefix was `truncated`, so the decoder used all of them.
        if length = bytes.length then .ok (i, length) else .error (.undecodable (.unsupported "trailing bytes"))
      | .error .truncated => go budget bytes
      | .error e => .error (.undecodable e)

def decode (m : Memory) (address : UInt64) : Except Fault (Instruction × Nat) :=
  decodeWith (m.byte .fetch) address

end X86
