import X86.Instruction

/-!
Intel syntax as llvm-objdump prints it, so that a decoded program can be
compared with an independent disassembler operand for operand.
-/

namespace X86.Print

def hexDigits (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def hex (n : Nat) : String := "0x" ++ hexDigits n

def signed (v : UInt64) : Int := v.toInt64.toInt

def signedHex (v : Int) : String :=
  if v < 0 then "-" ++ hex v.natAbs else hex v.toNat

/-- The x86 suffix of a condition, as in `jne`, `sete`, `cmovae`. -/
def conditionSuffix : Condition → String
  | .overflow => "o" | .notOverflow => "no" | .below => "b" | .aboveOrEqual => "ae"
  | .equal => "e" | .notEqual => "ne" | .belowOrEqual => "be" | .above => "a"
  | .negative => "s" | .notNegative => "ns" | .parityEven => "p" | .parityOdd => "np"
  | .less => "l" | .greaterOrEqual => "ge" | .lessOrEqual => "le" | .greater => "g"

def arithmeticMnemonic : ArithmeticOp → String
  | .add => "add" | .or => "or" | .addWithCarry => "adc" | .subtractWithBorrow => "sbb"
  | .and => "and" | .subtract => "sub" | .xor => "xor" | .compare => "cmp" | .testBits => "test"

def shiftMnemonic : ShiftOp → String
  | .left => "shl" | .rightLogical => "shr" | .rightArithmetic => "sar"

def vectorMoveMnemonic : VectorMove → String
  | .integerAligned => "movdqa" | .integerUnaligned => "movdqu"
  | .doubleAligned => "movapd" | .doubleUnaligned => "movupd"
  | .singleAligned => "movaps" | .singleUnaligned => "movups"

def bitwiseMnemonic (op : VectorBitwiseOp) (domain : VectorDomain) : String :=
  let base := match op with | .and => "and" | .andNot => "andn" | .or => "or" | .xor => "xor"
  match domain with
  | .integer => "p" ++ base
  | .double => base ++ "pd"
  | .single => base ++ "ps"

def doubleMnemonic : DoubleOp → String
  | .add => "add" | .subtract => "sub" | .multiply => "mul"

/-- The mnemonic llvm-objdump prints. -/
def mnemonic : Instruction → String
  | .arithmetic op .. => arithmeticMnemonic op
  | .move .. => "mov"
  | .moveImmediate64 .. => "movabs"
  | .moveZeroExtend .. => "movzx"
  | .moveSignExtend _ _ .bits32 _ => "movsxd"
  | .moveSignExtend .. => "movsx"
  | .loadAddress .. => "lea"
  | .increment .. => "inc"
  | .decrement .. => "dec"
  | .negate .. => "neg"
  | .complement .. => "not"
  | .multiplySigned .. => "imul"
  | .shift op .. => shiftMnemonic op
  | .setIf c _ => "set" ++ conditionSuffix c
  | .moveIf c .. => "cmov" ++ conditionSuffix c
  | .signExtendAccumulator .bits16 => "cbw"
  | .signExtendAccumulator .bits32 => "cwde"
  | .signExtendAccumulator _ => "cdqe"
  | .signExtendIntoData .bits16 => "cwd"
  | .signExtendIntoData .bits32 => "cdq"
  | .signExtendIntoData _ => "cqo"
  | .push _ => "push"
  | .pop _ => "pop"
  | .jumpIf c _ => "j" ++ conditionSuffix c
  | .jump _ | .jumpIndirect _ => "jmp"
  | .callRelative _ | .call _ => "call"
  | .returnToCaller => "ret"
  | .noOperation _ => "nop"
  | .moveVector kind .. => vectorMoveMnemonic kind
  | .moveIntegerToVector .bits64 .. | .moveVectorToInteger .bits64 .. => "movq"
  | .moveIntegerToVector .. | .moveVectorToInteger .. => "movd"
  | .moveScalarDouble .. => "movsd"
  | .vectorBitwise op domain .. => bitwiseMnemonic op domain
  | .testVectorBits .. => "ptest"
  | .interleaveLow32 .. => "punpckldq"
  | .interleaveLow64 .. => "punpcklqdq"
  | .interleaveLowDoubles .. => "unpcklpd"
  | .interleaveHighDoubles .. => "unpckhpd"
  | .packedDouble op .. => doubleMnemonic op ++ "pd"
  | .scalarDouble op .. => doubleMnemonic op ++ "sd"
  | .compareDoubles .. => "ucomisd"
  | .truncateDoubleToInt64 .. => "cvttsd2si"

def register64 : Register → String
  | .rax => "rax" | .rcx => "rcx" | .rdx => "rdx" | .rbx => "rbx"
  | .rsp => "rsp" | .rbp => "rbp" | .rsi => "rsi"
  | .rdi => "rdi"
  | r => "r" ++ toString r.index.val

def register (size : OperandSize) (r : Register) : String :=
  let i := r.index.val
  match size with
  | .bits64 => register64 r
  | .bits32 => if i < 8 then ["eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi"][i]! else register64 r ++ "d"
  | .bits16 => if i < 8 then ["ax", "cx", "dx", "bx", "sp", "bp", "si", "di"][i]! else register64 r ++ "w"
  | .bits8 => if i < 8 then ["al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil"][i]! else register64 r ++ "b"

def vectorRegister (v : VectorRegister) : String := "xmm" ++ toString v.val

def address : Address → String
  | .relativeToNextInstruction d =>
    let d := signed d
    "[rip" ++ (if d < 0 then " - " ++ hex d.natAbs else " + " ++ hex d.toNat) ++ "]"
  | .baseIndex base index d =>
    let d := signed d
    let terms := (base.map register64).toList ++
      (index.map fun (r, s) =>
        if s.val = 0 then register64 r else toString (2 ^ s.val) ++ "*" ++ register64 r).toList
    let body := " + ".intercalate terms
    let displacement :=
      if d = 0 then ""
      else if terms.isEmpty then signedHex d
      else if d < 0 then " - " ++ hex d.natAbs else " + " ++ hex d.toNat
    "[" ++ body ++ displacement ++ "]"

def memory (bytes : Nat) (a : Address) : String :=
  (match bytes with
   | 1 => "byte" | 2 => "word" | 4 => "dword" | 8 => "qword" | _ => "xmmword") ++ " ptr " ++ address a

def operand (size : OperandSize) : RegisterOrMemory → String
  | .register r => register size r
  | .highByte r => ["ah", "ch", "dh", "bh"][r.index.val % 4]!
  | .memory a => memory size.byteCount a

def vectorOperand (bytes : Nat) : VectorOrMemory → String
  | .register v => vectorRegister v
  | .memory a => memory bytes a

-- llvm-objdump prints 64-bit immediates signed and narrower ones unsigned.
def immediate (size : OperandSize) (v : UInt64) : String :=
  match size with
  | .bits64 => signedHex (signed v)
  | _ => hex (v &&& size.mask).toNat

def source (size : OperandSize) : Source → String
  | .operand x => operand size x
  | .immediate v => immediate size v

def list (l : List String) : String := ", ".intercalate l

/-- `next` is the address after `i`, from which branch targets count. -/
def instruction (next : UInt64) (i : Instruction) : String :=
  let target (offset : UInt64) := hex (next + offset).toNat
  let body := match i with
    | .arithmetic _ size d s | .move size d s => list [operand size d, source size s]
    | .moveImmediate64 d v => list [register64 d, hex v.toNat]
    | .moveZeroExtend size d sourceSize s | .moveSignExtend size d sourceSize s =>
      list [register size d, operand sourceSize s]
    | .loadAddress size d a => list [register size d, address a]
    | .increment size d | .decrement size d | .negate size d | .complement size d => operand size d
    | .multiplySigned size d s none => list [register size d, operand size s]
    | .multiplySigned size d s (some v) => list [register size d, operand size s, immediate size v]
    | .shift _ size d .one => list [operand size d, "1"]
    | .shift _ size d (.immediate c) => list [operand size d, hex c.toNat]
    | .shift _ size d .counter => list [operand size d, "cl"]
    | .setIf _ d => operand .bits8 d
    | .moveIf _ size d s => list [register size d, operand size s]
    | .signExtendAccumulator _ | .signExtendIntoData _ | .returnToCaller | .noOperation none => ""
    | .noOperation (some (size, x)) => operand size x
    | .push s => source .bits64 s
    | .pop d => operand .bits64 d
    | .jumpIf _ offset | .jump offset | .callRelative offset => target offset
    | .jumpIndirect t | .call t => operand .bits64 t
    | .moveVector _ d s => list [vectorOperand 16 d, vectorOperand 16 s]
    | .vectorBitwise _ _ d s | .testVectorBits d s | .interleaveLow32 d s | .interleaveLow64 d s
    | .interleaveLowDoubles d s | .interleaveHighDoubles d s | .packedDouble _ d s =>
      list [vectorRegister d, vectorOperand 16 s]
    | .moveIntegerToVector size d s => list [vectorRegister d, operand size s]
    | .moveVectorToInteger size d s => list [operand size d, vectorRegister s]
    | .moveScalarDouble d s => list [vectorOperand 8 d, vectorOperand 8 s]
    | .scalarDouble _ d s | .compareDoubles d s => list [vectorRegister d, vectorOperand 8 s]
    | .truncateDoubleToInt64 d s => list [register64 d, vectorOperand 8 s]
  if body.isEmpty then mnemonic i else mnemonic i ++ " " ++ body

end X86.Print
