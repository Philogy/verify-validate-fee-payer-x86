import ValidateFeePayer.Decode

/-!
Intel-syntax text of a decoded instruction, in llvm-objdump's format, so
`Checks.lean` can compare the decoder with `Disasm.lean` operand for operand.

This is the one place that maps the model's descriptive names to x86
mnemonics and register names. Only used for that check.
-/

namespace ValidateFeePayer.X86.Print

def hexDigits (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def hex (n : Nat) : String := "0x" ++ hexDigits n

def signedHex (v : Int) : String :=
  if v < 0 then "-" ++ hex v.natAbs else hex v.toNat

/-- The x86 suffix of a condition, as in `jne`, `sete`, `cmovae`. -/
def conditionSuffix : Condition → String
  | .overflow => "o" | .notOverflow => "no" | .below => "b" | .aboveOrEqual => "ae"
  | .equal => "e" | .notEqual => "ne" | .belowOrEqual => "be" | .above => "a"
  | .negative => "s" | .notNegative => "ns" | .parityEven => "p" | .parityOdd => "np"
  | .less => "l" | .greaterOrEqual => "ge" | .lessOrEqual => "le" | .greater => "g"

def arithmeticMnemonic : ArithmeticOp → String
  | .add => "add" | .or => "or" | .subtractWithBorrow => "sbb" | .and => "and"
  | .subtract => "sub" | .xor => "xor" | .compare => "cmp" | .testBits => "test"

/-- The mnemonic llvm-objdump prints. -/
def mnemonic : Instruction → String
  | .arithmetic op .. => arithmeticMnemonic op
  | .move .. => "mov"
  | .moveImmediate64 .. => "movabs"
  | .moveZeroExtendByte .. => "movzx"
  | .loadAddress .. => "lea"
  | .increment .. => "inc"
  | .multiplySigned .. => "imul"
  | .shiftRightSigned .. => "sar"
  | .setIf c _ => "set" ++ conditionSuffix c
  | .moveIf c .. => "cmov" ++ conditionSuffix c
  | .push _ => "push"
  | .pop _ => "pop"
  | .jumpIf c _ => "j" ++ conditionSuffix c
  | .jump _ => "jmp"
  | .call _ => "call"
  | .returnToCaller => "ret"
  | .moveVectorUnaligned .. => "movdqu"
  | .moveVectorAligned .. => "movapd"
  | .moveIntegerToVector .. => "movq"
  | .vectorBitwise .xor .. => "pxor"
  | .vectorBitwise .or .. => "por"
  | .vectorBitwise .xorDoubles .. => "xorpd"
  | .testVectorBits .. => "ptest"
  | .interleaveLow32 .. => "punpckldq"
  | .interleaveHighDoubles .. => "unpckhpd"
  | .subtractDoublePairs .. => "subpd"
  | .scalarDouble .add .. => "addsd"
  | .scalarDouble .subtract .. => "subsd"
  | .scalarDouble .multiply .. => "mulsd"
  | .compareDoubles .. => "ucomisd"
  | .truncateDoubleToInt64 .. => "cvttsd2si"

/-- The x86 name of a register's full 64 bits. -/
def register64 : Register → String
  | .accumulator => "rax" | .counter => "rcx" | .data => "rdx" | .base => "rbx"
  | .stackPointer => "rsp" | .framePointer => "rbp" | .sourceIndex => "rsi"
  | .destinationIndex => "rdi"
  | r => "r" ++ toString r.index.val

/-- The x86 name of a register's low `size` bits. -/
def register (size : OperandSize) (r : Register) : String :=
  let i := r.index.val
  match size with
  | .bits64 => register64 r
  | .bits32 => if i < 8 then ["eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi"][i]! else register64 r ++ "d"
  | .bits8 => if i < 8 then ["al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil"][i]! else register64 r ++ "b"

def vectorRegister (v : VectorRegister) : String := "xmm" ++ toString v.val

def address : Address → String
  | .relativeToNextInstruction d =>
    "[rip" ++ (if d < 0 then " - " ++ hex d.natAbs else " + " ++ hex d.toNat) ++ "]"
  | .baseIndex base index d =>
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

def bytesOf (size : OperandSize) : Nat := size.bits / 8

def operand (size : OperandSize) : RegisterOrMemory → String
  | .register r => register size r
  | .memory a => memory (bytesOf size) a

def vectorOperand (bytes : Nat) : VectorOrMemory → String
  | .register v => vectorRegister v
  | .memory a => memory bytes a

/-- llvm-objdump prints 64-bit immediates signed and narrower ones unsigned. -/
def immediate (size : OperandSize) (v : UInt64) : String :=
  match size with
  | .bits64 => signedHex (if v.toNat < 2 ^ 63 then (v.toNat : Int) else v.toNat - 2 ^ 64)
  | _ => hex (v.toNat % 2 ^ size.bits)

def source (size : OperandSize) : Source → String
  | .operand x => operand size x
  | .immediate v => immediate size v

def list (l : List String) : String := ", ".intercalate l

/-- The text of `i`, which ends at `next` (for branch targets). -/
def instruction (next : UInt64) (i : Instruction) : String :=
  let target (offset : Int) := hex ((next.toNat + offset) % 2 ^ 64).toNat
  let body := match i with
    | .arithmetic _ size d s => list [operand size d, source size s]
    | .move size d s => list [operand size d, source size s]
    | .moveImmediate64 d v => list [register64 d, hex v.toNat]
    | .moveZeroExtendByte size d s => list [register size d, operand .bits8 s]
    | .loadAddress d a => list [register64 d, address a]
    | .increment size d => operand size d
    | .multiplySigned d s none => list [register64 d, operand .bits64 s]
    | .multiplySigned d s (some v) => list [register64 d, operand .bits64 s, immediate .bits64 v]
    | .shiftRightSigned d c => list [operand .bits64 d, hex c.toNat]
    | .setIf _ d => operand .bits8 d
    | .moveIf _ size d s => list [register size d, operand size s]
    | .push r | .pop r => register64 r
    | .jumpIf _ offset | .jump offset => target offset
    | .call t => operand .bits64 t
    | .returnToCaller => ""
    | .moveVectorUnaligned d s | .moveVectorAligned d s | .vectorBitwise _ d s | .testVectorBits d s
    | .interleaveLow32 d s | .interleaveHighDoubles d s | .subtractDoublePairs d s =>
      list [vectorRegister d, vectorOperand 16 s]
    | .moveIntegerToVector d s => list [vectorRegister d, operand .bits64 s]
    | .scalarDouble _ d s | .compareDoubles d s => list [vectorRegister d, vectorOperand 8 s]
    | .truncateDoubleToInt64 d s => list [register64 d, vectorOperand 8 s]
  if body.isEmpty then mnemonic i else mnemonic i ++ " " ++ body

def entry (e : Decoded) : UInt64 × Nat × String :=
  (e.address, e.length, instruction (e.address + e.length.toUInt64) e.instruction)

end ValidateFeePayer.X86.Print
