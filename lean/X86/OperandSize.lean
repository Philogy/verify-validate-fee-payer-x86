namespace X86

inductive OperandSize where
  | bits8 | bits16 | bits32 | bits64
  deriving DecidableEq, Repr

namespace OperandSize

def bits : OperandSize → Nat
  | .bits8 => 8 | .bits16 => 16 | .bits32 => 32 | .bits64 => 64

def byteCount : OperandSize → Nat
  | .bits8 => 1 | .bits16 => 2 | .bits32 => 4 | .bits64 => 8

def mask : OperandSize → UInt64
  | .bits8 => 0xff | .bits16 => 0xffff | .bits32 => 0xffffffff | .bits64 => 0xffffffffffffffff

def signBit (size : OperandSize) : UInt64 := 1 <<< (size.bits - 1).toUInt64

def isNegative (size : OperandSize) (v : UInt64) : Bool := v &&& size.signBit != 0

/-- `v`, read as a `size`-bit two's-complement number, at 64 bits. -/
def signExtend (size : OperandSize) (v : UInt64) : UInt64 :=
  if size.isNegative v then v ||| ~~~size.mask else v &&& size.mask

def half : OperandSize → OperandSize
  | .bits64 => .bits32 | .bits32 => .bits16 | _ => .bits8

end OperandSize

end X86
