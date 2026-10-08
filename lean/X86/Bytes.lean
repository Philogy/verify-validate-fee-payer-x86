namespace X86

def littleEndianBytes : Nat → UInt64 → List UInt8
  | 0, _ => []
  | n + 1, v => v.toUInt8 :: littleEndianBytes n (v >>> 8)

def ofLittleEndian : List UInt8 → UInt64
  | [] => 0
  | b :: bs => b.toUInt64 ||| (ofLittleEndian bs <<< 8)

def lowHalf (v : BitVec 128) : UInt64 := UInt64.ofBitVec (v.setWidth 64)

def highHalf (v : BitVec 128) : UInt64 := UInt64.ofBitVec (v.extractLsb' 64 64)

def ofHalves (low high : UInt64) : BitVec 128 := high.toBitVec ++ low.toBitVec

end X86
