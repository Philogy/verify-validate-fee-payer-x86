/-!
Little-endian conversions between numbers and bytes, shared by the image
(pointer slots) and memory accesses.
-/

namespace ValidateFeePayer

/-- The low `8 * n` bits of `v` as `n` bytes, least significant first. -/
def leBytes (n v : Nat) : List UInt8 :=
  (List.range n).map fun i => (v >>> (8 * i)).toUInt8

/-- The number whose little-endian bytes are `bs`. -/
def ofLEBytes (bs : List UInt8) : Nat :=
  bs.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- The 8 bytes of `v` as they sit in memory. -/
def UInt64.toLEBytes (v : UInt64) : ByteArray :=
  ⟨#[v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8,
     (v >>> 32).toUInt8, (v >>> 40).toUInt8, (v >>> 48).toUInt8, (v >>> 56).toUInt8]⟩

@[simp] theorem UInt64.size_toLEBytes (v : UInt64) : (UInt64.toLEBytes v).size = 8 := rfl

end ValidateFeePayer
