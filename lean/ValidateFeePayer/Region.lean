/-!
A region is a contiguous piece of the carved memory image: code of one
function, or one data object. Addresses are as in the binary, i.e. at load
base 0; `Region.load` moves a region to an arbitrary base.
-/

namespace ValidateFeePayer

/-- An 8-byte word the dynamic loader fills in: at load base `B` it holds
`B + value`, little-endian. -/
structure Relocation where
  offset : Nat
  value : UInt64

structure Region where
  name : String
  vaddr : UInt64
  /-- At load base 0, i.e. relocated words hold their `value`. -/
  bytes : ByteArray
  relocations : List Relocation := []
  /-- False for objects whose address the code only passes on (the panic
  message and location), so a proof never needs their contents. -/
  readByCode : Bool := true

namespace Region

def size (r : Region) : Nat := r.bytes.size

/-- One past the last address, as a `Nat` so it cannot wrap. -/
def endAddr (r : Region) : Nat := r.vaddr.toNat + r.size

private def byteOf (v : UInt64) (i : Nat) : UInt8 := (v >>> (8 * i).toUInt64).toUInt8

/-- The region as it is in memory when the binary is loaded at base `B`. -/
def load (B : UInt64) (r : Region) : Region :=
  { r with
    vaddr := B + r.vaddr
    bytes := r.relocations.foldl
      (fun bytes rel => (List.range 8).foldl
        (fun bytes i => bytes.set! (rel.offset + i) (byteOf (B + rel.value) i)) bytes)
      r.bytes }

def byteAt? (r : Region) (addr : UInt64) : Option UInt8 :=
  if r.vaddr ≤ addr ∧ addr.toNat < r.endAddr then
    some (r.bytes.get! (addr.toNat - r.vaddr.toNat))
  else
    none

end Region

def Disjoint (a b : Region) : Prop := a.endAddr ≤ b.vaddr.toNat ∨ b.endAddr ≤ a.vaddr.toNat

instance (a b : Region) : Decidable (Disjoint a b) := by unfold Disjoint; infer_instance

end ValidateFeePayer
