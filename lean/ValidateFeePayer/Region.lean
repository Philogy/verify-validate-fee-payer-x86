import X86.Bytes

/-!
A region is one carved piece of the binary: a function's code or one data
object. Addresses are as in the binary, i.e. at load base 0.
-/

namespace ValidateFeePayer

inductive Contents where
  | code (bytes : ByteArray)
  | constant (bytes : ByteArray)
  /-- A GOT slot, which the dynamic loader fills with `loadBase + target`. -/
  | pointer (target : UInt64)
  /-- An object whose address the code only passes to the panic. The panic
  is terminal, so its contents can never matter; only its size is kept and
  it is left unmapped. This includes the panic `Location`, whose file-name
  pointer is relocated but only read by the panic runtime. -/
  | addressOnly (size : Nat)

namespace Contents

def size : Contents → Nat
  | code bytes | constant bytes => bytes.size
  | pointer _ => 8
  | addressOnly size => size

-- Code and constants contain no relocated words, so their bytes are the same
-- at every base.
def bytesAt (loadBase : UInt64) : Contents → Option ByteArray
  | code bytes | constant bytes => some bytes
  | pointer target => some ⟨(X86.littleEndianBytes 8 (loadBase + target)).toArray⟩
  | addressOnly _ => none

def isCode : Contents → Bool
  | code _ => true
  | _ => false

theorem size_bytesAt {c : Contents} {loadBase : UInt64} {bytes : ByteArray}
    (h : c.bytesAt loadBase = some bytes) : bytes.size = c.size := by
  cases c <;> simp [bytesAt] at h <;> subst h <;> rfl

end Contents

structure Region where
  name : String
  address : UInt64
  contents : Contents

namespace Region

def size (r : Region) : Nat := r.contents.size

-- A `Nat`, so that a region that ends at `2^64` does not wrap around to 0.
def endAddress (r : Region) : Nat := r.address.toNat + r.size

def Contains (r : Region) (address : UInt64) : Prop :=
  r.address.toNat ≤ address.toNat ∧ address.toNat < r.endAddress

instance (r : Region) (address : UInt64) : Decidable (r.Contains address) := by
  unfold Contains; infer_instance

end Region

def Disjoint (a b : Region) : Prop := a.endAddress ≤ b.address.toNat ∨ b.endAddress ≤ a.address.toNat

instance (a b : Region) : Decidable (Disjoint a b) := by unfold Disjoint; infer_instance

end ValidateFeePayer
