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

namespace Contents

def size : Contents → Nat
  | code bytes | constant bytes => bytes.size
  | pointer _ => 8

-- Code and constants contain no relocated words, so their bytes are the same
-- at every base.
def bytesAt (loadBase : UInt64) : Contents → ByteArray
  | code bytes | constant bytes => bytes
  | pointer target => ⟨(X86.littleEndianBytes 8 (loadBase + target)).toArray⟩

def isCode : Contents → Bool
  | code _ => true
  | _ => false

theorem size_bytesAt {c : Contents} {loadBase : UInt64} {bytes : ByteArray}
    (h : c.bytesAt loadBase = bytes) : bytes.size = c.size := by
  subst h; cases c <;> rfl

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
