import X86.Bytes

/-!
A region is one carved piece of the binary: a function's code or one data
object.
-/

namespace ValidateFeePayer

/-- An address in the binary, i.e. relative to the load base. -/
structure ImageOffset where
  off : UInt64
  deriving DecidableEq, Repr

instance : OfNat ImageOffset n := ⟨⟨OfNat.ofNat n⟩⟩

/-- Where `o` is once the image is loaded at `loadBase`. -/
def ImageOffset.at (o : ImageOffset) (loadBase : UInt64) : UInt64 := loadBase + o.off

inductive Contents where
  | code (bytes : ByteArray)
  | constant (bytes : ByteArray)
  /-- A GOT slot, which the dynamic loader fills with `target.at loadBase`. -/
  | pointer (target : ImageOffset)

namespace Contents

def size : Contents → Nat
  | code bytes | constant bytes => bytes.size
  | pointer _ => 8

-- Code and constants contain no relocated words, so their bytes are the same
-- at every base.
def bytesAt (loadBase : UInt64) : Contents → ByteArray
  | code bytes | constant bytes => bytes
  | pointer target => ⟨(X86.littleEndianBytes 8 (target.at loadBase)).toArray⟩

def isCode : Contents → Bool
  | code _ => true
  | _ => false

theorem size_bytesAt {c : Contents} {loadBase : UInt64} {bytes : ByteArray}
    (h : c.bytesAt loadBase = bytes) : bytes.size = c.size := by
  subst h; cases c <;> rfl

end Contents

structure Region where
  name : String
  address : ImageOffset
  contents : Contents

namespace Region

def size (r : Region) : Nat := r.contents.size

-- A `Nat`, so that a region that ends at `2^64` does not wrap around to 0.
def endAddress (r : Region) : Nat := r.address.off.toNat + r.size

def Contains (r : Region) (address : UInt64) : Prop :=
  r.address.off.toNat ≤ address.toNat ∧ address.toNat < r.endAddress

instance (r : Region) (address : UInt64) : Decidable (r.Contains address) := by
  unfold Contains; infer_instance

end Region

def Disjoint (a b : Region) : Prop := a.endAddress ≤ b.address.off.toNat ∨ b.endAddress ≤ a.address.off.toNat

instance (a b : Region) : Decidable (Disjoint a b) := by unfold Disjoint; infer_instance

end ValidateFeePayer
