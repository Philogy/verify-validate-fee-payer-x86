import X86.Memory

/-!
The bytes a call may touch, described as blocks: which must be mapped, that
no two overlap, and that everything else is left alone. Addresses are
`UInt64`, as the machine has them; sizes are `Nat` and every bound is
compared as a `Nat`, so a block that ends at `2^64` does not wrap around to 0.
-/

namespace Abi

open X86

structure Block where
  base : UInt64
  size : Nat

namespace Block

def endAddress (b : Block) : Nat := b.base.toNat + b.size

def Contains (b : Block) (a : UInt64) : Prop := b.base.toNat ≤ a.toNat ∧ a.toNat < b.endAddress

def NoWrap (b : Block) : Prop := b.endAddress ≤ 2 ^ 64

-- An empty block overlaps nothing: an empty `Vec`'s pointer is dangling and
-- may be any address.
def Apart (x y : Block) : Prop :=
  x.size = 0 ∨ y.size = 0 ∨ x.endAddress ≤ y.base.toNat ∨ y.endAddress ≤ x.base.toNat

/-- No two of the blocks overlap. -/
def Separate (bs : List Block) : Prop := bs.Pairwise Apart

def Readable (m : Memory) (b : Block) : Prop := m.Readable b.base b.size

def Writable (m : Memory) (b : Block) : Prop := m.Writable b.base b.size

end Block

/-- `m'` agrees with `m`, for every kind of access, on every byte outside `writes`. -/
def UnchangedOutside (writes : List Block) (m m' : Memory) : Prop :=
  ∀ access a, (∀ b ∈ writes, ¬ b.Contains a) → m'.byte access a = m.byte access a

/-- The 8-byte field at offset `field` of the object at `base` holds the
pointer `p`. Pointer targets are found only through this, so a reader of a
contract sees where it chases pointers. -/
def PtrAt (m : Memory) (base : UInt64) (field : Nat) (p : UInt64) : Prop :=
  m.Holds .bits64 (base + field.toUInt64) p

end Abi
