import ValidateFeePayer.Bytes

/-!
A region is a contiguous piece of the carved image: code of one function, or
one data object. Addresses are as in the binary, i.e. at load base 0; at base
`B` a region starts at `B + vaddr`, and its bytes there follow from its
`Contents` alone.
-/

namespace ValidateFeePayer

inductive Contents where
  /-- Machine code of a carved function. It has no relocations, so its bytes
  are the same at every base. -/
  | code (bytes : ByteArray)
  /-- Data the code reads. It contains no relocated words, so its bytes are
  the same at every base. -/
  | constant (bytes : ByteArray)
  /-- An 8-byte slot (GOT entry) that the dynamic loader fills with
  `B + target`; the code calls through it. -/
  | pointer (target : UInt64)
  /-- An object whose address the code only passes on, to the panic, which is
  terminal. Its contents can never matter, so only its size is kept, and the
  memory model leaves it unmapped: a read of it faults. The panic `Location`
  is one, although it holds a relocated pointer to its file name: that pointer
  is only ever read by the panic runtime, so it is dropped with the rest. -/
  | addressOnly (size : Nat)

namespace Contents

def size : Contents → Nat
  | code bytes | constant bytes => bytes.size
  | pointer _ => 8
  | addressOnly size => size

/-- The bytes in memory when the binary is loaded at base `B`; `none` if the
region is not mapped. -/
def bytesAt (B : UInt64) : Contents → Option ByteArray
  | code bytes | constant bytes => some bytes
  | pointer target => some (UInt64.toLEBytes (B + target))
  | addressOnly _ => none

def isCode : Contents → Bool
  | code _ => true
  | _ => false

theorem size_bytesAt {c : Contents} {B : UInt64} {bytes : ByteArray}
    (h : c.bytesAt B = some bytes) : bytes.size = c.size := by
  cases c <;> simp [bytesAt] at h <;> subst h <;> rfl

end Contents

structure Region where
  name : String
  vaddr : UInt64
  contents : Contents

namespace Region

def size (r : Region) : Nat := r.contents.size

/-- One past the last address, as a `Nat` so it cannot wrap. -/
def endAddr (r : Region) : Nat := r.vaddr.toNat + r.size

/-- `addr` (at load base 0) lies inside the region. -/
def Contains (r : Region) (addr : UInt64) : Prop := r.vaddr.toNat ≤ addr.toNat ∧ addr.toNat < r.endAddr

instance (r : Region) (addr : UInt64) : Decidable (r.Contains addr) := by
  unfold Contains; infer_instance

end Region

def Disjoint (a b : Region) : Prop := a.endAddr ≤ b.vaddr.toNat ∨ b.endAddr ≤ a.vaddr.toNat

instance (a b : Region) : Decidable (Disjoint a b) := by unfold Disjoint; infer_instance

end ValidateFeePayer
