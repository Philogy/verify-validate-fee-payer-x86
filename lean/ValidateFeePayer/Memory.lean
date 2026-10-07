import ValidateFeePayer.Image

/-!
Memory as a list of mapped intervals, each with its bytes and permissions.
The program only touches a few small areas: the carved image at load base
`B`, the stack and the argument structs. Every other address is unmapped.

An access is checked byte by byte, so one that straddles two adjacent
mappings works as on the CPU. A bad access is a `Fault`, the model's page
fault, which is a distinct outcome rather than a value.
-/

namespace ValidateFeePayer

/-- Permissions as x86-64 page tables express them: a mapped page is always
readable, writing and executing (NX clear) are separate bits. An unreadable
page is an unmapped one. -/
structure Perm where
  write : Bool
  exec : Bool
  deriving DecidableEq, Repr

namespace Perm
def r : Perm := ⟨false, false⟩
def rw : Perm := ⟨true, false⟩
def rx : Perm := ⟨false, true⟩
end Perm

inductive Access where
  | read
  | write
  /-- Instruction fetch. -/
  | fetch
  deriving DecidableEq, Repr

def Perm.allows (p : Perm) : Access → Bool
  | .read => true
  | .write => p.write
  | .fetch => p.exec

inductive Fault where
  | unmapped (addr : UInt64) (access : Access)
  /-- Mapped, but `access` is not permitted there. -/
  | denied (addr : UInt64) (access : Access)
  deriving DecidableEq, Repr

structure Mapping where
  base : UInt64
  bytes : ByteArray
  perm : Perm

namespace Mapping

/-- One past the last address, as a `Nat`. Bytes past `2^64` are unreachable. -/
def endAddr (mp : Mapping) : Nat := mp.base.toNat + mp.bytes.size

def Contains (mp : Mapping) (addr : UInt64) : Prop :=
  mp.base.toNat ≤ addr.toNat ∧ addr.toNat < mp.endAddr

instance (mp : Mapping) (addr : UInt64) : Decidable (mp.Contains addr) := by
  unfold Contains; infer_instance

def get (mp : Mapping) (addr : UInt64) (h : mp.Contains addr) : UInt8 :=
  mp.bytes[addr.toNat - mp.base.toNat]'(by unfold Contains endAddr at h; omega)

def set (mp : Mapping) (addr : UInt64) (h : mp.Contains addr) (v : UInt8) : Mapping :=
  { mp with bytes := mp.bytes.set (addr.toNat - mp.base.toNat) v (by unfold Contains endAddr at h; omega) }

def Disjoint (a b : Mapping) : Prop := a.endAddr ≤ b.base.toNat ∨ b.endAddr ≤ a.base.toNat

end Mapping

inductive Width where
  | w1 | w2 | w4 | w8 | w16
  deriving DecidableEq, Repr

def Width.size : Width → Nat
  | .w1 => 1 | .w2 => 2 | .w4 => 4 | .w8 => 8 | .w16 => 16

structure Memory where
  mappings : List Mapping

namespace Memory

/-- No two mappings overlap, so each address has at most one. -/
def WellFormed (m : Memory) : Prop := m.mappings.Pairwise Mapping.Disjoint

/-- The byte at `addr`, if `access` is allowed there. -/
def byte (m : Memory) (access : Access) (addr : UInt64) : Except Fault UInt8 :=
  go m.mappings
where
  go : List Mapping → Except Fault UInt8
    | [] => .error (.unmapped addr access)
    | mp :: rest =>
      if h : mp.Contains addr then
        if mp.perm.allows access then .ok (mp.get addr h) else .error (.denied addr access)
      else go rest

/-- `n` bytes from `addr` on, wrapping at `2^64` like the CPU's address
arithmetic; the first bad byte's fault otherwise. -/
def bytes (m : Memory) (access : Access) (addr : UInt64) (n : Nat) : Except Fault (List UInt8) :=
  (List.range n).mapM fun i => m.byte access (addr + i.toUInt64)

/-- Overwrites the byte at `addr` in the first mapping that contains it,
regardless of permissions; `write` checks them first. -/
def setByte (addr : UInt64) (v : UInt8) : List Mapping → List Mapping
  | [] => []
  | mp :: rest => if h : mp.Contains addr then mp.set addr h v :: rest else mp :: setByte addr v rest

/-- Little-endian load. -/
def read (m : Memory) (w : Width) (addr : UInt64) : Except Fault (BitVec (8 * w.size)) := do
  let bs ← m.bytes .read addr w.size
  return BitVec.ofNat _ (ofLEBytes bs)

/-- Little-endian store. Every byte must be writable before any is written:
a store either completes or faults with no effect. -/
def write (m : Memory) (w : Width) (addr : UInt64) (v : BitVec (8 * w.size)) : Except Fault Memory := do
  let _ ← m.bytes .write addr w.size
  return ⟨(leBytes w.size v.toNat).zipIdx.foldl
    (fun ms (b, i) => setByte (addr + i.toUInt64) b ms) m.mappings⟩

/-- `n` instruction bytes from `addr`. The decoder should fetch exactly the
bytes of the instruction (1 to 15), as a fetch past the end of code faults
here even when the CPU would not need those bytes. -/
def fetch (m : Memory) (addr : UInt64) (n : Nat) : Except Fault (List UInt8) :=
  m.bytes .fetch addr n

end Memory

/-! ## The initial memory -/

open Image in
def regions : List Region := functions ++ data

/-- One past the highest carved address at load base 0. -/
def imageEnd : Nat := regions.foldl (fun acc r => max acc r.endAddr) 0

/-- Load bases at which no carved address wraps around 2^64. The kernel loads
at page-aligned bases, but nothing in the carved code depends on that. -/
def ValidBase (B : UInt64) : Prop := B.toNat + imageEnd ≤ 2 ^ 64

instance : DecidablePred ValidBase := fun _B => inferInstanceAs (Decidable (_ ≤ _))

/-- Where a region sits at load base `B`: code is read/execute, data (the
pointer slots included, as after RELRO) read-only. Address-only objects are
not mapped. -/
def Region.mapping (B : UInt64) (r : Region) : Option Mapping :=
  r.contents.bytesAt B |>.map fun bytes =>
    { base := B + r.vaddr, bytes, perm := if r.contents.isCode then .rx else .r }

def imageMappings (B : UInt64) : List Mapping := regions.filterMap (·.mapping B)

/-- Bytes reserved below `rsp` that a leaf frame may use without moving it. -/
def redZone : Nat := 128

/-- The stack at entry, read/write. `above` is what lies from `rsp` up: the
return address, the stack arguments and as much of the caller's frame as the
proof needs. `below` is the `below.size` bytes under `rsp`; their contents
are stale, so a specification quantifies over them. It must cover the
callees' frames plus the red zone. Everything under it is unmapped, acting as
the guard page. -/
def stackMapping (rsp : UInt64) (below above : ByteArray) : Mapping :=
  { base := rsp - below.size.toUInt64, bytes := below ++ above, perm := .rw }

/-- The memory at entry: the carved image at load base `B`, the stack and the
argument structs (each its own mapping, usually read/write). A
specification requires it to be `WellFormed`; the image part is by
`imageMappings_disjoint`. -/
def initialMemory (B : UInt64) (stack : Mapping) (args : List Mapping) : Memory :=
  ⟨imageMappings B ++ stack :: args⟩

/-- Where execution starts. -/
def entry (B : UInt64) : UInt64 := B + Image.validate_fee_payer.vaddr

/-- Reaching this address is the panicked outcome; no code is mapped there. -/
def panicEntry (B : UInt64) : UInt64 := B + Image.panicEntry

end ValidateFeePayer
