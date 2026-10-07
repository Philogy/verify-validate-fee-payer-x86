import ValidateFeePayer.Image

/-!
Memory as a list of mapped intervals, each with its bytes and permissions.
The program only touches a few small areas: the carved image at load base
`loadBase`, the stack and the argument structs. Every other address is unmapped.

An access is checked byte by byte, so one that straddles two adjacent
mappings works as on the CPU. A bad access is a `Fault`, the model's page
fault, which is a distinct outcome rather than a value.
-/

namespace ValidateFeePayer

/-- Permissions as x86-64 page tables express them: a mapped page is always
readable, writing and executing (NX clear) are separate bits. An unreadable
page is an unmapped one. -/
structure Permissions where
  write : Bool
  exec : Bool
  deriving DecidableEq, Repr

namespace Permissions
/-- Data (ELF/x86: `r--`). -/
def readOnly : Permissions := ⟨false, false⟩
/-- Stack and argument objects (`rw-`). -/
def readWrite : Permissions := ⟨true, false⟩
/-- Code (`r-x`). -/
def readExecute : Permissions := ⟨false, true⟩
end Permissions

inductive Access where
  | read
  | write
  /-- Instruction fetch. -/
  | fetch
  deriving DecidableEq, Repr

def Permissions.allows (p : Permissions) : Access → Bool
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
  permissions : Permissions

namespace Mapping

/-- One past the last address, as a `Nat`. Bytes past `2^64` are unreachable. -/
def endAddress (mp : Mapping) : Nat := mp.base.toNat + mp.bytes.size

def Contains (mp : Mapping) (addr : UInt64) : Prop :=
  mp.base.toNat ≤ addr.toNat ∧ addr.toNat < mp.endAddress

instance (mp : Mapping) (addr : UInt64) : Decidable (mp.Contains addr) := by
  unfold Contains; infer_instance

def get (mp : Mapping) (addr : UInt64) (h : mp.Contains addr) : UInt8 :=
  mp.bytes[addr.toNat - mp.base.toNat]'(by unfold Contains endAddress at h; omega)

def set (mp : Mapping) (addr : UInt64) (h : mp.Contains addr) (v : UInt8) : Mapping :=
  { mp with bytes := mp.bytes.set (addr.toNat - mp.base.toNat) v (by unfold Contains endAddress at h; omega) }

def Disjoint (a b : Mapping) : Prop := a.endAddress ≤ b.base.toNat ∨ b.endAddress ≤ a.base.toNat

end Mapping

/-- How many bytes one memory access reads or writes. -/
inductive Width where
  | bytes1 | bytes2 | bytes4 | bytes8 | bytes16
  deriving DecidableEq, Repr

def Width.size : Width → Nat
  | .bytes1 => 1 | .bytes2 => 2 | .bytes4 => 4 | .bytes8 => 8 | .bytes16 => 16

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
        if mp.permissions.allows access then .ok (mp.get addr h) else .error (.denied addr access)
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
def imageEnd : Nat := regions.foldl (fun acc r => max acc r.endAddress) 0

/-- Load bases at which no carved address wraps around 2^64. The kernel loads
at page-aligned bases, but nothing in the carved code depends on that. -/
def ValidLoadBase (loadBase : UInt64) : Prop := loadBase.toNat + imageEnd ≤ 2 ^ 64

instance : DecidablePred ValidLoadBase := fun _ => inferInstanceAs (Decidable (_ ≤ _))

/-- Where a region sits at `loadBase`: code is read/execute, data (the
pointer slots included, as after RELRO) read-only. Address-only objects are
not mapped. -/
def Region.mapping (loadBase : UInt64) (r : Region) : Option Mapping :=
  r.contents.bytesAt loadBase |>.map fun bytes =>
    { base := loadBase + r.address, bytes, permissions := if r.contents.isCode then .readExecute else .readOnly }

def imageMappings (loadBase : UInt64) : List Mapping := regions.filterMap (·.mapping loadBase)

/-- The memory at entry: the carved image at `loadBase`, the stack (a
read/write mapping, see `Stack.lean`) and the argument structs (each its own
mapping, usually read/write). A specification requires it to be
`WellFormed`; the image part is by `imageMappings_disjoint`. -/
def initialMemory (loadBase : UInt64) (stack : Mapping) (args : List Mapping) : Memory :=
  ⟨imageMappings loadBase ++ stack :: args⟩

/-- Where execution starts. -/
def entryAddress (loadBase : UInt64) : UInt64 := loadBase + Image.validate_fee_payer.address

/-- Reaching this address is the panicked outcome; no code is mapped there. -/
def panicAddress (loadBase : UInt64) : UInt64 := loadBase + Image.panicEntry

end ValidateFeePayer
