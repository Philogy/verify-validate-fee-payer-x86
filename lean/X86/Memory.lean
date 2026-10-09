import X86.Bytes

namespace X86

structure Permissions where
  write : Bool
  execute : Bool
  deriving DecidableEq, Repr

namespace Permissions
def readOnly : Permissions := ⟨false, false⟩
def readWrite : Permissions := ⟨true, false⟩
def readExecute : Permissions := ⟨false, true⟩
end Permissions

inductive Access where
  | read
  | write
  | fetch
  deriving DecidableEq, Repr

-- x86-64 page tables cannot make a present page unreadable, so "not
-- readable" and "unmapped" are the same thing.
def Permissions.allows (p : Permissions) : Access → Bool
  | .read => true
  | .write => p.write
  | .fetch => p.execute

inductive PageFault where
  | unmapped (address : UInt64) (access : Access)
  | denied (address : UInt64) (access : Access)
  deriving DecidableEq, Repr

structure Mapping where
  base : UInt64
  bytes : ByteArray
  permissions : Permissions

namespace Mapping

-- A `Nat`, so that a mapping that ends at `2^64` does not wrap around to 0.
def endAddress (mp : Mapping) : Nat := mp.base.toNat + mp.bytes.size

def Contains (mp : Mapping) (address : UInt64) : Prop :=
  mp.base.toNat ≤ address.toNat ∧ address.toNat < mp.endAddress

instance (mp : Mapping) (address : UInt64) : Decidable (mp.Contains address) := by
  unfold Contains; infer_instance

def get (mp : Mapping) (address : UInt64) (h : mp.Contains address) : UInt8 :=
  mp.bytes[address.toNat - mp.base.toNat]'(by unfold Contains endAddress at h; omega)

def set (mp : Mapping) (address : UInt64) (h : mp.Contains address) (v : UInt8) : Mapping :=
  { mp with bytes := mp.bytes.set (address.toNat - mp.base.toNat) v (by unfold Contains endAddress at h; omega) }

def Disjoint (a b : Mapping) : Prop := a.endAddress ≤ b.base.toNat ∨ b.endAddress ≤ a.base.toNat

end Mapping

inductive Width where
  | bytes1 | bytes2 | bytes4 | bytes8
  deriving DecidableEq, Repr

def Width.size : Width → Nat
  | .bytes1 => 1 | .bytes2 => 2 | .bytes4 => 4 | .bytes8 => 8

def Width.mask : Width → UInt64
  | .bytes1 => 0xff | .bytes2 => 0xffff | .bytes4 => 0xffffffff | .bytes8 => 0xffffffffffffffff

structure Memory where
  mappings : List Mapping

namespace Memory

def byte (m : Memory) (access : Access) (address : UInt64) : Except PageFault UInt8 :=
  go m.mappings
where
  go : List Mapping → Except PageFault UInt8
    | [] => .error (.unmapped address access)
    | mp :: rest =>
      if h : mp.Contains address then
        if mp.permissions.allows access then .ok (mp.get address h) else .error (.denied address access)
      else go rest

-- Byte by byte, so that an access straddling two adjacent mappings works as
-- on the CPU.
def bytes (m : Memory) (access : Access) (address : UInt64) (n : Nat) : Except PageFault (List UInt8) :=
  (List.range n).mapM fun i => m.byte access (address + i.toUInt64)

def setByte (address : UInt64) (v : UInt8) : List Mapping → List Mapping
  | [] => []
  | mp :: rest =>
    if h : mp.Contains address then mp.set address h v :: rest else mp :: setByte address v rest

-- Every byte is checked before any is written: a faulting store has no effect.
def writeBytes (m : Memory) (address : UInt64) (bs : List UInt8) : Except PageFault Memory := do
  let _ ← m.bytes .write address bs.length
  return ⟨bs.zipIdx.foldl (fun ms (b, i) => setByte (address + i.toUInt64) b ms) m.mappings⟩

def read (m : Memory) (w : Width) (address : UInt64) : Except PageFault UInt64 := do
  return ofLittleEndian (← m.bytes .read address w.size)

def write (m : Memory) (w : Width) (address : UInt64) (v : UInt64) : Except PageFault Memory :=
  m.writeBytes address (littleEndianBytes w.size v)

def read128 (m : Memory) (address : UInt64) : Except PageFault (BitVec 128) := do
  let bs ← m.bytes .read address 16
  return ofHalves (ofLittleEndian (bs.take 8)) (ofLittleEndian (bs.drop 8))

def write128 (m : Memory) (address : UInt64) (v : BitVec 128) : Except PageFault Memory :=
  m.writeBytes address (littleEndianBytes 8 (lowHalf v) ++ littleEndianBytes 8 (highHalf v))

end Memory

end X86
