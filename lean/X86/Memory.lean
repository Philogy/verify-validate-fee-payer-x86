import X86.Bytes
import X86.OperandSize

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

structure Cell where
  permissions : Permissions
  byte : UInt8
  deriving DecidableEq, Repr

/-- What is at each address. One cell per address, so two mappings cannot
overlap. -/
structure Memory where
  cell : UInt64 → Option Cell

namespace Memory

def empty : Memory := ⟨fun _ => none⟩

/-- `m` with `bytes` mapped at `base`, replacing what was there. Bytes that
would lie past `2^64` are not mapped. -/
def map (m : Memory) (base : UInt64) (bytes : ByteArray) (permissions : Permissions) : Memory :=
  ⟨fun a => if h : base.toNat ≤ a.toNat ∧ a.toNat - base.toNat < bytes.size
    then some ⟨permissions, bytes[a.toNat - base.toNat]⟩ else m.cell a⟩

def byte (m : Memory) (access : Access) (address : UInt64) : Except PageFault UInt8 :=
  match m.cell address with
  | none => .error (.unmapped address access)
  | some c => if c.permissions.allows access then .ok c.byte else .error (.denied address access)

-- Byte by byte, so that an access straddling two adjacent mappings works as
-- on the CPU.
def bytes (m : Memory) (access : Access) (address : UInt64) (n : Nat) : Except PageFault (List UInt8) :=
  (List.range n).mapM fun i => m.byte access (address + i.toUInt64)

/-- Replace the byte at a mapped `address`, whatever its permissions. -/
def setByte (m : Memory) (address : UInt64) (v : UInt8) : Memory :=
  ⟨fun a => if a = address then (m.cell a).map ({ · with byte := v }) else m.cell a⟩

/-- `bs` stored from `a + k` on. -/
def stores (a : UInt64) (bs : List UInt8) (k : Nat) (m : Memory) : Memory :=
  (bs.zipIdx k).foldl (fun m (b, i) => m.setByte (a + i.toUInt64) b) m

-- Every byte is checked before any is written: a faulting store has no effect.
def writeBytes (m : Memory) (address : UInt64) (bs : List UInt8) : Except PageFault Memory := do
  let _ ← m.bytes .write address bs.length
  return stores address bs 0 m

def read (m : Memory) (w : OperandSize) (address : UInt64) : Except PageFault UInt64 := do
  return ofLittleEndian (← m.bytes .read address w.byteCount)

def write (m : Memory) (w : OperandSize) (address : UInt64) (v : UInt64) : Except PageFault Memory :=
  m.writeBytes address (littleEndianBytes w.byteCount v)

def read128 (m : Memory) (address : UInt64) : Except PageFault (BitVec 128) := do
  let bs ← m.bytes .read address 16
  return ofHalves (ofLittleEndian (bs.take 8)) (ofLittleEndian (bs.drop 8))

def write128 (m : Memory) (address : UInt64) (v : BitVec 128) : Except PageFault Memory :=
  m.writeBytes address (littleEndianBytes 8 (lowHalf v) ++ littleEndianBytes 8 (highHalf v))

def Holds (m : Memory) (w : OperandSize) (a v : UInt64) : Prop := m.read w a = .ok v

def HoldsBytes (m : Memory) (a : UInt64) (bs : List UInt8) : Prop := m.bytes .read a bs.length = .ok bs

def Readable (m : Memory) (a : UInt64) (n : Nat) : Prop :=
  ∀ i < n, ∃ b, m.byte .read (a + i.toUInt64) = .ok b

def Writable (m : Memory) (a : UInt64) (n : Nat) : Prop :=
  ∀ i < n, ∃ b, m.byte .write (a + i.toUInt64) = .ok b

end Memory

end X86
