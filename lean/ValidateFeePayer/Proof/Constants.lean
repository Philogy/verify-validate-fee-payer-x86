import ValidateFeePayer.Proof.Walk

/-! The carved constants and pointer slots, as the code reads them. -/

namespace ValidateFeePayer.Proof

open X86 Memory

theorem bytes_data {lb : UInt64} {m : Memory} (hd : DataAt lb m) {r : Region} (hr : r ∈ Image.data)
    {bytes : ByteArray} (hb : r.contents.bytesAt lb = some bytes) {k n : Nat} (hn : k + n ≤ bytes.size) :
    m.bytes .read (lb + r.address + k.toUInt64) n = .ok ((List.range n).map fun i => bytes.data[k + i]!) := by
  unfold Memory.bytes
  apply mapM_ok
  intro i hi
  have hi : i < n := by simpa using hi
  have e : lb + r.address + k.toUInt64 + i.toUInt64 = lb + r.address + (k + i).toUInt64 := by
    rw [UInt64.add_assoc]; congr 1
    simp only [Nat.toUInt64_eq]
    apply UInt64.toNat_inj.1
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
    omega
  rw [e, (hd r hr bytes hb (k + i) (by omega)).1]
  congr 1
  rw [getElem!_pos bytes.data (k + i) (by simpa using (show k + i < bytes.size by omega))]
  rfl

/-- A constant region read at byte `k`. -/
macro "constant_read" r:term:max a:num k:num : tactic => `(tactic| (
  rw [show ($a : UInt64) = ($r).address + (($k : Nat).toUInt64) from rfl, ← UInt64.add_assoc]
  first
    | rw [Memory.read128, bytes_data ‹DataAt _ _› (by simp [Image.data]) rfl (by decide)]
    | rw [Memory.read, bytes_data ‹DataAt _ _› (by simp [Image.data]) rfl (by decide)]
  decide))

theorem read128_exponents {lb : UInt64} {m : Memory} (hd : DataAt lb m) :
    m.read128 (lb + 0x2e6f30) = .ok (ofHalves 0x4530000043300000 0) := by
  constant_read Image.u64_to_f64_exponents 0x2e6f30 0

theorem read128_bias {lb : UInt64} {m : Memory} (hd : DataAt lb m) :
    m.read128 (lb + 0x2e59a0) = .ok (ofHalves 0x4330000000000000 0x4530000000000000) := by
  constant_read Image.u64_to_f64_bias 0x2e59a0 0

theorem read128_systemProgramId_low {lb : UInt64} {m : Memory} (hd : DataAt lb m) :
    m.read128 (lb + 0x2f1060) = .ok 0 := by
  constant_read Image.system_program_id 0x2f1060 0

theorem read128_systemProgramId_high {lb : UInt64} {m : Memory} (hd : DataAt lb m) :
    m.read128 (lb + 0x2f1070) = .ok 0 := by
  constant_read Image.system_program_id 0x2f1070 16

theorem read_f64_2pow63 {lb : UInt64} {m : Memory} (hd : DataAt lb m) :
    m.read .bytes8 (lb + 0x2f5f28) = .ok 0x43e0000000000000 := by
  constant_read Image.f64_2pow63 0x2f5f28 0

theorem read_f64_maxBelow2pow64 {lb : UInt64} {m : Memory} (hd : DataAt lb m) :
    m.read .bytes8 (lb + 0x2f3b78) = .ok 0x43efffffffffffff := by
  constant_read Image.f64_max_below_2pow64 0x2f3b78 0

theorem read_got {lb : UInt64} {m : Memory} (hd : DataAt lb m) {r : Region} (hr : r ∈ Image.data)
    {target : UInt64} (ht : r.contents = .pointer target) :
    m.read .bytes8 (lb + r.address) = .ok (lb + target) := by
  have hb : r.contents.bytesAt lb = some ⟨(littleEndianBytes 8 (lb + target)).toArray⟩ := by
    simp [ht, Contents.bytesAt]
  have := bytes_data hd hr hb (k := 0) (n := 8) (by simp [ByteArray.size, length_littleEndianBytes])
  rw [show lb + r.address = lb + r.address + (0 : Nat).toUInt64 by simp, Memory.read, Width.size, this]
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
  have e : ((List.range 8).map fun i => (littleEndianBytes 8 (lb + target)).toArray[0 + i]!) =
      littleEndianBytes 8 (lb + target) := by
    simp [littleEndianBytes, List.range_succ]
  rw [e]
  have := ofLittleEndian_littleEndianBytes .bytes8 (lb + target)
  simp only [Width.size, Width.mask] at this
  rw [this, ValidateFeePayer.Proof.and_allOnes]

theorem read_got_expectFailed {lb : UInt64} {m : Memory} (hd : DataAt lb m) :
    m.read .bytes8 (lb + 0x37e9378) = .ok (lb + 0x12be100) :=
  read_got hd (r := Image.got_expect_failed) (by simp [Image.data]) rfl

theorem read_got_rentCheck {lb : UInt64} {m : Memory} (hd : DataAt lb m) :
    m.read .bytes8 (lb + 0x37f5120) = .ok (lb + 0x27f3790) :=
  read_got hd (r := Image.got_check_static_account_rent_state_transition) (by simp [Image.data]) rfl

attribute [vexec] read128_exponents read128_bias read128_systemProgramId_low read128_systemProgramId_high
  read_f64_2pow63 read_f64_maxBelow2pow64 read_got_expectFailed read_got_rentCheck

end ValidateFeePayer.Proof
