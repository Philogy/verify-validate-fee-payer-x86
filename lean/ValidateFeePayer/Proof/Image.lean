import X86.MemoryFacts
import ValidateFeePayer.Checks

/-!
The carved image in memory: its bytes read (and the code fetches) as in the
binary, and none of them is writable. A store that succeeds therefore never
touches the image, which is how the image survives the run.
-/

namespace ValidateFeePayer.Proof

open X86 Memory

/-- Byte `i` of a carved region, in a memory the image is loaded in. -/
theorem byte_loaded {lb : UInt64} {m : Memory} (hl : Loaded lb m) {r : Region}
    (hr : r ∈ Image.regions) {bytes : ByteArray} (hb : r.contents.bytesAt lb = bytes) {i : Nat}
    (hi : i < bytes.size) (acc : Access) :
    m.byte acc (lb + r.address.off + i.toUInt64) =
      if r.permissions.allows acc then .ok bytes[i] else .error (.denied (lb + r.address.off + i.toUInt64) acc) := by
  subst hb
  have := hl.bytes r hr i hi
  simp only [ImageOffset.at] at this
  simp only [byte, this]

/-- The code of the carved functions at `lb`, as the decoder fetches it, and
not writable. -/
def CodeAt (lb : UInt64) (m : Memory) : Prop :=
  ∀ x b, codeByte x = .ok b → m.byte .fetch (lb + x) = .ok b ∧ ∀ v, m.byte .write (lb + x) ≠ .ok v

/-- The carved constants and pointer slots at `lb`: readable as in the
binary and not writable. -/
def DataAt (lb : UInt64) (m : Memory) : Prop :=
  ∀ r ∈ Image.data, ∀ bytes, r.contents.bytesAt lb = bytes → ∀ i (h : i < bytes.size),
    m.byte .read (lb + r.address.off + i.toUInt64) = .ok bytes[i] ∧
    ∀ v, m.byte .write (lb + r.address.off + i.toUInt64) ≠ .ok v

theorem codeByte_ok {x : UInt64} {b : UInt8} (h : codeByte x = .ok b) :
    ∃ r ∈ Image.functions, ∃ bytes, r.contents = .code bytes ∧ ∃ hi : x.toNat - r.address.off.toNat < bytes.size,
      r.address.off.toNat ≤ x.toNat ∧ bytes[x.toNat - r.address.off.toNat] = b := by
  unfold codeByte at h
  split at h
  · rename_i r name start bytes hf
    split at h
    · rename_i b' hb
      cases h
      have hr := List.mem_of_find?_eq_some hf
      have hc := List.find?_some hf
      simp only [Region.Contains, Region.endAddress] at hc
      rw [getElem?_eq_some_iff] at hb
      obtain ⟨hi, hb⟩ := hb
      exact ⟨_, hr, bytes, rfl, hi, (of_decide_eq_true hc).1, hb⟩
    · cases h
  · cases h

theorem codeAt_of_loaded {lb : UInt64} {m : Memory} (hl : Loaded lb m) : CodeAt lb m := by
  intro x b h
  obtain ⟨r, hr, bytes, hcode, hi, hle, hb⟩ := codeByte_ok h
  have hreg : r ∈ Image.regions := List.mem_append_left _ hr
  have hbytes : r.contents.bytesAt lb = bytes := by simp [hcode, Contents.bytesAt]
  have hx : lb + x = lb + r.address.off + (x.toNat - r.address.off.toNat).toUInt64 := by
    rw [UInt64.add_assoc]; congr 1
    apply UInt64.toNat_inj.1
    simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    have := x.toNat_lt; omega
  have hcodeb : r.contents.isCode = true := by simp [hcode, Contents.isCode]
  refine ⟨?_, fun v => ?_⟩
  · rw [hx, byte_loaded hl hreg hbytes hi]
    simp [Region.permissions, hcodeb, Permissions.allows, Permissions.readExecute, hb]
  · rw [hx, byte_loaded hl hreg hbytes hi]
    simp [Region.permissions, hcodeb, Permissions.allows, Permissions.readExecute]

theorem dataAt_of_loaded {lb : UInt64} {m : Memory} (hl : Loaded lb m) : DataAt lb m := by
  intro r hr bytes hb i hi
  have hreg : r ∈ Image.regions := List.mem_append_right _ hr
  have hdata : r.contents.isCode = false := by
    simp [Image.data] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  refine ⟨?_, fun v => ?_⟩
  · rw [byte_loaded hl hreg hb hi]; simp [Permissions.allows]
  · rw [byte_loaded hl hreg hb hi]; simp [Region.permissions, hdata, Permissions.allows, Permissions.readOnly]

end ValidateFeePayer.Proof
