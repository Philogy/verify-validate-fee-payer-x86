import X86.MemoryFacts
import ValidateFeePayer.Checks

/-!
The carved image in memory: its bytes read (and the code fetches) as in the
binary, and none of them is writable. A store that succeeds therefore never
touches the image, which is how the image survives the run.
-/

namespace ValidateFeePayer.Proof

open X86 Memory

theorem go_of_mem {acc : Access} {y : UInt64} :
    ∀ {ms : List Mapping} (rest : List Mapping) {mp : Mapping},
      ms.Pairwise Mapping.Disjoint → mp ∈ ms → (h : mp.Contains y) →
      byte.go acc y (ms ++ rest) =
        if mp.permissions.allows acc then .ok (mp.get y h) else .error (.denied y acc)
  | [], _, _, _, hm, _ => by simp at hm
  | mp' :: ms, rest, mp, hd, hm, h => by
    simp only [List.cons_append, byte.go]
    rcases List.mem_cons.1 hm with rfl | hm
    · simp [h]
    · have hdisj := (List.pairwise_cons.1 hd).1 mp hm
      have : ¬ mp'.Contains y := by
        unfold Mapping.Disjoint at hdisj; unfold Mapping.Contains at h ⊢; omega
      simp only [this, ↓reduceDIte]
      exact go_of_mem rest (List.pairwise_cons.1 hd).2 hm h

def mappingOf (lb : UInt64) (r : Region) (bytes : ByteArray) : Mapping where
  base := lb + r.address
  bytes := bytes
  permissions := if r.contents.isCode then .readExecute else .readOnly

/-- Byte `i` of a carved region, as the loader maps it at `lb`. -/
theorem byte_image {lb : UInt64} (hBase : ValidLoadBase lb) {rest : List Mapping} {r : Region}
    (hr : r ∈ regions) {bytes : ByteArray} (hb : r.contents.bytesAt lb = some bytes) {i : Nat}
    (hi : i < bytes.size) (acc : Access) :
    byte ⟨imageMappings lb ++ rest⟩ acc (lb + r.address + i.toUInt64) =
      if (if r.contents.isCode then Permissions.readExecute else Permissions.readOnly).allows acc
      then .ok bytes[i] else .error (.denied (lb + r.address + i.toUInt64) acc) := by
  have hm : r.mapping lb = some (mappingOf lb r bytes) := by
    simp [Region.mapping, hb, mappingOf]
  obtain ⟨hbase, hend⟩ := Region.mapping_bounds hBase hr hm
  have hs := Contents.size_bytesAt hb
  have hwithin := List.all_eq_true.1 regions_within_image r hr
  simp only [decide_eq_true_eq] at hwithin
  unfold ValidLoadBase at hBase
  unfold Region.endAddress Region.size at hend hwithin
  simp only [Mapping.endAddress, mappingOf] at hend hbase
  have hy : (lb + r.address + i.toUInt64).toNat = lb.toNat + r.address.toNat + i := by
    simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (a := lb.toNat + r.address.toNat) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hc : Mapping.Contains (mappingOf lb r bytes) (lb + r.address + i.toUInt64) := by
    unfold Mapping.Contains Mapping.endAddress; simp only [mappingOf]; omega
  have hmem : mappingOf lb r bytes ∈ imageMappings lb :=
    List.mem_filterMap.2 ⟨r, hr, hm⟩
  simp only [byte]
  rw [go_of_mem rest (imageMappings_disjoint hBase) hmem hc]
  simp only [Mapping.get, mappingOf]
  simp only [Nat.toUInt64_eq] at hy ⊢
  simp only [show (lb + r.address + UInt64.ofNat i).toNat - (lb + r.address).toNat = i by omega]

/-- The code of the carved functions at `lb`, as the decoder fetches it, and
not writable. -/
def CodeAt (lb : UInt64) (m : Memory) : Prop :=
  ∀ x b, codeByte x = .ok b → m.byte .fetch (lb + x) = .ok b ∧ ∀ v, m.byte .write (lb + x) ≠ .ok v

/-- The carved constants and pointer slots at `lb`: readable as in the
binary and not writable. -/
def DataAt (lb : UInt64) (m : Memory) : Prop :=
  ∀ r ∈ Image.data, ∀ bytes, r.contents.bytesAt lb = some bytes → ∀ i (h : i < bytes.size),
    m.byte .read (lb + r.address + i.toUInt64) = .ok bytes[i] ∧
    ∀ v, m.byte .write (lb + r.address + i.toUInt64) ≠ .ok v

theorem codeByte_ok {x : UInt64} {b : UInt8} (h : codeByte x = .ok b) :
    ∃ r ∈ Image.functions, ∃ bytes, r.contents = .code bytes ∧ ∃ hi : x.toNat - r.address.toNat < bytes.size,
      r.address.toNat ≤ x.toNat ∧ bytes[x.toNat - r.address.toNat] = b := by
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

theorem codeAt_image {lb : UInt64} (hBase : ValidLoadBase lb) (rest : List Mapping) :
    CodeAt lb ⟨imageMappings lb ++ rest⟩ := by
  intro x b h
  obtain ⟨r, hr, bytes, hcode, hi, hle, hb⟩ := codeByte_ok h
  have hreg : r ∈ regions := List.mem_append_left _ hr
  have hbytes : r.contents.bytesAt lb = some bytes := by simp [hcode, Contents.bytesAt]
  have hx : lb + x = lb + r.address + (x.toNat - r.address.toNat).toUInt64 := by
    rw [UInt64.add_assoc]; congr 1
    apply UInt64.toNat_inj.1
    simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    have := x.toNat_lt; omega
  have hcodeb : r.contents.isCode = true := by simp [hcode, Contents.isCode]
  refine ⟨?_, fun v => ?_⟩
  · rw [hx, byte_image hBase hreg hbytes hi]; simp [hcodeb, Permissions.allows, Permissions.readExecute, hb]
  · rw [hx, byte_image hBase hreg hbytes hi]; simp [hcodeb, Permissions.allows, Permissions.readExecute]

theorem dataAt_image {lb : UInt64} (hBase : ValidLoadBase lb) (rest : List Mapping) :
    DataAt lb ⟨imageMappings lb ++ rest⟩ := by
  intro r hr bytes hb i hi
  have hreg : r ∈ regions := List.mem_append_right _ hr
  have hdata : r.contents.isCode = false := by
    simp [Image.data] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  refine ⟨?_, fun v => ?_⟩
  · rw [byte_image hBase hreg hb hi]; simp [hdata, Permissions.allows]
  · rw [byte_image hBase hreg hb hi]; simp [hdata, Permissions.allows, Permissions.readOnly]

end ValidateFeePayer.Proof
