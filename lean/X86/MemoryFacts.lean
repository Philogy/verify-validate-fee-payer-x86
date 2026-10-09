import X86.Memory

-- No well-formedness is needed: `byte` reads from, and `setByte` writes to,
-- the first mapping containing an address, so they agree even if mappings
-- overlap.

namespace X86

theorem ByteArray.size_set' (bs : ByteArray) (i : Nat) (v : UInt8) (h : i < bs.size) :
    (bs.set i v h).size = bs.size := by
  cases bs; exact Array.size_set ..

theorem ByteArray.getElem_set' (bs : ByteArray) (i j : Nat) (v : UInt8) (hi : i < bs.size)
    (hj : j < (bs.set i v hi).size) :
    (bs.set i v hi)[j] = if i = j then v else bs[j]'(by rw [ByteArray.size_set'] at hj; exact hj) := by
  cases bs; exact Array.getElem_set ..

namespace Mapping

@[simp] theorem contains_set {mp : Mapping} {a x : UInt64} {h : mp.Contains a} {v : UInt8} :
    (mp.set a h v).Contains x ↔ mp.Contains x := by
  simp [set, Contains, endAddress, ByteArray.size_set']

@[simp] theorem permissions_set {mp : Mapping} {a : UInt64} {h : mp.Contains a} {v : UInt8} :
    (mp.set a h v).permissions = mp.permissions := rfl

theorem get_set_same {mp : Mapping} {a : UInt64} {h : mp.Contains a} {v : UInt8} (h' : (mp.set a h v).Contains a) :
    (mp.set a h v).get a h' = v := by
  simp [get, set, ByteArray.getElem_set']

theorem get_set_ne {mp : Mapping} {a x : UInt64} {h : mp.Contains a} {v : UInt8}
    (h' : (mp.set a h v).Contains x) (hx : mp.Contains x) (hne : a ≠ x) :
    (mp.set a h v).get x h' = mp.get x hx := by
  simp only [get, set, ByteArray.getElem_set']
  have : a.toNat ≠ x.toNat := fun e => hne (UInt64.toNat_inj.1 e)
  unfold Contains at h hx
  simp only [show ¬ a.toNat - mp.base.toNat = x.toNat - mp.base.toNat by omega, ↓reduceIte]

end Mapping

namespace Memory

def Mapped (ms : List Mapping) (x : UInt64) : Prop := ∃ mp ∈ ms, mp.Contains x

theorem mapped_of_go {acc : Access} {x : UInt64} {ms : List Mapping} {b : UInt8}
    (h : byte.go acc x ms = .ok b) : Mapped ms x := by
  induction ms with
  | nil => simp [byte.go] at h
  | cons mp rest ih =>
    simp only [byte.go] at h
    split at h
    · exact ⟨mp, by simp, by assumption⟩
    · obtain ⟨mp', hm, hc⟩ := ih h
      exact ⟨mp', by simp [hm], hc⟩

theorem mapped_setByte {a x : UInt64} {v : UInt8} {ms : List Mapping} :
    Mapped (setByte a v ms) x ↔ Mapped ms x := by
  induction ms with
  | nil => simp [setByte]
  | cons mp rest ih =>
    simp only [setByte]
    split <;> simp_all [Mapped]

theorem go_setByte_same {acc : Access} {a : UInt64} {v : UInt8} {ms : List Mapping}
    (hm : Mapped ms a) (hacc : acc = .read) : byte.go acc a (setByte a v ms) = .ok v := by
  subst hacc
  induction ms with
  | nil => obtain ⟨_, h, _⟩ := hm; simp at h
  | cons mp rest ih =>
    simp only [setByte]
    by_cases hc : mp.Contains a
    · simp only [hc, ↓reduceDIte, byte.go, Mapping.contains_set, Permissions.allows]
      simp [Mapping.get_set_same]
    · simp only [hc, ↓reduceDIte, byte.go]
      apply ih
      obtain ⟨mp', h', hc'⟩ := hm
      simp only [List.mem_cons] at h'
      rcases h' with rfl | h'
      · exact absurd hc' hc
      · exact ⟨mp', h', hc'⟩

theorem go_setByte_ne {acc : Access} {a x : UInt64} {v : UInt8} {ms : List Mapping} (hne : a ≠ x) :
    byte.go acc x (setByte a v ms) = byte.go acc x ms := by
  induction ms with
  | nil => rfl
  | cons mp rest ih =>
    simp only [setByte]
    by_cases hc : mp.Contains a
    · simp only [hc, ↓reduceDIte, byte.go, Mapping.contains_set, Mapping.permissions_set]
      by_cases hx : mp.Contains x
      · simp [hx, Mapping.get_set_ne _ hx hne]
      · simp [hx]
    · simp only [hc, ↓reduceDIte, byte.go, ih]

def stores (a : UInt64) (bs : List UInt8) (k : Nat) (ms : List Mapping) : List Mapping :=
  (bs.zipIdx k).foldl (fun ms (b, i) => setByte (a + i.toUInt64) b ms) ms

theorem stores_cons {a : UInt64} {b : UInt8} {bs : List UInt8} {k : Nat} {ms : List Mapping} :
    stores a (b :: bs) k ms = stores a bs (k + 1) (setByte (a + k.toUInt64) b ms) := by
  simp [stores, List.zipIdx_cons]

theorem add_ne {a : UInt64} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (h : i ≠ j) :
    a + i.toUInt64 ≠ a + j.toUInt64 := by
  intro e
  have := congrArg UInt64.toNat ((UInt64.add_right_inj a).mp e)
  simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  exact h this

theorem go_stores_outside {acc : Access} {a : UInt64} {bs : List UInt8} {k : Nat} {ms : List Mapping}
    {x : UInt64} (hx : ∀ i, k ≤ i → i < k + bs.length → a + i.toUInt64 ≠ x) :
    byte.go acc x (stores a bs k ms) = byte.go acc x ms := by
  induction bs generalizing k ms with
  | nil => rfl
  | cons b bs ih =>
    rw [stores_cons, ih (fun i h1 h2 => hx i (by omega) (by simp at h2 ⊢; omega)),
      go_setByte_ne (hx k (by omega) (by simp))]

theorem go_stores {a : UInt64} {bs : List UInt8} {k : Nat} {ms : List Mapping}
    (hk : k + bs.length ≤ 2 ^ 64) (hm : ∀ i < bs.length, Mapped ms (a + (k + i).toUInt64))
    (j : Nat) (hj : j < bs.length) :
    byte.go .read (a + (k + j).toUInt64) (stores a bs k ms) = .ok bs[j] := by
  induction bs generalizing k ms j with
  | nil => simp at hj
  | cons b bs ih =>
    rw [stores_cons]
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.getElem_cons_zero]
      rw [go_stores_outside (fun i h1 h2 => add_ne (by simp only [List.length_cons] at hk; omega)
        (by simp only [List.length_cons] at hk; omega) (by omega))]
      exact go_setByte_same (by simpa using hm 0 (by simp)) rfl
    | succ j =>
      simp only [List.getElem_cons_succ]
      have := ih (k := k + 1) (ms := setByte (a + k.toUInt64) b ms) (by simp at hk; omega)
        (fun i hi => mapped_setByte.2 (by have := hm (i + 1) (by simp; omega); rwa [show k + (i + 1) = k + 1 + i by omega] at this))
        j (by simpa using hj)
      rwa [show k + 1 + j = k + (j + 1) by omega] at this

theorem mapM_ok {α β ε : Type} {f : α → Except ε β} {g : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = .ok (g x)) → l.mapM f = .ok (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.mapM_cons, List.map_cons, h x (by simp),
      mapM_ok (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

theorem ok_of_mapM_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → ∀ x ∈ l, ∃ b, f x = .ok b
  | [], _, _, x, hx => by simp at hx
  | y :: l, r, h, x, hx => by
    simp only [List.mapM_cons] at h
    cases hy : f y with
    | error e => rw [hy] at h; cases h
    | ok b =>
      rw [hy] at h
      cases hl : l.mapM f with
      | error e => rw [hl] at h; cases h
      | ok bs =>
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨b, hy⟩
        · exact ok_of_mapM_ok hl x hx

theorem bytes_writeBytes {m m' : Memory} {a : UInt64} {bs : List UInt8}
    (h : m.writeBytes a bs = .ok m') (hlen : bs.length ≤ 2 ^ 64) :
    m'.bytes .read a bs.length = .ok bs := by
  simp only [writeBytes, bind, Except.bind] at h
  split at h
  · cases h
  rename_i checked hchecked
  cases h
  have hmapped : ∀ i < bs.length, Mapped m.mappings (a + (0 + i).toUInt64) := by
    intro i hi
    obtain ⟨b, hb⟩ := ok_of_mapM_ok hchecked i (by simp [hi])
    exact mapped_of_go (by simpa [byte] using hb)
  simp only [bytes, byte]
  rw [mapM_ok (g := fun j => bs.getD j 0)]
  · congr 1
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some]
  · intro j hj
    have hj : j < bs.length := by simpa using hj
    have := go_stores (a := a) (bs := bs) (k := 0) (ms := m.mappings) (by omega) hmapped j hj
    simp only [Nat.zero_add] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact this

theorem getElem_umod_256 (x : BitVec 64) (i : Nat) (h : i < 64) :
    (x % 256#64)[i] = (x[i] && decide (i < 8)) := by
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.getElem_eq_testBit_toNat, BitVec.toNat_umod,
    show (256#64).toNat = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow, Bool.and_comm]

/-- An equation of bitwise `UInt64` expressions, bit by bit. Unlike
`bv_decide`, the proof is checked by the kernel alone, with no native
computation. -/
macro "bits64" : tactic => `(tactic| (
  apply UInt64.toBitVec_inj.1
  ext i hi
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i
  all_goals first
    | omega
    | simp [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_and, BitVec.getElem_not,
        UInt64.toBitVec_ofNat, getElem_umod_256] at *))

theorem length_littleEndianBytes (n : Nat) (v : UInt64) : (littleEndianBytes n v).length = n := by
  induction n generalizing v <;> simp_all [littleEndianBytes]

theorem ofLittleEndian_littleEndianBytes (w : OperandSize) (v : UInt64) :
    ofLittleEndian (littleEndianBytes w.byteCount v) = v &&& w.mask := by
  cases w <;> simp only [OperandSize.byteCount, OperandSize.mask, littleEndianBytes, ofLittleEndian] <;> bits64

theorem read_write_same {m m' : Memory} {w : OperandSize} {a : UInt64} {v : UInt64}
    (h : m.write w a v = .ok m') : m'.read w a = .ok (v &&& w.mask) := by
  have hlen := length_littleEndianBytes w.byteCount v
  have := bytes_writeBytes h (by rw [hlen]; cases w <;> decide)
  rw [hlen] at this
  simp [read, this, bind, Except.bind, pure, Except.pure, ofLittleEndian_littleEndianBytes]

end Memory

end X86
