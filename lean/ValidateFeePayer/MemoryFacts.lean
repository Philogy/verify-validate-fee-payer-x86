import ValidateFeePayer.Memory

/-!
Basic facts about `Memory`: a store that succeeds can be read back.

The lemma needs no well-formedness: `byte` reads from, and `setByte` writes
to, the *first* mapping containing an address, so they agree even if
mappings overlap.
-/

namespace ValidateFeePayer

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
  simp [set, Contains, endAddr, ByteArray.size_set']

@[simp] theorem perm_set {mp : Mapping} {a : UInt64} {h : mp.Contains a} {v : UInt8} :
    (mp.set a h v).perm = mp.perm := rfl

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

/-- Some mapping contains `x`. -/
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
    · simp only [hc, ↓reduceDIte, byte.go, Mapping.contains_set, Perm.allows]
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
    · simp only [hc, ↓reduceDIte, byte.go, Mapping.contains_set, Mapping.perm_set]
      by_cases hx : mp.Contains x
      · simp [hx, Mapping.get_set_ne _ hx hne]
      · simp [hx]
    · simp only [hc, ↓reduceDIte, byte.go, ih]

/-- The mappings after storing `bs` at `a + k`, `a + k + 1`, …, as `write` does. -/
def stores (a : UInt64) (bs : List UInt8) (k : Nat) (ms : List Mapping) : List Mapping :=
  (bs.zipIdx k).foldl (fun ms (b, i) => setByte (a + i.toUInt64) b ms) ms

theorem stores_cons {a : UInt64} {b : UInt8} {bs : List UInt8} {k : Nat} {ms : List Mapping} :
    stores a (b :: bs) k ms = stores a bs (k + 1) (setByte (a + k.toUInt64) b ms) := by
  simp [stores, List.zipIdx_cons]

/-- Addresses `a + i` for distinct small `i` are distinct. -/
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

theorem mapped_stores {a : UInt64} {bs : List UInt8} {k : Nat} {ms : List Mapping} {x : UInt64} :
    Mapped (stores a bs k ms) x ↔ Mapped ms x := by
  induction bs generalizing k ms with
  | nil => rfl
  | cons b bs ih => rw [stores_cons, ih, mapped_setByte]

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

theorem length_leBytes (n v : Nat) : (leBytes n v).length = n := by simp [leBytes]

theorem ofLEBytes_leBytes : ∀ (n v : Nat), ofLEBytes (leBytes n v) = v % 2 ^ (8 * n)
  | 0, v => by simp [leBytes, ofLEBytes]; exact (Nat.mod_one v).symm
  | n + 1, v => by
    have hcons : leBytes (n + 1) v = (v.toUInt8) :: leBytes n (v >>> 8) := by
      simp only [leBytes, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      apply List.map_congr_left; intro i _
      simp only [Function.comp, ← Nat.shiftRight_add]; congr 2; omega
    rw [hcons]
    simp only [ofLEBytes, List.foldr_cons] at *
    have ih := ofLEBytes_leBytes n (v >>> 8)
    simp only [ofLEBytes] at ih
    rw [ih, Nat.shiftRight_eq_div_pow]
    simp only [Nat.toUInt8, UInt8.toNat_ofNat']
    rw [show 8 * (n + 1) = 8 + 8 * n by omega, Nat.pow_add, Nat.mod_mul]

/-- A store that succeeds can be read back. -/
theorem read_write_same {m m' : Memory} {w : Width} {a : UInt64} {v : BitVec (8 * w.size)}
    (h : m.write w a v = .ok m') : m'.read w a = .ok v := by
  simp only [write, bind, Except.bind] at h
  split at h
  · cases h
  rename_i bs hbs
  cases h
  have hw : w.size ≤ 16 := by cases w <;> decide
  -- Every address written is mapped.
  have hmapped : ∀ i < w.size, Mapped m.mappings (a + (0 + i).toUInt64) := by
    intro i hi
    obtain ⟨b, hb⟩ := ok_of_mapM_ok hbs i (by simp [hi])
    exact mapped_of_go (by simpa [byte] using hb)
  let bs := leBytes w.size v.toNat
  have hlen : bs.length = w.size := length_leBytes ..
  simp only [read, bytes, byte, bind, Except.bind]
  rw [mapM_ok (g := fun j => bs.getD j 0)]
  · simp only [pure, Except.pure, Except.ok.injEq]
    have : (List.range w.size).map (fun j => bs.getD j 0) = bs := by
      apply List.ext_getElem
      · simp [bs, length_leBytes]
      · intro i h₁ h₂
        simp only [List.getElem_map, List.getElem_range]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some]
    rw [this, ofLEBytes_leBytes, Nat.mod_eq_of_lt v.isLt]
    simp
  · intro j hj
    have hj : j < w.size := by simpa using hj
    have := go_stores (a := a) (bs := bs) (k := 0) (ms := m.mappings)
      (by rw [hlen]; omega) (by rw [hlen]; exact hmapped) j (by rw [hlen]; exact hj)
    simp only [Nat.zero_add] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hj), Option.getD_some]
    exact this

end Memory

end ValidateFeePayer
