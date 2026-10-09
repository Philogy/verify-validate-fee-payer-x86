import X86.Memory

namespace X86

namespace Memory

def Mapped (m : Memory) (x : UInt64) : Prop := ∃ c, m.cell x = some c

theorem mapped_of_byte {m : Memory} {acc : Access} {x : UInt64} {b : UInt8}
    (h : m.byte acc x = .ok b) : m.Mapped x := by
  unfold byte at h
  split at h
  · cases h
  · exact ⟨_, by assumption⟩

theorem cell_setByte {m : Memory} {a x : UInt64} {v : UInt8} :
    (m.setByte a v).cell x = if x = a then (m.cell x).map ({ · with byte := v }) else m.cell x := rfl

theorem mapped_setByte {m : Memory} {a x : UInt64} {v : UInt8} : (m.setByte a v).Mapped x ↔ m.Mapped x := by
  simp only [Mapped, cell_setByte]
  split
  · cases m.cell x <;> simp
  · rfl

theorem byte_setByte_same {m : Memory} {a : UInt64} {v : UInt8} (hm : m.Mapped a) :
    (m.setByte a v).byte .read a = .ok v := by
  obtain ⟨c, hc⟩ := hm
  simp [byte, cell_setByte, hc, Permissions.allows]

theorem byte_setByte_ne {m : Memory} {acc : Access} {a x : UInt64} {v : UInt8} (hne : a ≠ x) :
    (m.setByte a v).byte acc x = m.byte acc x := by
  simp only [byte, cell_setByte, show ¬ x = a from fun e => hne e.symm, ↓reduceIte]

/-- A store never changes whether an access succeeds, only the byte read. -/
theorem byte_setByte_ok {m : Memory} {acc : Access} {a x : UInt64} {v : UInt8}
    (h : ∃ b, m.byte acc x = .ok b) : ∃ b, (m.setByte a v).byte acc x = .ok b := by
  by_cases hx : x = a
  · obtain ⟨b, hb⟩ := h
    unfold byte at hb ⊢
    simp only [cell_setByte, hx, ↓reduceIte] at hb ⊢
    cases hc : m.cell a with
    | none => simp [hc] at hb
    | some c =>
      simp only [hc] at hb
      simp only [Option.map_some]
      split at hb
      · rename_i hp; exact ⟨v, by simp [hp]⟩
      · cases hb
  · rw [byte_setByte_ne (Ne.symm hx)]; exact h

theorem cell_map_inside {m : Memory} {base : UInt64} {bytes : ByteArray} {p : Permissions} {i : Nat}
    (hi : i < bytes.size) (hw : base.toNat + bytes.size ≤ 2 ^ 64) :
    (m.map base bytes p).cell (base + i.toUInt64) = some ⟨p, bytes[i]⟩ := by
  have : (base + i.toUInt64).toNat = base.toNat + i := by
    simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]
  simp only [map, this, Nat.add_sub_cancel_left]
  rw [dite_eq_left_of_eq_true (eq_true ⟨by omega, hi⟩)]

theorem cell_map_outside {m : Memory} {base a : UInt64} {bytes : ByteArray} {p : Permissions}
    (h : ¬ (base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + bytes.size)) : (m.map base bytes p).cell a = m.cell a := by
  simp only [map]
  rw [dite_eq_right_of_eq_false (eq_false (by omega))]

theorem stores_cons {a : UInt64} {b : UInt8} {bs : List UInt8} {k : Nat} {m : Memory} :
    stores a (b :: bs) k m = stores a bs (k + 1) (m.setByte (a + k.toUInt64) b) := by
  simp [stores, List.zipIdx_cons]

theorem add_ne {a : UInt64} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (h : i ≠ j) :
    a + i.toUInt64 ≠ a + j.toUInt64 := by
  intro e
  have := congrArg UInt64.toNat ((UInt64.add_right_inj a).mp e)
  simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  exact h this

theorem byte_stores_outside {acc : Access} {a : UInt64} {bs : List UInt8} {k : Nat} {m : Memory}
    {x : UInt64} (hx : ∀ i, k ≤ i → i < k + bs.length → a + i.toUInt64 ≠ x) :
    (stores a bs k m).byte acc x = m.byte acc x := by
  induction bs generalizing k m with
  | nil => rfl
  | cons b bs ih =>
    rw [stores_cons, ih (fun i h1 h2 => hx i (by omega) (by simp at h2 ⊢; omega)),
      byte_setByte_ne (hx k (by omega) (by simp))]

theorem byte_stores_ok {acc : Access} {a x : UInt64} :
    ∀ {bs : List UInt8} {k : Nat} {m : Memory},
      (∃ b, m.byte acc x = .ok b) → ∃ b, (stores a bs k m).byte acc x = .ok b
  | [], _, _, h => h
  | _ :: _, _, _, h => by rw [stores_cons]; exact byte_stores_ok (byte_setByte_ok h)

theorem byte_stores {a : UInt64} {bs : List UInt8} {k : Nat} {m : Memory}
    (hk : k + bs.length ≤ 2 ^ 64) (hm : ∀ i < bs.length, m.Mapped (a + (k + i).toUInt64))
    (j : Nat) (hj : j < bs.length) :
    (stores a bs k m).byte .read (a + (k + j).toUInt64) = .ok bs[j] := by
  induction bs generalizing k m j with
  | nil => simp at hj
  | cons b bs ih =>
    rw [stores_cons]
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.getElem_cons_zero]
      rw [byte_stores_outside (fun i h1 h2 => add_ne (by simp only [List.length_cons] at hk; omega)
        (by simp only [List.length_cons] at hk; omega) (by omega))]
      exact byte_setByte_same (by simpa using hm 0 (by simp))
    | succ j =>
      simp only [List.getElem_cons_succ]
      have := ih (k := k + 1) (m := m.setByte (a + k.toUInt64) b) (by simp at hk; omega)
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
  have hmapped : ∀ i < bs.length, m.Mapped (a + (0 + i).toUInt64) := by
    intro i hi
    obtain ⟨b, hb⟩ := ok_of_mapM_ok hchecked i (by simp [hi])
    exact mapped_of_byte (by simpa using hb)
  simp only [bytes]
  rw [mapM_ok (g := fun j => bs.getD j 0)]
  · congr 1
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some]
  · intro j hj
    have hj : j < bs.length := by simpa using hj
    have := byte_stores (a := a) (bs := bs) (k := 0) (m := m) (by omega) hmapped j hj
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
