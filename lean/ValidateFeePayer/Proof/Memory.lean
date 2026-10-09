import X86.MemoryFacts
import ValidateFeePayer.Proof.Image

/-!
Memory across a run, relative to the entry memory `m0`: `Stored m0 m ws`
says `m` differs from `m0` only at addresses in the ranges `ws`, and has the
same readable and writable bytes.
-/

namespace ValidateFeePayer.Proof

open X86 Memory

theorem mapM_congr {α β ε : Type} {f g : α → Except ε β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.mapM_cons, h x (by simp), mapM_congr (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem bytes_congr {m m' : Memory} {acc : Access} {a : UInt64} {n : Nat}
    (h : ∀ i < n, m'.byte acc (a + i.toUInt64) = m.byte acc (a + i.toUInt64)) :
    m'.bytes acc a n = m.bytes acc a n :=
  mapM_congr fun i hi => h i (List.mem_range.1 hi)

theorem read_congr {m m' : Memory} {w : Width} {a : UInt64}
    (h : ∀ i < w.size, m'.byte .read (a + i.toUInt64) = m.byte .read (a + i.toUInt64)) :
    m'.read w a = m.read w a := by
  simp only [Memory.read, bytes_congr h]

theorem read128_congr {m m' : Memory} {a : UInt64}
    (h : ∀ i < 16, m'.byte .read (a + i.toUInt64) = m.byte .read (a + i.toUInt64)) :
    m'.read128 a = m.read128 a := by
  simp only [Memory.read128, bytes_congr h]

theorem byte_of_bytes {m : Memory} {acc : Access} {a : UInt64} {n : Nat} {bs : List UInt8}
    (h : m.bytes acc a n = .ok bs) : ∀ i < n, ∃ b, m.byte acc (a + i.toUInt64) = .ok b :=
  fun i hi => ok_of_mapM_ok h i (List.mem_range.2 hi)

theorem bytes_ok {m : Memory} {acc : Access} {a : UInt64} :
    ∀ {n : Nat}, (∀ i < n, ∃ b, m.byte acc (a + i.toUInt64) = .ok b) → ∃ bs, m.bytes acc a n = .ok bs
  | 0, _ => ⟨[], rfl⟩
  | n + 1, h => by
    obtain ⟨bs, hbs⟩ := bytes_ok (n := n) fun i hi => h i (by omega)
    obtain ⟨b, hb⟩ := h n (by omega)
    refine ⟨bs ++ [b], ?_⟩
    simp only [bytes, List.range_succ, List.mapM_append] at hbs ⊢
    simp only [hbs, List.mapM_cons, hb, List.mapM_nil]
    rfl

theorem writeBytes_eq {m m' : Memory} {a : UInt64} {bs : List UInt8} (h : m.writeBytes a bs = .ok m') :
    (∃ checked, m.bytes .write a bs.length = .ok checked) ∧ m' = ⟨stores a bs 0 m.mappings⟩ := by
  simp only [writeBytes, bind, Except.bind] at h
  split at h
  · cases h
  · cases h; exact ⟨⟨_, by assumption⟩, rfl⟩

theorem writeBytes_ok {m : Memory} {a : UInt64} {bs : List UInt8}
    (h : ∀ i < bs.length, ∃ b, m.byte .write (a + i.toUInt64) = .ok b) :
    m.writeBytes a bs = .ok ⟨stores a bs 0 m.mappings⟩ := by
  obtain ⟨checked, hc⟩ := bytes_ok h
  simp only [writeBytes, bind, Except.bind, hc]
  rfl

theorem writeBytes_byte_outside {m m' : Memory} {a : UInt64} {bs : List UInt8} {acc : Access} {x : UInt64}
    (h : m.writeBytes a bs = .ok m') (hx : ∀ i < bs.length, a + i.toUInt64 ≠ x) :
    m'.byte acc x = m.byte acc x := by
  obtain ⟨_, rfl⟩ := writeBytes_eq h
  exact go_stores_outside fun i _ hi => hx i (by omega)

theorem go_setByte_ok {acc : Access} {a x : UInt64} {v : UInt8} :
    ∀ {ms : List Mapping}, (∃ b, byte.go acc x ms = .ok b) → ∃ b, byte.go acc x (setByte a v ms) = .ok b
  | [], h => h
  | mp :: rest, h => by
    simp only [setByte]
    by_cases ha : mp.Contains a
    · simp only [ha, ↓reduceDIte, byte.go, Mapping.contains_set, Mapping.permissions_set]
      simp only [byte.go] at h
      split at h
      · rename_i hx
        simp only [hx, ↓reduceDIte]
        split at h
        · rename_i hp; simp [hp]
        · obtain ⟨_, h⟩ := h; cases h
      · rename_i hx; simp only [hx, ↓reduceDIte]; exact h
    · simp only [ha, ↓reduceDIte, byte.go]
      simp only [byte.go] at h
      split at h
      · rename_i hx; simp only [hx, ↓reduceDIte]; exact h
      · rename_i hx; simp only [hx, ↓reduceDIte]; exact go_setByte_ok h

theorem go_stores_ok {acc : Access} {a x : UInt64} :
    ∀ {bs : List UInt8} {k : Nat} {ms : List Mapping},
      (∃ b, byte.go acc x ms = .ok b) → ∃ b, byte.go acc x (stores a bs k ms) = .ok b
  | [], _, _, h => h
  | _ :: _, _, _, h => by rw [stores_cons]; exact go_stores_ok (go_setByte_ok h)

theorem writeBytes_byte_ok {m m' : Memory} {a : UInt64} {bs : List UInt8} {acc : Access} {x : UInt64}
    (h : m.writeBytes a bs = .ok m') (hx : ∃ b, m.byte acc x = .ok b) : ∃ b, m'.byte acc x = .ok b := by
  obtain ⟨_, rfl⟩ := writeBytes_eq h
  exact go_stores_ok hx

/-! ## Reads after a store -/

theorem length_littleEndianBytes_size (w : Width) (v : UInt64) : (littleEndianBytes w.size v).length = w.size :=
  length_littleEndianBytes _ _

theorem length_of_mapM_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → r.length = l.length
  | [], r, h => by cases h; rfl
  | x :: l, r, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hl; cases h; simp [length_of_mapM_ok hl]

theorem bytes_take {m : Memory} {acc : Access} {a : UInt64} {n k : Nat} {bs : List UInt8}
    (h : m.bytes acc a n = .ok bs) (hk : k ≤ n) : m.bytes acc a k = .ok (bs.take k) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  simp only [bytes, List.range_add, List.mapM_append, bind, Except.bind] at h ⊢
  split at h
  · cases h
  · rename_i l hl
    split at h
    · cases h
    · rename_i l' hl'
      cases h
      have : l.length = k := by simpa using length_of_mapM_ok hl
      subst this
      simpa using hl

theorem read_low_byte {m m' : Memory} {a v : UInt64} (h : m.write .bytes4 a v = .ok m') :
    m'.read .bytes1 a = .ok (v &&& 0xff) := by
  have := bytes_writeBytes h (by simp [length_littleEndianBytes, Width.size])
  rw [length_littleEndianBytes] at this
  have h1 := bytes_take this (k := 1) (by decide)
  simp only [Memory.read, Width.size, h1, bind, Except.bind, pure, Except.pure]
  simp only [littleEndianBytes, List.take, ofLittleEndian]
  congr 1
  bits64

/-! ## Stores relative to the entry memory -/

def InRanges (ws : List (UInt64 × Nat)) (x : UInt64) : Prop :=
  ∃ p ∈ ws, ∃ i < p.2, p.1 + i.toUInt64 = x

structure Stored (m0 m : Memory) (ws : List (UInt64 × Nat)) : Prop where
  outside : ∀ acc x, ¬ InRanges ws x → m.byte acc x = m0.byte acc x
  readOnly : ∀ acc x, (∀ v, m0.byte .write x ≠ .ok v) → m.byte acc x = m0.byte acc x
  writable : ∀ x v, m0.byte .write x = .ok v → ∃ v', m.byte .write x = .ok v'

theorem Stored.refl (m : Memory) (ws : List (UInt64 × Nat)) : Stored m m ws :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ v h => ⟨v, h⟩⟩

theorem Stored.write {m0 m m' : Memory} {ws : List (UInt64 × Nat)} {w : Width} {a v : UInt64}
    (h : Stored m0 m ws) (hw : m.write w a v = .ok m') : Stored m0 m' ((a, w.size) :: ws) where
  outside acc x hx := by
    rw [writeBytes_byte_outside hw fun i hi e => hx ⟨_, List.mem_cons_self, i,
      by rwa [length_littleEndianBytes_size] at hi, e⟩]
    exact h.outside acc x fun ⟨p, hp, hi⟩ => hx ⟨p, List.mem_cons_of_mem _ hp, hi⟩
  readOnly acc x hx := by
    have hm := h.readOnly .write x hx
    rw [writeBytes_byte_outside hw]
    · exact h.readOnly acc x hx
    · intro i hi e
      obtain ⟨checked, hc⟩ := (writeBytes_eq hw).1
      obtain ⟨b, hb⟩ := byte_of_bytes hc i hi
      rw [e, hm] at hb
      exact hx b hb
  writable x v hv := by
    obtain ⟨v', h'⟩ := h.writable x v hv
    exact writeBytes_byte_ok hw ⟨v', h'⟩

theorem Stored.trans_code {lb : UInt64} {m0 m : Memory} {ws : List (UInt64 × Nat)} (h : Stored m0 m ws)
    (hc : CodeAt lb m0) : CodeAt lb m := by
  intro x b hx
  obtain ⟨hf, hw⟩ := hc x b hx
  refine ⟨by rw [h.readOnly _ _ hw]; exact hf, fun v => by rw [h.readOnly _ _ hw]; exact hw v⟩

theorem Stored.trans_data {lb : UInt64} {m0 m : Memory} {ws : List (UInt64 × Nat)} (h : Stored m0 m ws)
    (hc : DataAt lb m0) : DataAt lb m := by
  intro r hr bytes hb i hi
  obtain ⟨hf, hw⟩ := hc r hr bytes hb i hi
  refine ⟨by rw [h.readOnly _ _ hw]; exact hf, fun v => by rw [h.readOnly _ _ hw]; exact hw v⟩

end ValidateFeePayer.Proof
