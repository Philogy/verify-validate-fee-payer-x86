import ValidateFeePayer.Proof.Vexec
import ValidateFeePayer.Contract

/-!
Memory during a symbolic walk is the block's entry memory under a chain of
`wr`s. The lemmas here let `simp` read through such a chain, and the
dischargers prove their side conditions: writability from the entry
memory, and disjointness by `omega` on the addresses as `Nat`s.
-/

namespace ValidateFeePayer.Proof

open X86 Memory Lean Elab Tactic Meta

def WritableAt (m : Memory) (a : UInt64) (n : Nat) : Prop :=
  ∀ i < n, ∃ b, m.byte .write (a + i.toUInt64) = .ok b

theorem WritableAt.wr {m : Memory} {a b v : UInt64} {n : Nat} {w : Width} (h : WritableAt m a n) :
    WritableAt (wr m w b v) a n :=
  fun i hi => go_stores_ok (h i hi)

theorem WritableAt.le {m : Memory} {a : UInt64} {n n' : Nat} (h : WritableAt m a n) (hn : n' ≤ n) :
    WritableAt m a n' :=
  fun i hi => h i (by omega)

theorem WritableAt.sub {m : Memory} {a k : UInt64} {n n' : Nat} (h : WritableAt m a n)
    (hk : k.toNat + n' ≤ n) : WritableAt m (a + k) n' := by
  intro i hi
  obtain ⟨b, hb⟩ := h (k.toNat + i) (by omega)
  refine ⟨b, ?_⟩
  have e : a + k + i.toUInt64 = a + (k.toNat + i).toUInt64 := by
    rw [UInt64.add_assoc]
    congr 1
    apply UInt64.toNat_inj.1
    simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    have := k.toNat_lt
    omega
  rw [e]; exact hb

theorem WritableAt.of_writable {m : Memory} {a : UInt64} {n : Nat} (h : m.Writable a n) :
    WritableAt m a n := by
  obtain ⟨bs, hbs⟩ := h
  exact fun i hi => byte_of_bytes hbs i hi

theorem write_eq_wr {m : Memory} {w : Width} {a v : UInt64} (h : WritableAt m a w.size) :
    m.write w a v = .ok (wr m w a v) :=
  writeBytes_ok (by rw [length_littleEndianBytes_size]; exact h)

/-- `a` plus offsets below `n` never equals `b` plus offsets below `n'`. -/
def Apart (a : UInt64) (n : Nat) (b : UInt64) (n' : Nat) : Prop :=
  ∀ i < n, ∀ j < n', a + i.toUInt64 ≠ b + j.toUInt64

theorem byte_wr_other {m : Memory} {w : Width} {a v x : UInt64} {acc : Access}
    (h : ∀ j < w.size, a + j.toUInt64 ≠ x) : (wr m w a v).byte acc x = m.byte acc x :=
  go_stores_outside fun j _ hj => h j (by rw [length_littleEndianBytes_size] at hj; omega)

theorem read_wr_other {m : Memory} {w w' : Width} {a b v : UInt64} (h : Apart a w.size b w'.size) :
    (wr m w a v).read w' b = m.read w' b :=
  read_congr fun i hi => byte_wr_other fun j hj => h j hj i hi

theorem read128_wr_other {m : Memory} {w : Width} {a b v : UInt64} (h : Apart a w.size b 16) :
    (wr m w a v).read128 b = m.read128 b :=
  read128_congr fun i hi => byte_wr_other fun j hj => h j hj i hi

theorem bytes_wr_other {m : Memory} {w : Width} {a b v : UInt64} {n : Nat} (h : Apart a w.size b n) :
    (wr m w a v).bytes .read b n = m.bytes .read b n :=
  bytes_congr fun i hi => byte_wr_other fun j hj => h j hj i hi

theorem read_wr_same {m : Memory} {w : Width} {a v : UInt64} (h : WritableAt m a w.size) :
    (wr m w a v).read w a = .ok (v &&& w.mask) :=
  read_write_same (write_eq_wr h)

theorem read_wr_lowByte {m : Memory} {a v : UInt64} (h : WritableAt m a Width.bytes4.size) :
    (wr m .bytes4 a v).read .bytes1 a = .ok (v &&& 0xff) :=
  read_low_byte (write_eq_wr h)

/-- `m'` is `m` after stores that all succeeded. -/
def Evolved (m m' : Memory) : Prop := ∃ ws, Stored m m' ws

theorem Evolved.refl (m : Memory) : Evolved m m := ⟨[], Stored.refl m []⟩

theorem Evolved.wr {m m' : Memory} {w : Width} {a v : UInt64} (h : Evolved m m')
    (hw : WritableAt m' a w.size) : Evolved m (wr m' w a v) := by
  obtain ⟨ws, h⟩ := h
  exact ⟨_, h.write (write_eq_wr hw)⟩

theorem Evolved.code {lb : UInt64} {m m' : Memory} (h : Evolved m m') (hc : CodeAt lb m) :
    CodeAt lb m' := by
  obtain ⟨_, h⟩ := h; exact h.trans_code hc

theorem CodeAt.evolved {lb : UInt64} {m m' : Memory} (hc : CodeAt lb m) (h : Evolved m m') :
    CodeAt lb m' := h.code hc

theorem Evolved.data {lb : UInt64} {m m' : Memory} (h : Evolved m m') (hd : DataAt lb m) :
    DataAt lb m' := by
  obtain ⟨_, h⟩ := h; exact h.trans_data hd

theorem Evolved.writable {m m' : Memory} {a : UInt64} {n : Nat} (h : Evolved m m')
    (hw : WritableAt m a n) : WritableAt m' a n := by
  obtain ⟨ws, h⟩ := h
  intro i hi
  obtain ⟨b, hb⟩ := hw i hi
  exact h.writable _ _ hb

theorem Evolved.trans {m m' m'' : Memory} (h : Evolved m m') (h' : Evolved m' m'') : Evolved m m'' := by
  obtain ⟨ws, h⟩ := h
  obtain ⟨ws', h'⟩ := h'
  refine ⟨ws' ++ ws, fun acc x hx => ?_, fun acc x hx => ?_, fun x v hv => ?_⟩
  · rw [h'.outside acc x fun ⟨p, hp, hi⟩ => hx ⟨p, List.mem_append_left _ hp, hi⟩]
    exact h.outside acc x fun ⟨p, hp, hi⟩ => hx ⟨p, List.mem_append_right _ hp, hi⟩
  · rw [h'.readOnly acc x fun v e => hx v (by rw [← h.readOnly .write x hx]; exact e)]
    exact h.readOnly acc x hx
  · obtain ⟨v', hv'⟩ := h.writable x v hv
    exact h'.writable x v' hv'

/-! ## Dischargers -/

/-- `WritableAt` of a `wr` chain, from a `WritableAt` hypothesis about its
base, possibly for a larger range. -/
macro "writable" : tactic => `(tactic| (
  repeat' apply WritableAt.wr
  first
    | assumption
    | (apply WritableAt.le (by assumption); decide)
    | (apply WritableAt.sub (by assumption); decide)))

/-- `Evolved base chain`. -/
macro "evolved" : tactic => `(tactic| (
  repeat' (first | exact Evolved.refl _ | (apply Evolved.wr; rotate_left; writable))))

/-- Two objects as `Nat` intervals do not overlap. Kept behind a definition
so that `omega` does not see it: with many of these in context it would
split on every disjunction. -/
def Separate (a : UInt64) (n : Nat) (b : UInt64) (n' : Nat) : Prop :=
  a.toNat + n ≤ b.toNat ∨ b.toNat + n' ≤ a.toNat

/-- Prove `Apart a n b n'` by `omega` on the addresses as `Nat`s, using at
most one `Separate` hypothesis. -/
elab "apart" : tactic => do
  evalTactic (← `(tactic| (
    unfold Apart
    intro i hi j hj
    -- Dischargers run at reducible transparency, which does not unfold `≠`.
    with_unfolding_all intro e
    replace e := congrArg UInt64.toNat e
    simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt64.toNat_ofNat,
      Width.size, Nat.reducePow, Nat.reduceMod] at e hi hj)))
  if ← tryTactic (evalTactic (← `(tactic| omega))) then return
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type).isAppOf ``Separate then
      let h := mkIdent d.userName
      if ← tryTactic (evalTactic (← `(tactic| (have h' := $h; unfold Separate at h'; omega)))) then return
  throwError "apart: no hypothesis separates the addresses"

/-! ## Stepping -/

attribute [vexec] beq_iff_eq reduceCtorEq Bool.or_eq_true Bool.and_eq_true or_false false_or or_self
  and_true true_and and_false false_and ite_true ite_false Bool.false_eq_true
  not_false_eq_true not_true_eq_false decide_eq_true_eq decide_not Bool.not_eq_true' bne_iff_ne ne_eq
  Bool.not_eq_eq_eq_not Bool.not_true Bool.not_false Bool.and_true Bool.true_and Bool.or_false Bool.false_or
  dite_eq_ite
attribute [vexec] Nat.reducePow Nat.reduceMod Nat.reduceSub read_wr_lowByte read_wr_other read128_wr_other bytes_wr_other write_eq_wr
attribute [vexec high] read_wr_same

@[vexec] theorem resultFlags_zero {size : OperandSize} {r : UInt64} {c o a : Option Bool} :
    (Arithmetic.resultFlags size r c o a).zero = some (r == 0) := rfl

@[vexec] theorem resultFlags_carry {size : OperandSize} {r : UInt64} {c o a : Option Bool} :
    (Arithmetic.resultFlags size r c o a).carry = c := rfl

/-- Stack addresses stay `base + offset` with a literal offset. -/
@[vexec] theorem sub_literal (x : UInt64) (n : Nat) :
    x - (no_index (OfNat.ofNat n : UInt64)) = x + UInt64.ofNat (2 ^ 64 - n % 2 ^ 64) := by
  apply UInt64.toNat_inj.1
  simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat]
  have := x.toNat_lt
  omega

macro "walk_disch" : tactic => `(tactic| first | writable | apart)

/-- One instruction: look it up, execute it, and simplify the next state. -/
syntax "vstep" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| vstep) => `(tactic| vstep [])
  | `(tactic| vstep [$ls,*]) => `(tactic| (
    refine Finishes.step' (by assumption)
      (by (try dsimp only); first | assumption | (apply CodeAt.evolved ‹CodeAt _ _›; evolved)) rfl ?_
    simp (disch := walk_disch) only [decode_table, vexec, ↓reduceIte, ↓reduceDIte, $ls,*]))

end ValidateFeePayer.Proof
