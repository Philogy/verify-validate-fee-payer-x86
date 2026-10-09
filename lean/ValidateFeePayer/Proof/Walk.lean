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

theorem DataAt.evolved {lb : UInt64} {m m' : Memory} (hd : DataAt lb m) (h : Evolved m m') :
    DataAt lb m' := h.data hd

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

/-- The SSE constants are 16-byte aligned in the binary, so at a 16-byte
aligned base. -/
@[vexec] theorem aligned_add {lb c : UInt64} (h : lb % 16 = 0) : (lb + c) % 16 = c % 16 := by
  apply UInt64.toNat_inj.1
  have h := congrArg UInt64.toNat h
  simp only [UInt64.toNat_mod, UInt64.toNat_add, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h ⊢
  have := lb.toNat_lt
  have := c.toNat_lt
  omega

/-- Fold `a op b` on `UInt64` literals, with an `Eq.refl` proof at the
literals. The built-in `UInt64.reduceAdd` is a `dsimproc`: it leaves no
proof, so the kernel has to rediscover `lb + c ≡ lb + (a + b)` itself, and
it may do so by unfolding `+` on the symbolic `lb`, which recurses once per
unit of a literal near `2 ^ 64`. -/
def foldLiterals (op : UInt64 → UInt64 → UInt64) (e : Expr) : SimpM Simp.Step := do
  unless e.getAppNumArgs == 6 do return .continue
  let some (x, _) ← getOfNatValue? e.appFn!.appArg! ``UInt64 | return .continue
  let some (y, _) ← getOfNatValue? e.appArg! ``UInt64 | return .continue
  let r := toExpr (op (UInt64.ofNat x) (UInt64.ofNat y))
  return .done { expr := r, proof? := some (← mkExpectedTypeHint (← mkEqRefl r) (← mkEq e r)) }

simproc foldAdd ((_ + _ : UInt64)) := foldLiterals (· + ·)
simproc foldSub ((_ - _ : UInt64)) := foldLiterals (· - ·)
simproc foldMul ((_ * _ : UInt64)) := foldLiterals (· * ·)
simproc foldMod ((_ % _ : UInt64)) := foldLiterals (· % ·)
simproc foldAnd ((_ &&& _ : UInt64)) := foldLiterals (· &&& ·)
simproc foldOr ((_ ||| _ : UInt64)) := foldLiterals (· ||| ·)
simproc foldXor ((_ ^^^ _ : UInt64)) := foldLiterals (· ^^^ ·)
simproc foldShiftLeft ((_ <<< _ : UInt64)) := foldLiterals (· <<< ·)
simproc foldShiftRight ((_ >>> _ : UInt64)) := foldLiterals (· >>> ·)

simproc foldToUInt64 (UInt8.toUInt64 _) := fun e => do
  let_expr UInt8.toUInt64 a := e | return .continue
  let some (x, _) ← getOfNatValue? a ``UInt8 | return .continue
  let r := toExpr (UInt8.ofNat x).toUInt64
  return .done { expr := r, proof? := some (← mkExpectedTypeHint (← mkEqRefl r) (← mkEq e r)) }

attribute [vexec] foldAdd foldSub foldMul foldMod foldAnd foldOr foldXor foldShiftLeft foldShiftRight
  foldToUInt64 UInt64.reduceGE UInt64.reduceGT UInt64.reduceLT UInt64.reduceLE OperandSize.bits

/-- Decide `a = b` on `UInt64` literals. -/
simproc decideEq ((_ : UInt64) = _) := fun e => do
  let_expr Eq _ a b := e | return .continue
  let some (x, _) ← getOfNatValue? a ``UInt64 | return .continue
  let some (y, _) ← getOfNatValue? b ``UInt64 | return .continue
  Simp.evalPropStep e (UInt64.ofNat x == UInt64.ofNat y)

attribute [vexec] decideEq

/-! ## Vector registers -/

@[vexec] theorem lowHalf_ofHalves (l h : UInt64) : lowHalf (ofHalves l h) = l := by
  simp only [lowHalf, ofHalves]; bv_decide

@[vexec] theorem highHalf_ofHalves (l h : UInt64) : highHalf (ofHalves l h) = h := by
  simp only [highHalf, ofHalves]; bv_decide

@[vexec] theorem lowHalf_interleaveLow32 (a b : BitVec 128) :
    lowHalf (lane32 b 1 ++ lane32 a 1 ++ lane32 b 0 ++ lane32 a 0) =
      ((lowHalf b &&& 0xffffffff) <<< 32) ||| (lowHalf a &&& 0xffffffff) := by
  simp only [lowHalf, lane32]; bv_decide

@[vexec] theorem highHalf_interleaveLow32 (a b : BitVec 128) :
    highHalf (lane32 b 1 ++ lane32 a 1 ++ lane32 b 0 ++ lane32 a 0) =
      (lowHalf b &&& (0xffffffff00000000 : UInt64)) ||| (lowHalf a >>> 32) := by
  simp only [lowHalf, highHalf, lane32]; bv_decide

@[vexec] theorem lowHalf_xor_self (a : BitVec 128) : lowHalf (a ^^^ a) = 0 := by
  simp only [lowHalf]; bv_decide

@[vexec] theorem xor_self (x : UInt64) : x ^^^ x = 0 := by bv_decide

@[vexec] theorem signExtend_bits64 (x : UInt64) : OperandSize.bits64.signExtend x = x := by
  -- The 64-bit sign extension is the identity: both branches are `x`.
  rw [OperandSize.signExtend, show OperandSize.bits64.mask = 0xffffffffffffffff from rfl,
    show ~~~(0xffffffffffffffff : UInt64) = 0 from by bv_decide]
  rw [show (x ||| 0 = x) from by bv_decide, show (x &&& 0xffffffffffffffff = x) from by bv_decide]
  split <;> rfl

/-- `sar x, 63`. -/
@[vexec] theorem shiftRightArithmetic_63 (x : UInt64) :
    (x.toInt64 >>> UInt64.toInt64 63).toUInt64 = if x < 0x8000000000000000 then 0 else 0xffffffffffffffff := by
  split <;> bv_decide

attribute [vexec] DoubleOp.eval

/-! ## Merging the two outcomes of a conditional move

Both branches of `cmovcc` write the destination, so the result is one state
whose register is an `if`. Conditional jumps produce the same shape in the
instruction pointer, which the walk then splits on. -/

section
variable {α β : Type} {c : Prop} [Decidable c]

@[vexec] theorem ite_ok {ε : Type} (a b : α) :
    (if c then (.ok a : Except ε α) else .ok b) = .ok (if c then a else b) := by
  split <;> rfl

@[vexec] theorem ite_pair (a b : α) (x y : β) :
    (if c then (a, x) else (b, y)) = (if c then a else b, if c then x else y) := by
  split <;> rfl

@[vexec] theorem ite_state (i i' : UInt64) (r r' : Vector UInt64 16) (f f' : Flags)
    (v v' : Vector (BitVec 128) 16) (fc fc' : UInt32) (m m' : Memory) :
    (if c then State.mk i r f v fc m else State.mk i' r' f' v' fc' m') =
      State.mk (if c then i else i') (if c then r else r') (if c then f else f') (if c then v else v')
        (if c then fc else fc') (if c then m else m') := by
  split <;> rfl

@[vexec] theorem ite_vector {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : α} :
    (if c then (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] : Vector α 16) else #v[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]) =
      #v[if c then a0 else b0, if c then a1 else b1, if c then a2 else b2, if c then a3 else b3, if c then a4 else b4, if c then a5 else b5, if c then a6 else b6, if c then a7 else b7, if c then a8 else b8, if c then a9 else b9, if c then a10 else b10, if c then a11 else b11, if c then a12 else b12, if c then a13 else b13, if c then a14 else b14, if c then a15 else b15] := by
  split <;> rfl

attribute [vexec] ite_self
end

macro "walk_disch" : tactic => `(tactic| first
  | assumption
  | (apply DataAt.evolved ‹DataAt _ _›; evolved)
  | writable
  | apart)

/-- One instruction: look it up, execute it, and simplify the next state. -/
syntax "vstep" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| vstep) => `(tactic| vstep [])
  | `(tactic| vstep [$ls,*]) => `(tactic| (
    apply Finishes.walk
    case hip => rfl
    case hx => assumption
    case hc => (try dsimp only); first | assumption | (apply CodeAt.evolved ‹CodeAt _ _›; evolved)
    -- Look the instruction up first: `simp` rewrites inside the continuation
    -- before the `DecodeThen` around it, and there `execute` of an unknown
    -- instruction would unfold into every case.
    simp only [decode_table, decodeThen_ok]
    simp (disch := walk_disch) only [execThen_ok, vexec, ↓reduceIte, ↓reduceDIte, $ls,*]))

end ValidateFeePayer.Proof
