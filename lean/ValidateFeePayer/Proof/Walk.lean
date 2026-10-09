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

theorem _root_.X86.Memory.Writable.wr {m : Memory} {a b v : UInt64} {n : Nat} {w : OperandSize} (h : Writable m a n) :
    Writable (wr m w b v) a n :=
  fun i hi => go_stores_ok (h i hi)

theorem _root_.X86.Memory.Writable.le {m : Memory} {a : UInt64} {n n' : Nat} (h : Writable m a n) (hn : n' ≤ n) :
    Writable m a n' :=
  fun i hi => h i (by omega)

theorem _root_.X86.Memory.Writable.sub {m : Memory} {a k : UInt64} {n n' : Nat} (h : Writable m a n)
    (hk : k.toNat + n' ≤ n) : Writable m (a + k) n' := by
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

theorem write_eq_wr {m : Memory} {w : OperandSize} {a v : UInt64} (h : Writable m a w.byteCount) :
    m.write w a v = .ok (wr m w a v) :=
  writeBytes_ok (by rw [length_littleEndianBytes_size]; exact h)

/-- `a` plus offsets below `n` never equals `b` plus offsets below `n'`. -/
def Apart (a : UInt64) (n : Nat) (b : UInt64) (n' : Nat) : Prop :=
  ∀ i < n, ∀ j < n', a + i.toUInt64 ≠ b + j.toUInt64

theorem byte_wr_other {m : Memory} {w : OperandSize} {a v x : UInt64} {acc : Access}
    (h : ∀ j < w.byteCount, a + j.toUInt64 ≠ x) : (wr m w a v).byte acc x = m.byte acc x :=
  go_stores_outside fun j _ hj => h j (by rw [length_littleEndianBytes_size] at hj; omega)

theorem read_wr_other {m : Memory} {w w' : OperandSize} {a b v : UInt64} (h : Apart a w.byteCount b w'.byteCount) :
    (wr m w a v).read w' b = m.read w' b :=
  read_congr fun i hi => byte_wr_other fun j hj => h j hj i hi

theorem read128_wr_other {m : Memory} {w : OperandSize} {a b v : UInt64} (h : Apart a w.byteCount b 16) :
    (wr m w a v).read128 b = m.read128 b :=
  read128_congr fun i hi => byte_wr_other fun j hj => h j hj i hi

theorem bytes_wr_other {m : Memory} {w : OperandSize} {a b v : UInt64} {n : Nat} (h : Apart a w.byteCount b n) :
    (wr m w a v).bytes .read b n = m.bytes .read b n :=
  bytes_congr fun i hi => byte_wr_other fun j hj => h j hj i hi

theorem read_wr_same {m : Memory} {w : OperandSize} {a v : UInt64} (h : Writable m a w.byteCount) :
    (wr m w a v).read w a = .ok (v &&& w.mask) :=
  read_write_same (write_eq_wr h)

theorem read_wr_lowByte {m : Memory} {a v : UInt64} (h : Writable m a OperandSize.bits32.byteCount) :
    (wr m .bits32 a v).read .bits8 a = .ok (v &&& 0xff) :=
  read_low_byte (write_eq_wr h)

/-- `m'` is `m` after stores that all succeeded. -/
def Evolved (m m' : Memory) : Prop := ∃ ws, Stored m m' ws

theorem Evolved.refl (m : Memory) : Evolved m m := ⟨[], Stored.refl m []⟩

theorem Evolved.wr {m m' : Memory} {w : OperandSize} {a v : UInt64} (h : Evolved m m')
    (hw : Writable m' a w.byteCount) : Evolved m (wr m' w a v) := by
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

/-! ## Dischargers -/

/-- `Writable` of a `wr` chain, from a `Writable` hypothesis about its
base, possibly for a larger range. -/
macro "writableByApply" : tactic => `(tactic| (
  repeat' apply X86.Memory.Writable.wr
  -- Reducible unification only: matching `S + 80` against `met + ?k` at
  -- default transparency unfolds `UInt64` addition.
  first
    | with_reducible assumption
    | (with_reducible refine X86.Memory.Writable.le (n := ?n) ?h ?hn
       case h => with_reducible assumption
       case hn => decide)
    | (with_reducible refine X86.Memory.Writable.sub (n := ?n) ?h ?hk
       case h => with_reducible assumption
       case hk => decide)))

/-- `a` as `x + c` with `c` a literal, and a proof of `a = x + c`. -/
def withOffset (a : Expr) : MetaM (Expr × Expr × Expr) := do
  match_expr a with
  | HAdd.hAdd _ _ _ _ x c =>
    if (← getOfNatValue? c ``UInt64).isSome then return (x, c, ← mkEqRefl a)
  | _ => pure ()
  let zero := toExpr (0 : UInt64)
  return (a, zero, ← mkEqSymm (mkApp (mkConst ``UInt64.add_zero) a))

/-- A proof of `p` by `decide`, if it holds. -/
def decideProof? (p : Expr) : MetaM (Option Expr) := do
  let d ← mkDecide p
  let r ← withAtLeastTransparency .default <| whnf d
  unless r.isConstOf ``true do return none
  return some (mkApp3 (mkConst ``of_decide_eq_true) p d.appArg! (← mkEqRefl (mkConst ``true)))

/-- The memory under a chain of `wr`s, and the stores, outermost first, each
with the memory it stores into. -/
partial def stores (m : Expr) (acc : Array (Expr × Expr × Expr × Expr) := #[]) :
    Expr × Array (Expr × Expr × Expr × Expr) :=
  match_expr m with
  | wr m' w a v => stores m' (acc.push (m', w, a, v))
  | _ => (m, acc)

/-- `Writable m a n` from a hypothesis `Writable m a' n'` with `a` at a
literal offset in it. -/
def writableAtBase? (m a n : Expr) : MetaM (Option Expr) := do
  let (x, k, _) ← withOffset a
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let_expr X86.Memory.Writable m' a' n' := ← instantiateMVars d.type | continue
    unless m' == m do continue
    if a' == a then
      if n' == n then return some d.toExpr
      let some hn ← decideProof? (mkNatLE n n') | continue
      return some (mkAppN (mkConst ``X86.Memory.Writable.le) #[m, a, n', n, d.toExpr, hn])
    if a' == x then
      let some hk ← decideProof? (mkNatLE (mkNatAdd (mkApp (mkConst ``UInt64.toNat) k) n) n') | continue
      return some (mkAppN (mkConst ``X86.Memory.Writable.sub) #[m, a', k, n', n, d.toExpr, hk])
  return none

/-- `Writable` of a `wr` chain, as `writableByApply` proves it, built as a
term: by `apply`, a walk spends half its time here. -/
def writableProof? (t : Expr) : MetaM (Option Expr) := do
  let_expr X86.Memory.Writable m a n := t | return none
  if t.hasMVar then return none
  let (base, ss) := stores m
  let some h ← writableAtBase? base a n | return none
  return some <| ss.foldr (init := h) fun (m', w, b, v) pf =>
    mkAppN (mkConst ``X86.Memory.Writable.wr) #[m', a, b, v, n, w, pf]

/-- `Evolved base chain`, built as a term. -/
def evolvedProof? (t : Expr) : MetaM (Option Expr) := do
  let_expr Evolved base m := t | return none
  if t.hasMVar then return none
  let (base', ss) := stores m
  unless base' == base do return none
  let mut pf := mkApp (mkConst ``Evolved.refl) base
  for (m', w, a, v) in ss.reverse do
    let some hw ← writableProof? (mkApp3 (mkConst ``X86.Memory.Writable) m' a (mkApp (mkConst ``OperandSize.byteCount) w))
      | return none
    pf := mkAppN (mkConst ``Evolved.wr) #[base, m', w, a, v, pf, hw]
  return some pf

/-- Close the main goal with `proof? target`, else run `fallback`. -/
def closeWith (proof? : Expr → MetaM (Option Expr)) (fallback : TacticM Unit) : TacticM Unit := do
  let g ← getMainGoal
  if let some pf ← g.withContext do proof? (← instantiateMVars (← g.getType)) then
    g.assign pf; replaceMainGoal []
  else fallback

elab "writable" : tactic => closeWith writableProof? do evalTactic (← `(tactic| writableByApply))

/-- `Evolved base chain`. -/
macro "evolvedByApply" : tactic => `(tactic| (
  repeat' (first | with_reducible exact Evolved.refl _ | (apply Evolved.wr; rotate_left; writable))))

elab "evolved" : tactic => closeWith evolvedProof? do evalTactic (← `(tactic| evolvedByApply))

/-- Two objects as `Nat` intervals do not overlap; an empty one overlaps
nothing. Kept behind a definition so that `omega` does not see it: with many
of these in context it would split on every disjunction. -/
def Separate (a : UInt64) (n : Nat) (b : UInt64) (n' : Nat) : Prop :=
  n = 0 ∨ n' = 0 ∨ a.toNat + n ≤ b.toNat ∨ b.toNat + n' ≤ a.toNat

/-- The object an address points into: `x` for `x + c` with `c` a literal. -/
def addressBase (a : Expr) : MetaM Expr := do
  match_expr a with
  | HAdd.hAdd _ _ _ _ x c => if (← getOfNatValue? c ``UInt64).isSome then return x else return a
  | _ => return a

theorem Separate.symm {a b : UInt64} {n n' : Nat} (h : Separate a n b n') : Separate b n' a n := by
  unfold Separate at *; omega

theorem apart_of_separate {a b x y c1 c2 : UInt64} {n n' N N' : Nat} (ha : a = x + c1) (hb : b = y + c2)
    (hs : Separate x N y N') (hx : x.toNat + N ≤ 2 ^ 64) (hy : y.toNat + N' ≤ 2 ^ 64)
    (h1 : c1.toNat + n ≤ N) (h2 : c2.toNat + n' ≤ N') : Apart a n b n' := by
  subst ha hb
  intro i hi j hj e
  replace e := congrArg UInt64.toNat e
  simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat'] at e
  unfold Separate at hs
  omega

theorem apart_same {a b x c1 c2 : UInt64} {n n' : Nat} (ha : a = x + c1) (hb : b = x + c2)
    (h : c1.toNat + n ≤ c2.toNat ∧ c2.toNat + n' ≤ c1.toNat + 2 ^ 64 ∨
      c2.toNat + n' ≤ c1.toNat ∧ c1.toNat + n ≤ c2.toNat + 2 ^ 64) : Apart a n b n' := by
  subst ha hb
  intro i hi j hj e
  replace e := congrArg UInt64.toNat e
  simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat'] at e
  have := x.toNat_lt; have := c1.toNat_lt; have := c2.toNat_lt
  omega

/-- `Apart a n b n'` without `omega`, when both addresses are an object plus a
literal offset: from the offsets alone within one object, or from the
objects' `Separate` and bounds hypotheses. -/
def apartByOffsets? (a n b n' : Expr) : TacticM (Option Expr) := withMainContext do
  let (x, c1, ha) ← withOffset a
  let (y, c2, hb) ← withOffset b
  let toNat (e : Expr) := mkApp (mkConst ``UInt64.toNat) e
  let add (u v : Expr) := mkNatAdd u v
  let le (u v : Expr) := mkNatLE u v
  let pow64 := mkNatLit (2 ^ 64)
  if x == y then
    let p := mkOr (mkAnd (le (add (toNat c1) n) (toNat c2)) (le (add (toNat c2) n') (add (toNat c1) pow64)))
      (mkAnd (le (add (toNat c2) n') (toNat c1)) (le (add (toNat c1) n) (add (toNat c2) pow64)))
    let some h ← decideProof? p | return none
    return some (← mkAppM ``apart_same #[ha, hb, h])
  let lctx ← getLCtx
  let bound? (z N : Expr) : MetaM (Option Expr) := do
    for d in lctx do
      if d.isImplementationDetail then continue
      let_expr LE.le _ _ l r := d.type | continue
      let_expr HAdd.hAdd _ _ _ _ zt N' := l | continue
      let_expr UInt64.toNat z' := zt | continue
      unless z' == z && N' == N do continue
      if (← getNatValue? r) == some (2 ^ 64) || (r.isAppOf ``HPow.hPow) then return some d.toExpr
    return none
  for d in lctx do
    if d.isImplementationDetail then continue
    let_expr Separate p N q N' := d.type | continue
    let hs ← if p == x && q == y then pure d.toExpr
      else if p == y && q == x then mkAppM ``Separate.symm #[d.toExpr] else continue
    let (N, N') := if p == x then (N, N') else (N', N)
    let some hx ← bound? x N | return none
    let some hy ← bound? y N' | return none
    -- Within the object: by `decide` on literals, or the whole object at offset 0.
    let within (c m M : Expr) : MetaM (Option Expr) := do
      if let some h ← decideProof? (le (add (toNat c) m) M) then return some h
      if m == M && (← getUInt64Value? c) == some 0 then
        return some (← mkAppM ``Nat.le_of_eq #[← mkAppM ``Nat.zero_add #[m]])
      return none
    let some h1 ← within c1 n N | return none
    let some h2 ← within c2 n' N' | return none
    return some (← mkAppM ``apart_of_separate #[ha, hb, hs, hx, hy, h1, h2])
  return none

/-- Prove `Apart a n b n'` by `apartByOffsets?`, else by `omega` on the
addresses as `Nat`s, using at most one `Separate` hypothesis. `omega` reads
the whole context, which during a walk costs ~45ms a call. Hypotheses that hold on one path only, such
as the account data's bounds when it is long enough to be read, are
`p → _`; they are used when `p` is in context. -/
elab "apart" : tactic => do
  -- The `Separate` fact about the two objects the addresses point into, if any.
  let some (a, b) ← withMainContext do
      let t ← whnfR (← getMainTarget)
      let_expr Apart a _ b _ := t | return none
      return some (← addressBase a, ← addressBase b)
    | throwError "apart: not an Apart goal"
  let fast? ← withMainContext do
    let t ← whnfR (← getMainTarget)
    let_expr Apart a n b n' := t | return none
    apartByOffsets? a n b n'
  if let some pf := fast? then
    let g ← getMainGoal
    if ← isDefEq (← inferType pf) (← g.getType) then
      g.assign pf; replaceMainGoal []; return
  let direct ← withMainContext do
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let_expr Separate p _ q _ := ← instantiateMVars d.type | continue
      if (p == a && q == b) || (p == b && q == a) then return some (← Term.exprToSyntax d.toExpr)
    return none
  evalTactic (← `(tactic| (
    unfold Apart
    intro i hi j hj
    -- Dischargers run at reducible transparency, which does not unfold `≠`.
    with_unfolding_all intro e
    replace e := congrArg UInt64.toNat e
    simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt64.toNat_ofNat,
      OperandSize.byteCount, Nat.reducePow, Nat.reduceMod] at e hi hj)))
  if let some h := direct then
    if ← tryTactic (evalTactic (← `(tactic| (have h' := $h; unfold Separate at h'; omega)))) then return
  withMainContext do
  let mut separations : Array Term := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    -- By the free variable, not the name: `have :=` leaves several `this`.
    if ty.isAppOf ``Separate then separations := separations.push (← Term.exprToSyntax d.toExpr)
    else if ty.isArrow then
      let conclusion := ty.bindingBody!
      unless conclusion.isAppOf ``Separate || conclusion.isAppOf ``LE.le do continue
      let premise := ty.bindingDomain!
      let some p ← (← getLCtx).findDeclM? fun p => do
          if p.isImplementationDetail then return none
          if ← withReducible (isDefEq p.type premise) then return some p else return none
        | continue
      let h' := mkIdent (← mkFreshUserName `h)
      let pf ← Term.exprToSyntax (mkApp d.toExpr p.toExpr)
      evalTactic (← `(tactic| have $h' := $pf))
      if conclusion.isAppOf ``Separate then separations := separations.push h'
  if ← tryTactic (evalTactic (← `(tactic| omega))) then return
  for h in separations do
    if ← tryTactic (evalTactic (← `(tactic| (have h' := $h; unfold Separate at h'; omega)))) then return
  throwError "apart: no hypothesis separates the addresses"

/-- The conjuncts of `h : t`, as proofs. -/
partial def conjuncts (h t : Expr) : MetaM (Array Expr) := do
  match_expr t with
  | And p q => return (← conjuncts (← mkAppM ``And.left #[h]) p) ++ (← conjuncts (← mkAppM ``And.right #[h]) q)
  | _ => return #[h]

/-- `omega` with one conjunct of `h` at a time instead of all of `h`: each
conjunct is a disjunction, and `omega` splits on all of them together.
Falls back to plain `omega`. -/
elab "omega_conjunct " h:ident : tactic => do
  let g ← getMainGoal
  let parts ← g.withContext do
    let d ← getLocalDeclFromUserName h.getId
    conjuncts d.toExpr (← instantiateMVars d.type)
  for p in parts do
    let saved ← saveState
    let ok ← g.withContext do
      let p ← Term.exprToSyntax p
      tryTactic (evalTactic (← `(tactic| (have hp := $p; clear $h:ident; omega))))
    if ok then return
    saved.restore
  evalTactic (← `(tactic| omega))

/-! ## Stepping -/

attribute [vexec] beq_iff_eq reduceCtorEq Bool.or_eq_true Bool.and_eq_true or_false false_or or_self
  and_true true_and and_false false_and ite_true ite_false Bool.false_eq_true
  not_false_eq_true not_true_eq_false decide_eq_true_eq decide_not Bool.not_eq_true' bne_iff_ne ne_eq
  Bool.not_eq_eq_eq_not Bool.not_true Bool.not_false Bool.and_true Bool.true_and Bool.or_false Bool.false_or
  dite_eq_ite
attribute [vexec] UInt64.zero_add UInt64.zero_shiftLeft

/-- The scale of an indexed address is a `Fin 4` shift count. Not `Fin.val_one`
in general: the register lemmas match `Fin 16` indices as they are. -/
@[vexec] theorem scale_one (x : UInt64) : x <<< UInt64.ofNat ((1 : Fin 4) : Nat) = x <<< 1 := rfl
@[vexec] theorem scale_two (x : UInt64) : x <<< UInt64.ofNat ((2 : Fin 4) : Nat) = x <<< 2 := rfl
@[vexec] theorem scale_three (x : UInt64) : x <<< UInt64.ofNat ((3 : Fin 4) : Nat) = x <<< 3 := rfl
attribute [vexec] UInt64.add_zero UInt64.and_self OperandSize.mask VectorMove.aligned BitVec.xor_zero
  BitVec.zero_xor beq_eq_false_iff_ne

/-- `cmp x, c` sets the zero flag on `x - c`, which the walk sees as `x + (-c)`. -/
@[vexec] theorem add_literal_beq_zero (x c : UInt64) : (x + c == 0) = (x == 0 - c) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_zero]
  have := x.toNat_lt; have := c.toNat_lt
  omega
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

/-- Decide `a == b` on `UInt64` literals. -/
simproc decideBEq ((_ : UInt64) == _) := fun e => do
  let_expr BEq.beq _ _ a b := e | return .continue
  let some (x, _) ← getOfNatValue? a ``UInt64 | return .continue
  let some (y, _) ← getOfNatValue? b ``UInt64 | return .continue
  let r := toExpr (UInt64.ofNat x == UInt64.ofNat y)
  return .done { expr := r, proof? := some (← mkExpectedTypeHint (← mkEqRefl r) (← mkEq e r)) }

@[vexec] theorem ite_false_true {c : Prop} {hc : Decidable c} : (if c then False else True) = ¬c := by
  by_cases c <;> simp_all

theorem decide_inst {p : Prop} (h h' : Decidable p) : @decide p h = @decide p h' := by
  cases h <;> cases h' <;> simp_all

/-- Re-synthesize the instance of `decide p` when `p` was rewritten
definitionally (the register lemmas are `rfl`) and the instance still has
the old type: no `decide` lemma matches such a term. -/
simproc fixDecide (@decide _ _) := fun e => do
  let_expr Decidable.decide p inst := e | return .continue
  let_expr Decidable q := (← instantiateMVars (← inferType inst)) | return .continue
  if q == p then return .continue
  let .some inst' ← trySynthInstance (mkApp (mkConst ``Decidable) p) | return .continue
  return .visit { expr := mkApp2 (mkConst ``Decidable.decide) p inst',
                  proof? := some (mkApp3 (mkConst ``decide_inst) p inst inst') }

/-- `x * c` as `c * x` for a literal `c`, so the code's `imul` and the spec's
products of the same factors are one term. -/
simproc literalFirst ((_ * _ : UInt64)) := fun e => do
  let_expr HMul.hMul _ _ _ _ a b := e | return .continue
  let some _ ← getOfNatValue? b ``UInt64 | return .continue
  if (← getOfNatValue? a ``UInt64).isSome then return .continue
  return .done { expr := ← mkAppM ``HMul.hMul #[b, a], proof? := some (← mkAppM ``UInt64.mul_comm #[a, b]) }

attribute [vexec] decideEq decideBEq literalFirst fixDecide Bool.ite_eq_true_distrib Bool.ite_eq_false_distrib

/-! ## Vector registers -/

@[vexec] theorem lowHalf_ofHalves (l h : UInt64) : lowHalf (ofHalves l h) = l := by
  simp only [lowHalf, ofHalves]; bv_decide

@[vexec] theorem highHalf_ofHalves (l h : UInt64) : highHalf (ofHalves l h) = h := by
  simp only [highHalf, ofHalves]; bv_decide

@[vexec] theorem xor_self (x : UInt64) : x ^^^ x = 0 := UInt64.xor_self

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
  | with_reducible assumption
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
    -- Reducible only: unifying `m` with a `wr` chain at default transparency
    -- unfolds the stores into `if`s on symbolic addresses.
    case hc => (try dsimp only); first | with_reducible assumption | (apply CodeAt.evolved ‹CodeAt _ _›; evolved)
    -- Look the instruction up first: `simp` rewrites inside the continuation
    -- before the `DecodeThen` around it, and there `execute` of an unknown
    -- instruction would unfold into every case.
    simp only [decode_table, decodeThen_ok]
    simp (disch := walk_disch) only [execThen_ok, vexec, ↓reduceIte, ↓reduceDIte, $ls,*]))

/-- A conditional jump over one instruction: on the fall-through path, that
instruction leads to the jump target, so both paths continue from the target
in one state whose fields are `if`s on the condition. -/
theorem Finishes.skip {lb : UInt64} {exits : Exits} {regs : Vector UInt64 16} {f : Flags}
    {vr : Vector (BitVec 128) 16} {fc : UInt32} {m : Memory} {c : Prop} [Decidable c] {A B : UInt64}
    {n : Nat} {P : Outcome → Prop} (hx : CodeExits lb exits) (hc : CodeAt lb m)
    (h : DecodeThen (decodeWith codeByte B) fun i len =>
      ExecThen ((execute i).run (State.mk (lb + B + len.toUInt64) regs f vr fc m)) fun s' =>
        Finishes exits n (if c then State.mk (lb + A) regs f vr fc m else s') P) :
    Finishes exits (n + 1) (State.mk (if c then lb + A else lb + B) regs f vr fc m) P := by
  obtain ⟨i, len, hdec, s', hexec, h⟩ := h
  by_cases hcond : c
  · simp only [hcond, ↓reduceIte] at h ⊢
    exact h.mono (Nat.le_succ n)
  · simp only [hcond, ↓reduceIte] at h ⊢
    exact Finishes.exec hx hc rfl hdec hexec h

/-! Values merged by `vskip` meet masks and comparisons. -/

section
variable {c : Prop} {hc : Decidable c} {a b k : UInt64}
@[vexec] theorem ite_and : (if c then a else b) &&& k = if c then a &&& k else b &&& k := by split <;> rfl
@[vexec] theorem ite_or : (if c then a else b) ||| k = if c then a ||| k else b ||| k := by split <;> rfl
@[vexec] theorem ite_beq : ((if c then a else b) == k) = if c then a == k else b == k := by split <;> rfl
end

@[vexec] theorem lowByte_of_merge (x y : UInt64) : (x &&& ~~~255 ||| y) &&& 255 = y &&& 255 := by bits64
@[vexec] theorem and_mask_mask (x : UInt64) : x &&& 4294967295 &&& 4294967295 = x &&& 4294967295 := by
  rw [UInt64.and_assoc, UInt64.and_self]
/-- `cmp r32, c` sets the zero flag on the low 32 bits of `x - c`. -/
@[vexec] theorem add_literal_and_mask_eq_zero (x c : UInt64) :
    ((x &&& 4294967295) + c &&& 4294967295 = 0) = (x &&& 4294967295 = (0 - c) &&& 4294967295) := by
  apply propext
  simp only [← UInt64.toNat_inj, UInt64.toNat_and, UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_zero,
    show (UInt64.toNat 4294967295) = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := x.toNat_lt; have := c.toNat_lt
  omega
/-- The owner check reads the two halves of the owner and the system program
id, which is zero. -/
@[vexec] theorem zero_xor128 (x : BitVec 128) : 0 ^^^ x = x := BitVec.zero_xor
@[vexec] theorem xor_zero128 (x : BitVec 128) : x ^^^ 0 = x := BitVec.xor_zero
@[vexec] theorem and_self128 (x : BitVec 128) : x &&& x = x := BitVec.and_self

/-- Four bytes fit in the low 32 bits. -/
@[vexec] theorem ofLittleEndian_take4_and_mask (l : List UInt8) :
    ofLittleEndian (l.take 4) &&& 4294967295 = ofLittleEndian (l.take 4) := by
  match l with
  | [] => rfl
  | [a] => simp only [List.take, ofLittleEndian]; bits64
  | [a, b] => simp only [List.take, ofLittleEndian]; bits64
  | [a, b, c] => simp only [List.take, ofLittleEndian]; bits64
  | a :: b :: c :: d :: _ => simp only [List.take, ofLittleEndian]; bits64

@[vexec] theorem take4_add_literal_and_mask_eq_zero (l : List UInt8) (c : UInt64) :
    (ofLittleEndian (l.take 4) + c &&& 4294967295 = 0) = (ofLittleEndian (l.take 4) = (0 - c) &&& 4294967295) := by
  rw [← ofLittleEndian_take4_and_mask l, add_literal_and_mask_eq_zero, ofLittleEndian_take4_and_mask]

/-! `setcc` leaves a condition as `if c then 1 else 0`; `or` and `test` of
such bytes are the conditions' disjunction and negation. -/

section
variable {c d : Prop} {hc : Decidable c} {hd : Decidable d}
@[vexec high] theorem setcc_or :
    (if c then (1 : UInt64) else 0) ||| (if d then 1 else 0) = if c ∨ d then 1 else 0 := by
  by_cases c <;> by_cases d <;> simp_all
@[vexec high] theorem setcc_beq_zero : ((if c then (1 : UInt64) else 0) == 0) = !decide c := by
  by_cases c <;> simp_all
end

@[vexec] theorem lowByte_cleared (x : UInt64) : x &&& ~~~255 &&& 255 = 0 := by bits64
/-- `mov ecx, 2; sbb rcx, 0`: the callee's code for the pre-execution rent
state, 1 for rent-paying and 2 for rent-exempt. -/
@[vexec] theorem two_sub_setcc {c : Prop} {hc : Decidable c} :
    (2 : UInt64) - (if c then 1 else 0) = if c then 1 else 2 := by by_cases c <;> simp_all

@[vexec] theorem zero_or (x : UInt64) : 0 ||| x = x := UInt64.zero_or
@[vexec] theorem or_zero (x : UInt64) : x ||| 0 = x := UInt64.or_zero
@[vexec] theorem lt_zero (x : UInt64) : (x < 0) = False := by
  apply propext; simp only [iff_false, UInt64.lt_iff_toNat_lt, UInt64.toNat_zero]; omega

@[vexec] theorem zero_and (x : UInt64) : 0 &&& x = 0 := UInt64.zero_and

/-- One step of the fall-through instruction of a jump over it (`Finishes.skip`). -/
elab "vskip" : tactic => do
  evalTactic (← `(tactic| (
    apply Finishes.skip
    case hx => assumption
    case hc => (try dsimp only); first | with_reducible assumption | (apply CodeAt.evolved ‹CodeAt _ _›; evolved)
    simp only [decode_table, decodeThen_ok]
    simp (disch := walk_disch) only [execThen_ok, vexec, ↓reduceIte, ↓reduceDIte])))
  let t ← instantiateMVars (← getMainTarget)
  let_expr Finishes _ _ s _ := t | throwError "vskip: not a Finishes goal"
  let_expr X86.State.mk ip _ _ _ _ _ := s | throwError "vskip: the paths did not merge"
  if ip.isAppOf ``ite then throwError "vskip: the paths did not merge"

/-- `decide` with whatever instance `simp` left after rewriting the
proposition: the standard lemmas expect the synthesized one. -/
theorem decide_eq_false' {p : Prop} {h : Decidable p} : (@decide p h = false) = ¬p := by
  cases h <;> simp_all

/-- `a - b` on `UInt64` either does not wrap or wraps once. -/
theorem sub_toNat_cases (a b : UInt64) :
    (a - b).toNat + b.toNat = a.toNat ∨ (a - b).toNat + b.toNat = a.toNat + 18446744073709551616 := by
  have := a.toNat_lt; have := b.toNat_lt
  rw [UInt64.toNat_sub]
  omega

/-- The `UInt64` subtractions in `e`. -/
partial def nestedSubtractions (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if e.isAppOfArity ``HSub.hSub 6 && e.appFn!.appFn!.appFn!.appFn!.appArg!.isConstOf ``UInt64
      && !e.hasLooseBVars && !acc.contains e then acc.push e else acc
  match e with
  | .app f a => nestedSubtractions a (nestedSubtractions f acc)
  | .lam _ t b _ | .forallE _ t b _ => nestedSubtractions b (nestedSubtractions t acc)
  | .mdata _ b => nestedSubtractions b acc
  | _ => acc

/-- Replace each `a - b` by a variable known to satisfy `sub_toNat_cases`:
`toNat_sub` would turn it into a `%` of a truncated subtraction, which `omega`
often cannot see through. Innermost first, so nested subtractions become
subtractions of variables. -/
elab "name_subtractions" : tactic => do
  let mut skip : Array Expr := #[]
  for _ in [0:32] do
    let some e ← withMainContext do
        let subs := nestedSubtractions (← instantiateMVars (← getMainTarget))
        return subs.find? fun e =>
          !skip.contains e && (nestedSubtractions e.appFn!.appArg!).isEmpty &&
            (nestedSubtractions e.appArg!).isEmpty
      | return
    skip := skip.push e
    withMainContext do
      let pf ← mkAppM ``sub_toNat_cases #[e.appFn!.appArg!, e.appArg!]
      let g ← (← getMainGoal).assert `wrap (← inferType pf) pf
      -- A subtraction inside a stale instance cannot be abstracted; it stays.
      try
        let (_, g) ← g.generalize #[{ expr := e, xName? := `x }] (transparency := .reducible)
        replaceMainGoal [g]
      catch _ => pure ()

/-- The `UInt64.toNat` applications in `e`. -/
partial def toNatAtoms (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if e.isAppOfArity ``UInt64.toNat 1 && !e.hasLooseBVars && !acc.contains e then acc.push e else acc
  match e with
  | .app f a => toNatAtoms a (toNatAtoms f acc)
  | .lam _ t b _ | .forallE _ t b _ => toNatAtoms b (toNatAtoms t acc)
  | .mdata _ b => toNatAtoms b acc
  | _ => acc

/-- `x.toNat < 2 ^ 64` for every `x.toNat` in the goal, which `omega` does
not know by itself. -/
elab "toNat_bounds" : tactic => withMainContext do
  for e in toNatAtoms (← instantiateMVars (← getMainTarget)) do
    let pf ← mkAppM ``UInt64.toNat_lt #[e.appArg!]
    replaceMainGoal [← (← getMainGoal).assert `bound (← inferType pf) pf]

/-- What `uomega` rewrites: `UInt64` facts as facts about `toNat`. -/
macro "uomega" : tactic => `(tactic| (
  try simp only [fixDecide, decide_eq_false', decide_eq_false_iff_not, decide_eq_true_eq, not_and, Classical.not_not, Bool.not_eq_true,
    Bool.not_eq_false, beq_iff_eq, bne_iff_ne, beq_eq_false_iff_ne, Bool.not_eq_true', Bool.and_eq_true,
    Bool.or_eq_true, ite_false_true, decide_not, Bool.not_not, two_sub_setcc,
    ne_eq, Nat.toUInt64_eq, literalFirst]
  name_subtractions
  try simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, ← UInt64.toNat_inj,
    UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_zero, Nat.reducePow, Nat.reduceMod,
    UInt64.toNat_ofNat']
  all_goals (toNat_bounds; (try simp only [UInt64.size, Nat.reducePow]); intros; omega)))

/-- A proof of `¬ e` from the path conditions (hypotheses named `path`), if
`contradiction` or `uomega` finds one. -/
def refute? (e : Expr) : TacticM (Option Expr) := do
  let g ← mkFreshExprMVar (← mkArrow e (mkConst ``False))
  let paths := (← getLCtx).foldl (init := #[]) fun acc d =>
    if d.userName == `path && !d.isImplementationDetail then acc.push d.fvarId else acc
  let (_, g') ← g.mvarId!.revert paths (preserveOrder := true)
  -- `contradiction` compares hypotheses pairwise; the path conditions and
  -- `e` are the ones that can contradict each other.
  let entryFacts ← g'.withContext do
    (← getLCtx).foldlM (init := #[]) fun acc d => do
      if !d.isImplementationDetail && (← isProp d.type) then return acc.push d.fvarId else return acc
  let saved ← saveState
  for (tac, clear) in [(← `(tactic| (intros; contradiction)), true), (← `(tactic| uomega), false)] do
    setGoals [← if clear then g'.tryClearMany entryFacts else pure g']
    let ok ← tryCatchRuntimeEx (do withoutRecover (evalTactic tac); pure (← getGoals).isEmpty) fun ex => do
      trace[debug] "refute {e}: {tac} failed: {ex.toMessageData}\n{g'}"
      pure false
    -- On success keep the metavariable context the proof lives in; only the
    -- goal list goes back.
    if ok then
      setGoals saved.tactic.goals
      return some (← instantiateMVars g)
    saved.restore
  saved.restore
  return none

/-- Continue on the path where `path : h` holds, with `h` already proved. -/
def takePath (h prf : Expr) : TacticM Unit := do
  let (_, g) ← (← (← getMainGoal).assert `path h prf).intro1P
  setGoals [g]
  evalTactic (← `(tactic| try simp only [$(mkIdent `path):ident, ↓reduceIte, not_false_eq_true]))

/-- Put the new path condition in normal form and use it to rewrite the
state, so later conditions on the same values are decided by `simp`. -/
def normalizePath : TacticM Unit := do
  evalTactic (← `(tactic| try simp only [Bool.not_eq_false, beq_iff_eq, ne_eq, Classical.not_not,
    Bool.not_eq_true, beq_eq_false_iff_ne, ite_false_true, fixDecide, decide_eq_false',
    decide_eq_false_iff_not, decide_eq_true_eq] at $(mkIdent `path):ident))
  evalTactic (← `(tactic| try simp only [$(mkIdent `path):ident]))

/-- Split on the condition of the conditional jump that `vstep` left in the
instruction pointer, unless the path so far decides it. -/
elab "vsplit" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let_expr Finishes _ _ s _ := t | throwError "vsplit: not a Finishes goal"
  let_expr X86.State.mk ip _ _ _ _ _ := s | throwError "vsplit: state not explicit"
  let_expr ite _ c _ _ _ := ip | throwError "vsplit: no branch"
  if let some prf ← refute? c then
    takePath (mkNot c) prf; normalizePath
  else if let some prf ← refute? (mkNot c) then
    takePath c (← mkAppM ``Classical.byContradiction #[prf]); normalizePath
  else
    let path := mkIdent `path
    evalTactic (← `(tactic| by_cases $path:ident : $(← Term.exprToSyntax c) <;>
      simp only [$path:ident, ↓reduceIte, not_false_eq_true]))
    let gs ← getGoals
    let mut out := []
    for g in gs do
      setGoals [g]; normalizePath; out := out ++ (← getGoals)
    setGoals out

/-- Whether the goal's state is at `lb + a` with `a` inside the carved code,
so that `vwalk` should step it; exits and other targets are left to the caller. -/
def inCode (g : MVarId) : MetaM Bool := do
  let t ← instantiateMVars (← g.getType)
  let_expr Finishes _ _ s _ := t | return false
  let_expr X86.State.mk ip _ _ _ _ _ := s | return false
  if ip.isAppOf ``ite then return true
  let_expr HAdd.hAdd _ _ _ _ _ a := ip | return false
  let some (a, _) ← getOfNatValue? a ``UInt64 | return false
  return 0x27f3560 ≤ a && a < 0x27f3930

syntax "vwalk" (num)? (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

/-- `vstep` and `vsplit` until no goal moves. A loop rather than `repeat'`,
whose recursion is as deep as the code is long. -/
elab_rules : tactic
  | `(tactic| vwalk $[$n]? $[[$ls,*]]?) => withEnableInfoTree false do
    let ls := ls.getD ⟨#[]⟩
    let mut fuel := (n.map (·.getNat)).getD 100000
    let step ← `(tactic| first | vstep [$ls,*] | vskip | vsplit)
    let mut todo := ← getGoals
    let mut done : Array MVarId := #[]
    while !todo.isEmpty && fuel > 0 do
      fuel := fuel - 1
      let g := todo.head!
      todo := todo.tail
      if ← g.isAssigned then continue
      unless ← inCode g do done := done.push g; continue
      setGoals [g]
      let saved ← saveState
      let moved ← tryCatchRuntimeEx (do evalTactic step; pure true) fun e => do
        saved.restore
        if e.isRuntime then logWarning m!"vwalk: {e.toMessageData}\n{g}"
        pure false
      if moved then todo := (← getGoals) ++ todo
      else done := done.push g
    setGoals (done.toList ++ todo)

/-- Run `t` without recording info trees: they keep a copy of every goal,
and a walk's goals are whole machine states. -/
elab "without_info " t:tacticSeq : tactic => withEnableInfoTree false (evalTactic t)

end ValidateFeePayer.Proof
