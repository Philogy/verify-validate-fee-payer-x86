import X86.F64
import Std.Tactic.BVDecide

/-!
Facts about `F64` used by the conversion idioms the compiler emits for
`u64 as f64` and `f64 as u64`: rounding is invariant under scaling, a value
with at most 53 significant bits rounds exactly, and the bits `round`
produces decode back to the value.
-/

namespace X86.F64

/-! ## `roundShift` and `round` under scaling -/

theorem roundShift_scale (m k : Nat) (sh : Int) : roundShift (m * 2 ^ k) (sh + k) = roundShift m sh := by
  unfold roundShift
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  by_cases h1 : sh + k ≤ 0
  · have h2 : sh ≤ 0 := by omega
    simp only [h1, h2, ↓reduceIte, Prod.mk.injEq, and_true]
    rw [Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  · simp only [h1, ↓reduceIte]
    by_cases h2 : sh ≤ 0
    · simp only [h2, ↓reduceIte]
      have hk : 2 ^ k = 2 ^ sh.natAbs * 2 ^ (sh + k).toNat := by rw [← Nat.pow_add]; congr 1; omega
      have hq : m * 2 ^ k / 2 ^ (sh + k).toNat = m * 2 ^ sh.natAbs := by
        rw [hk, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
      have hr : m * 2 ^ k % 2 ^ (sh + k).toNat = 0 := by
        rw [hk, ← Nat.mul_assoc, Nat.mul_mod_left]
      have hhalf : 0 < 2 ^ ((sh + k).toNat - 1) := Nat.two_pow_pos _
      simp only [hq, hr, Prod.mk.injEq]
      have : ¬ (0 > 2 ^ ((sh + k).toNat - 1)) := by omega
      have : (0 == 2 ^ ((sh + k).toNat - 1)) = false := by
        simp only [beq_eq_false_iff_ne]; omega
      simp [*]
    · simp only [h2, ↓reduceIte]
      have hs : (sh + k).toNat = sh.toNat + k := by omega
      have hs1 : sh.toNat + k - 1 = (sh.toNat - 1) + k := by omega
      rw [hs, hs1, Nat.pow_add, Nat.pow_add, Nat.mul_div_mul_right _ _ hpos, Nat.mul_mod_mul_right]
      have hlt : ∀ a b : Nat, a * 2 ^ k > b * 2 ^ k ↔ a > b := fun a b =>
        ⟨fun h => Nat.lt_of_mul_lt_mul_right h, fun h => Nat.mul_lt_mul_of_pos_right h hpos⟩
      have heq : ∀ a b : Nat, (a * 2 ^ k == b * 2 ^ k) = (a == b) := fun a b =>
        Bool.eq_iff_iff.2 (by
          simp only [beq_iff_eq]
          exact ⟨Nat.eq_of_mul_eq_mul_right hpos, fun h => by rw [h]⟩)
      have hne : ∀ a : Nat, (a * 2 ^ k != 0) = (a != 0) := fun a =>
        Bool.eq_iff_iff.2 (by simp [bne_iff_ne, Nat.mul_eq_zero])
      simp only [hlt, heq, hne]

/-- `round` with the magnitude abstracted: it depends on `m` and `e` only
through the exponent `K` of the leading bit and the rounding function. -/
def roundAt (s : Bool) (K : Int) (g : Int → Nat × Bool) : UInt64 × Exceptions :=
  let q' := K - 53
  let (r', _) := g q'
  let tiny := (if r' = 2 ^ 53 then q' + 53 else q' + 52) < -1022
  let q := max (K - 53) (-1074)
  let (r, inexact) := g q
  let (r, q) := if r = 2 ^ 53 then (2 ^ 52, q + 1) else (r, q)
  let underflow := tiny && inexact
  if r < 2 ^ 52 then
    (signBit s ||| r.toUInt64, { underflow, inexact })
  else
    let biasedExponent := q + 1075
    if biasedExponent > 2046 then (infinity s, { overflow := true, inexact := true })
    else (signBit s ||| (biasedExponent.toNat.toUInt64 <<< 52) ||| (r - 2 ^ 52).toUInt64,
      { underflow, inexact })

theorem round_eq_roundAt (s : Bool) (m : Nat) (e : Int) :
    round s m e = roundAt s ((Nat.log2 m + 1 : Nat) + e) (fun t => roundShift m (t - e)) := rfl

theorem log2_mul_pow {m : Nat} (hm : m ≠ 0) (k : Nat) : Nat.log2 (m * 2 ^ k) = Nat.log2 m + k := by
  have h1 := Nat.log2_self_le hm
  have h2 := Nat.lt_log2_self (n := m)
  refine (Nat.log2_eq_iff (by simp [Nat.mul_eq_zero, hm])).2 ⟨?_, ?_⟩
  · rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ h1
  · rw [show Nat.log2 m + k + 1 = (Nat.log2 m + 1) + k by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos k)

theorem round_scale (s : Bool) {m : Nat} (hm : m ≠ 0) (k : Nat) (e : Int) :
    round s (m * 2 ^ k) (e - k) = round s m e := by
  rw [round_eq_roundAt, round_eq_roundAt, log2_mul_pow hm]
  have hK : (((Nat.log2 m + k + 1 : Nat) : Int) + (e - k)) = ((Nat.log2 m + 1 : Nat) : Int) + e := by omega
  have hg : (fun t => roundShift (m * 2 ^ k) (t - (e - k))) = fun t => roundShift m (t - e) := by
    funext t
    rw [show t - (e - k) = (t - e) + k by omega, roundShift_scale]
  rw [hK, hg]

theorem ofScaled_scale (n e : Int) (k : Nat) (z : Bool) :
    ofScaled (n * 2 ^ k) (e - k) z = ofScaled n e z := by
  unfold ofScaled
  by_cases hn : n = 0
  · simp [hn]
  · have hpos : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
    have h1 : n * 2 ^ k ≠ 0 := Int.mul_ne_zero hn (by omega)
    have h2 : (n * 2 ^ k < 0) = (n < 0) := by
      apply propext; constructor
      · intro h; apply Classical.byContradiction; intro h'
        have := Int.mul_nonneg (Int.not_lt.1 h') (Int.le_of_lt hpos); omega
      · intro h; exact Int.mul_neg_of_neg_of_pos h hpos
    have h3 : (n * 2 ^ k).natAbs = n.natAbs * 2 ^ k := by
      rw [Int.natAbs_mul, Int.natAbs_pow]; rfl
    simp only [h1, hn, ↓reduceIte, h2, h3]
    exact round_scale _ (by omega) k e

theorem ofScaled_scale' (n e : Int) (k : Nat) (z : Bool) :
    ofScaled (n * ((2 ^ k : Nat) : Int)) (e - k) z = ofScaled n e z := by
  rw [Int.natCast_pow]; exact ofScaled_scale n e k z

/-! ## Values with at most 53 significant bits round exactly -/

theorem round_normal {s : Bool} {r : Nat} {q : Int} (hr1 : 2 ^ 52 ≤ r) (hr2 : r < 2 ^ 53)
    (hq1 : -1074 ≤ q) (hq2 : q ≤ 971) :
    round s r q = (signBit s ||| ((q + 1075).toNat.toUInt64 <<< 52) ||| (r - 2 ^ 52).toUInt64, {}) := by
  have hlog : Nat.log2 r = 52 := (Nat.log2_eq_iff (by omega)).2 ⟨hr1, hr2⟩
  have h0 : ((52 + 1 : Nat) : Int) + q - 53 - q = 0 := by omega
  have hm : max (((52 + 1 : Nat) : Int) + q - 53) (-1074) = q := by omega
  have hrs : roundShift r 0 = (r, false) := by simp [roundShift]
  have hne : r ≠ 2 ^ 53 := by omega
  have hlt : ¬ r < 2 ^ 52 := by omega
  have hbe : ¬ q + 1075 > 2046 := by omega
  simp only [round, hlog, h0, hm, Int.sub_self, hrs, hne, hlt, hbe, ite_false, Bool.and_false]

/-- The bits of a normal double with sign `s`, biased exponent `E` and
fraction `f`. -/
def pack (s : Bool) (E f : Nat) : UInt64 := signBit s ||| (E.toUInt64 <<< 52) ||| f.toUInt64

/-- A nonzero `m` below `2 ^ 53`, times `2 ^ e`, rounds to itself. -/
theorem round_small {s : Bool} {m : Nat} {e : Int} (hm0 : m ≠ 0) (hm : m < 2 ^ 53)
    (he1 : -1074 ≤ e - (52 - Nat.log2 m)) (he2 : e - (52 - Nat.log2 m) ≤ 971) :
    round s m e = (pack s (e - (52 - Nat.log2 m) + 1075).toNat (m * 2 ^ (52 - Nat.log2 m) - 2 ^ 52), {}) := by
  have hl1 := Nat.log2_self_le hm0
  have hl2 := Nat.lt_log2_self (n := m)
  have hl : Nat.log2 m < 53 := (Nat.log2_lt hm0).2 hm
  rw [← round_scale s hm0 (52 - Nat.log2 m) e]
  have hcast : (((52 - Nat.log2 m : Nat)) : Int) = 52 - (Nat.log2 m : Int) := by omega
  rw [hcast]
  apply round_normal
  · rw [show 2 ^ 52 = 2 ^ Nat.log2 m * 2 ^ (52 - Nat.log2 m) by rw [← Nat.pow_add]; congr 1; omega]
    exact Nat.mul_le_mul_right _ hl1
  · rw [show 2 ^ 53 = 2 ^ (Nat.log2 m + 1) * 2 ^ (52 - Nat.log2 m) by rw [← Nat.pow_add]; congr 1; omega]
    exact Nat.mul_lt_mul_of_pos_right hl2 (Nat.two_pow_pos _)
  · omega
  · omega

theorem pack_fields {s : Bool} {E f : Nat} (hE : E < 2048) (hf : f < 2 ^ 52) :
    exponentField (pack s E f) = E ∧ fraction (pack s E f) = f ∧ sign (pack s E f) = s := by
  have hEU : E.toUInt64.toNat = E := by simp; omega
  have hfU : f.toUInt64.toNat = f := by simp; omega
  have hE' : E.toUInt64 < 2048 := by simp [UInt64.lt_iff_toNat_lt]; omega
  have hf' : f.toUInt64 < 0x10000000000000 := by simp [UInt64.lt_iff_toNat_lt]; omega
  generalize E.toUInt64 = EU at hEU hE'
  generalize f.toUInt64 = FU at hfU hf'
  subst hEU hfU
  simp only [exponentField, fraction, sign, pack, Nat.toUInt64_eq, UInt64.ofNat_toNat]
  refine ⟨?_, ?_, ?_⟩
  · congr 1; cases s <;> simp only [signBit] <;> bv_decide
  · congr 1; cases s <;> simp only [signBit] <;> bv_decide
  · cases s <;> simp only [signBit] <;> bv_decide

theorem scaled_of_fields {x : UInt64} {E f : Nat} (hE : exponentField x = E) (hf : fraction x = f)
    (hs : sign x = false) (hE1 : 1 ≤ E) : scaled x = ((f + 2 ^ 52) * 2 ^ (E - 1) : Nat) := by
  simp only [scaled, hE, hf, hs]
  have : E ≠ 0 := by omega
  simp [this]

theorem scaled_of_fields_neg {x : UInt64} {E f : Nat} (hE : exponentField x = E) (hf : fraction x = f)
    (hs : sign x = true) (hE1 : 1 ≤ E) : scaled x = -(((f + 2 ^ 52) * 2 ^ (E - 1) : Nat) : Int) := by
  simp only [scaled, hE, hf, hs]
  have : E ≠ 0 := by omega
  simp [this]

theorem ofScaled_exact {m k : Nat} (hm : m < 2 ^ 53) (hk : k ≤ 900) :
    let b := (ofScaled (m * 2 ^ k : Nat) 0 false).1
    isNaN b = false ∧ isInfinite b = false ∧ sign b = false ∧ scaled b = ((m * 2 ^ k * 2 ^ 1074 : Nat) : Int) := by
  intro b
  by_cases hm0 : m = 0
  · subst hm0
    simp [b, ofScaled, isNaN, isInfinite, sign, scaled, exponentField, fraction, signBit]
  · have hpos : m * 2 ^ k ≠ 0 := Nat.mul_ne_zero hm0 (Nat.ne_of_gt (Nat.two_pow_pos k))
    have hl := (Nat.log2_lt hm0).2 hm
    have hb : (ofScaled (m * 2 ^ k : Nat) 0 false) = round false m k := by
      simp only [ofScaled, Int.natCast_eq_zero, hpos, ↓reduceIte, Int.natAbs_natCast]
      have : ((m * 2 ^ k : Nat) : Int) < 0 ↔ False := iff_false_intro (Int.not_lt.2 (Int.natCast_nonneg _))
      simp only [this, decide_false]
      rw [show (0 : Int) = (k : Int) - k by omega, round_scale false hm0 k k]
    have hr := round_small (s := false) (e := k) hm0 hm (by omega) (by omega)
    rw [hr] at hb
    have hl1 := Nat.log2_self_le hm0
    have hl2 := Nat.lt_log2_self (n := m)
    have hfr1 : 2 ^ 52 ≤ m * 2 ^ (52 - Nat.log2 m) := by
      rw [show 2 ^ 52 = 2 ^ Nat.log2 m * 2 ^ (52 - Nat.log2 m) by rw [← Nat.pow_add]; congr 1; omega]
      exact Nat.mul_le_mul_right _ hl1
    have hfr2 : m * 2 ^ (52 - Nat.log2 m) < 2 ^ 53 := by
      rw [show 2 ^ 53 = 2 ^ (Nat.log2 m + 1) * 2 ^ (52 - Nat.log2 m) by rw [← Nat.pow_add]; congr 1; omega]
      exact Nat.mul_lt_mul_of_pos_right hl2 (Nat.two_pow_pos _)
    have hE : ((k : Int) - (52 - (Nat.log2 m : Int)) + 1075).toNat = k + Nat.log2 m + 1023 := by omega
    rw [hE] at hb
    obtain ⟨hfE, hff, hfs⟩ := pack_fields (s := false) (E := k + Nat.log2 m + 1023)
      (f := m * 2 ^ (52 - Nat.log2 m) - 2 ^ 52) (by omega) (by omega)
    have hbE : b = pack false (k + Nat.log2 m + 1023) (m * 2 ^ (52 - Nat.log2 m) - 2 ^ 52) := by
      simp only [b, hb]
    rw [hbE]
    refine ⟨?_, ?_, hfs, ?_⟩
    · simp only [isNaN, hfE]; simp; omega
    · simp only [isInfinite, hfE]; simp; omega
    · rw [scaled_of_fields hfE hff hfs (by omega), Nat.sub_add_cancel hfr1]
      have e2 : 2 ^ (52 - Nat.log2 m) * 2 ^ (k + Nat.log2 m + 1023 - 1) = 2 ^ k * 2 ^ 1074 := by
        rw [← Nat.pow_add, ← Nat.pow_add, show 52 - Nat.log2 m + (k + Nat.log2 m + 1023 - 1) = k + 1074 by omega]
      rw [Nat.mul_assoc, e2, ← Nat.mul_assoc]

/-! ## The `u64 as f64` idiom -/

theorem fields_or {x : UInt64} {E : UInt64} (hx : x < 0x100000000) (hE : E < 2047) :
    exponentField ((E <<< 52) ||| x) = E.toNat ∧ fraction ((E <<< 52) ||| x) = x.toNat ∧
      sign ((E <<< 52) ||| x) = false := by
  simp only [exponentField, fraction, sign]
  refine ⟨?_, ?_, ?_⟩
  · congr 1; bv_decide
  · congr 1; bv_decide
  · bv_decide

theorem finite_of_fields {y : UInt64} {E f : Nat} (hE : exponentField y = E) (hf : fraction y = f)
    (h : E < 2047) : isNaN y = false ∧ isInfinite y = false := by
  simp only [isNaN, isInfinite, hE, hf]; constructor <;> simp <;> omega

theorem bias_arith (x j : Nat) :
    (((x + 2 ^ 52) * 2 ^ (j + 1074) : Nat) : Int) + -(((0 + 2 ^ 52) * 2 ^ (j + 1074) : Nat) : Int) =
      ((x * 2 ^ j : Nat) : Int) * 2 ^ (1074 : Nat) := by
  rw [show ((2 : Int) ^ (1074 : Nat)) = (((2 : Nat) ^ 1074 : Nat) : Int) from (Int.natCast_pow 2 1074).symm,
    Nat.pow_add]
  generalize (2 : Nat) ^ 1074 = P
  generalize (2 : Nat) ^ j = J
  generalize (2 : Nat) ^ 52 = B
  rw [Nat.zero_add]
  simp only [Int.natCast_mul, Int.natCast_add]
  rw [Int.add_mul, Int.add_neg_cancel_right, Int.mul_assoc]

/-- `(2 ^ 52 + x) - 2 ^ 52` for a 32-bit `x`, as the bias subtraction
does it: exact. -/
theorem sub_bias_low {x : UInt64} (hx : x < 0x100000000) :
    (sub (0x4330000000000000 ||| x) 0x4330000000000000).1 = (ofScaled (x.toNat * 2 ^ 0 : Nat) 0 false).1 := by
  obtain ⟨haE, haf, has⟩ := fields_or (E := 0x433) hx (by decide)
  simp only [show (0x433 : UInt64) <<< 52 = 0x4330000000000000 from rfl] at haE haf has
  obtain ⟨na, ia⟩ := finite_of_fields haE haf (by decide)
  have nb : isNaN 0x4330000000000000 = false := by decide
  have nn : isNaN (negate 0x4330000000000000) = false := by decide
  have inn : isInfinite (negate 0x4330000000000000) = false := by decide
  have hns : sign (negate 0x4330000000000000) = true := by decide
  have hsn : scaled (negate 0x4330000000000000) = -(((0 + 2 ^ 52) * 2 ^ (1075 - 1) : Nat) : Int) :=
    scaled_of_fields_neg (by decide) (by decide) hns (by decide)
  simp only [sub, add, na, nb, nn, ia, inn, Bool.or_false, Bool.false_and,
    Bool.and_false, has, hns, Bool.false_eq_true, ite_false]
  rw [scaled_of_fields haE haf has (by decide), hsn, show UInt64.toNat 0x433 - 1 = 0 + 1074 from rfl,
    show 1075 - 1 = 0 + 1074 from rfl]
  rw [show (-1074 : Int) = 0 - ((1074 : Nat) : Int) from rfl, ← ofScaled_scale _ 0 1074 false]
  rw [bias_arith]

/-- `(2 ^ 84 + x * 2 ^ 32) - 2 ^ 84` for a 32-bit `x`: exact. -/
theorem sub_bias_high {x : UInt64} (hx : x < 0x100000000) :
    (sub (0x4530000000000000 ||| x) 0x4530000000000000).1 = (ofScaled (x.toNat * 2 ^ 32 : Nat) 0 false).1 := by
  obtain ⟨haE, haf, has⟩ := fields_or (E := 0x453) hx (by decide)
  simp only [show (0x453 : UInt64) <<< 52 = 0x4530000000000000 from rfl] at haE haf has
  obtain ⟨na, ia⟩ := finite_of_fields haE haf (by decide)
  have nb : isNaN 0x4530000000000000 = false := by decide
  have nn : isNaN (negate 0x4530000000000000) = false := by decide
  have inn : isInfinite (negate 0x4530000000000000) = false := by decide
  have hns : sign (negate 0x4530000000000000) = true := by decide
  have hsn : scaled (negate 0x4530000000000000) = -(((0 + 2 ^ 52) * 2 ^ (1107 - 1) : Nat) : Int) :=
    scaled_of_fields_neg (by decide) (by decide) hns (by decide)
  simp only [sub, add, na, nb, nn, ia, inn, Bool.or_false, Bool.false_and,
    Bool.and_false, has, hns, Bool.false_eq_true, ite_false]
  rw [scaled_of_fields haE haf has (by decide), hsn, show UInt64.toNat 0x453 - 1 = 32 + 1074 from rfl,
    show 1107 - 1 = 32 + 1074 from rfl]
  rw [show (-1074 : Int) = 0 - ((1074 : Nat) : Int) from rfl, ← ofScaled_scale _ 0 1074 false]
  rw [bias_arith]

theorem add_exact {a b : UInt64} {ma mb : Nat}
    (ha : isNaN a = false ∧ isInfinite a = false ∧ sign a = false ∧ scaled a = ((ma * 2 ^ 1074 : Nat) : Int))
    (hb : isNaN b = false ∧ isInfinite b = false ∧ sign b = false ∧ scaled b = ((mb * 2 ^ 1074 : Nat) : Int)) :
    (add a b).1 = (ofScaled (ma + mb : Nat) 0 false).1 := by
  obtain ⟨na, ia, sa, ha⟩ := ha
  obtain ⟨nb, ib, sb, hb⟩ := hb
  simp only [add, na, nb, ia, ib, sa, sb, Bool.or_false, Bool.false_and, Bool.and_false, Bool.false_eq_true,
    ite_false]
  -- `rw`, not `simp`: with these in the simp set the kernel ends up evaluating `2 ^ 1074` by unary recursion.
  rw [ha, hb, show (-1074 : Int) = 0 - ((1074 : Nat) : Int) from rfl, ← ofScaled_scale' _ 0 1074 false,
    ← Int.natCast_add, ← Nat.add_mul, Int.natCast_mul]

/-- The compiler's `u64 as f64`: split into 32-bit halves, make each an
exact double by splicing it under a biased exponent and subtracting the
bias, and add the halves, which rounds once. -/
theorem u64ToF64_halves (x : UInt64) :
    (add (sub ((0x4530000000000000 : UInt64) ||| x >>> 32) 0x4530000000000000).1
      (sub ((0x4330000000000000 : UInt64) ||| (x &&& 0xffffffff)) 0x4330000000000000).1).1 =
      (ofScaled x.toNat 0 false).1 := by
  rw [sub_bias_high (by bv_decide), sub_bias_low (by bv_decide)]
  have hhi : (x >>> 32).toNat < 2 ^ 53 := by
    have : (x >>> 32).toNat < 2 ^ 32 := by
      rw [UInt64.toNat_shiftRight]; simp; have := x.toNat_lt; omega
    omega
  have hlo : (x &&& 0xffffffff).toNat < 2 ^ 53 := by
    rw [UInt64.toNat_and]; have := Nat.and_le_right (n := x.toNat) (m := (0xffffffff : UInt64).toNat)
    simp at this ⊢; omega
  rw [add_exact (ofScaled_exact hhi (by decide)) (ofScaled_exact hlo (by decide))]
  have h1 : (x >>> 32).toNat = x.toNat / 2 ^ 32 := by
    rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  have h2 : (x &&& 0xffffffff).toNat = x.toNat % 2 ^ 32 := by
    rw [UInt64.toNat_and]
    have : (0xffffffff : UInt64).toNat = 2 ^ 32 - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod]
  rw [h1, h2, Nat.pow_zero, Nat.mul_one, show x.toNat / 2 ^ 32 * 2 ^ 32 + x.toNat % 2 ^ 32 = x.toNat by omega]

end X86.F64
