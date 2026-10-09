import ValidateFeePayer.Proof.Float
import ValidateFeePayer.Spec

/-!
The compiler's `f64 as u64`: `cvttsd2si` converts below `2 ^ 63`; at and
above it converts `x - 2 ^ 63` and puts the top bit back; two `ucomisd`s pick
`0` for negative and NaN inputs and `u64::MAX` above the largest double
below `2 ^ 64`. This is the run of those instructions, as the symbolic walk
leaves it, shown equal to `Spec.f64ToU64`.
-/

namespace ValidateFeePayer.Proof

open X86 X86.F64

/-- What `compareUnordered` compares: the value, with infinities beyond every
finite double. -/
def orderValue (x : UInt64) : Int :=
  if isInfinite x then (if sign x then -(2 : Int) ^ 2100 else 2 ^ 2100) else scaled x

theorem compare_nan {a b : UInt64} (h : isNaN a = true) : (compareUnordered a b).1 = (true, true, true) := by
  simp [compareUnordered, h]

def compareFlags (va vb : Int) : Bool × Bool × Bool :=
  if va < vb then (false, false, true) else if va = vb then (true, false, false) else (false, false, false)

theorem compare_ordered {a b : UInt64} (ha : isNaN a = false) (hb : isNaN b = false) :
    (compareUnordered a b).1 = compareFlags (orderValue a) (orderValue b) := by
  simp only [compareUnordered, ha, hb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, orderValue, compareFlags]
  rfl

theorem compareFlags_carry (va vb : Int) : (compareFlags va vb).2.2 = decide (va < vb) := by
  unfold compareFlags; split
  · simp_all
  · split <;> simp_all

theorem compareFlags_zero (va vb : Int) : (compareFlags va vb).1 = decide (va = vb) := by
  unfold compareFlags; split
  · rename_i h; have : va ≠ vb := by omega
    simp [this]
  · split <;> simp_all

theorem fraction_lt (x : UInt64) : fraction x < 2 ^ 52 := by
  simp only [fraction, UInt64.toNat_and]
  have := Nat.and_le_right (n := x.toNat) (m := (0xfffffffffffff : UInt64).toNat)
  simp at this ⊢; omega

theorem exponentField_lt (x : UInt64) : exponentField x < 2048 := by
  simp only [exponentField, UInt64.toNat_and]
  have := Nat.and_le_right (n := (x >>> 52).toNat) (m := (0x7ff : UInt64).toNat)
  simp at this ⊢; omega

/-- The magnitude of a double whose exponent field is `E`. -/
theorem scaled_nonneg {x : UInt64} (hs : sign x = false) :
    scaled x = ((if exponentField x = 0 then fraction x else (fraction x + 2 ^ 52) * 2 ^ (exponentField x - 1) : Nat) : Int) := by
  simp only [scaled, hs]; split <;> simp_all

theorem scaled_max : scaled 0x43efffffffffffff = (((2 ^ 52 - 1 + 2 ^ 52) * 2 ^ (1086 - 1) : Nat) : Int) :=
  scaled_of_fields (E := 1086) (f := 2 ^ 52 - 1) (by decide) (by decide) (by decide) (by decide)

end ValidateFeePayer.Proof
