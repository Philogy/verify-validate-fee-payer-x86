/-!
IEEE 754 binary64 arithmetic as SSE2 performs it, on raw bits:
`addsd`/`subsd`/`subpd`, `mulsd`, `ucomisd` and `cvttsd2si`.

Only the default floating-point control setting (x86: `MXCSR`) is modelled:
round to nearest even, all exceptions masked, no flush-to-zero, no
denormals-are-zero. The machine stops with `unsupported` on any other
setting rather than compute something else. Under that setting an operation
never traps; it returns a value and the exception flags it raises. The
machine does not record those flags (see `State.floatControl`).

Arithmetic is exact: every finite double is an integer multiple of `2^-1074`
(`scaled`), so a sum or product is an exact integer times a power of two,
and `round` rounds that once. Rules taken from the Intel SDM, vol. 1 §4.8–4.9
and §11.5, which the hardware comparison (`tests/x86/`) checks:

- NaN operand: the result is the first NaN operand (destination first),
  quieted; `invalid` only if some operand is a signalling NaN.
- `inf - inf`, `0 * inf`: the default NaN `0xFFF8…0` and `invalid`.
- `denormal` when an operand is denormal and no operand is a NaN.
- Tininess is detected after rounding; with underflow masked, `underflow` is
  set only when the (denormalised) result is also inexact.
- Overflow gives ±infinity with `overflow` and `inexact`.
- An exact zero sum is `+0`, except `(-0) + (-0) = -0`.
-/

namespace X86.F64

/-- The floating-point exception flags an operation raises, as bits 0–5 of
the float control word (x86: `MXCSR` bits `IE DE ZE OE UE PE`; divide-by-zero,
`ZE`, never arises here). -/
structure Exceptions where
  /-- x86: `IE`. -/
  invalid : Bool := false
  /-- An operand was denormal (x86: `DE`). -/
  denormal : Bool := false
  /-- x86: `OE`. -/
  overflow : Bool := false
  /-- x86: `UE`. -/
  underflow : Bool := false
  /-- The result was rounded (x86: `PE`, "precision"). -/
  inexact : Bool := false
  deriving DecidableEq, Repr

def Exceptions.merge (a b : Exceptions) : Exceptions :=
  ⟨a.invalid || b.invalid, a.denormal || b.denormal, a.overflow || b.overflow,
   a.underflow || b.underflow, a.inexact || b.inexact⟩

def Exceptions.bits (e : Exceptions) : UInt32 :=
  (if e.invalid then 1 else 0) ||| (if e.denormal then 2 else 0) ||| (if e.overflow then 8 else 0) |||
  (if e.underflow then 16 else 0) ||| (if e.inexact then 32 else 0)

def sign (x : UInt64) : Bool := x >>> 63 == 1
def exponentField (x : UInt64) : Nat := ((x >>> 52) &&& 0x7ff).toNat
def fraction (x : UInt64) : Nat := (x &&& 0xfffffffffffff).toNat

def isNaN (x : UInt64) : Bool := exponentField x == 2047 && fraction x != 0
/-- Signalling NaN: the top fraction bit is clear. -/
def isSignalingNaN (x : UInt64) : Bool := isNaN x && (x >>> 51) &&& 1 == 0
def isInfinite (x : UInt64) : Bool := exponentField x == 2047 && fraction x == 0
def isDenormal (x : UInt64) : Bool := exponentField x == 0 && fraction x != 0
def isZero (x : UInt64) : Bool := exponentField x == 0 && fraction x == 0

def quiet (x : UInt64) : UInt64 := x ||| 0x0008000000000000
def negate (x : UInt64) : UInt64 := x ^^^ 0x8000000000000000
/-- The "real indefinite" QNaN that invalid operations return. -/
def defaultNaN : UInt64 := 0xfff8000000000000
def signBit (s : Bool) : UInt64 := if s then 0x8000000000000000 else 0
def infinity (s : Bool) : UInt64 := signBit s ||| 0x7ff0000000000000

/-- A finite `x` as an integer `n` with `x = n * 2^-1074`. -/
def scaled (x : UInt64) : Int :=
  let magnitude : Nat := if exponentField x = 0 then fraction x
    else (fraction x + 2 ^ 52) * 2 ^ (exponentField x - 1)
  if sign x then -(magnitude : Int) else magnitude

/-- `m * 2^-shift` rounded to an integer, ties to even, and whether that was
inexact. -/
def roundShift (m : Nat) (shift : Int) : Nat × Bool :=
  if shift ≤ 0 then (m * 2 ^ shift.natAbs, false)
  else
    let shift := shift.toNat
    let q := m / 2 ^ shift
    let r := m % 2 ^ shift
    let half := 2 ^ (shift - 1)
    (if r > half || (r == half && q % 2 == 1) then q + 1 else q, r != 0)

/-- `±m * 2^e` (with `m > 0`) rounded to the nearest double, ties to even,
with the flags that raises. -/
def round (s : Bool) (m : Nat) (e : Int) : UInt64 × Exceptions :=
  -- `m * 2^e ∈ [2^(k-1), 2^k)`.
  let k : Int := (Nat.log2 m + 1 : Nat) + e
  -- Tininess after rounding: round to 53 bits with unbounded exponent.
  let q' := k - 53
  let (r', _) := roundShift m (q' - e)
  let tiny := (if r' = 2 ^ 53 then q' + 53 else q' + 52) < -1022
  -- The real rounding: 53 bits, but no finer than the denormal step 2^-1074.
  let q := max (k - 53) (-1074)
  let (r, inexact) := roundShift m (q - e)
  let (r, q) := if r = 2 ^ 53 then (2 ^ 52, q + 1) else (r, q)
  let underflow := tiny && inexact
  if r < 2 ^ 52 then
    -- Denormal or zero; then `q = -1074`.
    (signBit s ||| r.toUInt64, { underflow, inexact })
  else
    let biasedExponent := q + 1075
    if biasedExponent > 2046 then (infinity s, { overflow := true, inexact := true })
    else (signBit s ||| (biasedExponent.toNat.toUInt64 <<< 52) ||| (r - 2 ^ 52).toUInt64,
      { underflow, inexact })

/-- `n * 2^e` as a double; an exact zero gets sign `zeroSign`. -/
def ofScaled (n : Int) (e : Int) (zeroSign : Bool) : UInt64 × Exceptions :=
  if n = 0 then (signBit zeroSign, {}) else round (n < 0) n.natAbs e

/-- The result for NaN operands: the first one, quieted. -/
def nanResult (a b : UInt64) : UInt64 × Exceptions :=
  (if isNaN a then quiet a else quiet b, { invalid := isSignalingNaN a || isSignalingNaN b })

def add (a b : UInt64) : UInt64 × Exceptions :=
  if isNaN a || isNaN b then nanResult a b else
  let denormalFlag : Exceptions := { denormal := isDenormal a || isDenormal b }
  if isInfinite a && isInfinite b && sign a != sign b then (defaultNaN, { invalid := true })
  else if isInfinite a then (a, denormalFlag)
  else if isInfinite b then (b, denormalFlag)
  else
    let (r, e) := ofScaled (scaled a + scaled b) (-1074) (sign a && sign b)
    (r, e.merge denormalFlag)

/-- `a - b`. A NaN `b` keeps its sign, so negate only after the NaN check. -/
def sub (a b : UInt64) : UInt64 × Exceptions :=
  if isNaN a || isNaN b then nanResult a b else add a (negate b)

def mul (a b : UInt64) : UInt64 × Exceptions :=
  if isNaN a || isNaN b then nanResult a b else
  let denormalFlag : Exceptions := { denormal := isDenormal a || isDenormal b }
  let s := sign a != sign b
  if isInfinite a || isInfinite b then
    if isZero a || isZero b then (defaultNaN, { invalid := true })
    else (infinity s, denormalFlag)
  else
    let (r, e) := ofScaled (scaled a * scaled b) (-2148) s
    (r, e.merge denormalFlag)

/-- Compare without ordering NaNs (x86: `ucomisd a, b`): the `(zero, parity,
carry)` flags; unordered (a NaN operand) sets all three. Only a signalling NaN
raises `invalid`. -/
def compareUnordered (a b : UInt64) : (Bool × Bool × Bool) × Exceptions :=
  if isNaN a || isNaN b then ((true, true, true), { invalid := isSignalingNaN a || isSignalingNaN b }) else
  let v (x : UInt64) : Int :=
    if isInfinite x then (if sign x then -(2 : Int) ^ 2100 else 2 ^ 2100) else scaled x
  let flags := if v a < v b then (false, false, true)
    else if v a = v b then (true, false, false) else (false, false, false)
  (flags, { denormal := isDenormal a || isDenormal b })

/-- The "integer indefinite" value `truncateToInt64` returns for NaN or out of range. -/
def integerIndefinite : UInt64 := 0x8000000000000000

/-- Convert to a signed 64-bit integer, rounding toward zero (x86: `cvttsd2si r64`). -/
def truncateToInt64 (a : UInt64) : UInt64 × Exceptions :=
  if isNaN a || isInfinite a then (integerIndefinite, { invalid := true }) else
  let n := scaled a
  let t := n.tdiv (2 ^ 1074)
  if t < -(2 : Int) ^ 63 || t ≥ 2 ^ 63 then (integerIndefinite, { invalid := true })
  else ((t % 2 ^ 64).toNat.toUInt64, { inexact := n.tmod (2 ^ 1074) != 0 })

end X86.F64
