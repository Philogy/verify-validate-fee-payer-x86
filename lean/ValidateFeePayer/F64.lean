/-!
IEEE 754 binary64 arithmetic as SSE2 performs it, on raw bits, for the
operations the carved code uses: `addsd`/`subsd`/`subpd`, `mulsd`, `ucomisd`
and `cvttsd2si`.

Only the default MXCSR control setting is modelled: round to nearest even,
all exceptions masked, no flush-to-zero, no denormals-are-zero. The machine
stops with `unsupported` on any other setting rather than compute something
else. Under that setting an operation never traps; it returns a value and
the exception flags it raises, which the machine ORs into MXCSR.

Arithmetic is exact: every finite double is an integer multiple of `2^-1074`
(`scaled`), so a sum or product is an exact integer times a power of two,
and `round` rounds that once. Rules taken from the Intel SDM, vol. 1 §4.8–4.9
and §11.5, which the per-instruction oracle should confirm:

- NaN operand: the result is the first NaN operand (destination first),
  quieted; `IE` only if some operand is a signalling NaN.
- `inf - inf`, `0 * inf`: the default NaN `0xFFF8…0` and `IE`.
- `DE` when an operand is denormal and no operand is a NaN.
- Tininess is detected after rounding; with underflow masked, `UE` is set
  only when the (denormalised) result is also inexact.
- Overflow gives ±infinity with `OE` and `PE`.
- An exact zero sum is `+0`, except `(-0) + (-0) = -0`.
-/

namespace ValidateFeePayer.F64

/-- Exception flags, as MXCSR bits 0–5 (`IE DE ZE OE UE PE`; `ZE` never
arises here). -/
structure Exc where
  ie : Bool := false
  de : Bool := false
  oe : Bool := false
  ue : Bool := false
  pe : Bool := false
  deriving DecidableEq, Repr

def Exc.or (a b : Exc) : Exc :=
  ⟨a.ie || b.ie, a.de || b.de, a.oe || b.oe, a.ue || b.ue, a.pe || b.pe⟩

def Exc.bits (e : Exc) : UInt32 :=
  (if e.ie then 1 else 0) ||| (if e.de then 2 else 0) ||| (if e.oe then 8 else 0) |||
  (if e.ue then 16 else 0) ||| (if e.pe then 32 else 0)

def sign (x : UInt64) : Bool := x >>> 63 == 1
def expField (x : UInt64) : Nat := ((x >>> 52) &&& 0x7ff).toNat
def frac (x : UInt64) : Nat := (x &&& 0xfffffffffffff).toNat

def isNaN (x : UInt64) : Bool := expField x == 2047 && frac x != 0
/-- Signalling NaN: the top fraction bit is clear. -/
def isSNaN (x : UInt64) : Bool := isNaN x && (x >>> 51) &&& 1 == 0
def isInf (x : UInt64) : Bool := expField x == 2047 && frac x == 0
def isDenormal (x : UInt64) : Bool := expField x == 0 && frac x != 0
def isZero (x : UInt64) : Bool := expField x == 0 && frac x == 0

def quiet (x : UInt64) : UInt64 := x ||| 0x0008000000000000
def negate (x : UInt64) : UInt64 := x ^^^ 0x8000000000000000
/-- The "real indefinite" QNaN that invalid operations return. -/
def defaultNaN : UInt64 := 0xfff8000000000000
def signBit (s : Bool) : UInt64 := if s then 0x8000000000000000 else 0
def inf (s : Bool) : UInt64 := signBit s ||| 0x7ff0000000000000

/-- A finite `x` as an integer `n` with `x = n * 2^-1074`. -/
def scaled (x : UInt64) : Int :=
  let mag : Nat := if expField x = 0 then frac x else (frac x + 2 ^ 52) * 2 ^ (expField x - 1)
  if sign x then -(mag : Int) else mag

/-- `m * 2^-sh` rounded to an integer, ties to even, and whether that was
inexact. -/
def roundShift (m : Nat) (sh : Int) : Nat × Bool :=
  if sh ≤ 0 then (m * 2 ^ sh.natAbs, false)
  else
    let sh := sh.toNat
    let q := m / 2 ^ sh
    let r := m % 2 ^ sh
    let half := 2 ^ (sh - 1)
    (if r > half || (r == half && q % 2 == 1) then q + 1 else q, r != 0)

/-- `±m * 2^e` (with `m > 0`) rounded to the nearest double, ties to even,
with the flags that raises. -/
def round (s : Bool) (m : Nat) (e : Int) : UInt64 × Exc :=
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
  let ue := tiny && inexact
  if r < 2 ^ 52 then
    -- Denormal or zero; then `q = -1074`.
    (signBit s ||| r.toUInt64, { ue, pe := inexact })
  else
    let E := q + 1075
    if E > 2046 then (inf s, { oe := true, pe := true })
    else (signBit s ||| (E.toNat.toUInt64 <<< 52) ||| (r - 2 ^ 52).toUInt64, { ue, pe := inexact })

/-- `n * 2^e` as a double; an exact zero gets sign `zeroSign`. -/
def ofScaled (n : Int) (e : Int) (zeroSign : Bool) : UInt64 × Exc :=
  if n = 0 then (signBit zeroSign, {}) else round (n < 0) n.natAbs e

/-- The result for NaN operands: the first one, quieted. -/
def nanResult (a b : UInt64) : UInt64 × Exc :=
  (if isNaN a then quiet a else quiet b, { ie := isSNaN a || isSNaN b })

def add (a b : UInt64) : UInt64 × Exc :=
  if isNaN a || isNaN b then nanResult a b else
  let de : Exc := { de := isDenormal a || isDenormal b }
  if isInf a && isInf b && sign a != sign b then (defaultNaN, { ie := true })
  else if isInf a then (a, de)
  else if isInf b then (b, de)
  else
    let (r, e) := ofScaled (scaled a + scaled b) (-1074) (sign a && sign b)
    (r, e.or de)

/-- `a - b`. A NaN `b` keeps its sign, so negate only after the NaN check. -/
def sub (a b : UInt64) : UInt64 × Exc :=
  if isNaN a || isNaN b then nanResult a b else add a (negate b)

def mul (a b : UInt64) : UInt64 × Exc :=
  if isNaN a || isNaN b then nanResult a b else
  let de : Exc := { de := isDenormal a || isDenormal b }
  let s := sign a != sign b
  if isInf a || isInf b then
    if isZero a || isZero b then (defaultNaN, { ie := true })
    else (inf s, de)
  else
    let (r, e) := ofScaled (scaled a * scaled b) (-2148) s
    (r, e.or de)

/-- `ucomisd a, b`: `(ZF, PF, CF)`; unordered is all three set. Only a
signalling NaN raises `IE`. -/
def ucomisd (a b : UInt64) : (Bool × Bool × Bool) × Exc :=
  if isNaN a || isNaN b then ((true, true, true), { ie := isSNaN a || isSNaN b }) else
  let v (x : UInt64) : Int := if isInf x then (if sign x then -(2 : Int) ^ 2100 else 2 ^ 2100) else scaled x
  let flags := if v a < v b then (false, false, true)
    else if v a = v b then (true, false, false) else (false, false, false)
  (flags, { de := isDenormal a || isDenormal b })

/-- The "integer indefinite" `cvttsd2si` returns for NaN or out of range. -/
def intIndefinite : UInt64 := 0x8000000000000000

/-- `cvttsd2si r64`: truncate toward zero. -/
def cvttsd2si (a : UInt64) : UInt64 × Exc :=
  if isNaN a || isInf a then (intIndefinite, { ie := true }) else
  let n := scaled a
  let t := n.tdiv (2 ^ 1074)
  if t < -(2 : Int) ^ 63 || t ≥ 2 ^ 63 then (intIndefinite, { ie := true })
  else ((t % 2 ^ 64).toNat.toUInt64, { pe := n.tmod (2 ^ 1074) != 0 })

end ValidateFeePayer.F64
