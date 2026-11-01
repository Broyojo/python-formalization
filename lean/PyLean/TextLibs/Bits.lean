import PyLean.Core

/-!
Exact IEEE 754 helpers on bit patterns, used by the float format codes of
`struct` (`Modules/_struct.c`, `Objects/floatobject.c`).

A Python `float` is the `Nat` holding its 64 bits, so everything here is
decidable and provable, unlike Lean's `Float`. The hardware operations that the
C source performs with a cast (`(float)x`, `(double)f`, `PyLong_AsDouble`) have
no C body to mirror; they are IEEE round-to-nearest-even, written once in
`encodeRounded`.
-/

namespace PyLean.TextLibs

/-- Parameters of a binary interchange format. -/
structure Fmt where
  fracBits : Nat
  expBits : Nat

def f64 : Fmt := ⟨52, 11⟩
def f32 : Fmt := ⟨23, 8⟩

def Fmt.bias (F : Fmt) : Nat := 2 ^ (F.expBits - 1) - 1
def Fmt.expMax (F : Fmt) : Nat := 2 ^ F.expBits - 1
def Fmt.sign (F : Fmt) (v : Nat) : Nat := v / 2 ^ (F.fracBits + F.expBits) % 2
def Fmt.expOf (F : Fmt) (v : Nat) : Nat := v / 2 ^ F.fracBits % 2 ^ F.expBits
def Fmt.frac (F : Fmt) (v : Nat) : Nat := v % 2 ^ F.fracBits
def Fmt.isNaN (F : Fmt) (v : Nat) : Bool := F.expOf v == F.expMax && F.frac v != 0
def Fmt.isInf (F : Fmt) (v : Nat) : Bool := F.expOf v == F.expMax && F.frac v == 0
def Fmt.infBits (F : Fmt) (s : Nat) : Nat :=
  s * 2 ^ (F.fracBits + F.expBits) + F.expMax * 2 ^ F.fracBits

/-- Magnitude `m * 2 ^ e` of a finite value of format `F`. -/
def Fmt.mag (F : Fmt) (v : Nat) : Nat × Int :=
  if F.expOf v = 0 then (F.frac v, 1 - (F.bias : Int) - F.fracBits)
  else (F.frac v + 2 ^ F.fracBits, (F.expOf v : Int) - F.bias - F.fracBits)

/-- `m * 2 ^ (-s)` rounded to an integer, ties to even (`s` is an arbitrary shift). -/
def roundShift (m : Nat) (s : Int) : Nat :=
  if s ≤ 0 then m * 2 ^ (-s).toNat
  else
    let d := 2 ^ s.toNat
    let q := m / d
    let r := m % d
    if 2 * r > d ∨ (2 * r = d ∧ q % 2 = 1) then q + 1 else q

/-- Encode `(-1)^sign * m * 2 ^ e` in format `F`, rounding to nearest-even. `none`
means the magnitude rounded past the largest finite value. -/
def Fmt.encodeRounded (F : Fmt) (sign m : Nat) (e : Int) : Option Nat :=
  if m = 0 then some (sign * 2 ^ (F.fracBits + F.expBits))
  else
    let top : Int := (Nat.log2 m : Int) + e
    let minE : Int := 1 - (F.bias : Int)
    let body : Nat :=
      if top < minE then roundShift m (minE - F.fracBits - e)
      else (top - minE).toNat * 2 ^ F.fracBits + roundShift m (top - F.fracBits - e)
    if body ≥ F.expMax * 2 ^ F.fracBits then none
    else some (sign * 2 ^ (F.fracBits + F.expBits) + body)

/-- `(float)x` for a double bit pattern: rounds, overflows to infinity, and quiets a
NaN keeping the top payload bits (x86-64 `cvtsd2ss`). -/
def castDoubleToFloat (x : Nat) : Nat :=
  let s := f64.sign x
  if f64.isNaN x then
    f32.infBits s + (2 ^ 22 ||| (f64.frac x / 2 ^ 29))
  else if f64.isInf x then f32.infBits s
  else
    let (m, e) := f64.mag x
    (f32.encodeRounded s m e).getD (f32.infBits s)

/-- `(double)y` for a float bit pattern: exact, and quiets a NaN (`cvtss2sd`). -/
def castFloatToDouble (y : Nat) : Nat :=
  let s := f32.sign y
  if f32.isNaN y then
    f64.infBits s + (2 ^ 51 ||| (f32.frac y * 2 ^ 29))
  else if f32.isInf y then f64.infBits s
  else
    let (m, e) := f32.mag y
    (f64.encodeRounded s m e).getD (f64.infBits s)

/-- `PyLong_AsDouble`: `none` is `OverflowError`. -/
def intToDouble (n : Int) : Option Nat :=
  f64.encodeRounded (if n < 0 then 1 else 0) n.natAbs 0

/-- Bytes of `x`, little-endian (`memcpy` from an integer on a little-endian machine). -/
def leBytes : Nat → Nat → List Nat
  | 0, _ => []
  | i + 1, x => x % 256 :: leBytes i (x / 256)

/-- `x = (x<<8) | *bytes++` over the bytes in order. -/
def beVal (bytes : List Nat) : Nat := bytes.foldl (fun x b => x * 256 + b) 0

/-- Value of a little-endian byte string. -/
def leVal : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * leVal bs

end PyLean.TextLibs
