import PyLean.CoreLibs.CalStat.Text
import PyLean.MathInt.Isqrt

/-!
Exact model of the binary64 values and operations `Lib/statistics.py` uses, local to this
area until `lean/PyLean/Binary64/` is merged.

A finite non-zero `float` is the rational number it denotes; `Flt.ofRat` is the round-to-nearest,
ties-to-even map from `Rat` to binary64, with gradual underflow and overflow to infinity. `+ - * /`,
`fma` and `sqrt` are then "compute exactly, round once", which is the IEEE 754 definition, so nothing
here depends on Lean's `Float` and everything can be evaluated by the kernel.

The functions `math.fsum`, `math.sumprod`, `math.hypot` and built-in `sum` are
mirrors of their C sources over these operations.
-/

namespace PyLean.CoreLibs.CalStat

open PyLean

inductive Flt where
  | nan
  | inf (neg : Bool)
  | zero (neg : Bool)
  /-- A finite non-zero value. -/
  | fin (q : Rat)
  deriving DecidableEq, Inhabited, Repr

namespace Flt

/-- `2 ** e` as a rational. -/
def pow2 (e : Int) : Rat :=
  if 0 ≤ e then ((2 ^ e.toNat : Nat) : Rat) else mkRat 1 (2 ^ (-e).toNat)

/-- `floor(log2(n / d))` for `n, d > 0`. -/
def floorLog2 (n d : Nat) : Int :=
  let l : Int := (Nat.log2 n : Int) - (Nat.log2 d : Int)
  let ge : Bool :=
    if 0 ≤ l then decide (d * 2 ^ l.toNat ≤ n) else decide (d ≤ n * 2 ^ (-l).toNat)
  if ge then l else l - 1

/-- `round_half_even(a / b)` for `b > 0`. -/
def roundDiv (a b : Nat) : Nat :=
  let m := a / b
  let r := a % b
  if 2 * r > b ∨ (2 * r = b ∧ m % 2 = 1) then m + 1 else m

/-- The rounding of `n / d > 0`: the integer significand `m` and exponent `e` with value `m * 2**e`.
`e` is the exponent of a 53-bit significand, clamped at the subnormal exponent -1074. -/
def roundMag (n d : Nat) : Nat × Int :=
  let k := floorLog2 n d
  let e := max (k - 52) (-1074)
  let m := if 0 ≤ e then roundDiv n (d * 2 ^ e.toNat) else roundDiv (n * 2 ^ (-e).toNat) d
  (m, e)

/-- Round an exact value to binary64, ties to even; a non-zero value that rounds to zero keeps its
sign, one that rounds past the largest finite float is an infinity. The exact value 0 gives `+0.0`. -/
def ofRat (q : Rat) : Flt :=
  if q = 0 then .zero false
  else
    let neg := decide (q < 0)
    let (m, e) := roundMag q.num.natAbs q.den
    if m = 0 then .zero neg
    else
      let v : Rat := (m : Rat) * pow2 e
      if v ≥ pow2 1024 then .inf neg
      else .fin (if neg then -v else v)

def isNan : Flt → Bool
  | .nan => true
  | _ => false

def isInf : Flt → Bool
  | .inf _ => true
  | _ => false

def isFinite : Flt → Bool
  | .zero _ | .fin _ => true
  | _ => false

/-- `math.copysign`-free sign test used by the operators. -/
def signBit : Flt → Bool
  | .nan => false
  | .inf n => n
  | .zero n => n
  | .fin q => decide (q < 0)

def neg : Flt → Flt
  | .nan => .nan
  | .inf n => .inf (!n)
  | .zero n => .zero (!n)
  | .fin q => .fin (-q)

def abs : Flt → Flt
  | .nan => .nan
  | .inf _ => .inf false
  | .zero _ => .zero false
  | .fin q => .fin (if q < 0 then -q else q)

def add : Flt → Flt → Flt
  | .nan, _ | _, .nan => .nan
  | .inf a, .inf b => if a = b then .inf a else .nan
  | .inf a, _ => .inf a
  | _, .inf a => .inf a
  | .zero a, .zero b => .zero (a && b)
  | .zero _, .fin q => .fin q
  | .fin q, .zero _ => .fin q
  | .fin a, .fin b => ofRat (a + b)

def sub (x y : Flt) : Flt := add x (neg y)

def mul : Flt → Flt → Flt
  | .nan, _ | _, .nan => .nan
  | .inf a, .inf b => .inf (a != b)
  | .inf _, .zero _ | .zero _, .inf _ => .nan
  | .inf a, .fin q | .fin q, .inf a => .inf (a != decide (q < 0))
  | .zero a, .zero b => .zero (a != b)
  | .zero a, .fin q | .fin q, .zero a => .zero (a != decide (q < 0))
  | .fin a, .fin b =>
    match ofRat (a * b) with
    | .zero _ => .zero (decide (a * b < 0))
    | r => r

/-- IEEE division (C `/`, no exception on a zero divisor). -/
def div : Flt → Flt → Flt
  | .nan, _ | _, .nan => .nan
  | .inf _, .inf _ => .nan
  | .inf a, y => .inf (a != signBit y)
  | x, .inf a => .zero (signBit x != a)
  | .zero _, .zero _ => .nan
  | .zero a, .fin q => .zero (a != decide (q < 0))
  | .fin q, .zero a => .inf (decide (q < 0) != a)
  | .fin a, .fin b =>
    match ofRat (a / b) with
    | .zero _ => .zero (decide (a / b < 0))
    | r => r

/-- C `fma(x, y, z)`: one rounding of `x*y + z`. -/
def fma (x y z : Flt) : Flt :=
  match x, y, z with
  | .fin a, .fin b, .fin c => ofRat (a * b + c)
  | .fin a, .fin b, .zero _ => ofRat (a * b)
  | .fin _, .fin _, z => z
  | x, y, z => add (mul x y) z

/-- `x == y`. -/
def eq : Flt → Flt → Bool
  | .inf a, .inf b => a == b
  | .zero _, .zero _ => true
  | .zero _, .fin b => decide (0 = b)
  | .fin a, .zero _ => decide (a = 0)
  | .fin a, .fin b => decide (a = b)
  | _, _ => false

/-- The rational value of a finite float. -/
def toRat : Flt → Rat
  | .fin q => q
  | _ => 0

/-- `x < y`. -/
def lt : Flt → Flt → Bool
  | .nan, _ | _, .nan => false
  | .inf a, .inf b => a && !b
  | .inf a, _ => a
  | _, .inf b => !b
  | x, y => decide (x.toRat < y.toRat)

def le (x y : Flt) : Bool := lt x y || eq x y

def truthy : Flt → Bool
  | .zero _ => false
  | _ => true

def one : Flt := .fin 1
def two : Flt := .fin 2
def half : Flt := .fin (mkRat 1 2)
def pz : Flt := .zero false

/-- Python int to `Rat`-valued float without the exception. -/
def ofInt (i : Int) : Flt := ofRat (i : Rat)

/-- `sqrt` of a positive rational, correctly rounded: the integer root of `q * 4**p` with a sticky
low bit carries at least 60 significant bits, so the single rounding in `ofRat` is correct. -/
def sqrtRat (q : Rat) : Flt :=
  let k := floorLog2 q.num.natAbs q.den
  let p : Int := 64 - k / 2
  let scaled : Rat := q * pow2 (2 * p)
  -- scaled >= 1: floor(sqrt(scaled)) from the integer part
  let fl := (scaled.num.natAbs / scaled.den : Nat)
  let r := match MathInt.isqrt fl with
    | .ok r => r
    | .error _ => 0
  let exact := decide ((r * r : Nat) = fl) && decide (scaled.den = 1)
  let r' := if exact then r else r ||| 1
  ofRat ((r' : Rat) * pow2 (-p))

def sqrt : Flt → Flt
  | .nan => .nan
  | .inf false => .inf false
  | .inf true => .nan
  | .zero n => .zero n
  | .fin q => if q < 0 then .nan else sqrtRat q

/-- `frexp`'s exponent for a finite non-zero value: `x = m * 2**e`, `0.5 <= |m| < 1`. -/
def frexpExp (q : Rat) : Int :=
  let a := if q < 0 then -q else q
  floorLog2 a.num.natAbs a.den + 1

/-- `ldexp(1.0, e)` as an exact scale, for the exponents `vector_norm` uses. -/
def ldexp1 (e : Int) : Flt := ofRat (pow2 e)

end Flt

/-! ## Python-level conversions -/

/-- `float(int)`, Objects/longobject.c `PyLong_AsDouble`. -/
def intToFlt (i : Int) : Py Flt :=
  match Flt.ofInt i with
  | .inf _ => .error (.overflowError "int too large to convert to float")
  | x => .ok x

/-- `a / b` for ints, Objects/longobject.c `long_true_divide`: correctly rounded;
the sign of a zero result comes from the signs of `a` and `b`. -/
def intTrueDiv (a b : Int) : Py Flt :=
  if b = 0 then .error (.zeroDivisionError "division by zero")
  else
    let neg := (a < 0) != (b < 0)
    if a = 0 then .ok (.zero neg)
    else
      match Flt.ofRat ((a : Rat) / (b : Rat)) with
      | .inf _ => .error (.overflowError "integer division result too large for a float")
      | x => .ok x

/-- `float(Fraction)`: `numbers.Rational.__float__`, `int(num) / int(den)`. -/
def ratToFlt (q : Rat) : Py Flt := intTrueDiv q.num q.den

/-- Python `x / y` on floats, Objects/floatobject.c `float_div`. -/
def fltDiv (x y : Flt) : Py Flt :=
  match y with
  | .zero _ => .error (.zeroDivisionError "division by zero")
  | _ => .ok (Flt.div x y)

/-! ## `math.fsum`, Modules/mathmodule.c@3.14.7:1363-1484 -/

/-- The partials loop for one `x`: returns the new partial list (in order) and the final `x`. -/
def fsumInner : List Flt → Flt → List Flt → List Flt × Flt
  | [], x, acc => (acc.reverse, x)
  | y :: ys, x, acc =>
    let (x', y') := if Flt.lt (Flt.abs x) (Flt.abs y) then (y, x) else (x, y)
    let hi := Flt.add x' y'
    let yr := Flt.sub hi x'
    let lo := Flt.sub y' yr
    fsumInner ys hi (if Flt.eq lo Flt.pz then acc else lo :: acc)

structure FsumState where
  partials : List Flt := []
  special : Flt := Flt.pz
  infSum : Flt := Flt.pz

def fsumStep (st : FsumState) (xsave : Flt) : Py FsumState :=
  let (p, x) := fsumInner st.partials xsave []
  if Flt.eq x Flt.pz then .ok { st with partials := p }
  else if !x.isFinite then
    if xsave.isFinite then .error (.overflowError "intermediate overflow in fsum")
    else
      .ok { partials := [],
            infSum := if xsave.isInf then Flt.add st.infSum xsave else st.infSum,
            special := Flt.add st.special xsave }
  else .ok { st with partials := p ++ [x] }

/-- The final summation of the partials, mathmodule.c:1365-1394; `ps` is reversed (top first). -/
def fsumFinish : List Flt → Flt
  | [] => Flt.pz
  | top :: rest =>
    let rec go : List Flt → Flt → Flt → Flt × Flt × List Flt
      | [], hi, lo => (hi, lo, [])
      | y :: ys, x, _ =>
        let hi := Flt.add x y
        let yr := Flt.sub hi x
        let lo := Flt.sub y yr
        if !Flt.eq lo Flt.pz then (hi, lo, ys) else go ys hi lo
    let (hi, lo, remaining) := go rest top Flt.pz
    match remaining with
    | [] => hi
    | p :: _ =>
      if (Flt.lt lo Flt.pz && Flt.lt p Flt.pz) || (Flt.lt Flt.pz lo && Flt.lt Flt.pz p) then
        let y := Flt.mul lo Flt.two
        let x := Flt.add hi y
        let yr := Flt.sub x hi
        if Flt.eq y yr then x else hi
      else hi

/-- The end of `math.fsum`, mathmodule.c:1357-1394. -/
def fsumEnd (st : FsumState) : Py Flt :=
  if !Flt.eq st.special Flt.pz then
    if st.infSum.isNan then .error (.valueError "-inf + inf in fsum")
    else .ok st.special
  else .ok (fsumFinish st.partials.reverse)

/-! ## Compensated arithmetic, Modules/mathmodule.c:93-188 -/

structure DL where
  hi : Flt
  lo : Flt

def dlFastSum (a b : Flt) : DL :=
  let x := Flt.add a b
  ⟨x, Flt.add (Flt.sub a x) b⟩

def dlSum (a b : Flt) : DL :=
  let x := Flt.add a b
  let z := Flt.sub x a
  ⟨x, Flt.add (Flt.sub a (Flt.sub x z)) (Flt.sub b z)⟩

def dlMul (x y : Flt) : DL :=
  let z := Flt.mul x y
  ⟨z, Flt.fma x y (Flt.neg z)⟩

structure TL where
  hi : Flt := Flt.pz
  lo : Flt := Flt.pz
  tiny : Flt := Flt.pz

def tlFma (x y : Flt) (t : TL) : TL :=
  let pr := dlMul x y
  let sm := dlSum t.hi pr.hi
  let r1 := dlSum t.lo pr.lo
  let r2 := dlSum r1.hi sm.lo
  ⟨sm.hi, r2.hi, Flt.add (Flt.add t.tiny r1.lo) r2.lo⟩

def tlToD (t : TL) : Flt :=
  let last := dlSum t.lo t.hi
  Flt.add (Flt.add t.tiny last.lo) last.hi

/-! ## `math.hypot(x, y)`, `vector_norm`, Modules/mathmodule.c:1897-1936 -/

/-- `vector_norm` for finite coordinates without the subnormal recursion. -/
def vectorNormCore (vec : List Flt) (maxE : Int) : Flt :=
  let scale := Flt.ldexp1 (-maxE)
  let st := vec.foldl (fun (st : Flt × Flt × Flt) x =>
    let (csum, frac1, frac2) := st
    let x := Flt.mul x scale
    let pr := dlMul x x
    let sm := dlFastSum csum pr.hi
    (sm.hi, Flt.add frac1 pr.lo, Flt.add frac2 sm.lo)) (Flt.one, Flt.pz, Flt.pz)
  let (csum, frac1, frac2) := st
  let h := Flt.sqrt (Flt.add (Flt.sub csum Flt.one) (Flt.add frac1 frac2))
  let pr := dlMul (Flt.neg h) h
  let sm := dlFastSum csum pr.hi
  let csum := sm.hi
  let frac1 := Flt.add frac1 pr.lo
  let frac2 := Flt.add frac2 sm.lo
  let x := Flt.add (Flt.sub csum Flt.one) (Flt.add frac1 frac2)
  let h := Flt.add h (Flt.div x (Flt.mul Flt.two h))
  Flt.div h scale

/-- `DBL_MIN`. -/
def dblMin : Flt := .fin (Flt.pow2 (-1022))

def vectorNorm (vec : List Flt) (mx : Flt) (foundNan : Bool) : Flt :=
  if mx.isInf then mx
  else if foundNan then .nan
  else if Flt.eq mx Flt.pz || vec.length ≤ 1 then mx
  else
    let e := Flt.frexpExp mx.toRat
    if e < -1023 then
      let vec' := vec.map (fun x => Flt.div x dblMin)
      let mx' := Flt.div mx dblMin
      Flt.mul dblMin (vectorNormCore vec' (Flt.frexpExp mx'.toRat))
    else vectorNormCore vec e

/-- `math.hypot(x, y)`, Modules/mathmodule.c:2066-2096. -/
def hypot (x y : Flt) : Flt :=
  let a := Flt.abs x
  let b := Flt.abs y
  let mx0 := if Flt.lt Flt.pz a then a else Flt.pz
  let mx := if Flt.lt mx0 b then b else mx0
  vectorNorm [a, b] mx (a.isNan || b.isNan)

/-! ## Built-in `sum` over floats, Python/bltinmodule.c:2832-2855 and :2973-3017 -/

structure CS where
  hi : Flt
  lo : Flt

def csAdd (t : CS) (x : Flt) : CS :=
  let s := Flt.add t.hi x
  if Flt.le (Flt.abs x) (Flt.abs t.hi) then
    ⟨s, Flt.add t.lo (Flt.add (Flt.sub t.hi s) x)⟩
  else ⟨s, Flt.add t.lo (Flt.add (Flt.sub x s) t.hi)⟩

def csToDouble (t : CS) : Flt :=
  if Flt.truthy t.lo && t.lo.isFinite then Flt.add t.hi t.lo else t.hi

/-- `sum(xs, start)` with `xs` all floats and at least one of them, and `start` an int: the
int loop adds `start` to the first float (`PyNumber_Add`), then the float loop takes over. -/
def builtinSumFloats (start : Flt) : List Flt → Flt
  | [] => start
  | x :: xs => csToDouble (xs.foldl csAdd ⟨Flt.add start x, Flt.pz⟩)

/-! ## `hash(float)` and `hash(tuple)` -/

def hashModulus : Nat := 2 ^ 61 - 1
def uMask : Nat := 2 ^ 64

/-- `_Py_HashDouble`, Python/pyhash.c: `|x| mod (2**61 - 1)` with the sign of `x`, `-1` becoming
`-2`. For a dyadic value the loop computes the residue of numerator times the inverse power of 2;
`2**61 = 1` modulo the modulus gives the inverse as `2 ** (61 - k % 61)`. `nan` hashes by identity
and is not modelled (its `0` is never compared). -/
def hashFlt : Flt → Int
  | .nan => 0
  | .inf n => if n then -314159 else 314159
  | .zero _ => 0
  | .fin q =>
    let a := q.num.natAbs
    let k := Nat.log2 q.den
    let r := (a * 2 ^ ((61 - k % 61) % 61)) % hashModulus
    let v : Int := if q < 0 then -(r : Int) else r
    if v = -1 then -2 else v

def xxPrime1 : Nat := 11400714785074694791
def xxPrime2 : Nat := 14029467366897019727
def xxPrime5 : Nat := 2870177450012600261

/-- `tuple_hash`, Objects/tupleobject.c, as 64-bit unsigned arithmetic. -/
def hashTuple (items : List Int) : Int :=
  let u (x : Int) : Nat := (x % (uMask : Int)).toNat
  let acc := items.foldl (fun (acc : Nat) lane =>
    let a := (acc + u lane * xxPrime2) % uMask
    let a := ((a <<< 31) % uMask) ||| (a >>> 33)
    (a * xxPrime1) % uMask) xxPrime5
  let acc := (acc + (items.length ^^^ (xxPrime5 ^^^ 3527539))) % uMask
  let acc := if acc = uMask - 1 then 1546275796 else acc
  if acc ≥ 2 ^ 63 then (acc : Int) - uMask else acc

/-! ## `repr(float)` -/

/-- `10 ** e`. -/
def pow10 (e : Int) : Rat :=
  if 0 ≤ e then ((10 ^ e.toNat : Nat) : Rat) else mkRat 1 (10 ^ (-e).toNat)

/-- `floor(q)` for `q >= 0`. -/
def natFloor (q : Rat) : Nat := q.num.natAbs / q.den

/-- The largest `e` with `10**e <= q`, for `q > 0`. -/
def decExp (q : Rat) : Int :=
  let approx : Int :=
    (((Flt.floorLog2 q.num.natAbs q.den) * 30103) / 100000)
  let rec go : Nat → Int → Int
    | 0, e => e
    | f + 1, e => if pow10 (e + 1) ≤ q then go f (e + 1)
                  else if q < pow10 e then go f (e - 1) else e
  go 8 approx

/-- `dtoa` mode 0: the shortest digit string that rounds back to `x > 0`, closest to `x`
among those; returned as an integer of `k` digits and the decimal exponent of its last digit. -/
def shortestDigits (x : Rat) : Nat × Int :=
  let e := decExp x
  let rec go : Nat → Nat → Nat × Int
    | 0, k =>
      let ex := e - (k : Int) + 1
      (natFloor (x / pow10 ex + mkRat 1 2), ex)
    | f + 1, k =>
      let ex := e - (k : Int) + 1
      let scaled := x / pow10 ex
      let lo := natFloor scaled
      let hi := lo + 1
      let okLo := decide (Flt.ofRat ((lo : Rat) * pow10 ex) = .fin x)
      let okHi := decide (Flt.ofRat ((hi : Rat) * pow10 ex) = .fin x)
      if okLo && okHi then
        -- both candidates round to x: take the closer, ties to even digit
        let dLo := scaled - (lo : Rat)
        let dHi := (hi : Rat) - scaled
        if dLo < dHi then (lo, ex) else if dHi < dLo then (hi, ex)
        else if lo % 2 = 0 then (lo, ex) else (hi, ex)
      else if okLo then (lo, ex)
      else if okHi then (hi, ex)
      else go f (k + 1)
  go 17 1

/-- `repr(float)`, Python/pystrtod.c `format_float_short` with `'r'`: exponent form when
the decimal point position `decpt` is outside `-4 < decpt <= 16`. -/
def fltRepr : Flt → String
  | .nan => "nan"
  | .inf n => if n then "-inf" else "inf"
  | .zero n => if n then "-0.0" else "0.0"
  | .fin q =>
    let sign := if q < 0 then "-" else ""
    let a := if q < 0 then -q else q
    let (m, ex) := shortestDigits a
    let ds0 := Nat.toDigits 10 m
    let ds := (ds0.reverse.dropWhile (· == '0')).reverse
    let decpt : Int := (ds0.length : Int) + ex
    let n : Int := ds.length
    let body : List Char :=
      if decpt ≤ -4 ∨ decpt > 16 then
        let e := decpt - 1
        let tailDigits := ds.drop 1
        let es := Nat.toDigits 10 e.natAbs
        ds.take 1 ++ (if tailDigits.isEmpty then [] else '.' :: tailDigits) ++ ['e'] ++
          [if e < 0 then '-' else '+'] ++ (if es.length < 2 then ['0'] else []) ++ es
      else if decpt ≤ 0 then
        "0.".toList ++ List.replicate (-decpt).toNat '0' ++ ds
      else if decpt ≥ n then
        ds ++ List.replicate (decpt - n).toNat '0' ++ ".0".toList
      else
        ds.take decpt.toNat ++ ['.'] ++ ds.drop decpt.toNat
    sign ++ String.ofList body

end PyLean.CoreLibs.CalStat
