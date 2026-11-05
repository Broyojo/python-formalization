import PyLean.CoreLibs.Rand.Gen
import PyLean.Binary64.Model

/-!
IEEE 754 binary64 as the float type of `Lib/random.py`: the exact model `F64` of
`PyLean.Binary64`, with the C library as an explicit parameter.

What the hardware and IEEE 754 pin exactly is the `F64` operation: `+ - * /`, `sqrt`,
comparisons, `fabs`, `fmod`, `floor`, `float(int)` and the decimal literals of the
source (correctly rounded, as the compiler's `strtod` does). The transcendental
functions that `math.log`, `math.log2`, `math.exp`, `math.cos`, `math.sin`,
`math.acos` and `float.__pow__` call are the C library's, and C does not pin their
results. They are the fields of `RandLibm`. A property that needs a fact about one of
them states it as a hypothesis on the instance; the difftest instantiates it with the
pod's glibc (through Lean's `Float`, which calls the same functions).

`math.lgamma` is not libm: it is CPython's own `m_lgamma` (Modules/mathmodule.c:483-524),
mirrored below over `F64` and `RandLibm.log`.
-/

namespace PyLean.CoreLibs.Rand

open PyLean PyLean.Binary64

/-- The C library functions `Lib/random.py` reaches: `log` (`m_log`), `log2`
(`m_log2`), `exp`, `sin`, `cos`, `acos` (`math_1`) and `pow` (`float_pow`). -/
class RandLibm where
  log : F64 → F64
  log2 : F64 → F64
  exp : F64 → F64
  sin : F64 → F64
  cos : F64 → F64
  acos : F64 → F64
  pow : F64 → F64 → F64

namespace F64R

/-- A decimal literal `m * 10 ^ ∓e`, correctly rounded. -/
def ofDecimal (m : Nat) (neg : Bool) (e : Nat) : F64 :=
  if neg then F64.ofRat (mkRat m (10 ^ e)) else F64.ofRat ((m * 10 ^ e : Nat) : Rat)

/-- `x < n` for an `int` `n`, compared exactly (`float_richcompare`). -/
def ltInt (x : F64) (n : Int) : Bool :=
  if x.isNaN then false else if x.isInf then x.sign else decide (x.toRat < (n : Rat))

/-- `x == floor(x)` for a finite `x`. -/
def isInteger (x : F64) : Bool := x.isFinite && decide (x.toRat = (x.floorInt : Rat))

/-- `DOUBLE_IS_ODD_INTEGER(x)`: `fmod(fabs(x), 2.0) == 1.0`. -/
def isOdd (x : F64) : Bool := isInteger x && x.floorInt % 2 == 1

/-- `float(n)`: `none` when it rounds to an infinity (the `OverflowError`). -/
def ofIntOpt (n : Int) : Option F64 :=
  let x := F64.ofInt n
  if x.isInf then none else some x

/-- `lanczos_num_coeffs`, Modules/mathmodule.c:318-332. -/
def lanczosNum : List F64 := [
  ofDecimal 23531376880410759688572007674451636754734846804940 true 39,
  ofDecimal 42919803642649098768957899047001988850926355848959 true 39,
  ofDecimal 35711959237355668049440185451547166705960488635843 true 39,
  ofDecimal 17921034426037209699919755754458931112671403265390 true 39,
  ofDecimal 60395425863520280050642916443072979210699388420708 true 40,
  ofDecimal 14397204073117216736632230727949123939715485786772 true 40,
  ofDecimal 24887455786205415651146038641322942321632125127801 true 41,
  ofDecimal 31426415585400194380614231628318205362874684987640 true 42,
  ofDecimal 28763706289353724412254090516208496135991145378768 true 43,
  ofDecimal 18605626539522349504029498971604569928220784236328 true 44,
  ofDecimal 80716720023658162106380029022722506138218516325024 true 46,
  ofDecimal 21082427775157934587250973392071336271166969580291 true 47,
  ofDecimal 25066282746310002701649081771338373386264310793408 true 49]

/-- `lanczos_den_coeffs`, Modules/mathmodule.c:335-337. -/
def lanczosDen : List F64 :=
  [0, 39916800, 120543840, 150917976, 105258076, 45995730,
   13339535, 2637558, 357423, 32670, 1925, 66, 1].map (fun n : Nat => F64.ofInt n)

/-- `lanczos_g`, Modules/mathmodule.c:316. -/
def lanczosG : F64 := ofDecimal 6024680040776729583740234375 true 27

/-- `lanczos_sum`, Modules/mathmodule.c:351-378: Horner in `x` from the last
coefficient below `5.0`, in `1/x` from the first above. -/
def lanczosSum (x : F64) : F64 :=
  let pairs := lanczosNum.zip lanczosDen
  if F64.lt x (F64.ofInt 5) then
    let (n, d) := pairs.reverse.foldl (fun (acc : F64 × F64) (c : F64 × F64) =>
      (F64.add (F64.mul acc.1 x) c.1, F64.add (F64.mul acc.2 x) c.2)) (F64.zero false, F64.zero false)
    F64.div n d
  else
    let (n, d) := pairs.foldl (fun (acc : F64 × F64) (c : F64 × F64) =>
      (F64.add (F64.div acc.1 x) c.1, F64.add (F64.div acc.2 x) c.2)) (F64.zero false, F64.zero false)
    F64.div n d

/-- `m_lgamma`, Modules/mathmodule.c:483-524, for every argument except a negative
non-integer, whose reflection branch (:518-520) `Lib/random.py` cannot reach: it only
calls `_lgamma` on `m + 1`, `n - m + 1`, `k + 1` and `n - k + 1`, all integers `>= 1`.
That branch returns NaN here. The `EDOM` of a non-positive integer is reported by
`math_1a` as a `ValueError`; `Flt.mathLgamma` only sees the infinity, which is also
unreachable from `Lib/random.py`. -/
def lgamma [RandLibm] (x : F64) : F64 :=
  if !x.isFinite then (if x.isNaN then x else F64.inf false)
  else if isInteger x && F64.le x (F64.ofInt 2) then
    (if F64.le x (F64.zero false) then F64.inf false else F64.zero false)
  else
    let absx := x.abs
    if F64.lt absx (ofDecimal 1 true 20) then (RandLibm.log absx).neg
    else
      let r := F64.sub (RandLibm.log (lanczosSum absx)) lanczosG
      let r := F64.add r (F64.mul (F64.sub absx (ofDecimal 5 true 1))
        (F64.sub (RandLibm.log (F64.sub (F64.add absx lanczosG) (ofDecimal 5 true 1))) F64.one))
      if F64.lt x (F64.zero false) then F64.qnan else r

end F64R

/-- Binary64 as `Lib/random.py`'s float, given the C library. -/
instance instFltF64 [RandLibm] : Flt F64 where
  default := F64.zero false
  ofScientific := F64R.ofDecimal
  add := F64.add
  sub := F64.sub
  mul := F64.mul
  div := F64.div
  neg := F64.neg
  lt := F64.lt
  le := F64.le
  beq := F64.eq
  isNan := F64.isNaN
  isInf := F64.isInf
  sqrt := F64.sqrt
  log := RandLibm.log
  log2 := RandLibm.log2
  exp := RandLibm.exp
  sin := RandLibm.sin
  cos := RandLibm.cos
  acos := RandLibm.acos
  pow := RandLibm.pow
  fabs := F64.abs
  fmod := F64.fmod
  lgamma := F64R.lgamma
  floorInt := F64.floorInt
  ofInt := F64R.ofIntOpt
  ltInt := F64R.ltInt
  isInteger := F64R.isInteger
  isOddInteger := F64R.isOdd
  zeroLike x := F64.zero x.sign

/-- A C library used only as a witness: it shows that hypotheses on `RandLibm` (such as
`ExpNaN`, `exp(NaN)` is NaN) are satisfiable, and it instantiates refutations whose
lemmas hold for every library. It is never used to state a value. -/
@[instance_reducible] def annexWitness : RandLibm where
  log := id
  log2 := id
  exp := id
  sin := id
  cos := id
  acos := id
  pow x _ := x

end PyLean.CoreLibs.Rand
