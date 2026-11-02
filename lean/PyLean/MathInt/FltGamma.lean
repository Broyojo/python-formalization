import PyLean.MathInt.FltBase

/-!
# `Modules/mathmodule.c`: `gamma` and `lgamma`

CPython 3.15.2 computes the gamma function itself (`m_tgamma`, `m_lgamma`, with
`m_sinpi` and `lanczos_sum`), calling the C library only for `sin`, `cos`, `exp`, `pow`
and `log`. Those are parameters (`GammaLibm`); `fmod`, `round`, `floor`, `fabs` and
`copysign` are exact. `errno` is threaded through every call: a C library call stores
only a nonzero value.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64

/-- The C library functions `m_tgamma` and `m_lgamma` call. -/
structure GammaLibm where
  sin : CFun1
  cos : CFun1
  exp : CFun1
  log : CFun1
  pow : CFun2

/-- A C `double` literal: the decimal `m / 10 ^ k`, rounded to nearest. -/
def decLit (m k : Nat) : F64 := F64.ofRat (mkRat m (10 ^ k))

/-- `pi`, mathmodule.c:197. -/
def piG : F64 := decLit 3141592653589793238462643383279502884197 39
/-- `logpi`, mathmodule.c:198. -/
def logpi : F64 := decLit 1144729885849400174143427351353058711647 39
/-- `lanczos_g`, mathmodule.c:316. -/
def lanczos_g : F64 := decLit 6024680040776729583740234375 27
/-- `lanczos_g_minus_half`, mathmodule.c:317. -/
def lanczos_g_minus_half : F64 := decLit 5524680040776729583740234375 27

/-- `lanczos_num_coeffs`, mathmodule.c:318-332. -/
def lanczos_num_coeffs : List F64 := [
  decLit 23531376880410759688572007674451636754734846804940 39,
  decLit 42919803642649098768957899047001988850926355848959 39,
  decLit 35711959237355668049440185451547166705960488635843 39,
  decLit 17921034426037209699919755754458931112671403265390 39,
  decLit 60395425863520280050642916443072979210699388420708 40,
  decLit 14397204073117216736632230727949123939715485786772 40,
  decLit 24887455786205415651146038641322942321632125127801 41,
  decLit 31426415585400194380614231628318205362874684987640 42,
  decLit 28763706289353724412254090516208496135991145378768 43,
  decLit 18605626539522349504029498971604569928220784236328 44,
  decLit 80716720023658162106380029022722506138218516325024 46,
  decLit 21082427775157934587250973392071336271166969580291 47,
  decLit 25066282746310002701649081771338373386264310793408 49]

/-- `lanczos_den_coeffs`, mathmodule.c:335-337. -/
def lanczos_den_coeffs : List F64 :=
  [0, 39916800, 120543840, 150917976, 105258076, 45995730, 13339535, 2637558, 357423, 32670,
    1925, 66, 1].map F64.ofInt

/-- `gamma_integral`, mathmodule.c:341-347: the literals, `gamma_integral[k]` for `k + 1`. -/
def gamma_integral : List F64 :=
  [1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880, 3628800, 39916800, 479001600, 6227020800,
    87178291200, 1307674368000, 20922789888000, 355687428096000, 6402373705728000,
    121645100408832000, 2432902008176640000, 51090942171709440000,
    1124000727777607680000].map F64.ofInt

def c5 : F64 := F64.ofBits 0x4014000000000000
def c140 : F64 := F64.ofBits 0x4061800000000000
def c200 : F64 := F64.ofBits 0x4069000000000000
def c4 : F64 := F64.ofBits 0x4010000000000000
def c0p25 : F64 := F64.ofBits 0x3fd0000000000000
def c1em20 : F64 := decLit 1 20
def NGAMMA_INTEGRAL : F64 := F64.ofInt 23

/-- `lanczos_sum`, mathmodule.c:351-378, for `x > 0`. -/
def lanczos_sum (x : F64) : F64 :=
  let pairs := lanczos_num_coeffs.zip lanczos_den_coeffs
  let (num, den) :=
    if F64.lt x c5 then
      -- `for (i = LANCZOS_N; --i >= 0; )`
      pairs.reverse.foldl (fun (nd : F64 × F64) (c : F64 × F64) =>
        (F64.add (F64.mul nd.1 x) c.1, F64.add (F64.mul nd.2 x) c.2)) (c0, c0)
    else
      pairs.foldl (fun (nd : F64 × F64) (c : F64 × F64) =>
        (F64.add (F64.div nd.1 x) c.1, F64.add (F64.div nd.2 x) c.2)) (c0, c0)
  F64.div num den

/-- `(int)round(v)` for `0 <= v <= 4`. -/
def roundToInt (v : F64) : Int := (F64.roundAway v).truncInt

/-- Call a C library function with `errno` at `e`: the result and `errno` afterwards (a call
stores only a nonzero value). -/
def call1 (f : CFun1) (x : F64) (e : Errno) : F64 × Errno := ((f x).1, e.after (f x).2)

def call2 (f : CFun2) (x y : F64) (e : Errno) : F64 × Errno := ((f x y).1, e.after (f x y).2)

/-- `m_sinpi`, mathmodule.c:222-254, for finite `x`, with `errno` at `e` on entry. -/
def m_sinpi (L : GammaLibm) (x : F64) (e : Errno) : F64 × Errno :=
  let y := F64.fmod (F64.abs x) c2
  let n := roundToInt (F64.mul c2 y)
  let (r, e) :=
    match n with
    | 0 => call1 L.sin (F64.mul piG y) e
    | 1 => call1 L.cos (F64.mul piG (F64.sub y cHalf)) e
    | 2 => call1 L.sin (F64.mul piG (F64.sub c1 y)) e
    | 3 => let (c, e) := call1 L.cos (F64.mul piG (F64.sub y c1p5)) e; (F64.neg c, e)
    | _ => call1 L.sin (F64.mul piG (F64.sub y c2)) e
  (F64.mul (F64.copysign c1 x) r, e)

/-- The Lanczos part of `m_tgamma`, mathmodule.c:433-474, for `1e-20 <= absx <= 200` and
`x` not an integer in `[1, 23]`. -/
def tgammaLanczos (L : GammaLibm) (x absx : F64) : F64 × Errno :=
  let y := F64.add absx lanczos_g_minus_half
  let z0 :=
    if F64.lt lanczos_g_minus_half absx then
      let q := F64.sub y absx
      F64.sub q lanczos_g_minus_half
    else
      let q := F64.sub y lanczos_g_minus_half
      F64.sub q absx
  let z := F64.div (F64.mul z0 lanczos_g) y
  let (r, e) :=
    if F64.lt x c0 then
      let (s, e) := m_sinpi L absx .zero
      let (ey, e) := call1 L.exp y e
      let r := F64.div (F64.mul (F64.div (F64.div piG.neg s) absx) ey) (lanczos_sum absx)
      let r := F64.sub r (F64.mul z r)
      if F64.lt absx c140 then
        let (p, e) := call2 L.pow y (F64.sub absx cHalf) e
        (F64.div r p, e)
      else
        let (sqrtpow, e) := call2 L.pow y (F64.sub (F64.div absx c2) c0p25) e
        (F64.div (F64.div r sqrtpow) sqrtpow, e)
    else
      let (ey, e) := call1 L.exp y .zero
      let r := F64.div (lanczos_sum absx) ey
      let r := F64.add r (F64.mul z r)
      if F64.lt absx c140 then
        let (p, e) := call2 L.pow y (F64.sub absx cHalf) e
        (F64.mul r p, e)
      else
        let (sqrtpow, e) := call2 L.pow y (F64.sub (F64.div absx c2) c0p25) e
        (F64.mul (F64.mul r sqrtpow) sqrtpow, e)
  (r, if r.isInf then .erange else e)

/-- `m_tgamma`, mathmodule.c:381-475, called with `errno == 0`: the result and `errno`. -/
def m_tgamma (L : GammaLibm) (x : F64) : F64 × Errno :=
  if !x.isFinite then
    if x.isNaN || F64.lt c0 x then (x, .zero)
    else (cNaN, .edom)
  else if isZeroC x then (F64.copysign cInf x, .edom)
  else if F64.eq x (F64.floor x) && F64.lt x c0 then (cNaN, .edom)
  else if F64.eq x (F64.floor x) && F64.le x NGAMMA_INTEGRAL then
    (gamma_integral.getD (x.truncInt.toNat - 1) c0, .zero)
  else
    let absx := F64.abs x
    if F64.lt absx c1em20 then
      let r := F64.div c1 x
      (r, if r.isInf then .erange else .zero)
    else if F64.lt c200 absx then
      if F64.lt x c0 then
        let (s, e) := m_sinpi L x .zero
        (F64.div c0 s, e)
      else (cInf, .erange)
    else tgammaLanczos L x absx

/-- The Lanczos part of `m_lgamma`, mathmodule.c:516-523. -/
def lgammaLanczos (L : GammaLibm) (x absx : F64) : F64 × Errno :=
  let (l1, e) := call1 L.log (lanczos_sum absx) .zero
  let r := F64.sub l1 lanczos_g
  let (l2, e) := call1 L.log (F64.sub (F64.add absx lanczos_g) cHalf) e
  let r := F64.add r (F64.mul (F64.sub absx cHalf) (F64.sub l2 c1))
  let (r, e) :=
    if F64.lt x c0 then
      let (s, e) := m_sinpi L absx e
      let (ls, e) := call1 L.log (F64.abs s) e
      let (la, e) := call1 L.log absx e
      (F64.sub (F64.sub (F64.sub logpi ls) la) r, e)
    else (r, e)
  (r, if r.isInf then .erange else e)

/-- `m_lgamma`, mathmodule.c:482-524, called with `errno == 0`. -/
def m_lgamma (L : GammaLibm) (x : F64) : F64 × Errno :=
  if !x.isFinite then
    if x.isNaN then (x, .zero) else (cInf, .zero)
  else if F64.eq x (F64.floor x) && F64.le x c2 then
    if F64.le x c0 then (cInf, .edom) else (c0, .zero)
  else
    let absx := F64.abs x
    if F64.lt absx c1em20 then
      let (l, e) := call1 L.log absx .zero
      (F64.neg l, e)
    else lgammaLanczos L x absx

/-- `math.gamma`: `FUNC1AD(gamma, m_tgamma, ...)`, mathmodule.c:1118-1121. -/
def math_gamma (L : GammaLibm) (o : Arg) : Py F64 :=
  math_1a o (m_tgamma L) (some "expected a noninteger or positive integer, got ")

/-- `math.lgamma`: `FUNC1AD(lgamma, m_lgamma, ...)`, mathmodule.c:1122-1125. -/
def math_lgamma (L : GammaLibm) (o : Arg) : Py F64 :=
  math_1a o (m_lgamma L) (some "expected a noninteger or positive integer, got ")

end PyLean.MathInt
