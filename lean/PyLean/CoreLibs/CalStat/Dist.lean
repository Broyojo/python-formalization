import PyLean.CoreLibs.CalStat.Stat

/-!
Mirror of `Lib/statistics.py` (CPython 3.15.2): `geometric_mean`, the kernels, `kde`, `kde_random`,
`NormalDist` and `_normal_dist_inv_cdf`.

Everything libm computes inexactly is the parameter `L : Libm`: `exp`, `log`, the trigonometric
functions, `cosh`, `erfc` and `pow`. The difftest instantiates it with the platform's functions;
a property that needs a fact about one of them states it as a hypothesis (C99 Annex F values).
`sqrt`, `+ - * /` and `fma` are correctly rounded by IEEE 754, so they are not parameters.
-/

namespace PyLean.CoreLibs.CalStat

open PyLean

structure Libm where
  exp : Flt → Flt
  log : Flt → Flt
  sin : Flt → Flt
  cos : Flt → Flt
  tan : Flt → Flt
  asin : Flt → Flt
  acos : Flt → Flt
  atan : Flt → Flt
  cosh : Flt → Flt
  erfc : Flt → Flt
  pow : Flt → Flt → Flt

/-- `math.pi`. -/
def piF : Flt := .fin (mkRat 884279719003555 281474976710656)
/-- `math.tau`. -/
def tauF : Flt := .fin (mkRat 884279719003555 140737488355328)

/-- `math_1`, Modules/mathmodule.c:788-825. The messages that embed the argument are not rendered. -/
def math1 (f : Flt → Flt) (canOverflow : Bool) (msg : String) (x : Flt) : Py Flt :=
  let r := f x
  if r.isNan && !x.isNan then .error (.valueError msg)
  else if r.isInf && x.isFinite then
    if canOverflow then .error (.overflowError "math range error")
    else .error (.valueError msg)
  else .ok r

def mathExp (L : Libm) := math1 L.exp true "math domain error"
def mathCosh (L : Libm) := math1 L.cosh true "math domain error"
def mathCos (L : Libm) := math1 L.cos false "~expected a finite input"
def mathSin (L : Libm) := math1 L.sin false "~expected a finite input"
def mathTan (L : Libm) := math1 L.tan false "~expected a finite input"
def mathAsin (L : Libm) := math1 L.asin false "~expected a number in range from -1 up to 1"
def mathAcos (L : Libm) := math1 L.acos false "~expected a number in range from -1 up to 1"
def mathAtan (L : Libm) := math1 L.atan false "math domain error"

/-- `m_log`, Modules/mathmodule.c:629-649. -/
def mLog (L : Libm) (x : Flt) : Flt :=
  match x with
  | .nan => .nan
  | .inf false => x
  | .inf true => .nan
  | .zero _ => .inf true
  | .fin q => if q > 0 then L.log x else .nan

/-- `math.erfc`: `math_1a` around libm, which sets no error for finite results. -/
def mathErfc (L : Libm) (x : Flt) : Flt := L.erfc x

/-- `math.log(x)` for a float. -/
def mathLogF (L : Libm) (x : Flt) : Py Flt :=
  math1 (mLog L) false "~expected a positive input" x

/-- `loghelper_int` and `loghelper`, Modules/mathmodule.c:1583-1639, `math.log(x)` for any real `x`. -/
def mathLog (L : Libm) (v : Val) : Py Flt :=
  match v with
  | .int i =>
    if i ≤ 0 then .error (.valueError "expected a positive input")
    else match intToFlt i with
      | .ok x => .ok (mLog L x)
      | .error _ =>
        -- `_PyLong_Frexp`: `x * 2**e`, `0.5 <= x < 1`
        let e := Flt.frexpExp (i : Rat)
        let x := Flt.ofRat ((i : Rat) * Flt.pow2 (-e))
        .ok (Flt.add (mLog L x) (Flt.mul (mLog L Flt.two) (Flt.ofInt e)))
  | v => do mathLogF L (← asDouble v)

/-- `x ** y` for floats, Objects/floatobject.c `float_pow`. Negative bases with a fractional
exponent (complex results) do not arise here. -/
def floatPow (L : Libm) (x y : Flt) : Py Flt :=
  if Flt.eq y Flt.pz then .ok Flt.one
  else if x.isNan then .ok x
  else if y.isNan then .ok (if Flt.eq x Flt.one then Flt.one else y)
  else if x.isInf || y.isInf then .ok (L.pow x y)
  else if Flt.eq x Flt.pz then
    if Flt.lt y Flt.pz then .error (.zeroDivisionError "zero to a negative power")
    else .ok (L.pow x y)
  else if Flt.eq (Flt.abs x) Flt.one then .ok (L.pow x y)
  else
    let r := L.pow x y
    if r.isInf then .error (.overflowError "~(34, 'Result too large')") else .ok r

/-! ## `_normal_dist_inv_cdf`, Modules/_statisticsmodule.c:37-126, statistics.py:1798-1873 -/

/-- A horner polynomial with coefficients given highest degree first. -/
def horner (r : Flt) : List Rat → Flt
  | [] => Flt.pz
  | c :: cs => cs.foldl (fun acc k => Flt.add (Flt.mul acc r) (Flt.ofRat k)) (Flt.ofRat c)

def dec10 (m : Int) (e : Nat) : Rat := (m : Rat) / ((10 ^ e : Nat) : Rat)

def invNum1 : List Rat := [
  dec10 25090809287301226727 16,
  dec10 33430575583588128105 15,
  dec10 67265770927008700853 15,
  dec10 45921953931549871457 15,
  dec10 13731693765509461125 15,
  dec10 19715909503065514427 16,
  dec10 13314166789178437745 17,
  dec10 33871328727963666080 19]

def invDen1 : List Rat := [
  dec10 52264952788528545610 16,
  dec10 28729085735721942674 15,
  dec10 39307895800092710610 15,
  dec10 21213794301586595867 15,
  dec10 53941960214247511077 16,
  dec10 68718700749205790830 17,
  dec10 42313330701600911252 18,
  1]

def invNum2 : List Rat := [
  dec10 774545014278341407640 24,
  dec10 227238449892691845833 22,
  dec10 241780725177450611770 21,
  dec10 127045825245236838258 20,
  dec10 364784832476320460504 20,
  dec10 576949722146069140550 20,
  dec10 463033784615654529590 20,
  dec10 142343711074968357734 20]

def invDen2 : List Rat := [
  dec10 105075007164441684324 29,
  dec10 547593808499534494600 24,
  dec10 151986665636164571966 22,
  dec10 148103976427480074590 21,
  dec10 689767334985100004550 21,
  dec10 167638483018380384940 20,
  dec10 205319162663775882187 20,
  1]

def invNum3 : List Rat := [
  dec10 201033439929228813265 27,
  dec10 271155556874348757815 25,
  dec10 124266094738807843860 23,
  dec10 265321895265761230930 22,
  dec10 296560571828504891230 21,
  dec10 178482653991729133580 20,
  dec10 546378491116411436990 20,
  dec10 665790464350110377720 20]

def invDen3 : List Rat := [
  dec10 204426310338993978564 35,
  dec10 142151175831644588870 27,
  dec10 184631831751005468180 25,
  dec10 786869131145613259100 24,
  dec10 148753612908506148525 22,
  dec10 136929880922735805310 21,
  dec10 599832206555887937690 21,
  1]

/-- The C function `_normal_dist_inv_cdf`; statistics.py imports it over the Python one
(statistics.py:1876-1880). Only the errors differ between the twins: the C function has the extra
range checks and the `den == 0.0` checks. -/
def normalDistInvCdf (L : Libm) (p mu sigma : Flt) : Py Flt :=
  let err : PyExc := .valueError "inv_cdf undefined for these parameters"
  if Flt.le p Flt.pz || Flt.le Flt.one p then .error err
  else
    let q := Flt.sub p Flt.half
    if Flt.le (Flt.abs q) (Flt.ofRat (dec10 425 3)) then
      let r := Flt.sub (Flt.ofRat (dec10 180625 6)) (Flt.mul q q)
      let num := Flt.mul (horner r invNum1) q
      let den := horner r invDen1
      if Flt.eq den Flt.pz then .error err
      else .ok (Flt.add mu (Flt.mul (Flt.div num den) sigma))
    else
      let r := if Flt.le q Flt.pz then p else Flt.sub Flt.one p
      if Flt.le r Flt.pz || Flt.le Flt.one r then .error err
      else
        let r := Flt.sqrt (Flt.neg (L.log r))
        let (num, den) :=
          if Flt.le r (Flt.ofRat 5) then
            let r := Flt.sub r (Flt.ofRat (dec10 16 1))
            (horner r invNum2, horner r invDen2)
          else
            let r := Flt.sub r (Flt.ofRat 5)
            (horner r invNum3, horner r invDen3)
        if Flt.eq den Flt.pz then .error err
        else
          let x := Flt.div num den
          let x := if Flt.lt q Flt.pz then Flt.neg x else x
          .ok (Flt.add mu (Flt.mul x sigma))

/-! ## Kernels, statistics.py:821-929 -/

structure Kernel where
  pdf : Flt → Py Flt
  cdf : Flt → Py Flt
  invcdf : Flt → Py Flt
  /-- `None` or the half width of the support. -/
  support : Option Flt

/-- `x / y` of two floats where the source divides by a constant. -/
def fdiv := fltDiv

/-- The value of `sumprod` on float tuples. -/
def sumprodF (a b : List Flt) : Py Flt := do
  toFloat (← sumprod (a.map (fun x => (Val.flt x).toN)) (b.map (fun x => (Val.flt x).toN)))

/-- `_newton_raphson`, statistics.py:876-883. The `while` runs on fuel. -/
def newtonLoop (f fPrime : Flt → Py Flt) (y : Flt) : Nat → Flt → Py Flt
  | 0, _ => .error .modelFuel
  | fuel + 1, x => do
    let diff := Flt.sub (← f x) y
    if Flt.lt (Flt.ofRat (dec10 1 12)) (Flt.abs diff) then
      let step ← fltDiv diff (← fPrime x)
      newtonLoop f fPrime y fuel (Flt.sub x step)
    else return x

def newtonRaphson (est f fPrime : Flt → Py Flt) (y : Flt) : Py Flt := do
  newtonLoop f fPrime y 10000 (← est y)

def fq (n d : Int) : Flt := Flt.ofRat ((n : Rat) / (d : Rat))

/-- `(1.0, p) if p <= 1/2 else (-1.0, 1.0 - p)`. -/
def signSplit (p : Flt) : Flt × Flt :=
  if Flt.le p Flt.half then (Flt.one, p) else (Flt.neg Flt.one, Flt.sub Flt.one p)

/-- `_quartic_invcdf_estimate`, statistics.py:885-893. -/
def quarticEstimate (L : Libm) (p : Flt) : Py Flt := do
  let (sign, p) := signSplit p
  if Flt.lt p (Flt.ofRat (dec10 106 4)) then
    let b ← floatPow L (Flt.mul Flt.two p) (Flt.ofRat (dec10 3838 4))
    return Flt.mul (Flt.sub b Flt.one) sign
  let b ← floatPow L (Flt.mul Flt.two p) (Flt.ofRat (dec10 4258865685331 13))
  let x := Flt.sub b Flt.one
  let x ← if Flt.lt p (Flt.ofRat (dec10 499 3)) then do
      let s ← mathSin L (Flt.add (Flt.mul (Flt.ofRat (dec10 7101753784 9)) p)
        (Flt.ofRat (dec10 273230839482953 14)))
      pure (Flt.add x (Flt.mul (Flt.ofRat (dec10 26818732 9)) s))
    else pure x
  return Flt.mul x sign

/-- `_triweight_invcdf_estimate`, statistics.py:904-910. -/
def triweightEstimate (L : Libm) (p : Flt) : Py Flt := do
  let (sign, p) := signSplit p
  let b ← floatPow L (Flt.mul Flt.two p) (Flt.ofRat (dec10 3400218741872791 16))
  let x := Flt.sub b Flt.one
  let x ← if Flt.lt (Flt.ofRat (dec10 1 5)) p && Flt.lt p (Flt.ofRat (dec10 499 3)) then do
      let s ← mathSin L (Flt.mul (Flt.mul (Flt.ofRat (dec10 107 2)) tauF)
        (Flt.sub p (Flt.ofRat (dec10 35 3))))
      pure (Flt.sub x (Flt.mul (Flt.ofRat (dec10 33 3)) s))
    else pure x
  return Flt.mul x sign

def normalKernel (L : Libm) : Kernel :=
  let sqrt2pi := Flt.sqrt (Flt.mul Flt.two piF)
  let negSqrt2 := Flt.neg (Flt.sqrt Flt.two)
  { pdf := fun t => do
      let e ← mathExp L (Flt.mul (Flt.mul (Flt.neg Flt.half) t) t)
      fltDiv e sqrt2pi
    cdf := fun t => do
      let a ← fltDiv t negSqrt2
      return Flt.mul Flt.half (mathErfc L a)
    invcdf := fun t => normalDistInvCdf L t Flt.pz Flt.one
    support := none }

def logisticKernel (L : Libm) : Kernel :=
  { pdf := fun t => do
      let c ← mathCosh L t
      fltDiv Flt.half (Flt.add Flt.one c)
    cdf := fun t => do
      let e ← mathExp L t
      return Flt.sub Flt.one (← fltDiv Flt.one (Flt.add e Flt.one))
    invcdf := fun p => do
      mathLogF L (← fltDiv p (Flt.sub Flt.one p))
    support := none }

def sigmoidKernel (L : Libm) : Kernel :=
  let c1 := Flt.div Flt.one piF
  let c2 := Flt.div Flt.two piF
  let c3 := Flt.div piF Flt.two
  { pdf := fun t => do fltDiv c1 (← mathCosh L t)
    cdf := fun t => do
      let e ← mathExp L t
      return Flt.mul c2 (← mathAtan L e)
    invcdf := fun p => do
      mathLogF L (← mathTan L (Flt.mul p c3))
    support := none }

def rectangularKernel : Kernel :=
  { pdf := fun _ => .ok Flt.half
    cdf := fun t => .ok (Flt.add (Flt.mul Flt.half t) Flt.half)
    invcdf := fun p => .ok (Flt.sub (Flt.mul Flt.two p) Flt.one)
    support := some Flt.one }

def triangularKernel : Kernel :=
  { pdf := fun t => .ok (Flt.sub Flt.one (Flt.abs t))
    cdf := fun t =>
      let c := if Flt.lt t Flt.pz then Flt.half else Flt.neg Flt.half
      .ok (Flt.add (Flt.add (Flt.mul (Flt.mul t t) c) t) Flt.half)
    invcdf := fun p => do
      if Flt.lt p Flt.half then
        return Flt.sub (← mathSqrt (Flt.mul Flt.two p)) Flt.one
      else
        return Flt.sub Flt.one (← mathSqrt (Flt.sub Flt.two (Flt.mul Flt.two p)))
    support := some Flt.one }

def parabolicKernel (L : Libm) : Kernel :=
  { pdf := fun t => .ok (Flt.mul (fq 3 4) (Flt.sub Flt.one (Flt.mul t t)))
    cdf := fun t => do
      let t3 ← floatPow L t (Flt.ofInt 3)
      sumprodF [fq (-1) 4, fq 3 4, Flt.half] [t3, t, Flt.one]
    invcdf := fun p => do
      let a ← mathAcos L (Flt.sub (Flt.mul Flt.two p) Flt.one)
      let c ← mathCos L (Flt.div (Flt.add a piF) (Flt.ofInt 3))
      return Flt.mul Flt.two c
    support := some Flt.one }

def quarticPdf (L : Libm) (t : Flt) : Py Flt := do
  let b ← floatPow L (Flt.sub Flt.one (Flt.mul t t)) Flt.two
  return Flt.mul (fq 15 16) b

def quarticCdf (L : Libm) (t : Flt) : Py Flt := do
  let t5 ← floatPow L t (Flt.ofInt 5)
  let t3 ← floatPow L t (Flt.ofInt 3)
  sumprodF [fq 3 16, fq (-5) 8, fq 15 16, Flt.half] [t5, t3, t, Flt.one]

def quarticKernel (L : Libm) : Kernel :=
  { pdf := quarticPdf L
    cdf := quarticCdf L
    invcdf := newtonRaphson (quarticEstimate L) (quarticCdf L) (quarticPdf L)
    support := some Flt.one }

def triweightPdf (L : Libm) (t : Flt) : Py Flt := do
  let b ← floatPow L (Flt.sub Flt.one (Flt.mul t t)) (Flt.ofInt 3)
  return Flt.mul (fq 35 32) b

def triweightCdf (L : Libm) (t : Flt) : Py Flt := do
  let t7 ← floatPow L t (Flt.ofInt 7)
  let t5 ← floatPow L t (Flt.ofInt 5)
  let t3 ← floatPow L t (Flt.ofInt 3)
  sumprodF [fq (-5) 32, fq 21 32, fq (-35) 32, fq 35 32, Flt.half] [t7, t5, t3, t, Flt.one]

def triweightKernel (L : Libm) : Kernel :=
  { pdf := triweightPdf L
    cdf := triweightCdf L
    invcdf := newtonRaphson (triweightEstimate L) (triweightCdf L) (triweightPdf L)
    support := some Flt.one }

def cosineKernel (L : Libm) : Kernel :=
  let c1 := Flt.div piF (Flt.ofInt 4)
  let c2 := Flt.div piF Flt.two
  { pdf := fun t => do return Flt.mul c1 (← mathCos L (Flt.mul c2 t))
    cdf := fun t => do
      return Flt.add (Flt.mul Flt.half (← mathSin L (Flt.mul c2 t))) Flt.half
    invcdf := fun p => do
      let a ← mathAsin L (Flt.sub (Flt.mul Flt.two p) Flt.one)
      fltDiv (Flt.mul Flt.two a) piF
    support := some Flt.one }

/-- `_kernel_specs.get(kernel)`, as filled by `register`, statistics.py:812-819. -/
def kernelSpec (L : Libm) (name : String) : Option Kernel :=
  match name with
  | "normal" | "gauss" => some (normalKernel L)
  | "logistic" => some (logisticKernel L)
  | "sigmoid" => some (sigmoidKernel L)
  | "rectangular" | "uniform" => some rectangularKernel
  | "triangular" => some triangularKernel
  | "parabolic" | "epanechnikov" => some (parabolicKernel L)
  | "quartic" | "biweight" => some (quarticKernel L)
  | "triweight" => some (triweightKernel L)
  | "cosine" => some (cosineKernel L)
  | _ => none

/-! ## `kde`, `kde_random`, statistics.py:936-1137 -/

/-- The checks shared by `kde` and `kde_random`, statistics.py:1036-1048. -/
def kdeSpec (L : Libm) (data : List PyN) (h : Val) (kernel : String) : Py Kernel := do
  if data.isEmpty then throw (statErr "Empty data sequence")
  match (pick data 0).v with
  | .int _ | .flt _ => pure ()
  | _ => throw (.typeError "Data sequence must contain ints or floats")
  if ← vlePy h (.flt Flt.pz) then throw (statErr "~Bandwidth h must be positive")
  match kernelSpec L kernel with
  | none => throw (statErr s!"~Unknown kernel name: '{kernel}'")
  | some k => return k

/-- `(x - x_i) / h` as the float the kernels take. -/
def scaledT (x xi h : Val) : Py Flt := do
  toFloat (← vdiv (← vsub x xi) h)

/-- `sum(fs, start)` of floats. -/
def sumF (start : Int) (fs : List Flt) : Val :=
  match fs with
  | [] => .int start
  | _ => .flt (builtinSumFloats (Flt.ofInt start) fs)

/-- The closure state of a bounded kernel: `sample` and `n` from the last refresh. -/
structure KdeState where
  n : Nat
  sample : List PyN

/-- `if len(data) != n: sample = sorted(data); n = len(data)`, statistics.py:1068-1070 and :1078-1080. -/
def kdeRefresh (st : KdeState) (data : List PyN) : Py KdeState :=
  if data.length != st.n then do
    return { n := data.length, sample := ← pySorted data }
  else .ok st

/-- `sample[i : j]` with the bisections, statistics.py:1071-1073. -/
def supported (sample : List PyN) (x bandwidth : Val) : Py (Nat × List PyN) := do
  let i := bisectLeft (fun a b => vlt a.v b.v) sample (← vsub x bandwidth).toN
  let j := bisectRight (fun a b => vlt a.v b.v) sample (← vadd x bandwidth).toN
  return (i, (sample.take j).drop i)

/-- `pdf(x)` of `kde`, statistics.py:1055-1056 and :1066-1074. -/
def kdePdf (k : Kernel) (h : Val) (st : KdeState) (data : List PyN) (x : Val) : Py Val := do
  match k.support with
  | none =>
    let vals ← data.mapM (fun p => do k.pdf (← scaledT x p.v h))
    vdiv (sumF 0 vals) (← vmul (.int data.length) h)
  | some s =>
    let st ← kdeRefresh st data
    let bw ← vmul h (.flt s)
    let (_, sup) ← supported st.sample x bw
    let vals ← sup.mapM (fun p => do k.pdf (← scaledT x p.v h))
    vdiv (sumF 0 vals) (← vmul (.int st.n) h)

/-- `cdf(x)` of `kde`, statistics.py:1058-1059 and :1076-1084. -/
def kdeCdf (k : Kernel) (h : Val) (st : KdeState) (data : List PyN) (x : Val) : Py Val := do
  match k.support with
  | none =>
    let vals ← data.mapM (fun p => do k.cdf (← scaledT x p.v h))
    vdiv (sumF 0 vals) (.int data.length)
  | some s =>
    let st ← kdeRefresh st data
    let bw ← vmul h (.flt s)
    let (i, sup) ← supported st.sample x bw
    let vals ← sup.mapM (fun p => do k.cdf (← scaledT x p.v h))
    vdiv (sumF i vals) (.int st.n)

/-- `kde(data, h, kernel, cumulative=...)` called at `x` on the (possibly changed) list `data'`. -/
def kdeAt (L : Libm) (data data' : List PyN) (h : Val) (kernel : String) (cumulative : Bool)
    (x : Val) : Py Val := do
  let k ← kdeSpec L data h kernel
  let st : KdeState ← match k.support with
    | some _ => do pure { n := data.length, sample := ← pySorted data }
    | none => pure { n := data.length, sample := [] }
  if cumulative then kdeCdf k h st data' x else kdePdf k h st data' x

/-- `rand()` of `kde_random`, statistics.py:1132-1133, given what `prng.choice(data)` and
`prng.random()` returned. -/
def kdeRandomOnce (k : Kernel) (h : Val) (chosen : Val) (u : Flt) : Py Val := do
  vadd chosen (← vmul h (.flt (← k.invcdf u)))

def kdeRandomAt (L : Libm) (data : List PyN) (h : Val) (kernel : String)
    (draws : List (Nat × Flt)) : Py (List Val) := do
  let k ← kdeSpec L data h kernel
  draws.mapM (fun d => kdeRandomOnce k h (pick data d.1).v d.2)

/-! ## `geometric_mean`, statistics.py:225-262 -/

structure GmSt where
  n : Nat := 0
  foundZero : Bool := false
  fs : FsumState := {}

def gmStep (L : Libm) (st : GmSt) (x : Val) : Py GmSt := do
  let st := { st with n := st.n + 1 }
  let pos ← vltPy (.flt Flt.pz) x
  let isnan : Bool ← if pos then pure false else (fun d => d.isNan) <$> asDouble x
  if pos || isnan then
    return { st with fs := ← fsumStep st.fs (← mathLog L x) }
  else if veq x (.flt Flt.pz) then return { st with foundZero := true }
  else throw (statErr "~No negative inputs allowed: x")

def geometricMean (L : Libm) (data : List PyN) : Py Flt := do
  let st ← (data.map (·.v)).foldlM (gmStep L) ({} : GmSt)
  let total ← fsumEnd st.fs
  if st.n = 0 then throw (statErr "Must have a non-empty dataset")
  if total.isNan then return .nan
  if st.foundZero then return if Flt.eq total (.inf false) then .nan else Flt.pz
  mathExp L (← fltDiv total (Flt.ofInt st.n))

/-! ## `NormalDist`, statistics.py:1229-1449 -/

structure ND where
  mu : Flt
  sigma : Flt
  deriving DecidableEq, Inhabited, Repr

/-- `NormalDist.__init__`, statistics.py:1239-1244. -/
def ND.mk' (mu sigma : Val) : Py ND := do
  if ← vltPy sigma (.flt Flt.pz) then throw (statErr "sigma must be non-negative")
  return ⟨← toFloat mu, ← toFloat sigma⟩

/-- `NormalDist.from_samples`, statistics.py:1246-1249. -/
def ND.fromSamples (data : List PyN) : Py ND := do
  let (m, s) ← meanStdev data
  ND.mk' (.flt m) (.flt s)

/-- `NormalDist.samples`, statistics.py:1251-1257; `us` are the values of `rnd()`. -/
def ND.samples (L : Libm) (X : ND) (us : List Flt) : Py (List Flt) :=
  us.mapM (fun u => normalDistInvCdf L u X.mu X.sigma)

/-- `_SQRT2PI`, Lib/statistics.py:148. -/
def sqrt2pi : Flt := Flt.sqrt tauF

/-- `NormalDist.pdf`, Lib/statistics.py:1259-1265: `-0.5 * z * z` associates to the left. -/
def ND.pdf (L : Libm) (X : ND) (x : Val) : Py Val := do
  let sigma := X.sigma
  if !sigma.truthy then throw (statErr "pdf() not defined when sigma is zero")
  let z ← vdiv (← vsub x (.flt X.mu)) (.flt sigma)
  let top ← vmul (← vmul (.flt (Flt.neg Flt.half)) z) z
  let e ← mathExp L (← asDouble top)
  return .flt (← fltDiv e (Flt.mul sqrt2pi sigma))

def sqrt2 : Flt := Flt.sqrt Flt.two

/-- `NormalDist.cdf`, statistics.py:1267-1271. -/
def ND.cdf (L : Libm) (X : ND) (x : Val) : Py Val := do
  if !X.sigma.truthy then throw (statErr "cdf() not defined when sigma is zero")
  let top ← vsub (.flt X.mu) x
  let a ← vdiv top (.flt (Flt.mul X.sigma sqrt2))
  return .flt (Flt.mul Flt.half (mathErfc L (← asDouble a)))

/-- `NormalDist.inv_cdf`, statistics.py:1273-1285. -/
def ND.invCdf (L : Libm) (X : ND) (p : Val) : Py Flt := do
  if (← vlePy p (.flt Flt.pz)) || (← vlePy (.flt Flt.one) p) then
    throw (statErr "p must be in the range 0.0 < p < 1.0")
  normalDistInvCdf L (← toFloat p) X.mu X.sigma

/-- `NormalDist.quantiles`, statistics.py:1287-1296. -/
def ND.quantiles (L : Libm) (X : ND) (n : Int) : Py (List Flt) :=
  (rangeI 1 n).mapM (fun i => do ND.invCdf L X (.flt (← intTrueDiv i n)))

/-- The `mean`, `median`, `mode` and `stdev` properties, statistics.py:1343-1365. -/
def ND.meanP (X : ND) : Flt := X.mu
def ND.medianP (X : ND) : Flt := X.mu
def ND.modeP (X : ND) : Flt := X.mu
def ND.stdevP (X : ND) : Flt := X.sigma

/-- `NormalDist.variance`, statistics.py:1368-1370. -/
def ND.variance (X : ND) : Flt := Flt.mul X.sigma X.sigma

/-- `NormalDist.overlap`, statistics.py:1298-1330 (`other` a `NormalDist`). -/
def ND.overlap (L : Libm) (A B : ND) : Py Flt := do
  let swap := Flt.lt B.sigma A.sigma || (Flt.eq B.sigma A.sigma && Flt.lt B.mu A.mu)
  let (X, Y) := if swap then (B, A) else (A, B)
  let xv := X.variance
  let yv := Y.variance
  if !xv.truthy || !yv.truthy then throw (statErr "overlap() not defined when sigma is zero")
  let dv := Flt.sub yv xv
  let dm := Flt.abs (Flt.sub Y.mu X.mu)
  if !dv.truthy then
    return mathErfc L (Flt.div dm (Flt.mul (Flt.mul Flt.two X.sigma) sqrt2))
  let a := Flt.sub (Flt.mul X.mu yv) (Flt.mul Y.mu xv)
  let lg ← mathLogF L (Flt.div yv xv)
  let b := Flt.mul (Flt.mul X.sigma Y.sigma)
    (← mathSqrt (Flt.add (Flt.mul dm dm) (Flt.mul dv lg)))
  let x1 := Flt.div (Flt.add a b) dv
  let x2 := Flt.div (Flt.sub a b) dv
  let c (Z : ND) (x : Flt) : Py Flt := do toFloat (← ND.cdf L Z (.flt x))
  let t1 := Flt.abs (Flt.sub (← c Y x1) (← c X x1))
  let t2 := Flt.abs (Flt.sub (← c Y x2) (← c X x2))
  return Flt.sub Flt.one (Flt.add t1 t2)

/-- `NormalDist.zscore`, statistics.py:1332-1341. -/
def ND.zscore (X : ND) (x : Val) : Py Val := do
  if !X.sigma.truthy then throw (statErr "zscore() not defined when sigma is zero")
  vdiv (← vsub x (.flt X.mu)) (.flt X.sigma)

/-- `NormalDist.__add__` with a constant, statistics.py:1384; `__radd__` is the same method. -/
def ND.addConst (X : ND) (c : Val) : Py ND := do
  ND.mk' (← vadd (.flt X.mu) c) (.flt X.sigma)

/-- `NormalDist.__add__` with a `NormalDist`, statistics.py:1382-1383. -/
def ND.add (X Y : ND) : Py ND :=
  ND.mk' (.flt (Flt.add X.mu Y.mu)) (.flt (hypot X.sigma Y.sigma))

/-- `NormalDist.__sub__` with a constant, statistics.py:1398. -/
def ND.subConst (X : ND) (c : Val) : Py ND := do
  ND.mk' (← vsub (.flt X.mu) c) (.flt X.sigma)

/-- `NormalDist.__sub__` with a `NormalDist`, statistics.py:1396-1397. -/
def ND.sub (X Y : ND) : Py ND :=
  ND.mk' (.flt (Flt.sub X.mu Y.mu)) (.flt (hypot X.sigma Y.sigma))

/-- `NormalDist.__mul__`, statistics.py:1400-1406; `__rmul__` is the same method. -/
def ND.mulConst (X : ND) (c : Val) : Py ND := do
  let m ← vmul (.flt X.mu) c
  let f ← mathFabs c
  ND.mk' m (.flt (Flt.mul X.sigma f))

/-- `NormalDist.__truediv__`, statistics.py:1408-1414. -/
def ND.divConst (X : ND) (c : Val) : Py ND := do
  let m ← vdiv (.flt X.mu) c
  let f ← mathFabs c
  ND.mk' m (.flt (← fltDiv X.sigma f))

/-- `NormalDist.__pos__`, statistics.py:1416-1418. -/
def ND.pos (X : ND) : Py ND := ND.mk' (.flt X.mu) (.flt X.sigma)

/-- `NormalDist.__neg__`, statistics.py:1420-1422. -/
def ND.neg (X : ND) : Py ND := ND.mk' (.flt (Flt.neg X.mu)) (.flt X.sigma)

/-- `NormalDist.__rsub__`, statistics.py:1426-1428: `-(x1 - x2)` for a constant `x2`. -/
def ND.rsubConst (X : ND) (c : Val) : Py ND := do
  ND.neg (← ND.subConst X c)

/-- `NormalDist.__eq__` between two instances, statistics.py:1432-1436. -/
def ND.beq (X Y : ND) : Bool := Flt.eq X.mu Y.mu && Flt.eq X.sigma Y.sigma

/-- `NormalDist.__hash__`, statistics.py:1438-1440. -/
def ND.hash (X : ND) : Int := hashTuple [hashFlt X.mu, hashFlt X.sigma]

/-- `NormalDist.__repr__`, statistics.py:1442-1443. -/
def ND.repr (X : ND) : String :=
  s!"NormalDist(mu={fltRepr X.mu}, sigma={fltRepr X.sigma})"

/-- `NormalDist.__getstate__`, statistics.py:1445-1446. -/
def ND.getstate (X : ND) : Flt × Flt := (X.mu, X.sigma)

/-- `NormalDist.__setstate__`, statistics.py:1448-1449. -/
def ND.setstate (_X : ND) (s : Flt × Flt) : ND := ⟨s.1, s.2⟩

end PyLean.CoreLibs.CalStat
