import PyLean.DiffCore
import PyLean.CoreLibs.CalStat.Dist
import PyLean.CoreLibs.CalStat.StatND
import PyLean.CoreLibs.CalStat.DiffCal

/-! Differential-test dispatch for the `statistics` half of the area.

Values travel as strings: `i:12`, `b:1`, `q:n/d`, `f:n/d` (also `f:nan`, `f:inf`, `f:-inf`, `f:0`,
`f:-0`), `d:n/d` (also `d:nan`, `d:snan`, `d:inf`, `d:-inf`), `s:text`, `n:`, `o:type`, or an object
`{"c": name, "mro": [...], "m": [...] or null, "v": <value>}` for a user subclass. A result is
`[class name, value]`. The libm functions come from Lean's `Float`, which calls the same C library
as the interpreter, except `erfc`, which `Float` lacks: the case carries a table of the
`erfc(x)` calls the run makes. -/

namespace PyLean.CoreLibs.CalStat

open Lean PyLean PyLean.Diff

def parseRat (s : String) : Except String Rat :=
  match s.splitOn "/" with
  | [n, d] =>
    match n.toInt?, d.toNat? with
    | some n, some d => .ok (mkRat n d)
    | _, _ => .error s!"bad rational {s}"
  | [n] =>
    match n.toInt? with
    | some n => .ok (n : Rat)
    | _ => .error s!"bad rational {s}"
  | _ => .error s!"bad rational {s}"

def parseFlt (s : String) : Except String Flt :=
  match s with
  | "nan" => .ok .nan
  | "inf" => .ok (.inf false)
  | "-inf" => .ok (.inf true)
  | "0" => .ok (.zero false)
  | "-0" => .ok (.zero true)
  | s => .fin <$> parseRat s

def parseDec (s : String) : Except String Dec :=
  match s with
  | "nan" => .ok .nan
  | "snan" => .ok .snan
  | "inf" => .ok (.inf false)
  | "-inf" => .ok (.inf true)
  | s => .fin <$> parseRat s

def parseVal (s : String) : Except String PyN := do
  let body := String.ofList (s.toList.drop 2)
  match s.toList.take 2 with
  | ['i', ':'] =>
    match body.toInt? with
    | some i => return (Val.int i).toN
    | none => throw s!"bad int {s}"
  | ['b', ':'] => return ⟨clsBool, .int (if body == "1" then 1 else 0)⟩
  | ['q', ':'] => return (Val.frac (← parseRat body)).toN
  | ['f', ':'] => return (Val.flt (← parseFlt body)).toN
  | ['d', ':'] => return (Val.dec (← parseDec body)).toN
  | ['s', ':'] => return (Val.str body).toN
  | ['n', ':'] => return Val.none.toN
  | ['o', ':'] => return (Val.other body).toN
  | ['a', ':'] =>
    match body.splitOn "/" with
    | [n, d] => return (Val.abc (n.toInt?.getD 0) (d.toNat?.getD 1)).toN
    | _ => throw s!"bad abc {s}"
  | _ => throw s!"bad value {s}"

def getVal (j : Json) : Except String PyN := do
  match j with
  | .str s => parseVal s
  | _ =>
    let name ← getStr j "c"
    let mro ← (← (← field j "mro").getArr?).toList.mapM (·.getStr?)
    let members ← match j.getObjVal? "m" with
      | .ok .null | .error _ => pure none
      | .ok v => do pure (some (← (← v.getArr?).toList.mapM (·.getInt?)))
    let v ← getVal' (← field j "v")
    return ⟨⟨name, mro, members⟩, v.v⟩
where
  getVal' (j : Json) : Except String PyN := do parseVal (← j.getStr?)

def getV (j : Json) (k : String) : Except String PyN := do getVal (← field j k)
def getL (j : Json) (k : String) : Except String (List PyN) := do
  (← (← field j k).getArr?).toList.mapM getVal
def getOptV (j : Json) (k : String) : Except String (Option PyN) :=
  match j.getObjVal? k with
  | .ok .null | .error _ => .ok none
  | .ok v => some <$> getVal v
def getOptL (j : Json) (k : String) : Except String (Option (List PyN)) :=
  match j.getObjVal? k with
  | .ok .null | .error _ => .ok none
  | .ok _ => some <$> getL j k

def ratStr (q : Rat) : String := s!"{q.num}/{q.den}"

def fltStr : Flt → String
  | .nan => "nan"
  | .inf n => if n then "-inf" else "inf"
  | .zero n => if n then "-0" else "0"
  | .fin q => ratStr q

def decStr : Dec → String
  | .nan => "nan"
  | .snan => "snan"
  | .inf n => if n then "-inf" else "inf"
  | .fin q => ratStr q

def valStr : Val → String
  | .int i => s!"i:{i}"
  | .frac q => s!"q:{ratStr q}"
  | .flt x => s!"f:{fltStr x}"
  | .dec d => s!"d:{decStr d}"
  | .str s => s!"s:{s}"
  | .none => "n:"
  | .other t => s!"o:{t}"
  | .abc n d => s!"a:{n}/{d}"

def encF (x : Flt) : Json := toJson (fltStr x)
def encV (v : Val) : Json := Json.arr #[toJson v.cls.name, toJson (valStr v)]
def encN (n : PyN) : Json := Json.arr #[toJson n.cls.name, toJson (valStr n.v)]

/-! ### libm through `Float` -/

def Flt.toFloat : Flt → Float
  | .nan => (0.0 : Float) / 0.0
  | .inf n => if n then (-1.0 : Float) / 0.0 else (1.0 : Float) / 0.0
  | .zero n => if n then -(0.0 : Float) else 0.0
  | .fin q =>
    let a := if q < 0 then -q else q
    let (m, e) := Flt.roundMag a.num.natAbs a.den
    let v := Float.scaleB (Float.ofNat m) e
    if q < 0 then -v else v

def Flt.ofFloat (x : Float) : Flt :=
  let b := x.toBits.toNat
  let neg := b >>> 63 == 1
  let e := (b >>> 52) &&& 0x7ff
  let f := b &&& (2 ^ 52 - 1)
  if e == 0x7ff then (if f == 0 then .inf neg else .nan)
  else if e == 0 && f == 0 then .zero neg
  else
    let (m, ex) : Nat × Int := if e == 0 then (f, -1074) else (f + 2 ^ 52, (e : Int) - 1075)
    let v : Rat := (m : Rat) * Flt.pow2 ex
    .fin (if neg then -v else v)

def lift1 (f : Float → Float) (x : Flt) : Flt := Flt.ofFloat (f (Flt.toFloat x))

/-- `pow` with `erfc` given by the table of the case. -/
def diffLibm (tbl : List (Flt × Flt)) : Libm where
  exp := lift1 Float.exp
  log := lift1 Float.log
  sin := lift1 Float.sin
  cos := lift1 Float.cos
  tan := lift1 Float.tan
  asin := lift1 Float.asin
  acos := lift1 Float.acos
  atan := lift1 Float.atan
  cosh := lift1 Float.cosh
  erfc := fun x => match tbl.find? (fun p => p.1 == x) with
    | some p => p.2
    | none => .nan
  pow := fun x y => Flt.ofFloat (Float.pow (Flt.toFloat x) (Flt.toFloat y))

def getLibm (j : Json) : Except String Libm := do
  match j.getObjVal? "erfc" with
  | .error _ | .ok .null => return diffLibm []
  | .ok t =>
    let a ← t.getArr?
    let tbl ← a.toList.mapM (fun p => do
      let q ← p.getArr?
      return (← parseFlt (← (q[0]!).getStr?), ← parseFlt (← (q[1]!).getStr?)))
    return diffLibm tbl

def getCls (j : Json) (k : String) : Except String Cls := do
  let v ← field j k
  let name ← getStr v "c"
  let mro ← (← (← field v "mro").getArr?).toList.mapM (·.getStr?)
  let members ← match v.getObjVal? "m" with
    | .ok .null | .error _ => pure none
    | .ok w => do pure (some (← (← w.getArr?).toList.mapM (·.getInt?)))
  return ⟨name, mro, members⟩

def encCls (c : Cls) : Json := toJson c.name

def getND (j : Json) (k : String) : Except String ND := do
  let a ← (← field j k).getArr?
  return ⟨← parseFlt (← (a[0]!).getStr?), ← parseFlt (← (a[1]!).getStr?)⟩

def encND (X : ND) : Json := Json.arr #[encF X.mu, encF X.sigma]

def encRatio : Ratio → Json
  | .ratio n d => Json.arr #[toJson n, toJson d]
  | .special v => Json.arr #[encV v, Json.null]

def numEq (a b : PyN) : Bool := veq a.v b.v

def getFL (j : Json) (k : String) : Except String (List Flt) := do
  (← (← field j k).getArr?).toList.mapM (fun x => do parseFlt (← x.getStr?))

/-- The exception classes the difftest raises from its iterators. -/
def mkExc (c m : String) : PyExc :=
  match c with
  | "ValueError" => .valueError m
  | "TypeError" => .typeError m
  | _ => .named c m

/-- The class relation of the difftest: the builtin table plus its two subclasses. -/
def diffHier : PyLean.CoreLibs.Warn.Hier :=
  ⟨fun c b => match c with
    | "MyTypeError" => b == "MyTypeError" || PyLean.CoreLibs.Warn.excIsA "TypeError" b
    | "MyValueError" => b == "MyValueError" || PyLean.CoreLibs.Warn.excIsA "ValueError" b
    | _ => PyLean.CoreLibs.Warn.excIsA c b⟩

def getExc (j : Json) (k : String) : Except String PyExc := do
  let a ← (← field j k).getArr?
  return mkExc (← (a[0]!).getStr?) (← (a[1]!).getStr?)

/-- The iterable a case describes: what `len()` gives and how iteration ends. -/
def getIter (items : List PyN) (src : String) (exc : Except String PyExc) : Except String PyIter := do
  let noLen : PyExc := .typeError "~object has no len()"
  let pep479 : PyExc := .named "RuntimeError" "generator raised StopIteration"
  match src with
  | "list" | "tuple" => return PyIter.ofList items
  | "iter" => return ⟨.error noLen, items, none⟩
  | "fail" => return ⟨.error noLen, items, some (← exc)⟩
  | "badlen" => return ⟨.error (← exc), items, none⟩
  | "gen" => return ⟨.error noLen, items, some pep479⟩
  | _ => throw s!"bad src {src}"

def runStat (fn : String) (j : Json) : Option (Except String Json) :=
  match fn with
  | "s._exact_ratio" => some do
    return encPy encRatio (exactRatio (← getV j "x").v)
  | "s._isfinite" => some do return encPy toJson (isFiniteV (← getV j "x").v)
  | "s._coerce" => some do return encPy encCls (coerce (← getCls j "T") (← getCls j "S"))
  | "s._sum" => some do
    return encPy (fun t => Json.arr #[encCls t.1, encV t.2.1, toJson t.2.2]) (sumOf (← getL j "data"))
  | "s._ss" => some do
    return encPy (fun t => Json.arr #[encCls t.1, encV t.2.1, encV t.2.2.1, toJson t.2.2.2])
      (ssOf (← getL j "data") (← getOptV j "c"))
  | "s._convert" => some do return encPy encN (convert (← getV j "x").v (← getCls j "T"))
  | "s._fail_neg" => some do
    return encPy (encL encV) (failNeg ((← getL j "data").map (·.v)) "negative value")
  | "s._rank" => some do
    return encPy (encL encV) (rankOf ((← getL j "data").map (·.v)) (← getBool j "reverse")
      (← getStr j "ties") (← getV j "start").v)
  | "s._integer_sqrt_of_frac_rto" => some do
    return encPy toJson (integerSqrtOfFracRto (← getInt j "n") (← getInt j "m"))
  | "s._float_sqrt_of_frac" => some do
    return encPy encF (floatSqrtOfFrac (← getInt j "n") (← getInt j "m"))
  | "s._decimal_sqrt_of_frac" => some do
    return encPy (fun r => encV (.dec (.fin r))) (decimalSqrtOfFrac (← getInt j "n") (← getInt j "m"))
  | "s._mean_stdev" => some do
    return encPy (fun p => Json.arr #[encF p.1, encF p.2]) (meanStdev (← getL j "data"))
  | "s._sqrtprod" => some do
    return encPy encF (sqrtprod (← parseFlt (← getStr j "x")) (← parseFlt (← getStr j "y")))
  | "s.mean" => some do return encPy encN (mean (← getL j "data"))
  | "s.fmean" => some do return encPy encV (fmean (← getL j "data") (← getOptL j "weights"))
  | "s.quantiles_it" => some do
    let data ← getIter (← getL j "data") (← getStr j "src") (getExc j "exc")
    return encPy (encL encN) (quantilesIt data (← getInt j "n") (← getStr j "method"))
  | "s.fmean_it" => some do
    let data ← getIter (← getL j "data") (← getStr j "src") (getExc j "exc")
    let w ← match ← getOptL j "weights" with
      | none => pure none
      | some wl => some <$> getIter wl (← getStr j "wsrc") (getExc j "wexc")
    return encPy encV (fmeanIt diffHier data w)
  | "s.geometric_mean" => some do
    return encPy encF (geometricMean (← getLibm j) (← getL j "data"))
  | "s.harmonic_mean" => some do
    return encPy encN (harmonicMean (← getL j "data") (← getOptL j "weights"))
  | "s.median" => some do return encPy encN (median (← getL j "data"))
  | "s.median_low" => some do return encPy encN (medianLow (← getL j "data"))
  | "s.median_high" => some do return encPy encN (medianHigh (← getL j "data"))
  | "s.median_grouped" => some do
    return encPy encF (medianGrouped (← getL j "data") (← getV j "interval").v)
  | "s.mode" => some do return encPy encN (mode numEq (← getL j "data"))
  | "s.multimode" => some do return wrapL (multimode numEq (← getL j "data"))
  | "s.variance" => some do return encPy encN (variance (← getL j "data") (← getOptV j "c"))
  | "s.pvariance" => some do return encPy encN (pvariance (← getL j "data") (← getOptV j "c"))
  | "s.stdev" => some do return encPy encV (stdev (← getL j "data") (← getOptV j "c"))
  | "s.pstdev" => some do return encPy encV (pstdev (← getL j "data") (← getOptV j "c"))
  | "s.covariance" => some do return encPy encV (covariance (← getL j "x") (← getL j "y"))
  | "s.correlation" => some do
    return encPy encV (correlation (← getL j "x") (← getL j "y") (← getStr j "method"))
  | "s.linear_regression" => some do
    return encPy (fun p => Json.arr #[encV p.1, encV p.2])
      (linearRegression (← getL j "x") (← getL j "y") (← getBool j "proportional"))
  | "s.quantiles" => some do
    return encPy (encL encN) (quantiles (← getL j "data") (← getInt j "n") (← getStr j "method"))
  | "s.kde" => some do
    return encPy encV (kdeAt (← getLibm j) (← getL j "data") (← getL j "data2") (← getV j "h").v
      (← getStr j "kernel") (← getBool j "cumulative") (← getV j "x").v)
  | "s.kde_random" => some do
    let draws ← (← (← field j "draws").getArr?).toList.mapM (fun d => do
      let a ← d.getArr?
      return ((← (a[0]!).getNat?), ← parseFlt (← (a[1]!).getStr?)))
    return encPy (encL encV) (kdeRandomAt (← getLibm j) (← getL j "data") (← getV j "h").v
      (← getStr j "kernel") draws)
  | "s.kernel" => some do
    let L ← getLibm j
    let name ← getStr j "kernel"
    let t ← parseFlt (← getStr j "t")
    match kernelSpec L name with
    | none => throw "no kernel"
    | some k =>
      let r := match ← getStr j "which" with
        | "pdf" => k.pdf t
        | "cdf" => k.cdf t
        | _ => k.invcdf t
      return encPy encF r
  | "s.nd.init" => some do return encPy encND (ND.mk' (← getV j "mu").v (← getV j "sigma").v)
  | "s.nd.from_samples" => some do return encPy encND (ND.fromSamples (← getL j "data"))
  | "s.nd.samples" => some do
    return encPy (encL encF) (ND.samples (← getLibm j) (← getND j "X") (← getFL j "us"))
  | "s.nd.pdf" => some do return encPy encV (ND.pdf (← getLibm j) (← getND j "X") (← getV j "x").v)
  | "s.nd.cdf" => some do return encPy encV (ND.cdf (← getLibm j) (← getND j "X") (← getV j "x").v)
  | "s.nd.inv_cdf" => some do return encPy encF (ND.invCdf (← getLibm j) (← getND j "X") (← getV j "x").v)
  | "s.nd.quantiles" => some do
    return encPy (encL encF) (ND.quantiles (← getLibm j) (← getND j "X") (← getInt j "n"))
  | "s.nd.overlap" => some do
    return encPy encF (ND.overlap (← getLibm j) (← getND j "X") (← getND j "Y"))
  | "s.nd.zscore" => some do return encPy encV (ND.zscore (← getND j "X") (← getV j "x").v)
  | "s.nd.props" => some do
    let X ← getND j "X"
    return Json.arr #[encF X.meanP, encF X.medianP, encF X.modeP, encF X.stdevP, encF X.variance]
  | "s.nd.add" => some do return encPy encND (ND.add (← getND j "X") (← getND j "Y"))
  | "s.nd.sub" => some do return encPy encND (ND.sub (← getND j "X") (← getND j "Y"))
  | "s.nd.addc" => some do return encPy encND (ND.addConst (← getND j "X") (← getV j "x").v)
  | "s.nd.subc" => some do return encPy encND (ND.subConst (← getND j "X") (← getV j "x").v)
  | "s.nd.mulc" => some do return encPy encND (ND.mulConst (← getND j "X") (← getV j "x").v)
  | "s.nd.divc" => some do return encPy encND (ND.divConst (← getND j "X") (← getV j "x").v)
  | "s.nd.rsubc" => some do return encPy encND (ND.rsubConst (← getND j "X") (← getV j "x").v)
  | "s.nd.pos" => some do return encPy encND (ND.pos (← getND j "X"))
  | "s.nd.neg" => some do return encPy encND (ND.neg (← getND j "X"))
  | "s.nd.eq" => some do return toJson (ND.beq (← getND j "X") (← getND j "Y"))
  | "s.nd.hash" => some do return toJson (ND.hash (← getND j "X"))
  | "s.nd.repr" => some do return toJson (ND.repr (← getND j "X"))
  | "s.nd.state" => some do
    let X ← getND j "X"
    let p := X.getstate
    return Json.arr #[encF p.1, encF p.2, encND (X.setstate p)]
  | _ => none
where
  wrapL (l : List PyN) : Json := encL encN l

end PyLean.CoreLibs.CalStat
