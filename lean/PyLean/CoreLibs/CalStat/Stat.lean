import PyLean.CoreLibs.CalStat.Num

/-!
Mirror of `Lib/statistics.py` (CPython 3.14.7): the private utilities and the
functions over `int`, `Fraction`, `float` and `Decimal` data. `NormalDist` and the kernels are
in `Dist.lean`.

Python's `set` of types in `_sum` and `_ss` has no defined order; `reduceCoerce` takes the
types in first-seen order and the `order` parameter lets a property range over all orders.
-/

namespace PyLean.CoreLibs.CalStat

open PyLean

def statErr (m : String) : PyExc := .named "StatisticsError" m

/-- `xs[i]` for an index the source has established to be in range. -/
def pick {α : Type} [Inhabited α] (xs : List α) (i : Nat) : α := xs.getD i default

/-! ## `_exact_ratio`, statistics.py:1597-1620 -/

inductive Ratio where
  | ratio (n : Int) (d : Nat)
  /-- `(x, None)`: a float or Decimal NaN or infinity. -/
  | special (v : Val)
  deriving DecidableEq

def exactRatio (x : Val) : Py Ratio :=
  match x with
  | .int i => .ok (.ratio i 1)
  | .frac q => .ok (.ratio q.num q.den)
  | .flt (.zero _) => .ok (.ratio 0 1)
  | .flt (.fin q) => .ok (.ratio q.num q.den)
  | .flt _ => .ok (.special x)
  | .dec (.fin q) => .ok (.ratio q.num q.den)
  | .dec _ => .ok (.special x)
  | .abc n d => .ok (.ratio n d)
  | v => .error (.typeError s!"can't convert type '{v.cls.name}' to numerator/denominator")

/-! ## `_coerce`, statistics.py:1565-1594 -/

def coerce (T S : Cls) : Py Cls :=
  if T.same clsBool then .error (.assertionError "initial type T is bool")
  else if T.same S then .ok T
  else if S.same clsInt || S.same clsBool then .ok T
  else if T.same clsInt then .ok S
  else if isSubclass S T then .ok S
  else if isSubclass T S then .ok T
  else if isSubclass T clsInt then .ok S
  else if isSubclass S clsInt then .ok T
  else if isSubclass T clsFraction && isSubclass S clsFloat then .ok S
  else if isSubclass T clsFloat && isSubclass S clsFraction then .ok T
  else .error (.typeError s!"~don't know how to coerce {T.name} and {S.name}")

/-- `reduce(_coerce, types, int)`, with `types` in the order given. -/
def reduceCoerce (types : List Cls) : Py Cls := types.foldlM coerce clsInt

/-- `types.add(typ)`. -/
def addType (types : List Cls) (c : Cls) : List Cls :=
  if types.any (fun t => t.same c) then types else types ++ [c]

/-! ## `_sum`, statistics.py:1453-1508 -/

structure SumSt where
  count : Nat := 0
  types : List Cls := []
  /-- `partials`, denominators in first-seen order. -/
  partials : List (Nat × Int) := []
  /-- `partials[None]`. -/
  special : Option Val := none

/-- `partials[d] = partials.get(d, 0) + n`. -/
def addPartial (ps : List (Nat × Int)) (d : Nat) (n : Int) : List (Nat × Int) :=
  match ps with
  | [] => [(d, n)]
  | (e, v) :: rest => if e = d then (e, v + n) :: rest else (e, v) :: addPartial rest d n

/-- `sum(Fraction(n, d) for d, n in partials.items())`. -/
def sumPartials (ps : List (Nat × Int)) : Rat :=
  ps.foldr (fun p acc => mkRat p.2 p.1 + acc) 0

/-- One item of the loop. -/
def sumStep (st : SumSt) (x : PyN) : Py SumSt := do
  let st := { st with types := addType st.types x.cls }
  match ← exactRatio x.v with
  | .ratio n d =>
    return { st with count := st.count + 1, partials := addPartial st.partials d n }
  | .special v =>
    let s ← vadd (st.special.getD (.int 0)) v
    return { st with count := st.count + 1, special := some s }

/-- The end of `_sum`; the `reduce` comes last, statistics.py:1498-1508. `order` is the iteration
order of the set of types. -/
def sumFinish (order : List Cls → List Cls) (st : SumSt) : Py (Cls × Val × Nat) := do
  let total : Val := match st.special with
    | some s => s
    | none => if st.partials.isEmpty then .int 0 else .frac (sumPartials st.partials)
  let T ← reduceCoerce (order st.types)
  return (T, total, st.count)

def sumOf (data : List PyN) (order : List Cls → List Cls := id) : Py (Cls × Val × Nat) := do
  sumFinish order (← data.foldlM sumStep {})

/-! ## `_ss`, statistics.py:1511-1555 -/

structure SsSt where
  count : Nat := 0
  types : List Cls := []
  sx : List (Nat × Int) := []
  sxx : List (Nat × Int) := []
  specialX : Option Val := none

def ssStep (st : SsSt) (x : PyN) : Py SsSt := do
  let st := { st with types := addType st.types x.cls }
  match ← exactRatio x.v with
  | .ratio n d =>
    return { st with count := st.count + 1, sx := addPartial st.sx d n,
                     sxx := addPartial st.sxx d (n * n) }
  | .special v =>
    let s ← vadd (st.specialX.getD (.int 0)) v
    -- `sxx_partials[None] += n * n`: its value is never used, its operations can raise
    let _ ← vmul v v
    return { st with count := st.count + 1, specialX := some s }

/-- `sum(Fraction(n, d*d) for d, n in sxx_partials.items())`. -/
def sumPartialsSq (ps : List (Nat × Int)) : Rat :=
  ps.foldr (fun p acc => mkRat p.2 (p.1 * p.1) + acc) 0

/-- `_ss(data, c)`: `(T, ssd, c, count)`. -/
def ssOf (data : List PyN) (c : Option PyN) (order : List Cls → List Cls := id) :
    Py (Cls × Val × Val × Nat) := do
  match c with
  | some c =>
    let st ← data.foldlM (fun st x => do
      let d ← vsub x.v c.v
      let e ← vmul d d
      sumStep st e.toN) ({} : SumSt)
    let (T, ssd, count) ← sumFinish order st
    return (T, ssd, c.v, count)
  | none =>
    let st ← data.foldlM ssStep ({} : SsSt)
    let (ssd, c) : Val × Val :=
      if st.count = 0 then (.frac 0, .frac 0)
      else match st.specialX with
        | some s => (s, s)
        | none =>
          let sx := sumPartials st.sx
          let sxx := sumPartialsSq st.sxx
          let n : Rat := (st.count : Rat)
          (.frac ((n * sxx - sx * sx) / n), .frac (sx / n))
    let T ← reduceCoerce (order st.types)
    return (T, ssd, c, st.count)

/-! ## `_convert`, statistics.py:1623-1640 -/

/-- `T(value)` for a value that is a `Fraction`, or a NaN or infinity. -/
def construct (T : Cls) (value : Val) : Py PyN :=
  if isSubclass T clsInt then
    match value with
    | .frac q =>
      match T.members with
      | some ms =>
        if ms.contains q.num then .ok ⟨T, .int q.num⟩
        else .error (.valueError s!"~Fraction({q.num}, 1) is not a valid {T.name}")
      | none => .ok ⟨T, .int q.num⟩
    | v => (fun x => (⟨T, .flt x⟩ : PyN)) <$> toFloat v
  else if isSubclass T clsFloat then do return ⟨T, .flt (← toFloat value)⟩
  else if isSubclass T clsFraction then
    match value with
    | .frac q => .ok ⟨T, .frac q⟩
    | v => .error (.valueError s!"~cannot convert to Fraction: {v.tyName}")
  else if isSubclass T clsDecimal then
    match value with
    | .frac q => do
      -- `T(value)` is a TypeError; the handler divides `T(numerator)` by `T(denominator)`
      let r ← Dec.div (.fin (q.num : Rat)) (.fin (q.den : Rat))
      return (Val.dec r).toN
    | .dec d => .ok ⟨T, .dec d⟩
    | v => .error (.typeError s!"~conversion from {v.tyName} to Decimal is not supported")
  else .error (.typeError s!"~{T.name}() cannot convert")

def convert (value : Val) (T : Cls) : Py PyN :=
  if value.cls.same T then .ok ⟨T, value⟩
  else
    let T' := match value with
      | .frac q => if isSubclass T clsInt && q.den != 1 then clsFloat else T
      | _ => T
    construct T' value

/-! ## `_fail_neg`, statistics.py:1643-1648 -/

/-- `_fail_neg(values, errmsg)` consumed to the end. -/
def failNeg (values : List Val) (errmsg : String) : Py (List Val) :=
  values.mapM (fun x => do
    if ← vltPy x (.int 0) then .error (statErr errmsg) else .ok x)

/-! ## Averages -/

/-- `mean`, statistics.py:158-178. -/
def mean (data : List PyN) (order : List Cls → List Cls := id) : Py PyN := do
  let (T, total, n) ← sumOf data order
  if n < 1 then throw (statErr "mean requires at least one data point")
  convert (← vdiv total (.int n)) T

/-- `fmean`, statistics.py:181-221. Iterators and sequences take the same path through `fsum`,
except that for an iterator `n` is counted while it is consumed. -/
def fmean (data : List PyN) (weights : Option (List PyN)) : Py Val := do
  match weights with
  | none =>
    let total ← fsumV (data.map (·.v))
    let n := data.length
    if n = 0 then throw (statErr "fmean requires at least one data point")
    vdiv (.flt total) (.int n)
  | some w =>
    let num ← match sumprod data w with
      | .error (.valueError _) => .error (statErr "data and weights must be the same length")
      | r => r
    let den ← fsumV (w.map (·.v))
    if !den.truthy then throw (statErr "sum of weights must be non-zero")
    vdiv num (.flt den)

/-- The part of `median_low` after sorting, statistics.py:367-373, for any element type. -/
def medianLowSorted {α : Type} [Inhabited α] (data : List α) : Py α :=
  let n := data.length
  if n = 0 then .error (statErr "no median for empty data")
  else if n % 2 = 1 then .ok (pick data (n / 2))
  else .ok (pick data (n / 2 - 1))

/-- The part of `median_high` after sorting, statistics.py:389-392. -/
def medianHighSorted {α : Type} [Inhabited α] (data : List α) : Py α :=
  let n := data.length
  if n = 0 then .error (statErr "no median for empty data")
  else .ok (pick data (n / 2))

/-- The part of `median` after sorting, statistics.py:341-348, with `avg` for `(a + b) / 2`. -/
def medianSorted {α : Type} [Inhabited α] (avg : α → α → Py α) (data : List α) : Py α :=
  let n := data.length
  if n = 0 then .error (statErr "no median for empty data")
  else if n % 2 = 1 then .ok (pick data (n / 2))
  else
    let i := n / 2
    avg (pick data (i - 1)) (pick data i)

/-- `(a + b) / 2` on Python numbers. -/
def avgN (a b : PyN) : Py PyN := do
  return (← vdiv (← vadd a.v b.v) (.int 2)).toN

/-- `median`, statistics.py:327-348. -/
def median (data : List PyN) : Py PyN := do medianSorted avgN (← pySorted data)

/-- `median_low`, statistics.py:351-373. -/
def medianLow (data : List PyN) : Py PyN := do medianLowSorted (← pySorted data)

/-- `median_high`, statistics.py:376-392. -/
def medianHigh (data : List PyN) : Py PyN := do medianHighSorted (← pySorted data)

/-- The bisection of `median_grouped`, statistics.py:445-450. -/
def groupedBounds {α : Type} [Inhabited α] (lt : α → α → Bool) (data : List α) : Nat × Nat :=
  let x := pick data (data.length / 2)
  let i := bisectLeft lt data x
  (i, bisectRight lt data x i)

/-- `median_grouped`, statistics.py:395-464. -/
def medianGrouped (data : List PyN) (interval : Val) : Py Flt := do
  let data ← pySorted data
  let n := data.length
  if n = 0 then throw (statErr "no median for empty data")
  let x := pick data (n / 2)
  let (i, j) := groupedBounds (fun a b => vlt a.v b.v) data
  let conv (v : Val) : Py Flt := match toFloat v with
    | .error (.valueError _) => .error (.typeError "Value cannot be converted to a float")
    | r => r
  let interval ← conv interval
  let x ← conv x.v
  let L := Flt.sub x (Flt.div interval Flt.two)
  let cf := i
  let f := j - i
  let n2 ← intTrueDiv n 2
  let t ← fltDiv (Flt.mul interval (Flt.sub n2 (Flt.ofInt cf))) (Flt.ofInt f)
  return Flt.add L t

/-! ## `Counter`, `mode`, `multimode` -/

/-- `Counter`: insertion-ordered, the first of equal keys is kept, as in a dict. -/
def counterAdd {α : Type} (eq : α → α → Bool) (c : List (α × Nat)) (x : α) : List (α × Nat) :=
  match c with
  | [] => [(x, 1)]
  | (k, n) :: rest => if eq k x then (k, n + 1) :: rest else (k, n) :: counterAdd eq rest x

def counterOf {α : Type} (eq : α → α → Bool) (data : List α) : List (α × Nat) :=
  data.foldl (counterAdd eq) []

/-- `max(items, key=count)`: the first item with the largest count. -/
def firstMax {α : Type} : List (α × Nat) → Option (α × Nat)
  | [] => none
  | a :: rest =>
    some (rest.foldl (fun best x => if x.2 > best.2 then x else best) a)

/-- `mode`, statistics.py:467-494: `Counter(data).most_common(1)`, which is `heapq.nlargest(1, ...)`,
which is `max`. -/
def mode {α : Type} (eq : α → α → Bool) (data : List α) : Py α :=
  match firstMax (counterOf eq data) with
  | some p => .ok p.1
  | none => .error (statErr "no mode for empty data")

/-- `multimode`, statistics.py:497-515. -/
def multimode {α : Type} (eq : α → α → Bool) (data : List α) : List α :=
  let counts := counterOf eq data
  match counts with
  | [] => []
  | _ =>
    let maxcount := (counts.map (·.2)).foldl max 0
    (counts.filter (fun p => p.2 == maxcount)).map (·.1)

/-! ## Square roots of fractions -/

def bitLen (n : Int) : Int := (bitLength n.natAbs : Int)

/-- `math.isqrt` on the values reached here. -/
def isqrtInt (n : Int) : Py Int := (fun (r : Nat) => (r : Int)) <$> MathInt.isqrt n

/-- `_integer_sqrt_of_frac_rto`, statistics.py:1705-1709. -/
def integerSqrtOfFracRto (n m : Int) : Py Int := do
  let a ← isqrtInt (n / m)
  return if a * a * m ≠ n then ((a.toNat ||| 1 : Nat) : Int) else a

/-- `_sqrt_bit_width`, statistics.py:1714. -/
def sqrtBitWidth : Int := 2 * 53 + 3

/-- `_float_sqrt_of_frac`, statistics.py:1717-1727. -/
def floatSqrtOfFrac (n m : Int) : Py Flt := do
  let q := (bitLen n - bitLen m - sqrtBitWidth) / 2
  if q ≥ 0 then
    let r ← integerSqrtOfFracRto n (m * 2 ^ (2 * q).toNat)
    intTrueDiv (r * 2 ^ q.toNat) 1
  else
    let r ← integerSqrtOfFracRto (n * 2 ^ (-2 * q).toNat) m
    intTrueDiv r (2 ^ (-q).toNat)

/-- `_decimal_sqrt_of_frac`, statistics.py:1730-1755. -/
def decimalSqrtOfFrac (n m : Int) : Py Rat :=
  if n = 0 then .ok 0
  else
    let (n, m) := if n ≤ 0 then (-n, -m) else (n, m)
    match Dec.div (.fin (n : Rat)) (.fin (m : Rat)) with
    | .ok (.fin quot) =>
      if quot < 0 then .error invalidOp
      else
        let root := decSqrtFin quot
        let nr := root.num
        let dr : Int := root.den
        let plus := decNextPlus root
        let np := plus.num
        let dp : Int := plus.den
        if 4 * n * (dr * dp) ^ 2 > m * (dr * np + dp * nr) ^ 2 then .ok plus
        else
          let minus := decNextMinus root
          let nm := minus.num
          let dm : Int := minus.den
          if 4 * n * (dr * dm) ^ 2 < m * (dr * nm + dm * nr) ^ 2 then .ok minus
          else .ok root
    | .ok _ => .error invalidOp
    | .error e => .error e

/-! ## Spread -/

/-- `variance`, statistics.py:520-563. -/
def variance (data : List PyN) (xbar : Option PyN) : Py PyN := do
  let (T, ss, _, n) ← ssOf data xbar
  if n < 2 then throw (statErr "variance requires at least two data points")
  convert (← vdiv ss (.int ((n : Int) - 1))) T

/-- `pvariance`, statistics.py:566-606. -/
def pvariance (data : List PyN) (mu : Option PyN) : Py PyN := do
  let (T, ss, _, n) ← ssOf data mu
  if n < 1 then throw (statErr "pvariance requires at least one data point")
  convert (← vdiv ss (.int n)) T

/-- The common tail of `stdev` and `pstdev`, statistics.py:622-629 and :645-652. -/
def sqrtTail (T : Cls) (mss : Val) : Py Val :=
  match mss with
  | .frac q =>
    if isSubclass T clsDecimal then (fun r => Val.dec (.fin r)) <$> decimalSqrtOfFrac q.num q.den
    else .flt <$> floatSqrtOfFrac q.num q.den
  | _ => .error (.valueError "inf or nan encountered in data")

/-- `stdev`, statistics.py:609-629. -/
def stdev (data : List PyN) (xbar : Option PyN) : Py Val := do
  let (T, ss, _, n) ← ssOf data xbar
  if n < 2 then throw (statErr "stdev requires at least two data points")
  sqrtTail T (← vdiv ss (.int ((n : Int) - 1)))

/-- `pstdev`, statistics.py:632-652. -/
def pstdev (data : List PyN) (mu : Option PyN) : Py Val := do
  let (T, ss, _, n) ← ssOf data mu
  if n < 1 then throw (statErr "pstdev requires at least one data point")
  sqrtTail T (← vdiv ss (.int n))

/-- `_mean_stdev`, statistics.py:1758-1768. -/
def meanStdev (data : List PyN) : Py (Flt × Flt) := do
  let (_, ss, xbar, n) ← ssOf data none
  if n < 2 then throw (statErr "stdev requires at least two data points")
  let mss ← vdiv ss (.int ((n : Int) - 1))
  match mss with
  | .frac q =>
    let m ← toFloat xbar
    return (m, ← floatSqrtOfFrac q.num q.den)
  | _ =>
    let m ← toFloat xbar
    let s ← toFloat ss
    return (m, ← fltDiv m s)

/-! ## Two inputs -/

/-- `[xi - c for xi in x]`. -/
def centered (x : List PyN) (c : Flt) : Py (List PyN) :=
  x.mapM (fun xi => do return (← vsub xi.v (.flt c)).toN)

/-- `fsum(x) / n`. -/
def fbar (x : List PyN) : Py Flt := do
  fltDiv (← fsumV (x.map (·.v))) (Flt.ofInt x.length)

/-- `covariance`, statistics.py:657-683. -/
def covariance (x y : List PyN) : Py Val := do
  let n := x.length
  if y.length != n then
    throw (statErr "covariance requires that both inputs have same number of data points")
  if n < 2 then throw (statErr "covariance requires at least two data points")
  let xbar ← fbar x
  let ybar ← fbar y
  let sxy ← sumprod (← centered x xbar) (← centered y ybar)
  vdiv sxy (.int ((n : Int) - 1))

/-- `math.sqrt(x)`. -/
def mathSqrt (x : Flt) : Py Flt :=
  let r := Flt.sqrt x
  if r.isNan && !x.isNan then
    .error (.valueError s!"~expected a nonnegative input, got {fltRepr x}")
  else .ok r

/-- `_sqrtprod`, statistics.py:1771-1794. The two rescaling branches recurse at most once more. -/
def sqrtprodGo : Nat → Flt → Flt → Py Flt
  | 0, _, _ => .error .modelFuel
  | f + 1, x, y => do
    let h ← mathSqrt (Flt.mul x y)
    if !h.isFinite then
      if h.isInf && !x.isInf && !y.isInf then
        let scale := Flt.ofRat (Flt.pow2 (-512))
        let r ← sqrtprodGo f (Flt.mul scale x) (Flt.mul scale y)
        return Flt.div r scale
      return h
    if !h.truthy then
      if x.truthy && y.truthy then
        let scale := Flt.ofRat (Flt.pow2 537)
        let r ← sqrtprodGo f (Flt.mul scale x) (Flt.mul scale y)
        return Flt.div r scale
      return h
    let d ← sumprod [(Val.flt x).toN, (Val.flt h).toN] [(Val.flt y).toN, (Val.flt (Flt.neg h)).toN]
    let d ← toFloat d
    return Flt.add h (Flt.div d (Flt.mul Flt.two h))

def sqrtprod (x y : Flt) : Py Flt := sqrtprodGo 4 x y

/-- The lexicographic `<` of `(value, position)` pairs: `tuple` compares with `==` first. -/
def pairLt (a b : Val × Nat) : Bool :=
  if veq a.1 b.1 then decide (a.2 < b.2) else vlt a.1 b.1

/-- `itertools.groupby` on the first component, with `==`. -/
def groupRuns : List (Val × Nat) → List (List (Val × Nat))
  | [] => []
  | a :: rest =>
    match groupRuns rest with
    | [] => [[a]]
    | g :: gs =>
      match g.head? with
      | some h => if veq a.1 h.1 then (a :: g) :: gs else [a] :: g :: gs
      | none => [a] :: gs

/-- The rank assignment loop, statistics.py:1693-1701. -/
def rankLoop : Val → List (List (Val × Nat)) → List (Nat × Val) → Py (List (Nat × Val))
  | _, [], acc => .ok acc
  | i, g :: gs, acc => do
    let size := g.length
    let half ← intTrueDiv ((size : Int) + 1) 2
    let rank ← vadd i (.flt half)
    let acc := acc ++ g.map (fun p => (p.2, rank))
    let i ← vadd i (.int size)
    rankLoop i gs acc

/-- `_rank(data, ties=ties, reverse=reverse, start=start)`, statistics.py:1651-1702. -/
def rankOf (data : List Val) (reverse : Bool) (ties : String) (start : Val) : Py (List Val) := do
  if ties != "average" then throw (.valueError s!"~Unknown tie resolution method: '{ties}'")
  let _ ← pySorted (data.map Val.toN)
  let valPos := ListSort.listSort pairLt data.zipIdx reverse
  let i ← vsub start (.int 1)
  let assoc ← rankLoop i (groupRuns valPos) []
  return (List.range data.length).map (fun k =>
    match assoc.find? (fun p => p.1 == k) with
    | some p => p.2
    | none => .int 0)

/-- `correlation`, statistics.py:686-738. -/
def correlation (x y : List PyN) (method : String) : Py Val := do
  let n := x.length
  if y.length != n then
    throw (statErr "correlation requires that both inputs have same number of data points")
  if n < 2 then throw (statErr "correlation requires at least two data points")
  if method != "linear" && method != "ranked" then
    throw (.valueError s!"~Unknown method: '{method}'")
  let (x', y') ← if method = "ranked" then do
      let start ← intTrueDiv ((n : Int) - 1) (-2)
      let rx ← rankOf (x.map (·.v)) false "average" (.flt start)
      let ry ← rankOf (y.map (·.v)) false "average" (.flt start)
      pure (rx.map Val.toN, ry.map Val.toN)
    else do
      let xbar ← fbar x
      let ybar ← fbar y
      pure (← centered x xbar, ← centered y ybar)
  let sxy ← sumprod x' y'
  let sxx ← sumprod x' x'
  let syy ← sumprod y' y'
  let d ← sqrtprod (← toFloat sxx) (← toFloat syy)
  match vdiv sxy (.flt d) with
  | .error (.zeroDivisionError _) => .error (statErr "at least one of the inputs is constant")
  | r => r

/-- `linear_regression`, statistics.py:744-804. -/
def linearRegression (x y : List PyN) (proportional : Bool) : Py (Val × Val) := do
  let n := x.length
  if y.length != n then
    throw (statErr "linear regression requires that both inputs have same number of data points")
  if n < 2 then throw (statErr "linear regression requires at least two data points")
  let (x', y', xbar, ybar) ← if !proportional then do
      let xbar ← fbar x
      let ybar ← fbar y
      pure (← centered x xbar, ← centered y ybar, xbar, ybar)
    else pure (x, y, Flt.pz, Flt.pz)
  let sxy ← vadd (← sumprod x' y') (.flt Flt.pz)
  let sxx ← sumprod x' x'
  let slope ← match vdiv sxy sxx with
    | .error (.zeroDivisionError _) => .error (statErr "x is constant")
    | r => r
  let intercept ← if proportional then pure (Val.flt Flt.pz)
    else do vsub (.flt ybar) (← vmul slope (.flt xbar))
  return (slope, intercept)

/-! ## Harmonic and geometric mean -/

/-- The `try` body of `harmonic_mean`, statistics.py:315-317: the items of
`_sum(w / x if w else 0 for w, x in zip(weights, _fail_neg(data)))`. -/
def hmSum (ws data : List Val) (errmsg : String) : Py (Cls × Val × Nat) := do
  let st ← (ws.zip data).foldlM (fun st p => do
    let (w, x) := p
    if ← vltPy x (.int 0) then throw (statErr errmsg)
    let term ← if w.truthy then vdiv w x else pure (.int 0)
    sumStep st term.toN) ({} : SumSt)
  sumFinish id st

/-- `harmonic_mean`, statistics.py:264-324. -/
def harmonicMean (data : List PyN) (weights : Option (List PyN)) : Py PyN := do
  let errmsg := "harmonic mean does not support negative values"
  let n := data.length
  if n < 1 then throw (statErr "harmonic_mean requires at least one data point")
  match data, weights with
  | [x], none =>
    match x.v with
    | .int _ | .flt _ | .frac _ | .dec _ =>
      if ← vltPy x.v (.int 0) then throw (statErr errmsg)
      return x
    | _ => throw (.typeError "unsupported type")
  | _, _ =>
    let (ws, sumWeights) ← match weights with
      | none => pure ((List.replicate n (Val.int 1)), Val.int n)
      | some w => do
        if w.length != n then throw (statErr "Number of weights does not match data size")
        let st ← w.foldlM (fun st x => do
          if ← vltPy x.v (.int 0) then throw (statErr errmsg)
          sumStep st x) ({} : SumSt)
        let (_, sw, _) ← sumFinish id st
        pure (w.map (·.v), sw)
    match hmSum ws (data.map (·.v)) errmsg with
    | .error e => if excIsZeroDiv e then return (Val.int 0).toN else .error e
    | .ok (T, total, _) =>
      if ← vlePy total (.int 0) then throw (statErr "Weighted sum must be positive")
      convert (← vdiv sumWeights total) T

/-! ## `quantiles`, statistics.py:1175-1223 -/

/-- The inclusive interpolation, statistics.py:1206-1209. -/
def quantInclusive (data : List Val) (n : Int) (m i : Int) : Py Val := do
  let j := (i * m) / n
  let delta := (i * m) % n
  let a ← vmul (pick data j.toNat) (.int (n - delta))
  let b ← vmul (pick data (j.toNat + 1)) (.int delta)
  vdiv (← vadd a b) (.int n)

/-- The exclusive interpolation, statistics.py:1215-1220. -/
def quantExclusive (data : List Val) (n : Int) (ld m i : Int) : Py Val := do
  let j0 := (i * m) / n
  let j := if j0 < 1 then 1 else if j0 > ld - 1 then ld - 1 else j0
  let delta := i * m - j * n
  let a ← vmul (pick data (j.toNat - 1)) (.int (n - delta))
  let b ← vmul (pick data j.toNat) (.int delta)
  vdiv (← vadd a b) (.int n)

def quantiles (data : List PyN) (n : Int) (method : String) : Py (List PyN) := do
  if n < 1 then throw (statErr "n must be at least 1")
  let data ← pySorted data
  let vals := data.map (·.v)
  let ld : Int := data.length
  if ld < 2 then
    if ld = 1 then return List.replicate (n - 1).toNat (pick data 0)
    throw (statErr "must have at least one data point")
  if method = "inclusive" then
    return ← (rangeI 1 n).mapM (fun i => Val.toN <$> quantInclusive vals n (ld - 1) i)
  if method = "exclusive" then
    return ← (rangeI 1 n).mapM (fun i => Val.toN <$> quantExclusive vals n ld (ld + 1) i)
  throw (.valueError s!"~Unknown method: '{method}'")

end PyLean.CoreLibs.CalStat
