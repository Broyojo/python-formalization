import PyLean.CoreLibs.CalStat.Flt
import PyLean.ListSort.Model

/-!
The numeric tower `statistics.py` works over, as data.

* `Val`: the payload of a Python value: an int (also `bool` and int subclasses), a `Fraction`
  (`Rat`, which is canonical like `Fraction`), a `float` (`Flt`), a `Decimal` (`Dec`), or something
  non-numeric.
* `Cls`: a class, modelled by the names of its MRO; `is` compares names and `issubclass` looks in
  the MRO. A user-defined numeric subclass is just another `Cls`. An `IntEnum`-like class
  has `members`: its constructor only accepts those values.
* `PyN`: a value with its class.

`Decimal` is modelled at the level of values with the default context (28 digits,
`ROUND_HALF_EVEN`): the result of an operation is the exact result rounded once, which is what
libmpdec guarantees for `+ - * /` and `sqrt`. Exponent bookkeeping (`Decimal('1.0')` vs
`Decimal('1.00')`), the sign of zero, and `Emax` are not modelled; the difftest compares Decimals by
value and stays far from `Emax`.
-/

namespace PyLean.CoreLibs.CalStat

open PyLean

/-! ## Decimal -/

inductive Dec where
  | nan
  | snan
  | inf (neg : Bool)
  | fin (q : Rat)
  deriving DecidableEq, Inhabited, Repr

/-- Round `|q|`, non-zero, to 28 significant digits, half-even. -/
def decRoundAbs (a : Rat) : Rat :=
  let ex := decExp a - 27
  let scaled := a / pow10 ex
  let m := natFloor scaled
  let frac := scaled - (m : Rat)
  let half := mkRat 1 2
  let m' := if frac > half ∨ (frac = half ∧ m % 2 = 1) then m + 1 else m
  (m' : Rat) * pow10 ex

def decRound (q : Rat) : Rat :=
  if q = 0 then 0
  else if q < 0 then -(decRoundAbs (-q)) else decRoundAbs q

def invalidOp : PyExc := .named "InvalidOperation" "~[<class 'decimal.InvalidOperation'>]"

def Dec.isFinite : Dec → Bool
  | .fin _ => true
  | _ => false

def Dec.add : Dec → Dec → Py Dec
  | .snan, _ | _, .snan => .error invalidOp
  | .nan, _ | _, .nan => .ok .nan
  | .inf a, .inf b => if a = b then .ok (.inf a) else .error invalidOp
  | .inf a, _ | _, .inf a => .ok (.inf a)
  | .fin a, .fin b => .ok (.fin (decRound (a + b)))

def Dec.neg : Dec → Dec
  | .inf a => .inf (!a)
  | .fin q => .fin (-q)
  | d => d

def Dec.sub (x y : Dec) : Py Dec :=
  match y with
  | .snan => .error invalidOp
  | _ => Dec.add x (Dec.neg y)

def Dec.mul : Dec → Dec → Py Dec
  | .snan, _ | _, .snan => .error invalidOp
  | .nan, _ | _, .nan => .ok .nan
  | .inf a, .inf b => .ok (.inf (a != b))
  | .inf a, .fin q | .fin q, .inf a =>
    if q = 0 then .error invalidOp else .ok (.inf (a != decide (q < 0)))
  | .fin a, .fin b => .ok (.fin (decRound (a * b)))

def Dec.div : Dec → Dec → Py Dec
  | .snan, _ | _, .snan => .error invalidOp
  | .nan, _ | _, .nan => .ok .nan
  | .inf _, .inf _ => .error invalidOp
  | .inf a, .fin q => .ok (.inf (a != decide (q < 0)))
  | .fin _, .inf _ => .ok (.fin 0)
  | .fin a, .fin b =>
    if b = 0 then
      if a = 0 then .error (.named "InvalidOperation" "~[<class 'decimal.DivisionUndefined'>]")
      else .error (.named "DivisionByZero" "~[<class 'decimal.DivisionByZero'>]")
    else .ok (.fin (decRound (a / b)))

/-- The exponent of the last of the 28 digits of `|q|`. -/
def decUlpExp (a : Rat) : Int := decExp a - 27

/-- `Decimal.sqrt` of a non-negative finite value: the exact root rounded half-even to 28 digits.
The integer root of `q * 100**p`, with a sticky digit, carries more than 30 digits. -/
def decSqrtFin (q : Rat) : Rat :=
  if q = 0 then 0
  else
    let e := decExp q
    let p : Int := 34 - e / 2
    let scaled : Rat := q * pow10 (2 * p)
    let fl := natFloor scaled
    let r := match MathInt.isqrt fl with
      | .ok r => r
      | .error _ => 0
    let exact := decide ((r * r : Nat) = fl) && decide (scaled.den = 1)
    let v : Rat := ((if exact then r else r * 10 + 1 : Nat) : Rat) *
      pow10 (if exact then -p else -p - 1)
    decRound v

/-- `Decimal.next_plus()` of a finite value with at most 28 digits. -/
def decNextPlus (q : Rat) : Rat :=
  if q = 0 then pow10 (-1000026)
  else if q > 0 then q + pow10 (decUlpExp q)
  else
    let a := -q
    let u := decUlpExp a
    -- moving towards zero from a power of ten uses the finer spacing below it
    if a = pow10 (u + 27) then -(a - pow10 (u - 1)) else -(a - pow10 u)

/-- `Decimal.next_minus()`, the mirror image of `next_plus`. -/
def decNextMinus (q : Rat) : Rat := -(decNextPlus (-q))

/-! ## Classes -/

structure Cls where
  name : String
  /-- Names of the class and its bases, `object` left out. -/
  mro : List String
  /-- `Some members` for an enum: the constructor takes these values only. -/
  members : Option (List Int) := none
  deriving DecidableEq, Inhabited, Repr

def clsInt : Cls := ⟨"int", ["int"], none⟩
def clsBool : Cls := ⟨"bool", ["bool", "int"], none⟩
def clsFloat : Cls := ⟨"float", ["float"], none⟩
def clsFraction : Cls := ⟨"Fraction", ["Fraction"], none⟩
def clsDecimal : Cls := ⟨"Decimal", ["Decimal"], none⟩

/-- `T is S`. -/
def Cls.same (T S : Cls) : Bool := T.name == S.name

/-- `issubclass(S, T)`. -/
def isSubclass (S T : Cls) : Bool := S.mro.contains T.name

/-! ## Values -/

inductive Val where
  | int (i : Int)
  | flt (x : Flt)
  | frac (q : Rat)
  | dec (d : Dec)
  | str (s : String)
  | none
  /-- An object of a class that is none of the above, known by its type name. -/
  | other (ty : String)
  /-- An object with `numerator`/`denominator` attributes only (`_exact_ratio`'s second branch). -/
  | abc (n : Int) (d : Nat)
  deriving DecidableEq, Inhabited, Repr

/-- The built-in class of a result of arithmetic. -/
def Val.cls : Val → Cls
  | .int _ => clsInt
  | .flt _ => clsFloat
  | .frac _ => clsFraction
  | .dec _ => clsDecimal
  | .str _ => ⟨"str", ["str"], .none⟩
  | .none => ⟨"NoneType", ["NoneType"], .none⟩
  | .other t => ⟨t, [t], .none⟩
  | .abc _ _ => ⟨"abc", ["abc"], .none⟩

/-- `type(x).__name__` as an operator error message spells it. -/
def Val.tyName (v : Val) : String :=
  match v with
  | .dec _ => "decimal.Decimal"
  | _ => v.cls.name

structure PyN where
  cls : Cls
  v : Val
  deriving DecidableEq, Inhabited, Repr

def Val.toN (v : Val) : PyN := ⟨v.cls, v⟩

def unsupported (sym : String) (a b : Val) : PyExc :=
  .typeError s!"~unsupported operand type(s) for {sym}: '{a.tyName}' and '{b.tyName}'"

structure ArithOp where
  sym : String
  onInt : Int → Int → Py Val
  onRat : Rat → Rat → Py Val
  onFlt : Flt → Flt → Py Flt
  onDec : Dec → Dec → Py Dec

/-- Binary arithmetic on Python numbers: `int` with `int`; `Fraction` with `int` or `Fraction`;
`Fraction._operator_fallbacks` turns `Fraction` with `float` into `float`; `int` with `float` goes
through `float(int)`; `Decimal` accepts `int` and `Decimal` and refuses the others. -/
def arith (op : ArithOp) (a b : Val) : Py Val :=
  match a, b with
  | .int x, .int y => op.onInt x y
  | .int x, .frac y => op.onRat (x : Rat) y
  | .frac x, .int y => op.onRat x (y : Rat)
  | .frac x, .frac y => op.onRat x y
  | .flt x, .flt y => .flt <$> op.onFlt x y
  | .int x, .flt y => do return .flt (← op.onFlt (← intToFlt x) y)
  | .flt x, .int y => do return .flt (← op.onFlt x (← intToFlt y))
  | .frac x, .flt y => do return .flt (← op.onFlt (← ratToFlt x) y)
  | .flt x, .frac y => do return .flt (← op.onFlt x (← ratToFlt y))
  | .dec x, .dec y => .dec <$> op.onDec x y
  | .dec x, .int y => .dec <$> op.onDec x (.fin (y : Rat))
  | .int x, .dec y => .dec <$> op.onDec (.fin (x : Rat)) y
  | a, b => .error (unsupported op.sym a b)

def addOp : ArithOp :=
  ⟨"+", fun x y => .ok (.int (x + y)), fun x y => .ok (.frac (x + y)),
   fun x y => .ok (Flt.add x y), Dec.add⟩

def subOp : ArithOp :=
  ⟨"-", fun x y => .ok (.int (x - y)), fun x y => .ok (.frac (x - y)),
   fun x y => .ok (Flt.sub x y), Dec.sub⟩

def mulOp : ArithOp :=
  ⟨"*", fun x y => .ok (.int (x * y)), fun x y => .ok (.frac (x * y)),
   fun x y => .ok (Flt.mul x y), Dec.mul⟩

/-- `Fraction.__truediv__` by zero raises `ZeroDivisionError('Fraction(n, 0)')`. -/
def divOp : ArithOp :=
  ⟨"/", fun x y => .flt <$> intTrueDiv x y,
   fun x y => if y = 0 then .error (.zeroDivisionError "~Fraction(n, 0)") else .ok (.frac (x / y)),
   fltDiv, Dec.div⟩

def vadd := arith addOp
def vsub := arith subOp
def vmul := arith mulOp
def vdiv := arith divOp

/-- `ZeroDivisionError` and its subclass `decimal.DivisionByZero`, what `except
ZeroDivisionError` catches. -/
def excIsZeroDiv : PyExc → Bool
  | .zeroDivisionError _ => true
  | .named "DivisionByZero" _ => true
  | _ => false

/-! ### Comparison -/

inductive Ext where
  | nan
  | inf (neg : Bool)
  | fin (q : Rat)
  deriving DecidableEq

def Val.ext : Val → Option Ext
  | .int i => some (.fin (i : Rat))
  | .frac q => some (.fin q)
  | .flt .nan => some .nan
  | .flt (.inf n) => some (.inf n)
  | .flt (.zero _) => some (.fin 0)
  | .flt (.fin q) => some (.fin q)
  | .dec .nan | .dec .snan => some .nan
  | .dec (.inf n) => some (.inf n)
  | .dec (.fin q) => some (.fin q)
  | _ => Option.none

def Ext.lt : Ext → Ext → Bool
  | .nan, _ | _, .nan => false
  | .inf a, .inf b => a && !b
  | .inf a, .fin _ => a
  | .fin _, .inf b => !b
  | .fin a, .fin b => decide (a < b)

/-- `a < b` for numbers and for strings. Incomparable pairs are `False` here; `checkSortable`
and `vltPy` raise the `TypeError` where the source would. -/
def vlt (a b : Val) : Bool :=
  match a, b with
  | .str s, .str t => decide (s < t)
  | _, _ =>
    match a.ext, b.ext with
    | some x, some y => x.lt y
    | _, _ => false

/-- `a == b`. A NaN is unequal to everything. -/
def veq (a b : Val) : Bool :=
  match a, b with
  | .str s, .str t => decide (s = t)
  | .none, .none => true
  | _, _ =>
    match a.ext, b.ext with
    | some .nan, _ | _, some .nan => false
    | some x, some y => decide (x = y)
    | _, _ => false

def vle (a b : Val) : Bool := vlt a b || veq a b

/-- True for values on which `<` raises against a number. -/
def Val.ordered (v : Val) : Bool :=
  match v with
  | .int _ | .flt _ | .frac _ => true
  | .dec .nan | .dec .snan => false
  | .dec _ => true
  | _ => false

/-- `a < b` with the exceptions: `TypeError` between unordered types,
`InvalidOperation` from a Decimal NaN. -/
def vltPy (a b : Val) : Py Bool :=
  match a, b with
  | .str _, .str _ => .ok (vlt a b)
  | .dec .nan, _ | .dec .snan, _ | _, .dec .nan | _, .dec .snan => .error invalidOp
  | a, b =>
    if a.ordered && b.ordered then .ok (vlt a b)
    else .error (.typeError s!"~'<' not supported between instances of '{a.tyName}' and '{b.tyName}'")

def vlePy (a b : Val) : Py Bool := do
  let r ← vltPy a b
  return r || veq a b

def Val.truthy : Val → Bool
  | .int i => i != 0
  | .flt x => x.truthy
  | .frac q => q != 0
  | .dec (.fin q) => q != 0
  | .dec _ => true
  | .str s => !s.isEmpty
  | .none => false
  | _ => true

/-! ### Conversions to float -/

/-- `float(Decimal)`: through the shortest string, correctly rounded, with no `OverflowError`. -/
def decToFlt : Dec → Flt
  | .nan | .snan => .nan
  | .inf n => .inf n
  | .fin q => Flt.ofRat q

/-- `float(x)`, Objects/floatobject.c `float_new`. -/
def toFloat (v : Val) : Py Flt :=
  match v with
  | .int i => intToFlt i
  | .flt x => .ok x
  | .frac q => ratToFlt q
  | .dec d => .ok (decToFlt d)
  | .str s => .error (.valueError s!"~could not convert string to float: '{s}'")
  | a => .error (.typeError s!"~float() argument must be a string or a real number, not '{a.tyName}'")

/-- `PyFloat_AsDouble`, the conversion of `math` functions. -/
def asDouble (v : Val) : Py Flt :=
  match v with
  | .str _ | .none | .other _ | .abc _ _ =>
    .error (.typeError s!"~must be real number, not {v.tyName}")
  | v => toFloat v

/-- `math.fabs(x)`. -/
def mathFabs (v : Val) : Py Flt := do
  return Flt.abs (← asDouble v)

/-- `math.fsum(xs)`, item conversion included. -/
def fsumV (xs : List Val) : Py Flt := do
  let st ← xs.foldlM (fun st v => do fsumStep st (← asDouble v)) ({} : FsumState)
  fsumEnd st

/-! ## `math.sumprod`, Modules/mathmodule.c:2775-2970 -/

structure SP where
  total : Val := .int 0
  intEnabled : Bool := true
  intInUse : Bool := false
  intTotal : Int := 0
  fltEnabled : Bool := true
  fltInUse : Bool := false
  fltTotal : TL := {}

def fitsLong (x : Int) : Bool := decide (-(2 ^ 63) ≤ x ∧ x ≤ 2 ^ 63 - 1)

def spFinalizeInt (st : SP) : Py SP := do
  let st' := { st with intEnabled := false }
  if st.intInUse then
    let t ← vadd st.total (.int st.intTotal)
    return { st' with total := t, intTotal := 0, intInUse := false }
  else return st'

def spFinalizeFlt (st : SP) : Py SP := do
  let st' := { st with fltEnabled := false }
  if st.fltInUse then
    let t ← vadd st.total (.flt (tlToD st.fltTotal))
    return { st' with total := t, fltTotal := {}, fltInUse := false }
  else return st'

/-- The pair of doubles for the float path, or `none` for `goto finalize_flt_path`. -/
def spFloats (p q : PyN) : Option (Flt × Flt) :=
  let isF (x : PyN) := x.cls.same clsFloat
  let isI (x : PyN) := x.cls.same clsInt || x.cls.same clsBool
  let asDbl (x : PyN) : Option Flt := match x.v with
    | .int i => (match intToFlt i with
      | .ok d => some d
      | .error _ => none)
    | _ => none
  match p.v, q.v with
  | .flt a, .flt b => if isF p && isF q then some (a, b)
    else if isF p && isI q then (asDbl q).map (fun d => (a, d))
    else if isF q && isI p then (asDbl p).map (fun d => (d, b))
    else none
  | .flt a, _ => if isF p && isI q then (asDbl q).map (fun d => (a, d)) else none
  | _, .flt b => if isF q && isI p then (asDbl p).map (fun d => (d, b)) else none
  | _, _ => none

/-- One element of the main loop. `.inl st` is `continue`. -/
def spStep (st : SP) (p q : PyN) : Py SP := do
  -- the int path
  let viaInt : Option Int :=
    if st.intEnabled && p.cls.same clsInt && q.cls.same clsInt then
      match p.v, q.v with
      | .int a, .int b =>
        if fitsLong a && fitsLong b && fitsLong (a * b) && fitsLong (st.intTotal + a * b) then
          some (a * b)
        else .none
      | _, _ => .none
    else .none
  match viaInt with
  | some prod => return { st with intTotal := st.intTotal + prod, intInUse := true }
  | none =>
    let st ← if st.intEnabled then spFinalizeInt st else pure st
    let viaFlt : Option TL :=
      if st.fltEnabled then
        match spFloats p q with
        | some (a, b) =>
          let nt := tlFma a b st.fltTotal
          if nt.hi.isFinite then some nt else .none
        | none => .none
      else .none
    match viaFlt with
    | some nt => return { st with fltTotal := nt, fltInUse := true }
    | none =>
      let st ← if st.fltEnabled then spFinalizeFlt st else pure st
      let term ← vmul p.v q.v
      return { st with total := ← vadd st.total term }

def sumprodLoop : SP → List PyN → List PyN → Py Val
  | st, [], [] => do
    let st ← if st.intEnabled then spFinalizeInt st else pure st
    let st ← if st.fltEnabled then spFinalizeFlt st else pure st
    return st.total
  | st, p :: ps, q :: qs => do sumprodLoop (← spStep st p q) ps qs
  | _, _, _ => .error (.valueError "Inputs are not the same length")

def sumprod (p q : List PyN) : Py Val := sumprodLoop {} p q

/-! ## `sorted` and `bisect` -/

def isDecNan (x : PyN) : Bool :=
  match x.v with
  | .dec .nan | .dec .snan => true
  | _ => false

def isStrV (x : PyN) : Bool :=
  match x.v with
  | .str _ => true
  | _ => false

/-- `sorted(xs)`: the `ListSort` mirror of `list.sort` with `vlt`. Any list of two or more items
makes every item meet `<` at least once, so a Decimal NaN or a value without an order
against the others raises; which pair raises first is not modelled, hence the `~`. -/
def pySorted (xs : List PyN) : Py (List PyN) :=
  if xs.length ≥ 2 then
    match xs.find? isDecNan with
    | some _ => .error invalidOp
    | none =>
      if xs.all isStrV || xs.all (fun x => x.v.ordered) then
        .ok (ListSort.listSort (fun a b => vlt a.v b.v) xs)
      else .error (.typeError "~'<' not supported between instances")
  else .ok xs

/-- `bisect_left(a, x, lo, hi)`, Modules/_bisectmodule.c `internal_bisect_left`:
`if a[mid] < x: lo = mid + 1 else: hi = mid`, with an abstract `<`. -/
def bisectLeftGo {α : Type} (lt : α → α → Bool) (a : List α) (x : α) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      match a[mid]? with
      | some v => if lt v x then bisectLeftGo lt a x f (mid + 1) hi
                  else bisectLeftGo lt a x f lo mid
      | none => lo
    else lo

def bisectLeft {α : Type} (lt : α → α → Bool) (a : List α) (x : α) (lo : Nat := 0) : Nat :=
  bisectLeftGo lt a x (a.length + 1) lo a.length

/-- `bisect_right`: `if x < a[mid]: hi = mid else: lo = mid + 1`. -/
def bisectRightGo {α : Type} (lt : α → α → Bool) (a : List α) (x : α) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      match a[mid]? with
      | some v => if lt x v then bisectRightGo lt a x f lo mid
                  else bisectRightGo lt a x f (mid + 1) hi
      | none => lo
    else lo

def bisectRight {α : Type} (lt : α → α → Bool) (a : List α) (x : α) (lo : Nat := 0) : Nat :=
  bisectRightGo lt a x (a.length + 1) lo a.length

end PyLean.CoreLibs.CalStat
