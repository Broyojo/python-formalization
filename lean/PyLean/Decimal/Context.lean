import PyLean.Decimal.Division
import PyLean.Decimal.Parse

/-!
`_pydecimal`'s `Context` class and the module-level context functions.

`Ctx` (`Arith.lean`) is what an operation reads; `PyContext` here is the object
itself, with `flags` and `traps` as the dicts they are (`SigDict`, insertion order
kept, because `__repr__` and `__reduce__` read them in that order).

`Arg` is an operand as Python sees it: a Decimal, an int, or anything else.
Identity is not modelled: `_shallow_copy` shares its dicts with the original where
`copy` does not, which a value model cannot tell apart.
-/

namespace PyLean.Decimal

open PyLean

/-! ## Formatting an object into a message -/

/-- What `str()` or `repr()` of an object raises: `none` when it returns its text (which the model
does not render; messages built from it start with `~`). An int of more than 4300 digits raises the
int/str-limit `ValueError` (Objects/longobject.c:2207-2216); a `__str__` or `__repr__` written in
Python can raise anything. -/
abbrev StrErr := Option PyExc

/-- `str(n)` or `repr(n)` of an int. -/
def intStrErr (n : Int) : StrErr :=
  if maxStrDigits < numDigits n.natAbs then some (.valueError limitToStrMsg) else none

/-- `raise E(fmt % x)` for a format `fmt` with one `%s` and an `x` that is not a tuple: `%s` takes
`str(x)` (Objects/unicode_format.c:720), whose exception, if any, is what is raised; otherwise `ok`,
the exception built from the formatted message. -/
def pctExc (strErr : StrErr) (ok : PyExc) : PyExc := strErr.getD ok

/-- `raise E(fmt % t)` for a format with one `%s` and a tuple `t`, `elems` being what `str()` of
each element raises: `%` takes the tuple as its argument tuple (Objects/unicode_format.c): no
element is "not enough arguments" (:96-113), the first element is formatted with `str()` (:720),
and a second one left over is "not all arguments converted" (:1093-1099). -/
def pctTupleExc (elems : List StrErr) (ok : PyExc) : PyExc :=
  match elems with
  | [] => .typeError "not enough arguments for format string (got 0)"
  | e :: rest =>
    match e with
    | some x => x
    | none =>
      match rest with
      | [] => ok
      | _ => .typeError s!"not all arguments converted during string formatting (required 1, got {rest.length + 1})"

/-! ## Operands -/

/-- An operand of a `Context` method or a binary operator. -/
inductive Arg where
  | dec (d : Dec)
  | int (n : Int)
  /-- A tuple, which `"..." % other` takes as its argument tuple; `elems` is what `str()` of each
  element raises (a huge int, a `__str__` that raises). -/
  | tuple (elems : List StrErr)
  /-- Any other object; `str` is what `str()` of it raises (`str([10**5000])` and
  `str(Fraction(10**5000))` raise the int/str-limit `ValueError`). -/
  | other (str : StrErr := none)
  deriving Repr, Inhabited

/-- `"Unable to convert %s to Decimal" % other`, formatted text the model does not render. -/
def unableMsg : String := "~Unable to convert to Decimal"

/-- `raise TypeError("Unable to convert %s to Decimal" % x)` (_pydecimal.py:6112, and the
`Context` wrappers' `% b`, :4248, :4474, :4497, :4518, :5054, :5300, :5404, :5595) for an operand
`x` that is not a Decimal or an int: the exception raised, from the formatting or the `TypeError`. -/
def unableExc : Arg → PyExc
  | .tuple t => pctTupleExc t (.typeError unableMsg)
  | .other s => pctExc s (.typeError unableMsg)
  | _ => .typeError unableMsg

/-- `_convert_other(other, raiseit)`, _pydecimal.py:6096-6113, without `allow_float`,
which nothing in the module passes. `none` is `NotImplemented`. -/
def convertOther (raiseit : Bool) : Arg → Py (Option Dec)
  | .dec d => .ok (some d)
  | .int n => do return some (← pyFromInt n)
  | .tuple t => if raiseit then .error (unableExc (.tuple t)) else .ok none
  | .other s => if raiseit then .error (unableExc (.other s)) else .ok none

/-- `_convert_other(other, raiseit=True)`, which never returns `NotImplemented`. -/
def convertRaise (x : Arg) : Py Dec := do
  match ← convertOther true x with
  | some d => return d
  | none => throw (.typeError unableMsg)

/-- The operator prologue `other = _convert_other(other); if other is NotImplemented:
return other`. -/
def opArg {α : Type} (f : Ctx → Dec → Dec → DM α) (c : Ctx) (a : Dec) (b : Arg) : DM (Option α) := do
  match ← liftPy (convertOther false b) with
  | some o => return some (← f c a o)
  | none => return none

/-- A reflected operator: `__rsub__`, `__rtruediv__`, `__rdivmod__`, `__rmod__`,
`__rfloordiv__`, _pydecimal.py:1304-1310, :1466-1471, :1509-1514, :1543-1548,
:1655-1660: `other.__op__(self, context=context)` after the same prologue. -/
def ropArg {α : Type} (f : Ctx → Dec → Dec → DM α) (c : Ctx) (a : Dec) (b : Arg) : DM (Option α) := do
  match ← liftPy (convertOther false b) with
  | some o => return some (← f c o a)
  | none => return none

def rsub := ropArg sub
def rtruediv := ropArg truediv
def rdivmod := ropArg divmodD
def rmod := ropArg modD
def rfloordiv := ropArg floordivD

/-! ## `Context` methods: three shapes -/

/-- `a = _convert_other(a, raiseit=True); r = a.__op__(b, context=self); if r is
NotImplemented: raise TypeError(...); else: return r`: `Context.add`, `subtract`,
`multiply`, `divide`, `divide_int`, `divmod`, `remainder` (the message formats `b`, :4248). -/
def ctxOp {α : Type} (f : Ctx → Dec → Dec → DM α) (c : Ctx) (a b : Arg) : DM α := do
  let x ← liftPy (convertRaise a)
  match ← opArg f c x b with
  | some r => return r
  | none => throw (unableExc b)

/-- `a = _convert_other(a, raiseit=True); return a.m(b, context=self)`, where
`a.m` starts with `other = _convert_other(other, raiseit=True)`. -/
def ctxBin {α : Type} (f : Ctx → Dec → Dec → DM α) (c : Ctx) (a b : Arg) : DM α := do
  let x ← liftPy (convertRaise a)
  let y ← liftPy (convertRaise b)
  f c x y

/-- `a = _convert_other(a, raiseit=True); return a.m(context=self)`. -/
def ctxUn {α : Type} (f : Ctx → Dec → DM α) (c : Ctx) (a : Arg) : DM α := do
  let x ← liftPy (convertRaise a)
  f c x

/-- `Context.fma`, _pydecimal.py:4546-4567; `Decimal.fma` converts `other` and
`third` first, :1975-1996. -/
def contextFma (c : Ctx) (a b t : Arg) : DM Dec := do
  let x ← liftPy (convertRaise a)
  let y ← liftPy (convertRaise b)
  let z ← liftPy (convertRaise t)
  fma c x y z

def contextAdd := ctxOp add
def contextSubtract := ctxOp sub
def contextMultiply := ctxOp mul
def contextDivide := ctxOp truediv
def contextDivideInt := ctxOp floordivD
def contextDivmod := ctxOp divmodD
def contextRemainder := ctxOp modD

def contextCompare := ctxBin compareD
def contextCompareSignal := ctxBin compareSignal
def contextMax := ctxBin maxD
def contextMaxMag := ctxBin maxMag
def contextMin := ctxBin minD
def contextMinMag := ctxBin minMag
def contextLogicalAnd := ctxBin logicalAnd
def contextLogicalOr := ctxBin logicalOr
def contextLogicalXor := ctxBin logicalXor
def contextNextToward := ctxBin nextToward
def contextQuantize := ctxBin (fun c a b => quantize c a b)
def contextRemainderNear := ctxBin remainderNear
def contextRotate := ctxBin rotate
def contextScaleb := ctxBin scaleb
def contextShift := ctxBin shift
def contextCompareTotal := ctxBin (fun _ a b => (pure (decOfInt (compareTotal a b)) : DM Dec))
def contextCompareTotalMag := ctxBin (fun _ a b => (pure (decOfInt (compareTotalMag a b)) : DM Dec))
def contextCopySign := ctxBin (fun _ a b => (pure (copySign a b) : DM Dec))
def contextSameQuantum := ctxBin (fun _ a b => (pure (sameQuantum a b) : DM Bool))

def contextAbs := ctxUn (fun c a => dunderAbs c a)
def contextLogb := ctxUn logb
def contextLogicalInvert := ctxUn logicalInvert
def contextMinus := ctxUn dunderNeg
def contextPlus := ctxUn dunderPos
def contextNextMinus := ctxUn nextMinus
def contextNextPlus := ctxUn nextPlus
def contextNormalize := ctxUn normalize
def contextToIntegralExact := ctxUn (fun c a => toIntegralExact c a)
def contextToIntegralValue := ctxUn (fun c a => toIntegralValue c a)
def contextNumberClass := ctxUn (fun c a => (pure (numberClass c a) : DM String))
def contextIsNormal := ctxUn (fun c a => (pure (isNormal c a) : DM Bool))
def contextIsSubnormal := ctxUn (fun c a => (pure (isSubnormal c a) : DM Bool))
def contextToEngString := ctxUn (fun c a => liftPy (pyEng a c.capitals))
def contextToSciString := ctxUn (fun c a => liftPy (pyStr a c.capitals))
def contextCopyAbs := ctxUn (fun _ a => (pure (copyAbs a) : DM Dec))
def contextCopyNegate := ctxUn (fun _ a => (pure (copyNegate a) : DM Dec))
def contextCopyDecimal := ctxUn (fun _ a => (pure a : DM Dec))
def contextIsFinite := ctxUn (fun _ a => (pure (isFinite a) : DM Bool))
def contextIsInfinite := ctxUn (fun _ a => (pure (isInfinite a) : DM Bool))
def contextIsNan := ctxUn (fun _ a => (pure (isNanP a) : DM Bool))
def contextIsQnan := ctxUn (fun _ a => (pure (isQnan a) : DM Bool))
def contextIsSigned := ctxUn (fun _ a => (pure (isSigned a) : DM Bool))
def contextIsSnan := ctxUn (fun _ a => (pure (isSnan a) : DM Bool))
def contextIsZero := ctxUn (fun _ a => (pure (isZero a) : DM Bool))

/-- `Context.radix`, _pydecimal.py:5362-5368. -/
def contextRadix : Dec := radixD

/-- `Context.canonical`, _pydecimal.py:4255-4266: unlike the other methods this one
takes only a Decimal. -/
def contextCanonical : Arg → Py Dec
  | .dec d => .ok (canonicalD d)
  | _ => .error (.typeError "canonical requires a Decimal as an argument.")

/-- `Context.is_canonical`, _pydecimal.py:4569-4580. -/
def contextIsCanonical : Arg → Py Bool
  | .dec d => .ok (isCanonical d)
  | _ => .error (.typeError "is_canonical requires a Decimal as an argument.")

/-- `Context._apply`, _pydecimal.py:4252-4253. -/
def contextApply (c : Ctx) (a : Dec) : DM (List Char) := do
  let r ← fix c a
  liftPy (pyStr r c.capitals)

/-! ## The `Context` object -/

/-- `_signals`, _pydecimal.py:332-333. -/
def pySignals : List Signal :=
  [.clamped, .divisionByZero, .inexact, .overflow, .rounded,
   .underflow, .invalidOperation, .subnormal, .floatOperation]

/-- What `mode == value` gives, in `value in _rounding_modes`, for an object `value` of a class
that is not `str` (or a subclass of it): `str.__eq__` returns `NotImplemented`, so the reflected
`value.__eq__(mode)` runs (Objects/object.c:1122-1147, `PyObject_RichCompareBool`). `yes` is a
true result (after `__bool__`), `no` a false one, `NotImplemented` included (the identity
fallback), and `raises e` an exception from `__eq__` or from the result's `__bool__`. -/
inductive EqAns where
  | yes
  | no
  | raises (e : PyExc)
  deriving Repr, DecidableEq, Inhabited

/-- An element of a list, or a key of a dict, passed as `flags` or `traps`. -/
inductive SigKey where
  | sig (s : Signal)
  /-- Any other object. `repr` is what `repr()` of it raises (`none`: it returns; an int of more
  than 4300 digits raises the limit `ValueError`, `intKey`), `hash` what `hash()` of it raises
  (`none`: hashable; a list raises `TypeError`), and `eq` what its `__eq__` answers against the
  nine signals, in `_signals` order (a missing answer is `no`; `NotImplemented` is `no`, since a
  signal's own `type.__eq__` then gives `NotImplemented` too and the identity fallback is false,
  Objects/object.c:1049-1094). `x in _signals`, `s in traps` and `key in d` (_pydecimal.py:3994,
  :4023, :4026) run that `__eq__`, so it can accept a key or raise.
  For an element of a list passed as `flags` or `traps` there is more: `hv` is the value `hash()`
  returns, and `prev` what `x == self` answers, as `PyObject_RichCompareBool(x, self, Py_EQ)`
  (Objects/object.c:1122-1147: identity first, then `x.__eq__(self)`, the reflected
  `self.__eq__(x)` and the identity fallback), for the element `x` at each earlier position of the
  list that is not a signal (a missing answer is `no`; the entries at a signal's position are not
  read). `k in traps` (:3994) compares each earlier element with `k` (`list_contains`,
  Objects/listobject.c:677-692), and `dict(...)` compares `k` with each key already in the dict
  whose hash equals `k`'s (Objects/dictobject.c, `compare_generic`, the stored key on the left), so
  two equal elements with equal hashes are one key; the same object twice is `yes` by identity.
  Scope: `__eq__` is a function of its argument (no state, no mutation of the list or dict being
  searched); and the hash of an object, when it returns, differs from every signal's (a signal
  hashes by identity), so the dict lookups and insertions compare it with no signal. The C twin
  reads none of these fields: it compares signals by identity. -/
  | other (repr : StrErr := none) (hash : StrErr := none) (eq : List EqAns := []) (hv : Int := 0)
      (prev : List EqAns := [])
  deriving Repr, DecidableEq, Inhabited

/-- An int element or key: hashable, and `repr()` of it raises past 4300 digits. -/
def intKey (n : Int) : SigKey := .other (intStrErr n) none

def SigKey.isSig : SigKey → Bool
  | .sig _ => true
  | .other .. => false

/-- What `repr()` of an element or key raises; a signal is a class, whose repr always returns. -/
def SigKey.reprErr : SigKey → StrErr
  | .sig _ => none
  | .other r .. => r

/-- The position of a signal in `_signals` (_pydecimal.py:332-333). -/
def Signal.idx : Signal → Nat
  | .clamped => 0 | .divisionByZero => 1 | .inexact => 2 | .overflow => 3 | .rounded => 4
  | .underflow => 5 | .invalidOperation => 6 | .subnormal => 7 | .floatOperation => 8

/-- What comparing an element or key with the signal `s` answers: a signal is equal only to itself
(classes compare by identity; a metaclass overriding `__eq__` is out of scope), any other object
answers through its own `__eq__`. -/
def SigKey.eqSig : SigKey → Signal → EqAns
  | .sig t, s => if t = s then .yes else .no
  | .other _ _ eq _ _, s => eq.getD s.idx .no

/-- `x in seq` for an `x` whose comparisons with the items of `seq` answer `as`, in order
(`list_contains`, Objects/listobject.c:677-692, with `PyObject_RichCompareBool`): the first true
answer stops it, an exception propagates, and no true answer is `False`. -/
def ansIn : List EqAns → Py Bool
  | [] => .ok false
  | .yes :: _ => .ok true
  | .no :: rest => ansIn rest
  | .raises e :: _ => .error e

/-- A value of a dict passed as `flags` or `traps`: its truth value, which is all
`_raise_error` reads (`if not self.traps[error]`, :4118; a `__bool__` that raises is out of
scope), and what `repr()` of it raises (`{Clamped: 10**5000, ...}`). -/
structure SigVal where
  truth : Bool
  repr : StrErr := none
  deriving Repr, DecidableEq, Inhabited

/-- A valid signal dict, in insertion order. -/
abbrev SigDict := List (Signal × Bool)

/-- What `repr()` of a list raises: the first element whose `repr()` raises
(Objects/listobject.c:623-638). -/
def listReprErr : List SigKey → StrErr
  | [] => none
  | k :: rest =>
    match k.reprErr with
    | some e => some e
    | none => listReprErr rest

/-- What `repr()` of a dict raises: key, then value, item by item in insertion order
(Objects/dictobject.c:3672-3702, `anydict_repr_impl`). -/
def dictReprErr : List (SigKey × SigVal) → StrErr
  | [] => none
  | (k, v) :: rest =>
    match k.reprErr with
    | some e => some e
    | none =>
      match v.repr with
      | some e => some e
      | none => dictReprErr rest

/-- A value assigned to a context attribute or passed to `Context()`. `int` is an object of
exact type `int` (an `int` subclass that overrides `__str__` or `__eq__` is out of scope). -/
inductive CtxArg where
  | none
  | int (n : Int)
  /-- `True` or `False`: an `int` to `isinstance`, but `%s` prints its name. -/
  | bool (b : Bool)
  /-- An object `id` of a class that is not `str`, whose `__eq__` answers the eight mode names
  of `_rounding_modes`, in that order, as `eq` says (a missing answer is `no`), and `str()` of
  which raises `str` (`none`: it returns). -/
  | eqObj (id : Nat) (eq : List EqAns) (str : StrErr := none)
  | str (s : String)
  | list (l : List SigKey)
  | dict (d : List (SigKey × SigVal))
  /-- A tuple, which `"%s ..." % d` takes as its argument tuple; `elems` is what `str()` of each
  element raises. -/
  | tuple (elems : List StrErr)
  /-- Any other object; `str` is what `str()` of it raises. Scope: its class defines no
  `__radd__` (which `_signals + value` in `Context()` would call, _pydecimal.py:3994) and no
  `__eq__` that answers true for a rounding mode (that is `eqObj`). -/
  | obj (str : StrErr := none)
  deriving Repr, Inhabited

/-- What `str()` of a value raises, for a value that is not a tuple: an int past the limit, a
list or dict through the `repr()` of its elements, an object through its own `__str__`. `None`,
a bool and a str always print. -/
def CtxArg.strErr : CtxArg → StrErr
  | .int n => intStrErr n
  | .eqObj _ _ s => s
  | .list l => listReprErr l
  | .dict d => dictReprErr d
  | .obj s => s
  | _ => Option.none

/-- `raise E(fmt % v)` for a format with one `%s`: the exception the formatting raises, or `ok`. -/
def CtxArg.pct (v : CtxArg) (ok : PyExc) : PyExc :=
  match v with
  | .tuple t => pctTupleExc t ok
  | v => pctExc v.strErr ok

structure PyContext where
  prec : Int
  rounding : Rounding
  emin : Int
  emax : Int
  capitals : Int
  clamp : Int
  flags : SigDict
  traps : SigDict
  ignored : List Signal
  /-- The object stored in `rounding` when it is not a str (an `eqObj`, `rounding` then holding
  the first mode it compared equal to); `none` when `rounding` holds the mode name itself. What
  an operation does under such a context (`_pick_rounding_function[rounding]` hashes the object)
  is out of scope. -/
  roundingObj : Option (Nat × List EqAns × StrErr) := none
  /-- The keys of the `flags` and `traps` dicts that are not signals, which `_set_signal_dict`
  stores when their `__eq__` answers true against a signal (`Context(traps=[k])` for such a `k`).
  `__repr__`, `__reduce__` and `copy` read them in Python; their models do not. -/
  flagsExtra : List (SigKey × SigVal) := []
  trapsExtra : List (SigKey × SigVal) := []
  deriving Repr, DecidableEq, Inhabited

def Rounding.name : Rounding → String
  | .up => "ROUND_UP" | .down => "ROUND_DOWN" | .ceiling => "ROUND_CEILING"
  | .floor => "ROUND_FLOOR" | .halfUp => "ROUND_HALF_UP" | .halfDown => "ROUND_HALF_DOWN"
  | .halfEven => "ROUND_HALF_EVEN" | .r05up => "ROUND_05UP"

/-- `_rounding_modes`, _pydecimal.py:342-343. -/
def roundingModes : List Rounding :=
  [.down, .halfUp, .halfEven, .ceiling, .floor, .up, .halfDown, .r05up]

def roundingOfName (s : String) : Option Rounding := roundingModes.find? (fun r => r.name == s)

/-- `"%s" % value` for an int-valued `value` (an int or a bool): `str(value)`, which for an int
of more than 4300 digits raises the int/str-limit `ValueError` (Objects/longobject.c:2207-2216). -/
def intText : CtxArg → Py String
  | .int n => do strLimit n.natAbs; return toString n
  | .bool b => .ok (if b then "True" else "False")
  | _ => .ok "~"

/-- The int an `isinstance(value, int)` value holds. -/
def intValue : CtxArg → Option Int
  | .int n => some n
  | .bool b => some (if b then 1 else 0)
  | _ => none

/-- `Context._set_integer_check`, _pydecimal.py:4005-4017: `none` is `'-inf'` / `'inf'`. The
message is built only when the value is refused, and its `%s` of `value` can itself raise
(`intText`). -/
def setIntegerCheck (name : String) (v : CtxArg) (vmin vmax : Option Int) : Py Int :=
  match intValue v with
  | some value =>
    match vmin, vmax with
    | none, some hi =>
      if value > hi then do .error (.valueError s!"{name} must be in [-inf, {hi}]. got: {← intText v}")
      else .ok value
    | some lo, none =>
      if value < lo then do .error (.valueError s!"{name} must be in [{lo}, inf]. got: {← intText v}")
      else .ok value
    | some lo, some hi =>
      if value < lo ∨ value > hi then do .error (.valueError s!"{name} must be in [{lo}, {hi}]. got {← intText v}")
      else .ok value
    | none, none => .ok value
  | none => .error (.typeError s!"{name} must be an integer")

def hasKey (d : List (SigKey × SigVal)) (k : SigKey) : Bool := d.any (fun p => p.1 == k)

/-- A key that is not a signal: `for key in d: if not key in _signals` (_pydecimal.py:4022-4023). -/
def hasOther (d : List (SigKey × SigVal)) : Bool := d.any (fun p => !p.1.isSig)

/-- Drop the key wrapper from a dict all of whose keys are signals, keeping each value's truth. -/
def sigEntries (d : List (SigKey × SigVal)) : SigDict :=
  d.filterMap (fun p => match p.1 with
    | .sig s => some (s, p.2.truth)
    | .other .. => none)

/-- The keys of a dict that are not signals, with their values. -/
def extrasOf (d : List (SigKey × SigVal)) : List (SigKey × SigVal) := d.filter (fun p => !p.1.isSig)

/-- `for key in d: if not key in _signals: raise KeyError(...)` (_pydecimal.py:4022-4024): each key
in insertion order is searched for in the list `_signals`, whose `list_contains` compares
`signal == key`; a signal's `type.__eq__` gives `NotImplemented` for anything but itself, so a key
that is not a signal answers through its own reflected `__eq__` (`SigKey.eqSig`). The first key
found in none refuses the dict with `fmt`; an exception from `__eq__` propagates. -/
def checkKeys (fmt : PyExc) : List (SigKey × SigVal) → Py Unit
  | [] => .ok ()
  | (k, _) :: rest => do
    if !(← ansIn (pySignals.map k.eqSig)) then throw fmt
    checkKeys fmt rest

/-- `Context._set_signal_dict`, _pydecimal.py:4019-4028: what is stored is the dict itself, its
signal entries and any other keys `__eq__` let through. `key in d` for each signal (:4025-4027) is
a dict lookup, which compares no key under the hash scope of `SigKey.other`. Each refusal formats
`d` with `%s` (:4021, :4024, :4027), which can itself raise (`CtxArg.pct`). Scope: `.dict` is a
`dict` or a subclass that keeps `dict`'s own iteration and lookup; a subclass overriding `__iter__`
or `__contains__`, which `isinstance(d, dict)` (:4020) admits, is out of scope. -/
def setSignalDict (v : CtxArg) : Py (SigDict × List (SigKey × SigVal)) :=
  match v with
  | .dict d => do
    checkKeys (v.pct (.keyError "~is not a valid signal dict")) d
    if !pySignals.all (fun s => hasKey d (.sig s)) then throw (v.pct (.keyError "~is not a valid signal dict"))
    return (sigEntries d, extrasOf d)
  | v => .error (v.pct (.typeError "~must be a signal dict"))

/-- The signals of a list assigned to `_ignored_flags`. `_raise_error` and `_regard_flags`
only test signals for membership and remove them (_pydecimal.py:4113, :4141), so other
elements change nothing they do, unless their `__eq__` against a signal answers true or raises
(`error in self._ignored_flags` runs it), which is out of scope with any other object: it is
stored as is in Python, `_ignored_flags` is private, and the module only ever assigns a list of
signals. -/
def ignoredOf : CtxArg → List Signal
  | .list l => l.filterMap (fun k => match k with
    | .sig s => some s
    | .other .. => none)
  | _ => []

/-- `value in _rounding_modes` (_pydecimal.py:4042) for an `eqObj`: `tuple_contains` compares the
modes in order and stops at the first true answer or exception (Objects/tupleobject.c:424-432). -/
def eqIn : List EqAns → List Rounding → Py (Option Rounding)
  | _, [] => .ok none
  | [], _ :: _ => .ok none
  | a :: as, r :: rs =>
    match a with
    | .yes => .ok (some r)
    | .no => eqIn as rs
    | .raises e => .error e

/-- `raise TypeError("%s: invalid rounding mode" % value)` (_pydecimal.py:4045): the text of the
message for a value `%s` prints without raising. -/
def roundingMsg : CtxArg → String
  | .int n => s!"{n}: invalid rounding mode"
  | .bool b => s!"{if b then "True" else "False"}: invalid rounding mode"
  | .none => "None: invalid rounding mode"
  | .str s => s!"{s}: invalid rounding mode"
  | _ => "~: invalid rounding mode"

/-- The exception `raise TypeError("%s: invalid rounding mode" % value)` raises: the formatting's
own (an int over the limit, a list holding one, a `__str__` that raises, a tuple as `%`'s argument
tuple), or the `TypeError`. -/
def invalidRoundingExc (v : CtxArg) : PyExc := v.pct (.typeError (roundingMsg v))

/-- `Context.__setattr__`, _pydecimal.py:4030-4053. -/
def pySetattr (c : PyContext) (name : String) (v : CtxArg) : Py PyContext := do
  if name == "prec" then return { c with prec := ← setIntegerCheck name v (some 1) none }
  else if name == "Emin" then return { c with emin := ← setIntegerCheck name v none (some 0) }
  else if name == "Emax" then return { c with emax := ← setIntegerCheck name v (some 0) none }
  else if name == "capitals" then return { c with capitals := ← setIntegerCheck name v (some 0) (some 1) }
  else if name == "clamp" then return { c with clamp := ← setIntegerCheck name v (some 0) (some 1) }
  else if name == "rounding" then
    match v with
    | .str s =>
      match roundingOfName s with
      | some r => return { c with rounding := r, roundingObj := none }
      | none => throw (invalidRoundingExc (.str s))
    | .eqObj id eq st =>
      match ← eqIn eq roundingModes with
      | some r => return { c with rounding := r, roundingObj := some (id, eq, st) }
      | none => throw (invalidRoundingExc (.eqObj id eq st))
    | v => throw (invalidRoundingExc v)
  else if name == "flags" then
    let (d, x) ← setSignalDict v
    return { c with flags := d, flagsExtra := x }
  else if name == "traps" then
    let (d, x) ← setSignalDict v
    return { c with traps := d, trapsExtra := x }
  else if name == "_ignored_flags" then return { c with ignored := ignoredOf v }
  else throw (.named "AttributeError" s!"'decimal.Context' object has no attribute '{name}'")

/-- `Context.__delattr__`, _pydecimal.py:4055-4056. -/
def pyDelattr (name : String) : Py Unit :=
  .error (.named "AttributeError" s!"{name} cannot be deleted")

/-- The arguments of `Context(...)`. -/
structure CtxInit where
  prec : CtxArg := .none
  rounding : CtxArg := .none
  emin : CtxArg := .none
  emax : CtxArg := .none
  capitals : CtxArg := .none
  clamp : CtxArg := .none
  flags : CtxArg := .none
  traps : CtxArg := .none
  ignored : Option (List Signal) := none
  deriving Repr, Inhabited

/-- `PyDict_SetItem` of a key whose `hash()` raises `e`: a `TypeError` is replaced by
"cannot use '<type>' as a dict key (<e>)", any other exception propagates
(Objects/dictobject.c:2442-2461, :2749-2755). -/
def dictKeyExc (e : PyExc) : PyExc :=
  match e with
  | .typeError m => .typeError s!"~cannot use as a dict key ({m})"
  | e => e

/-- `int(s in l)` then the insertion, for the signals of `_signals + l`, in `_signals` order: `s in l`
compares each element with `s` until one answers true (`SigKey.eqSig`; another signal is
unequal), and an exception from an element's `__eq__` stops the construction. -/
def sigItems (l : List SigKey) : List Signal → Py (List (SigKey × SigVal))
  | [] => .ok []
  | s :: rest => do
    let b ← ansIn (l.map (fun x : SigKey => x.eqSig s))
    return (.sig s, { truth := b }) :: (← sigItems l rest)

/-- What `x == k` answers, `x` the element at position `i` of the list and `k` a later element
that is not a signal: a signal `t` gives `t == k`, which is `NotImplemented` from `type.__eq__` and
then `k`'s reflected `__eq__` (`SigKey.eqSig`); any other element answers as `k.prev` records. A
signal `k` is never searched for this way (`otherItems` skips it). -/
def SigKey.prevAns (k : SigKey) (i : Nat) : SigKey → EqAns
  | .sig t => match k with
    | .sig _ => .no
    | .other .. => k.eqSig t
  | .other .. => match k with
    | .sig _ => .no
    | .other _ _ _ _ p => p.getD i .no

/-- The hash value of an element (a signal's is never compared, see `SigKey.other`). -/
def SigKey.hashVal : SigKey → Int
  | .sig _ => 0
  | .other _ _ _ hv _ => hv

/-- `k in l` for an element `k` that is not a signal, `pre` the elements before it: `list_contains`
(Objects/listobject.c:677-692) compares each of them with `k` (`earlier == k`, line 686) before it
reaches `k` itself, which is true by identity; the first true answer stops it, an exception
propagates. -/
def selfIn (k : SigKey) (pre : List SigKey) : Py Unit := do
  let _ ← ansIn (pre.mapIdx k.prevAns)
  return ()

/-- The comparisons inserting `k` into the dict makes: with each key already there whose hash
equals `k`'s, in insertion order (the probe sequence of one hash value visits its keys in the order
they were inserted), `stored == k`. `keys` holds each key with its position in the list. -/
def dictAns (k : SigKey) (keys : List (Nat × SigKey)) : List EqAns :=
  (keys.filter (fun q => q.2.hashVal == k.hashVal)).map (fun q => k.prevAns q.1 q.2)

/-- The keys `dict(...)` holds after the elements of `l` that are not signals (each with the value
`int(k in l)`, which is 1), in insertion order, `pre` the elements already consumed and `keys` the
non-signal keys already inserted, with their positions. A signal is already a key: its
`int(s in l)` repeats the comparisons its first pass made, with the same answers, and the dict keeps
its value. Any other element runs `selfIn`, is hashed (a `hash()` that raises stops the
construction), and is compared with the keys of equal hash: an equal one keeps its key (the new
value, 1, replaces the old 1), otherwise it is a new key; an exception from that `__eq__`
propagates (`PyDict_SetItem`, Objects/dictobject.c). -/
def otherItems (pre : List SigKey) (keys : List (Nat × SigKey)) : List SigKey → Py (List (Nat × SigKey))
  | [] => .ok keys
  | .sig t :: rest => otherItems (pre ++ [.sig t]) keys rest
  | .other r h eq hv p :: rest => do
    selfIn (.other r h eq hv p) pre
    match h with
    | some e => .error (dictKeyExc e)
    | none =>
      let dup ← ansIn (dictAns (.other r none eq hv p) keys)
      otherItems (pre ++ [.other r none eq hv p])
        (if dup then keys else keys ++ [(pre.length, .other r none eq hv p)]) rest

/-- `dict((s, int(s in l)) for s in _signals + l)`, _pydecimal.py:3994: the signals first, each
set when an element compares equal to it, then the keys the other elements make, which stay in the
dict for `_set_signal_dict` to check. -/
def signalDictOf (l : List SigKey) : Py (List (SigKey × SigVal)) := do
  let sigs ← sigItems l pySignals
  let rest ← otherItems [] [] l
  return sigs ++ rest.map (fun q => (q.2, { truth := true }))

/-- The value `Context()` assigns to `traps` or `flags`, _pydecimal.py:3991-4003. A
value that is neither a dict nor a list fails at `_signals + value` (`list_concat`,
Objects/listobject.c; an object whose class defines `__radd__` is out of scope, see `CtxArg.obj`). -/
def signalArg (dflt : List (SigKey × SigVal)) : CtxArg → Py CtxArg
  | .none => .ok (.dict dflt)
  | .dict d => .ok (.dict d)
  | .list l => do return .dict (← signalDictOf l)
  | _ => .error (.typeError "~can only concatenate list to list")

def orElseArg (a dflt : CtxArg) : CtxArg :=
  match a with
  | .none => dflt
  | v => v

def keyed (d : SigDict) : List (SigKey × SigVal) := d.map (fun p => (.sig p.1, { truth := p.2 }))

/-- The object a context's `rounding` attribute holds, as a value to assign again. -/
def PyContext.roundingArg (c : PyContext) : CtxArg :=
  match c.roundingObj with
  | none => .str c.rounding.name
  | some (id, eq, st) => .eqObj id eq st

/-- `Context.__init__(...)`, _pydecimal.py:3969-4003; `dc` is `DefaultContext`. -/
def pyContextNew (dc : PyContext) (a : CtxInit) : Py PyContext := do
  let c := dc
  let c ← pySetattr c "prec" (orElseArg a.prec (.int dc.prec))
  let c ← pySetattr c "rounding" (orElseArg a.rounding dc.roundingArg)
  let c ← pySetattr c "Emin" (orElseArg a.emin (.int dc.emin))
  let c ← pySetattr c "Emax" (orElseArg a.emax (.int dc.emax))
  let c ← pySetattr c "capitals" (orElseArg a.capitals (.int dc.capitals))
  let c ← pySetattr c "clamp" (orElseArg a.clamp (.int dc.clamp))
  let c ← pySetattr c "_ignored_flags" (.list ((a.ignored.getD []).map .sig))
  let c ← pySetattr c "traps" (← signalArg (keyed dc.traps ++ dc.trapsExtra) a.traps)
  pySetattr c "flags" (← signalArg (keyed (pySignals.map (fun s => (s, false)))) a.flags)

/-- `Context.__repr__`, _pydecimal.py:4066-4077: the names in dict order. -/
def setNames (d : SigDict) : List String := (d.filter (·.2)).map (fun p => p.1.name)

def pyContextRepr (c : PyContext) : String :=
  s!"Context(prec={c.prec}, rounding={c.rounding.name}, Emin={c.emin}, Emax={c.emax}, " ++
    s!"capitals={c.capitals}, clamp={c.clamp}, flags=[{", ".intercalate (setNames c.flags)}], " ++
    s!"traps=[{", ".intercalate (setNames c.traps)}])"

/-- `Context.clear_flags`, `clear_traps`, _pydecimal.py:4079-4087. -/
def clearDict (d : SigDict) : SigDict := d.map (fun p => (p.1, false))
def clearFlags (c : PyContext) : PyContext := { c with flags := clearDict c.flags }
def clearTraps (c : PyContext) : PyContext := { c with traps := clearDict c.traps }

/-- `Context.copy`, _pydecimal.py:4096-4102, and `Context._shallow_copy`, :4089-4094. -/
def contextCopy (dc c : PyContext) : Py PyContext :=
  pyContextNew dc
    { prec := .int c.prec, rounding := c.roundingArg, emin := .int c.emin, emax := .int c.emax
      capitals := .int c.capitals, clamp := .int c.clamp, flags := .dict (keyed c.flags ++ c.flagsExtra)
      traps := .dict (keyed c.traps ++ c.trapsExtra), ignored := some c.ignored }

/-- `Context.__reduce__`, _pydecimal.py:4059-4064: the arguments to rebuild the context. -/
def contextReduce (c : PyContext) : CtxInit :=
  { prec := .int c.prec, rounding := c.roundingArg, emin := .int c.emin, emax := .int c.emax
    capitals := .int c.capitals, clamp := .int c.clamp
    flags := .list ((c.flags.filter (·.2)).map (fun p => .sig p.1))
    traps := .list ((c.traps.filter (·.2)).map (fun p => .sig p.1)) }

/-- `Context._set_rounding`, _pydecimal.py:4156-4173. -/
def setRounding (c : PyContext) (type : CtxArg) : Py (PyContext × Rounding) := do
  let c' ← pySetattr c "rounding" type
  return (c', c.rounding)

/-- `Context._ignore_flags`, _pydecimal.py:4131-4136. -/
def ignoreFlags (c : PyContext) (fl : List Signal) : PyContext × List Signal :=
  ({ c with ignored := c.ignored ++ fl }, fl)

/-- `Context._ignore_all_flags`, _pydecimal.py:4127-4129. -/
def ignoreAllFlags (c : PyContext) : PyContext × List Signal := ignoreFlags c pySignals

/-- `Context._regard_flags`, _pydecimal.py:4138-4143: `self._ignored_flags.remove(flag)`
for each flag, which raises when one is missing. -/
def regardFlags (c : PyContext) : List Signal → Py PyContext
  | [] => .ok c
  | f :: fs =>
    if f ∈ c.ignored then regardFlags { c with ignored := c.ignored.erase f } fs
    else .error (.valueError "list.remove(x): x not in list")

/-- The fields of `Ctx` a `PyContext` holds; flags live in the `DM` state. -/
def PyContext.toCtx (c : PyContext) : Ctx :=
  { prec := c.prec.toNat, rounding := c.rounding, emin := c.emin, emax := c.emax
    capitals := c.capitals != 0, clamp := c.clamp != 0
    traps := (c.traps.filter (·.2)).map (·.1) }

/-! ## `create_decimal` -/

/-- `num != num.strip() or '_' in num`, _pydecimal.py:4181. -/
def needsStrip (s : List Char) : Bool := strip s != s || s.contains '_'

/-- `Context.create_decimal(num)` for a str, _pydecimal.py:4175-4190. -/
def createDecimalStr (c : Ctx) (s : List Char) : DM Dec := do
  if needsStrip s then return ← invalid c
  match pyParse s with
  | .error e => if e == invalidOp then return ← invalid c else throw e
  | .ok d =>
    if isnan d ≠ 0 ∧ (if payloadOf d = 0 then (0 : Int) else numDigits (payloadOf d)) >
        (c.prec : Int) - (if c.clamp then 1 else 0) then
      return ← invalid c
    fix c d

/-- `Context.create_decimal(num)` for a Decimal or an int: `Decimal(num, context=self)` is exact. -/
def createDecimalArg (c : Ctx) (a : Arg) : DM Dec := do
  let d ← liftPy (convertRaise a)
  if isnan d ≠ 0 ∧ (if payloadOf d = 0 then (0 : Int) else numDigits (payloadOf d)) >
      (c.prec : Int) - (if c.clamp then 1 else 0) then
    return ← invalid c
  fix c d

/-! ## The current context -/

/-- The thread's `_current_context_var`. -/
structure ThreadCtx where
  current : Option PyContext
  deriving Repr, DecidableEq, Inhabited

/-- `getcontext`, _pydecimal.py:358-370: a thread with no context gets `Context()`. -/
def getContext (dc : PyContext) (t : ThreadCtx) : Py (PyContext × ThreadCtx) :=
  match t.current with
  | some c => .ok (c, t)
  | none => do
    let c ← pyContextNew dc {}
    return (c, { current := some c })

/-- `setcontext`, _pydecimal.py:372-377. `template` says that the object is
`DefaultContext`, `BasicContext` or `ExtendedContext`. -/
def setContext (dc : PyContext) (ctx : PyContext) (template : Bool) : Py ThreadCtx := do
  if template then
    let c ← contextCopy dc ctx
    return { current := some (clearFlags c) }
  return { current := some ctx }

/-- `_ContextManager`, _pydecimal.py:3935-3948. -/
structure CtxManager where
  newContext : PyContext
  saved : Option PyContext := none
  deriving Repr, Inhabited

/-- `_ContextManager.__init__`, _pydecimal.py:3941-3942. -/
def managerInit (dc ctx : PyContext) : Py CtxManager := do
  return { newContext := ← contextCopy dc ctx }

/-- `_ContextManager.__enter__`, _pydecimal.py:3943-3946. -/
def managerEnter (dc : PyContext) (m : CtxManager) (t : ThreadCtx) :
    Py (CtxManager × ThreadCtx × PyContext) := do
  let (saved, t1) ← getContext dc t
  let m' := { m with saved := some saved }
  let t2 ← setContext dc m.newContext false
  let _ := t1
  return (m', t2, m.newContext)

/-- `_ContextManager.__exit__`, _pydecimal.py:3947-3948. -/
def managerExit (dc : PyContext) (m : CtxManager) : Py ThreadCtx :=
  match m.saved with
  | some s => setContext dc s false
  | none => .error (.named "AttributeError" "~saved_context")

/-- `_context_attributes`, _pydecimal.py:354-356. -/
def contextAttributes : List String :=
  ["prec", "Emin", "Emax", "capitals", "clamp", "rounding", "flags", "traps"]

/-- `setattr(ctx_manager.new_context, key, value)` for each keyword, in order. -/
def applyKwargs (m : CtxManager) : List (String × CtxArg) → Py CtxManager
  | [] => .ok m
  | (key, value) :: rest =>
    if key ∈ contextAttributes then do
      let nc ← pySetattr m.newContext key value
      applyKwargs { m with newContext := nc } rest
    else .error (.typeError s!"'{key}' is an invalid keyword argument for this function")

/-- `localcontext`, _pydecimal.py:381-424. -/
def localContext (dc : PyContext) (t : ThreadCtx) (ctx : Option PyContext)
    (kwargs : List (String × CtxArg)) : Py (CtxManager × ThreadCtx) := do
  let (base, t1) ← match ctx with
    | some c => pure (c, t)
    | none => getContext dc t
  let m ← managerInit dc base
  let m ← applyKwargs m kwargs
  return (m, t1)

/-- `IEEE_CONTEXT_MAX_BITS`, _pydecimal.py:89, for a 64-bit `sys.maxsize`. -/
def ieeeMaxBits : Int := 512

/-- `IEEEContext`, _pydecimal.py:427-445. -/
def ieeeContext (dc : PyContext) (bits : Int) : Py PyContext := do
  if bits ≤ 0 ∨ bits > ieeeMaxBits ∨ bits % 32 ≠ 0 then
    throw (.valueError s!"argument must be a multiple of 32, with a maximum of {ieeeMaxBits}")
  let ctx ← pyContextNew dc {}
  let ctx ← pySetattr ctx "prec" (.int (9 * (bits / 32) - 2))
  let emax : Int := 3 * (2 ^ (bits / 16 + 3).toNat)
  let ctx ← pySetattr ctx "Emax" (.int emax)
  let ctx ← pySetattr ctx "Emin" (.int (1 - emax))
  let ctx ← pySetattr ctx "rounding" (.str "ROUND_HALF_EVEN")
  let ctx ← pySetattr ctx "clamp" (.int 1)
  pySetattr ctx "traps" (.dict (keyed (pySignals.map (fun s => (s, false)))))

/-! ## Numbers the module exports -/

/-- `DefaultContext`, _pydecimal.py:6157-6165. -/
def defaultContext : PyContext :=
  { prec := 28, rounding := .halfEven, emin := -999999, emax := 999999, capitals := 1, clamp := 0
    flags := pySignals.map (fun s => (s, false))
    traps := pySignals.map (fun s => (s, s == .divisionByZero || s == .overflow || s == .invalidOperation))
    ignored := [] }

end PyLean.Decimal
