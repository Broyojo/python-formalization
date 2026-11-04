import PyLean.Itertools.Model

/-!
`itertools.count` (Modules/itertoolsmodule.c:3475-3721) and `itertools.repeat`
(:3723-3851), driven by a sequence of operations (`next(it)`, `repr(it)`,
`it.__length_hint__()`), and their doc equivalents (rst:325-331, :631-638).

`count` keeps a C `Py_ssize_t cnt` while in "fast mode" (int start that fits,
step exactly 1) and otherwise, or at `PY_SSIZE_T_MAX`, adds Python objects. Its
arguments are any numbers ("Either long_cnt or long_step may be a float, Fraction,
or Decimal", :3500): a `CVal ν` says what the C code can see of one, and `NumOps`
gives `PyNumber_Add` and `%R` for everything but exact ints, so the model is
generic in the number types. `CountFloat.lean` instantiates it with `float`.

`NumOps.add` here cannot call back into the count object. `CountReentry.lean` mirrors
`count_nextlong` with an add that can (the re-entrant `__radd__` of python/cpython#154670,
a use-after-free of the `long_cnt` that `count_nextlong` does not hold across the add), and
shows that without re-entry it is `cCountNext`.
-/

namespace PyLean.Itertools

open PyLean

inductive Op where
  | next
  | repr
  | hint
  deriving Repr, DecidableEq

/-- Result of one operation: an int, a string, `StopIteration` or an exception. -/
inductive OpRes (α : Type) where
  | val (v : α)
  | str (s : String)
  | stop
  | exc (e : PyExc)

/-! ## count -/

/-- A Python object as `count` sees it. `int` is an exact int; `intSub` a subclass
of int (`bool`, say) with its value; `num` passes `PyNumber_Check` but not
`PyLong_Check`; `nonNum` fails `PyNumber_Check`. `ν` is the rest of the object. -/
inductive CVal (ν : Type) where
  | int (i : Int)
  | intSub (i : Int) (x : ν)
  | num (x : ν)
  | nonNum (x : ν)

/-- `PyNumber_Check`. -/
def CVal.isNumber {ν : Type} : CVal ν → Bool
  | .nonNum _ => false
  | _ => true

/-- `PyLong_Check`. -/
def CVal.isLong {ν : Type} : CVal ν → Bool
  | .int _ | .intSub _ _ => true
  | _ => false

/-- The value of a `PyLong_Check`ed object. -/
def CVal.longVal {ν : Type} : CVal ν → Int
  | .int i | .intSub i _ => i
  | _ => 0

/-- What the number types do: `PyNumber_Add`, and `%R`, which can raise. Exact ints
are built in (`pyAdd`, `pyRepr`), so this is everything else. Nothing is assumed
of these functions. -/
structure NumOps (ν : Type) where
  add : CVal ν → CVal ν → Py (CVal ν)
  repr : CVal ν → Py String

variable {ν : Type}

/-- `PyNumber_Add`: of two exact ints, their sum. -/
def pyAdd (N : NumOps ν) : CVal ν → CVal ν → Py (CVal ν)
  | .int a, .int b => .ok (.int (a + b))
  | a, b => N.add a b

/-- `_MAX_STR_DIGITS_ERROR_FMT_TO_STR` (Objects/longobject.c:33) with the default limit. -/
def intStrLimitMsg : String :=
  "Exceeds the limit (4300 digits) for integer string conversion; use sys.set_int_max_str_digits() to increase the limit"

/-- `%R` of an exact int is `long_to_decimal_string` (Objects/longobject.c:2321-2327), which
raises `ValueError` for more than `sys.get_int_max_str_digits()` digits. Under the default
limit of 4300 (`_PY_LONG_DEFAULT_MAX_STR_DIGITS`, Include/internal/pycore_long.h:29) that is
exactly `|a| ≥ 10**4300`: the exact check at :2207-2217 counts the digits without the sign,
and the pre-check at :2125-2135 fires only from 481 30-bit digits, past `10**4334`, so it
also refuses every int before the `_pylong` path at :2138-2146 (more than 1000 digits), which
has no exact check. A limit changed by `sys.set_int_max_str_digits()` is out of scope. -/
def intRepr (a : Int) : Py String :=
  if 10 ^ 4300 ≤ a.natAbs then .error (.valueError intStrLimitMsg) else .ok (toString a)

/-- `%R`: of an exact int, `intRepr`. -/
def pyRepr (N : NumOps ν) : CVal ν → Py String
  | .int a => intRepr a
  | v => N.repr v

/-- `countobject` (:3477-3482): `longCnt = none` is `long_cnt == NULL`. -/
structure CountState (ν : Type) where
  cnt : Int
  longCnt : Option (CVal ν)
  longStep : CVal ν

/-- `PyLong_AsLong` on an int, "-1 with the error cleared" on overflow. -/
def asLongOrMinus1 (x : Int) : Int := if ssizeMin ≤ x ∧ x ≤ ssizeMax then x else -1

/-- `arg != NULL && !PyNumber_Check(arg)`. -/
def argBad : Option (CVal ν) → Bool
  | some v => !v.isNumber
  | none => false

/-- `arg == NULL || PyLong_Check(arg)`. -/
def argLong : Option (CVal ν) → Bool
  | some v => v.isLong
  | none => true

/-- `itertools_count_impl` (:3520-3595). `cnt` is only ever kept in fast mode. -/
def cCountNew (start step : Option (CVal ν)) : Py (CountState ν) :=
  -- :3529-3533
  if argBad start || argBad step then .error (.typeError "a number is required")
  else
    -- :3535-3536
    let fast := argLong start && argLong step
    -- :3539-3551: `PyLong_AsSsize_t`, overflow clears `fast_mode`
    let (cnt, longCnt, fast) : Int × CVal ν × Bool :=
      match start with
      | some s =>
        if fast then
          match asSsize s.longVal with
          | .ok v => (v, s, true)
          | .error _ => (-1, s, false)
        else (0, s, false)
      | none => (0, .int 0, fast)
    -- :3555-3557
    let longStep := step.getD (.int 1)
    -- :3563-3571: fast mode only works when the step is 1
    let fast := fast && asLongOrMinus1 longStep.longVal == 1
    -- :3573-3576
    if fast then .ok { cnt := cnt, longCnt := none, longStep := longStep }
    else .ok { cnt := ssizeMax, longCnt := some longCnt, longStep := longStep }

/-- `count_next` (:3645-3672, GIL build) and `count_nextlong` (:3620-3642): the switch
to slow mode stores `long_cnt` at once (:3622-3628), and the sum is computed before the
current value is handed over, so a failed add raises in its place (:3635-3638) and
keeps `long_cnt`. In fast mode `cnt` becomes an exact int: the type of a `bool` start,
and `__add__` of an int subclass, are not consulted. -/
def cCountNext (N : NumOps ν) (s : CountState ν) : OpRes (CVal ν) × CountState ν :=
  if s.cnt = ssizeMax then
    let lc := s.longCnt.getD (.int ssizeMax)
    let s := { s with longCnt := some lc }
    match pyAdd N lc s.longStep with
    | .error e => (.exc e, s)
    | .ok up => (.val lc, { s with longCnt := some up })
  else (.val (.int s.cnt), { s with cnt := s.cnt + 1 })

/-- `PyLong_Check(lz->long_step)` and its value is 1 (:3684-3689). -/
def stepIsOne (step : CVal ν) : Bool := step.isLong && asLongOrMinus1 step.longVal == 1

/-- `count_repr` (:3675-3699). `ty` is `_PyType_Name(Py_TYPE(lz))`. -/
def cCountRepr (N : NumOps ν) (ty : String) (s : CountState ν) : Py String :=
  match s.longCnt with
  | none => .ok s!"{ty}({s.cnt})"
  | some lc =>
    if stepIsOne s.longStep then
      match pyRepr N lc with
      | .error e => .error e
      | .ok r => .ok s!"{ty}({r})"
    else
      match pyRepr N lc with
      | .error e => .error e
      | .ok r =>
        match pyRepr N s.longStep with
        | .error e => .error e
        | .ok t => .ok s!"{ty}({r}, {t})"

/-- A `repr()` as an operation result. -/
def reprRes {α : Type} : Py String → OpRes α
  | .ok r => .str r
  | .error e => .exc e

def cCountOps (N : NumOps ν) (ty : String) (s : CountState ν) : List Op → List (OpRes (CVal ν))
  | [] => []
  | .next :: ops => let (r, s) := cCountNext N s; r :: cCountOps N ty s ops
  | .repr :: ops => reprRes (cCountRepr N ty s) :: cCountOps N ty s ops
  | .hint :: ops => .exc (.typeError "~no __length_hint__") :: cCountOps N ty s ops

/-- `count(start, step)` then the operations; `ty` is the type's name, so
`"count"` unless subclassed. -/
def cCount (N : NumOps ν) (start step : Option (CVal ν)) (ops : List Op) (ty : String := "count") :
    List (OpRes (CVal ν)) :=
  match cCountNew start step with
  | .error e => [.exc e]
  | .ok s => cCountOps N ty s ops

/-- The doc's `count(start=0, step=1)` (rst:325-331) under `k` calls of `next()`:
`yield n`, and only on the next call `n += step`. -/
def docCountRun (N : NumOps ν) (step : CVal ν) : Nat → CVal ν → Run (CVal ν)
  | 0, _ => ([], none)
  | 1, n => ([n], none)
  | k + 2, n =>
    match pyAdd N n step with
    | .error e => ([n], some e)
    | .ok m => let r := docCountRun N step (k + 1) m; (n :: r.1, r.2)

/-! ## repeat -/

/-- `repeatobject` (:3725-3729): `cnt = -1` is "endless". -/
structure RepeatState (α : Type) where
  elem : α
  cnt : Int

variable {α : Type}

/-- `repeat_new` (:3734-3757): `times` parsed with format `n`; a supplied
negative `times` becomes 0. -/
def cRepeatNew (elem : α) (times : Option Int) : Py (RepeatState α) :=
  match times with
  | none => .ok { elem := elem, cnt := -1 }
  | some t =>
    match asSsize t with
    | .error e => .error e
    | .ok c => .ok { elem := elem, cnt := if c < 0 then 0 else c }

/-- `repeat_next` (:3780-3792). -/
def cRepeatNext (s : RepeatState α) : Option α × RepeatState α :=
  if s.cnt = 0 then (none, s)
  else if s.cnt > 0 then (some s.elem, { s with cnt := s.cnt - 1 })
  else (some s.elem, s)

/-- `repeat_repr` (:3795-3805); `rp` is `repr` of the element. -/
def cRepeatRepr (rp : α → String) (s : RepeatState α) : String :=
  if s.cnt = -1 then s!"repeat({rp s.elem})" else s!"repeat({rp s.elem}, {s.cnt})"

/-- `repeat_len` (:3808-3816), i.e. `__length_hint__`. -/
def cRepeatHint (s : RepeatState α) : OpRes Int :=
  if s.cnt = -1 then .exc (.typeError "len() of unsized object") else .val s.cnt

/-- One entry of the ops' results: an item, or a hint/repr answer. -/
def cRepeatOps (rp : α → String) (s : RepeatState α) : List Op → List (OpRes α ⊕ OpRes Int)
  | [] => []
  | .next :: ops =>
    let (v, s) := cRepeatNext s
    .inl (match v with | some x => OpRes.val x | none => .stop) :: cRepeatOps rp s ops
  | .repr :: ops => .inr (.str (cRepeatRepr rp s)) :: cRepeatOps rp s ops
  | .hint :: ops => .inr (cRepeatHint s) :: cRepeatOps rp s ops

def cRepeat (rp : α → String) (elem : α) (times : Option Int) (ops : List Op) :
    List (OpRes α ⊕ OpRes Int) :=
  match cRepeatNew elem times with
  | .error e => [.inr (.exc e)]
  | .ok s => cRepeatOps rp s ops

/-- The doc's `repeat(object, times=None)` (rst:631-638): the first `k`
values. `range(times)` accepts every int. -/
def docRepeatValues (elem : α) (times : Option Int) (k : Nat) : List α :=
  match times with
  | none => List.replicate k elem
  | some t => List.replicate (min k t.toNat) elem

end PyLean.Itertools
