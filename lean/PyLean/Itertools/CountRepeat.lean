import PyLean.Itertools.Model

/-!
`itertools.count` (Modules/itertoolsmodule.c:3485-3727) and `itertools.repeat`
(:3729-3857) with int arguments, driven by a sequence of operations
(`next(it)`, `repr(it)`, `it.__length_hint__()`), and their doc equivalents
(rst:320-326, :626-633).

`count` keeps a C `Py_ssize_t cnt` while in "fast mode" (int start that fits,
step exactly 1) and switches to PyLong arithmetic at `PY_SSIZE_T_MAX`.
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

/-- The `PyNumber_Check` of `itertools_count_impl` (:3537-3541): non-numbers
are rejected. (Numbers that are not ints take the slow path with their own
`+`; they are out of scope here.) -/
def cCountCheck (startIsNum stepIsNum : Bool) : Py Unit :=
  if !startIsNum || !stepIsNum then .error (.typeError "a number is required") else .ok ()


/-- `countobject` (:3487-3492): `longCnt = none` is `long_cnt == NULL`. -/
structure CountState where
  cnt : Int
  longCnt : Option Int
  longStep : Int
  deriving Repr, DecidableEq

/-- `PyLong_AsLong` on an int, "-1 with the error cleared" on overflow. -/
def asLongOrMinus1 (x : Int) : Int := if ssizeMin ≤ x ∧ x ≤ ssizeMax then x else -1

/-- `itertools_count_impl` (:3529-3604) for int (or omitted) arguments; both
are `PyLong`s so `fast_mode` starts true. -/
def cCountNew (start step : Option Int) : CountState :=
  let longStep := step.getD 1
  -- :3548-3567: `cnt = PyLong_AsSsize_t(long_cnt)`, overflow → slow mode
  let (cnt, longCnt, fast) : Int × Int × Bool :=
    match start with
    | some s =>
      match asSsize s with
      | .ok v => (v, s, true)
      | .error _ => (-1, s, false)
    | none => (0, 0, true)
  -- :3571-3581: fast mode only works when the step is 1
  let fast := fast && asLongOrMinus1 longStep == 1
  -- :3582-3585
  if fast then { cnt := cnt, longCnt := none, longStep := longStep }
  else { cnt := ssizeMax, longCnt := some longCnt, longStep := longStep }

/-- `count_next` (:3651-3678, GIL build) and `count_nextlong` (:3629-3648). -/
def cCountNext (s : CountState) : Int × CountState :=
  if s.cnt = ssizeMax then
    let lc := s.longCnt.getD ssizeMax
    (lc, { s with longCnt := some (lc + s.longStep) })
  else (s.cnt, { s with cnt := s.cnt + 1 })

/-- `count_repr` (:3681-3705). `%R` of an int is its decimal form. -/
def cCountRepr (s : CountState) : String :=
  match s.longCnt with
  | none => s!"count({s.cnt})"
  | some lc =>
    if asLongOrMinus1 s.longStep = 1 then s!"count({lc})"
    else s!"count({lc}, {s.longStep})"

def cCountOps (s : CountState) : List Op → List (OpRes Int)
  | [] => []
  | .next :: ops => let (v, s) := cCountNext s; .val v :: cCountOps s ops
  | .repr :: ops => .str (cCountRepr s) :: cCountOps s ops
  | .hint :: ops => .exc (.typeError "~no __length_hint__") :: cCountOps s ops

def cCount (start step : Option Int) (ops : List Op) : List (OpRes Int) :=
  cCountOps (cCountNew start step) ops

/-- The doc's `count(start=0, step=1)` (rst:320-326): the `k`-th value. -/
def docCountValues (start step : Option Int) (k : Nat) : List Int :=
  let s := start.getD 0
  let st := step.getD 1
  (List.range k).map (fun (i : Nat) => s + (i : Int) * st)

/-! ## repeat -/

/-- `repeatobject` (:3731-3735): `cnt = -1` is "endless". -/
structure RepeatState (α : Type) where
  elem : α
  cnt : Int

variable {α : Type}

/-- `repeat_new` (:3740-3763): `times` parsed with format `n`; a supplied
negative `times` becomes 0. -/
def cRepeatNew (elem : α) (times : Option Int) : Py (RepeatState α) :=
  match times with
  | none => .ok { elem := elem, cnt := -1 }
  | some t =>
    match asSsize t with
    | .error e => .error e
    | .ok c => .ok { elem := elem, cnt := if c < 0 then 0 else c }

/-- `repeat_next` (:3786-3798). -/
def cRepeatNext (s : RepeatState α) : Option α × RepeatState α :=
  if s.cnt = 0 then (none, s)
  else if s.cnt > 0 then (some s.elem, { s with cnt := s.cnt - 1 })
  else (some s.elem, s)

/-- `repeat_repr` (:3801-3811); `rp` is `repr` of the element. -/
def cRepeatRepr (rp : α → String) (s : RepeatState α) : String :=
  if s.cnt = -1 then s!"repeat({rp s.elem})" else s!"repeat({rp s.elem}, {s.cnt})"

/-- `repeat_len` (:3814-3822), i.e. `__length_hint__`. -/
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

/-- The doc's `repeat(object, times=None)` (rst:626-633): the first `k`
values. `range(times)` accepts every int. -/
def docRepeatValues (elem : α) (times : Option Int) (k : Nat) : List α :=
  match times with
  | none => List.replicate k elem
  | some t => List.replicate (min k t.toNat) elem

end PyLean.Itertools
