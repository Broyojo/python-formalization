import PyLean.Itertools.Model

/-!
`itertools.islice`: the C object (Modules/itertoolsmodule.c:1576-1734) and the
doc equivalent (Doc/library/itertools.rst:469-511).

Arguments after the iterable are `args : List (Option Int)` of length 1 to 3
(`none` is `None`), i.e. `islice(it, stop)` or `islice(it, start, stop[, step])`.
The observable result is the drained run plus the number of items consumed
from the input iterator (the doc promises `max(start, stop)`). An argument
that is not an int behaves as an out-of-range int: `PyNumber_AsSsize_t` fails
and `islice_new` clears the error, so non-index objects need no separate case.
The input is an `Obj`, so it may be non-iterable or raise after its items.
-/

namespace PyLean.Itertools

open PyLean

variable {α : Type}

def isliceStopMsg : String :=
  "Stop argument for islice() must be None or an integer: 0 <= x <= sys.maxsize."
def isliceIdxMsg : String :=
  "Indices for islice() must be None or an integer: 0 <= x <= sys.maxsize."
def isliceStepMsg : String := "Step for islice() must be a positive integer or None."

/-- `PyNumber_AsSsize_t(a, PyExc_OverflowError)` followed by "if the result is
-1 and an error is set, clear it": the value, or `-1` on overflow. -/
def asSsizeOrMinus1 (x : Int) : Int :=
  match asSsize x with
  | .ok v => v
  | .error _ => -1

/-- `isliceobject` (:1589-1596); `it = none` after `Py_CLEAR(lz->it)`. -/
structure IsliceState (α : Type) where
  it : Option (Src α)
  next : Int
  stop : Int
  step : Int
  cnt : Int

/-- `islice_new` (:1590-1674): validated `(start, stop, step)`, with
`stop = -1` for `None`. -/
def cIsliceArgs (args : List (Option Int)) : Py (Int × Int × Int) :=
  let (a1, a2, a3) : Option Int × Option Int × Option (Option Int) :=
    match args with
    | [a1] => (a1, none, none)
    | [a1, a2] => (a1, a2, none)
    | a1 :: a2 :: a3 :: _ => (a1, a2, some a3)
    | [] => (none, none, none)
  -- (start, stop) after :1618-1646
  let startStop : Py (Int × Int) :=
    if args.length = 1 then
      -- numargs == 2: islice(seq, stop)
      match a1 with
      | none => .ok (0, -1)
      | some v =>
        let stop := asSsizeOrMinus1 v
        if stop = -1 then .error (.valueError isliceStopMsg) else .ok (0, stop)
    else
      let start := match a1 with | none => 0 | some v => asSsizeOrMinus1 v
      match a2 with
      | none => .ok (start, -1)
      | some v =>
        let stop := asSsizeOrMinus1 v
        if stop = -1 then .error (.valueError isliceStopMsg) else .ok (start, stop)
  match startStop with
  | .error e => .error e
  | .ok (start, stop) =>
    -- :1648-1653
    if start < 0 ∨ stop < -1 then .error (.valueError isliceIdxMsg)
    else
      -- :1655-1664
      let step := match a3 with | some (some v) => asSsizeOrMinus1 v | _ => 1
      if step < 1 then .error (.valueError isliceStepMsg) else .ok (start, stop, step)

/-- The `while (lz->cnt < lz->next)` skip loop (:1721-1727): `none` when the
input ran out (`goto empty`). Each iteration consumes one item. -/
def cIsliceSkip (next : Int) : List α → Int → Option (List α) × Int
  | [], cnt => if cnt < next then (none, cnt) else (some [], cnt)
  | x :: rest, cnt => if cnt < next then cIsliceSkip next rest (cnt + 1) else (some (x :: rest), cnt)

/-- `goto empty` (:1742-1744) after `iternext` returned `NULL`: `it` is cleared
and the error, if any, stays set. -/
def cIsliceEnded (s : IsliceState α) (err : Option PyExc) (cnt : Int) : Step (IsliceState α) α :=
  match err with
  | none => .stop { s with it := none, cnt := cnt }
  | some e => .raise e { s with it := none, cnt := cnt }

/-- `islice_next` (:1697-1734). The step is added in `size_t` and converted
back (:1734-1739), i.e. with two's complement wraparound. -/
def cIsliceNext (s : IsliceState α) : Step (IsliceState α) α :=
  match s.it with
  | none => .stop s
  | some ⟨l, err⟩ =>
    match cIsliceSkip s.next l s.cnt with
    | (none, cnt) => cIsliceEnded s err cnt
    | (some l, cnt) =>
      if s.stop != -1 && cnt >= s.stop then .stop { s with it := none, cnt := cnt }
      else match l with
        | [] => cIsliceEnded s err cnt
        | item :: rest =>
          let cnt := cnt + 1
          let oldnext := s.next
          let next := wrapSsize (s.next + s.step)
          let next := if next < oldnext || (s.stop != -1 && next > s.stop) then s.stop else next
          .yield item { it := some ⟨rest, err⟩, next := next, stop := s.stop, step := s.step, cnt := cnt }

/-- `PyArg_UnpackTuple(args, "islice", 2, 4, ...)` (:1615) and the keyword
check (:1611-1613), before `cIsliceArgs`; `nargs` counts the iterable too.
Keywords are rejected only for `islice` itself and subclasses that inherit its
`tp_init`; `customInit` is a subclass defining `__init__`. -/
def cIsliceArity (nargs : Nat) (hasKw : Bool) (customInit : Bool := false) : Py Unit :=
  if hasKw && !customInit then .error (.typeError "islice() takes no keyword arguments")
  else if nargs < 2 then .error (.typeError s!"islice expected at least 2 arguments, got {nargs}")
  else if nargs > 4 then .error (.typeError s!"islice expected at most 4 arguments, got {nargs}")
  else .ok ()

/-- The body of `islice_new` after unpacking (:1618-1684): the arguments are
checked first, then `PyObject_GetIter(seq)`. -/
def cIsliceNew (seq : Obj α) (args : List (Option Int)) : Py (IsliceState α) :=
  match cIsliceArgs args with
  | .error e => .error e
  | .ok (start, stop, step) =>
    match getIter seq with
    | .error e => .error e
    | .ok it => .ok { it := some it, next := start, stop := stop, step := step, cnt := 0 }

/-- `list(islice(seq, *args))` in C, and the number of items consumed from the
input (`lz->cnt`). Fuel `seq.len + 1` suffices: each call consumes an item or
clears `it`. -/
def cIslice (seq : Obj α) (args : List (Option Int)) : Run α × Int :=
  match cIsliceNew seq args with
  | .error e => (Run.err e, 0)
  | .ok s =>
    let r := drainSt cIsliceNext (seq.len + 1) s
    (r.1, r.2.cnt)

/-! ### Doc equivalent -/

/-- `slice(*args)` then the defaults and the check of rst:489-494: `(start,
stop, step)` with `stop = none` for `None`. The doc raises a bare
`ValueError`. -/
def docIsliceArgs (args : List (Option Int)) : Py (Int × Option Int × Int) :=
  let (a, b, c) : Option Int × Option Int × Option Int :=
    match args with
    | [s] => (none, s, none)
    | [a, b] => (a, b, none)
    | a :: b :: c :: _ => (a, b, c)
    | [] => (none, none, none)
  let start := a.getD 0
  let step := c.getD 1
  if decide (start < 0) || (match b with | some s => decide (s < 0) | none => false) || decide (step ≤ 0) then .error (.valueError "")
  else .ok (start, b, step)

/-- `zip(range(m), ...)` has run out of indices at position `i`. -/
def pastBound : Option Int → Int → Bool
  | some m, i => decide (m ≤ i)
  | none, _ => false

/-- The `for i, element in zip(indices, iterable)` loop (rst:496-501):
`indices` is `range(bound)` (`some bound`) or `count()` (`none`); `zip` pulls
the index first, so an exhausted `range` stops without touching the input.
Returns the yielded items, the number of input items consumed, and the
exception, `err`, if the loop pulled past the last item. -/
def docIsliceLoop (bound : Option Int) (step : Int) (err : Option PyExc) :
    Int → Int → List α → List α × Nat × Option PyExc
  | i, _, [] => if pastBound bound i then ([], 0, none) else ([], 0, err)
  | i, nextI, x :: xs =>
    if pastBound bound i then ([], 0, none)
    else
      if i = nextI then
        let r := docIsliceLoop bound step err (i + 1) (nextI + step) xs
        (x :: r.1, r.2.1 + 1, r.2.2)
      else
        let r := docIsliceLoop bound step err (i + 1) nextI xs
        (r.1, r.2.1 + 1, r.2.2)

/-- The doc's `islice(iterable, *args)`, drained, and the items consumed. -/
def docIslice (seq : Obj α) (args : List (Option Int)) : Run α × Int :=
  match docIsliceArgs args with
  | .error e => (Run.err e, 0)
  | .ok (start, stop, step) =>
    match getIter seq with
    | .error e => (Run.err e, 0)
    | .ok ⟨l, err⟩ =>
      let bound := stop.map (fun s => max start s)
      let r := docIsliceLoop bound step err 0 start l
      ((r.1, r.2.2), r.2.1)

end PyLean.Itertools
