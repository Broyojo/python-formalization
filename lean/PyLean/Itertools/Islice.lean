import PyLean.Itertools.Model

/-!
`itertools.islice`: the C object (Modules/itertoolsmodule.c:1582-1740) and the
doc equivalent (Doc/library/itertools.rst:459-501).

Arguments after the iterable are `args : List (Option Int)` of length 1 to 3
(`none` is `None`), i.e. `islice(it, stop)` or `islice(it, start, stop[, step])`.
The observable result is the drained run plus the number of items consumed
from the input iterator (the doc promises `max(start, stop)`).
-/

namespace PyLean.Itertools

open PyLean

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

/-- `isliceobject` (:1584-1591); `it = none` after `Py_CLEAR(lz->it)`. -/
structure IsliceState where
  it : Option (List Int)
  next : Int
  stop : Int
  step : Int
  cnt : Int
  deriving Repr, DecidableEq

/-- `islice_new` (:1596-1680): validated `(start, stop, step)`, with
`stop = -1` for `None`. -/
def cIsliceArgs (args : List (Option Int)) : Py (Int × Int × Int) :=
  let (a1, a2, a3) : Option Int × Option Int × Option (Option Int) :=
    match args with
    | [a1] => (a1, none, none)
    | [a1, a2] => (a1, a2, none)
    | a1 :: a2 :: a3 :: _ => (a1, a2, some a3)
    | [] => (none, none, none)
  -- (start, stop) after :1613-1641
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
    -- :1643-1648
    if start < 0 ∨ stop < -1 then .error (.valueError isliceIdxMsg)
    else
      -- :1650-1659
      let step := match a3 with | some (some v) => asSsizeOrMinus1 v | _ => 1
      if step < 1 then .error (.valueError isliceStepMsg) else .ok (start, stop, step)

/-- The `while (lz->cnt < lz->next)` skip loop (:1716-1722): `none` when the
input ran out (`goto empty`). Each iteration consumes one item. -/
def cIsliceSkip (next : Int) : List Int → Int → Option (List Int) × Int
  | [], cnt => if cnt < next then (none, cnt) else (some [], cnt)
  | x :: rest, cnt => if cnt < next then cIsliceSkip next rest (cnt + 1) else (some (x :: rest), cnt)

/-- `islice_next` (:1703-1740). The step is added in `size_t` and converted
back (:1729-1734), i.e. with two's complement wraparound. -/
def cIsliceNext (s : IsliceState) : Step IsliceState Int :=
  match s.it with
  | none => .stop s
  | some l =>
    let empty (cnt : Int) : Step IsliceState Int := .stop { s with it := none, cnt := cnt }
    match cIsliceSkip s.next l s.cnt with
    | (none, cnt) => empty cnt
    | (some l, cnt) =>
      if s.stop != -1 && cnt >= s.stop then empty cnt
      else match l with
        | [] => empty cnt
        | item :: rest =>
          let cnt := cnt + 1
          let oldnext := s.next
          let next := wrapSsize (s.next + s.step)
          let next := if next < oldnext || (s.stop != -1 && next > s.stop) then s.stop else next
          .yield item { it := some rest, next := next, stop := s.stop, step := s.step, cnt := cnt }

/-- `list(islice(l, *args))` in C, and the number of items consumed from `l`
(`lz->cnt`). Fuel `l.length + 1` suffices: each call consumes an item or
clears `it`. -/
def cIslice (l : List Int) (args : List (Option Int)) : Run Int × Int :=
  match cIsliceArgs args with
  | .error e => (Run.err e, 0)
  | .ok (start, stop, step) =>
    let r := drainSt cIsliceNext (l.length + 1)
      { it := some l, next := start, stop := stop, step := step, cnt := 0 }
    (r.1, r.2.cnt)

/-! ### Doc equivalent -/

/-- `slice(*args)` then the defaults and the check of rst:483-487: `(start,
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

/-- The `for i, element in zip(indices, iterable)` loop (rst:489-493):
`indices` is `range(bound)` (`some bound`) or `count()` (`none`); `zip` pulls
the index first, so an exhausted `range` stops without touching the input.
Returns the yielded items and the number of input items consumed. -/
def docIsliceLoop (bound : Option Int) (step : Int) : Int → Int → List Int → List Int × Nat
  | _, _, [] => ([], 0)
  | i, nextI, x :: xs =>
    if pastBound bound i then ([], 0)
    else
      if i = nextI then
        let r := docIsliceLoop bound step (i + 1) (nextI + step) xs
        (x :: r.1, r.2 + 1)
      else
        let r := docIsliceLoop bound step (i + 1) nextI xs
        (r.1, r.2 + 1)

/-- The doc's `islice(iterable, *args)`, drained, and the items consumed. -/
def docIslice (l : List Int) (args : List (Option Int)) : Run Int × Int :=
  match docIsliceArgs args with
  | .error e => (Run.err e, 0)
  | .ok (start, stop, step) =>
    let bound := stop.map (fun s => max start s)
    let r := docIsliceLoop bound step 0 start l
    (Run.ok r.1, r.2)

end PyLean.Itertools
