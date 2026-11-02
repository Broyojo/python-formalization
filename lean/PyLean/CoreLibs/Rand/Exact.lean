import PyLean.CoreLibs.Rand.Gen
import PyLean.RangeSlice.Model
import PyLean.Accel.Bisect

/-!
The integer and sequence layer of `Lib/random.py` (CPython 3.15.2), over any `Gen`.

`below` in this file stands for `self._randbelow`, which `__init_subclass__`
chooses per class (`randbelowWith` or `randbelowWithout`). Loops that wait for the
generator to produce an acceptable value use fuel; `modelFuel` means the fuel ran
out and is never a Python outcome.

Python objects that reach a method as arguments are data: `IntArg` for anything
passed through `operator.index`, `SeqObj` for a sequence (its `len`, its
`__getitem__` and its iteration). Elements are of an abstract type `α`.
-/

namespace PyLean.CoreLibs.Rand

open PyLean PyLean.RangeSlice RM Flt

variable {σ F α : Type}

/-! ### `_randbelow`, Lib/random.py:245-272 -/

/-- `self.getrandbits(k)` with an `int` argument. -/
@[inline] def gb (g : Gen σ F) (k : Nat) : RM σ Nat := g.getrandbits (.int k)

/-- `while r >= n: r = self.getrandbits(k)`, Lib/random.py:250-251. -/
def belowLoop (g : Gen σ F) (n k : Nat) : Nat → Nat → RM σ Nat
  | 0, r => if r ≥ n then raise .modelFuel else pure r
  | fuel + 1, r =>
    if r ≥ n then do
      let r ← gb g k
      belowLoop g n k fuel r
    else pure r

/-- `Random._randbelow_with_getrandbits`, Lib/random.py:245-252. Defined for `n > 0`.
(`n = 0` would loop forever in Python: `k = 0`, `getrandbits(0) = 0 >= 0`.) -/
def randbelowWith (g : Gen σ F) (fuel n : Nat) : RM σ Nat := do
  let k := bitLength n
  let r ← gb g k
  belowLoop g n k fuel r

/-- `self.random()`. -/
@[inline] def rnd (g : Gen σ F) : RM σ F := fun s => let (x, s) := g.random s; (.ok x, s)

/-- `while r >= limit: r = random()`, Lib/random.py:270-271. -/
def drawBelow [Flt F] (g : Gen σ F) (limit : F) : Nat → F → RM σ F
  | 0, r => if Flt.le limit r then raise .modelFuel else pure r
  | fuel + 1, r =>
    if Flt.le limit r then do
      let r ← rnd g
      drawBelow g limit fuel r
    else pure r

/-- `Random._randbelow_without_getrandbits`, Lib/random.py:254-272. Defined for
`n > 0`. The `warn(...)` of :263-265 prints a `UserWarning` and has no effect on
the result, so it is not modelled. `(maxsize - rem) / maxsize` is `int / int`
(correctly rounded), which equals float division here because both operands are
at most `2**53` and so convert exactly. `Int.toNat` is the identity because
`random()` is never negative. -/
def randbelowWithout [Flt F] (g : Gen σ F) (fuel n : Nat) (maxsize : Nat := 2 ^ 53) : RM σ Nat := do
  if n ≥ maxsize then
    let r ← rnd g
    let nf ← lift (pyFloat (n : Int))
    let v ← lift (mathFloor (r * nf))
    return v.toNat
  else
    let rem := maxsize % n
    let a : F ← lift (pyFloat ((maxsize - rem : Nat) : Int))
    let b : F ← lift (pyFloat (maxsize : Int))
    let limit := a / b
    let r ← rnd g
    let r ← drawBelow g limit fuel r
    let v ← lift (mathFloor (r * b))
    return (v % (n : Int)).toNat

/-! ### `randbytes`, Lib/random.py:287-289 -/

/-- `n * 8`, Lib/random.py:289, before the result reaches `getrandbits`. A float,
`str` or `bytes` `n` stays that type and is rejected by `getrandbits`. -/
def mul8 : IntArg → Py IntArg
  | .int n => .ok (.int (n * 8))
  | .bool b => .ok (.int (if b then 8 else 0))
  | .other ty =>
    if ty = "NoneType" then
      .error (.typeError "unsupported operand type(s) for *: 'NoneType' and 'int'")
    else .ok (.other ty)

/-- `r.to_bytes(n, 'little')` for `n ≥ 0`: `int.to_bytes`, Objects/longobject.c. -/
def toBytesLE (r n : Nat) : Py (List Nat) :=
  if r ≥ 2 ^ (8 * n) then .error (.overflowError "int too big to convert")
  else .ok ((List.range n).map fun i => (r >>> (8 * i)) % 256)

/-- `Random.randbytes`, Lib/random.py:287-289. -/
def randbytes (g : Gen σ F) (n : IntArg) : RM σ (List Nat) := do
  let k ← lift (mul8 n)
  let r ← g.getrandbits k
  let m ← lift n.index
  lift (toBytesLE r m.toNat)

/-! ### `randrange`, `randint`, Lib/random.py:294-342 -/

/-- `sys.get_int_max_str_digits()` default. -/
def intMaxStrDigits : Nat := 4300

/-- `str(n)` for an `int`: refuses more than 4300 decimal digits. -/
def intStr (n : Int) : Py String :=
  if n.natAbs ≥ 10 ^ intMaxStrDigits then
    .error (.valueError "Exceeds the limit (4300 digits) for integer string conversion; use sys.set_int_max_str_digits() to increase the limit")
  else .ok (toString n)

/-- `str(x)` for an argument that `operator.index` accepted. -/
def argStr : IntArg → Py String
  | .int n => intStr n
  | .bool b => .ok (if b then "True" else "False")
  | .other ty => .ok ty

/-- Python's `a // b` for `b ≠ 0`. -/
def floorDiv (a b : Int) : Int := if b > 0 then a / b else (-a) / (-b)

/-- `step is not _ONE`, Lib/random.py:308. `none` is the default argument, which
is `_ONE`. A literal `1` is the same cached small-int object; `True` is not. -/
def stepIsOne : Option IntArg → Bool
  | none => true
  | some (.int 1) => true
  | some _ => false

/-- `ValueError(f"empty range in randrange({start}, {stop})")`, Lib/random.py:322. -/
def emptyRange2 (start stop : IntArg) : Py String := do
  let a ← argStr start
  let b ← argStr stop
  return s!"empty range in randrange({a}, {b})"

/-- `ValueError(f"empty range in randrange({start}, {stop}, {step})")`, Lib/random.py:332. -/
def emptyRange3 (start stop step : IntArg) : Py String := do
  let a ← argStr start
  let b ← argStr stop
  let c ← argStr step
  return s!"empty range in randrange({a}, {b}, {c})"

/-- Raise the `ValueError` whose message is `msg`; formatting the message can
itself raise (the 4300-digit limit). -/
def raiseValue (msg : Py String) : RM σ α := fun s =>
  match msg with
  | .ok m => (.error (.valueError m), s)
  | .error e => (.error e, s)

/-- `Random.randrange`, Lib/random.py:294-333. `stop = none` is `None`; `step = none`
is the default `_ONE`. -/
def randrange (below : Nat → RM σ Nat) (start : IntArg) (stop step : Option IntArg) : RM σ Int := do
  let istart ← lift start.index
  match stop with
  | none =>
    if !stepIsOne step then raise (.typeError "Missing a non-None stop argument")
    else if istart > 0 then
      let r ← below istart.toNat
      return (r : Int)
    else raise (.valueError "empty range for randrange()")
  | some stopArg =>
    let istop ← lift stopArg.index
    let width := istop - istart
    let stepArg := step.getD (.int 1)
    let istep ← lift stepArg.index
    if istep = 1 then
      if width > 0 then
        let r ← below width.toNat
        return istart + r
      else raiseValue (emptyRange2 start stopArg)
    else
      if istep = 0 then raise (.valueError "zero step for randrange()")
      else
        let n := if istep > 0 then floorDiv (width + istep - 1) istep
                 else floorDiv (width + istep + 1) istep
        if n ≤ 0 then raiseValue (emptyRange3 start stopArg stepArg)
        else
          let r ← below n.toNat
          return istart + istep * r

/-- `Random.randint`, Lib/random.py:335-342. -/
def randint (below : Nat → RM σ Nat) (a b : IntArg) : RM σ Int := do
  let ia ← lift a.index
  let ib ← lift b.index
  if ib < ia then raiseValue (do
    let sa ← intStr ia
    let sb ← intStr ib
    return s!"empty range in randint({sa}, {sb})")
  else
    let r ← below (ib - ia + 1).toNat
    return ia + r

/-! ### Sequences, Lib/random.py:347-495 -/

/-- A Python object used as a sequence. -/
structure SeqObj (α : Type) where
  /-- `isinstance(x, collections.abc.Sequence)`. -/
  isSequence : Bool := true
  /-- `len(x)`. -/
  len : Py Nat
  /-- `x[i]` for `i ≥ 0`. -/
  getItem : Nat → Py α
  /-- `list(x)`. A thunk, because a `range` can be far too long to build. -/
  toList : Unit → List α

/-- `l[i]` for `i ≥ 0`. -/
def listGet (l : List α) (i : Nat) : Py α :=
  match l[i]? with
  | some a => .ok a
  | none => .error (.indexError "list index out of range")

/-- A `list` (or any other concrete sequence with a list's error message). -/
def listSeq (l : List α) : SeqObj α :=
  { len := .ok l.length, getItem := listGet l, toList := fun _ => l }

/-- `Random.choice`, Lib/random.py:347-354. `seq` is any object with `__len__`
and `__getitem__`. -/
def choice (below : Nat → RM σ Nat) (seq : SeqObj α) : RM σ α := do
  let n ← lift seq.len
  if n = 0 then raise (.indexError "Cannot choose from an empty sequence")
  else
    let n' ← lift seq.len
    let j ← below n'
    lift (seq.getItem j)

/-- `x[i], x[j] = x[j], x[i]`, Lib/random.py:363: the right-hand side reads both
items, then `x[i]` and `x[j]` are assigned in that order. -/
def swapAssign (x : List α) (i j : Nat) : Py (List α) := do
  let xj ← listGet x j
  let xi ← listGet x i
  return (x.set i xj).set j xi

/-- `for i in reversed(range(1, len(x)))`, Lib/random.py:360-363. The first
argument `i` means the Python index `i + 1`, so `0` ends the loop. -/
def shuffleLoop (below : Nat → RM σ Nat) : Nat → List α → RM σ (List α)
  | 0, x => pure x
  | i + 1, x => do
    let j ← below (i + 2)
    let x ← lift (swapAssign x (i + 1) j)
    shuffleLoop below i x

/-- `Random.shuffle`, Lib/random.py:356-363. `immutable = some ty` is a sequence
of type `ty` without item assignment: the first swap fails after one draw. The
model returns the shuffled list, where Python mutates it in place and returns
`None`. -/
def shuffle (below : Nat → RM σ Nat) (x : List α) (immutable : Option String := none) : RM σ (List α) :=
  match immutable, x.length with
  | some ty, n + 2 => do
    let _ ← below (n + 2)
    raise (.typeError s!"'{ty}' object does not support item assignment")
  | _, n => shuffleLoop below (n - 1) x

/-- The pool branch of `sample`, Lib/random.py:444-448:
`j = randbelow(n - i); result[i] = pool[j]; pool[j] = pool[n - i - 1]`. -/
def poolLoop (below : Nat → RM σ Nat) (n : Nat) : Nat → Nat → List α → RM σ (List α)
  | 0, _, _ => pure []
  | c + 1, i, pool => do
    let j ← below (n - i)
    let x ← lift (listGet pool j)
    let v ← lift (listGet pool (n - i - 1))
    let rest ← poolLoop below n c (i + 1) (pool.set j v)
    return x :: rest

/-- `while j in selected: j = randbelow(n)`, Lib/random.py:454-455. -/
def pickLoop (below : Nat → RM σ Nat) (n : Nat) (selected : List Nat) : Nat → Nat → RM σ Nat
  | 0, j => if j ∈ selected then raise .modelFuel else pure j
  | fuel + 1, j =>
    if j ∈ selected then do
      let j ← below n
      pickLoop below n selected fuel j
    else pure j

/-- The set branch of `sample`, Lib/random.py:450-457. `selected` is the Python
set, as a list of its elements. -/
def setLoop (below : Nat → RM σ Nat) (pop : SeqObj α) (n fuel : Nat) : Nat → List Nat → RM σ (List α)
  | 0, _ => pure []
  | c + 1, selected => do
    let j ← below n
    let j ← pickLoop below n selected fuel j
    let x ← lift (pop.getItem j)
    let rest ← setLoop below pop n fuel c (j :: selected)
    return x :: rest

/-- The smallest `m` with `4 ** m ≥ x`, for `x ≥ 2`. -/
def ceilLog4 (x : Nat) : Nat := (Nat.log2 (x - 1) + 2) / 2

/-- `setsize`, Lib/random.py:438-440. `_ceil(_log(k * 3, 4))` is computed in
floats, and `ceilLog4 (k * 3)` is its exact value. `k * 3` is never a power of 4,
so the two can differ only if the double `log` lands on the wrong side of an
integer: the nearest power of 4 is at least 1 away from `k * 3`, so that takes
`k` around `2**49`, for which `[None] * k` (:437, before this line) cannot be
allocated. The difftest checks the formula up to `k = 2**40`. -/
def setsize (k : Nat) : Nat :=
  21 + (if k > 5 then 4 ^ ceilLog4 (k * 3) else 0)

/-- `sample` from `if not 0 <= k <= n` on, Lib/random.py:435-458. -/
def sampleCore (below : Nat → RM σ Nat) (fuel : Nat) (pop : SeqObj α) (n : Nat) (k : Int) :
    RM σ (List α) :=
  if ¬(0 ≤ k ∧ k ≤ (n : Int)) then
    raise (.valueError "Sample larger than population or is negative")
  else
    let k := k.toNat
    if n ≤ setsize k then poolLoop below n k 0 (pop.toList ())
    else setLoop below pop n fuel k []

/-- `range(total)` as a `SeqObj`: `len` is `rangeLength`, which overflows past
`sys.maxsize`. -/
def rangeSeq (total : Nat) : SeqObj Nat :=
  { len := do
      let n ← rangeLength (range1 total)
      return n.toNat
    getItem := fun i =>
      if i < total then .ok i else .error (.indexError "range object index out of range")
    toList := fun _ => List.range total }

/-- An element of `counts`: an `int`, or some other number (`none`). -/
abbrev CountV := Option Int

/-- `list(_accumulate(counts))`, Lib/random.py:423. A non-`int` value stays
non-`int` in every later prefix sum, and only `isinstance(total, int)` looks at it. -/
def accumulateCounts : List CountV → List CountV
  | [] => []
  | c :: cs =>
    let rec go (acc : CountV) : List CountV → List CountV
      | [] => []
      | x :: xs =>
        let next := match acc, x with
          | some a, some b => some (a + b)
          | _, _ => none
        next :: go next xs
    c :: go c cs

/-- The `counts` argument. -/
inductive CountsArg where
  | seq (xs : List CountV)
  | notIterable (tyName : String)
  deriving Repr, DecidableEq

/-- `bisect(cum_counts, s)`, Lib/random.py:432-433: `_bisect.bisect_right` with
defaults, on the list without its last element. -/
def bisectCounts (cum : List Int) (s : Nat) : Py Int :=
  PyLean.Accel.cBisectRight cum (s : Int) 0 none none

/-- The tail of the counts branch: `[population[bisect(cum_counts, s)] for s in selections]`,
Lib/random.py:433. -/
def mapSelections (pop : SeqObj α) (cum : List Int) : List Nat → Py (List α)
  | [] => .ok []
  | s :: ss => do
    let i ← bisectCounts cum s
    let x ← pop.getItem i.toNat
    let rest ← mapSelections pop cum ss
    return x :: rest

/-- `self.sample(range(total), k=k)`, Lib/random.py:431. -/
def sampleRange (below : Nat → RM σ Nat) (fuel total : Nat) (k : Int) : RM σ (List Nat) := do
  let m ← lift (rangeSeq total).len
  sampleCore below fuel (rangeSeq total) m k

/-- `Random.sample`, Lib/random.py:365-458. `k` is an `int`. -/
def sample (below : Nat → RM σ Nat) (fuel : Nat) (pop : SeqObj α) (k : Int)
    (counts : Option CountsArg := none) : RM σ (List α) := do
  if !pop.isSequence then
    raise (.typeError "Population must be a sequence.  For dicts or sets, use sorted(d).")
  else
    let n ← lift pop.len
    match counts with
    | none => sampleCore below fuel pop n k
    | some (.notIterable ty) => raise (.typeError s!"'{ty}' object is not iterable")
    | some (.seq cs) =>
      let cum := accumulateCounts cs
      if cum.length ≠ n then
        raise (.valueError "The number of counts does not match the population")
      else
        let total : CountV := cum.getLast?.getD (some 0)
        match total with
        | none => raise (.typeError "Counts must be integers")
        | some total =>
          if total < 0 then raise (.valueError "Counts must be non-negative")
          else
            let selections ← sampleRange below fuel total.toNat k
            lift (mapSelections pop (cum.dropLast.filterMap id) selections)

/-! ### `choices`, Lib/random.py:460-495 -/

/-- A number in `weights` or `cum_weights`. -/
inductive Num (F : Type) where
  | int (n : Int)
  | flt (x : F)
  deriving Inhabited

/-- `a + b` on the Python number tower. -/
def Num.add [Flt F] : Num F → Num F → Py (Num F)
  | .int a, .int b => .ok (.int (a + b))
  | .flt a, .flt b => .ok (.flt (a + b))
  | .int a, .flt b => do
    let x ← pyFloat a
    return .flt (x + b)
  | .flt a, .int b => do
    let y ← pyFloat b
    return .flt (a + y)

/-- `list(_accumulate(weights))`, Lib/random.py:475. -/
def accumulateNums [Flt F] : List (Num F) → Py (List (Num F))
  | [] => .ok []
  | c :: cs =>
    let rec go (acc : Num F) : List (Num F) → Py (List (Num F))
      | [] => .ok []
      | x :: xs => do
        let next ← acc.add x
        let rest ← go next xs
        return next :: rest
    do
      let rest ← go c cs
      return c :: rest

/-- `x < a` for a float `x` and a number `a`: exact, as Python compares. -/
def ltNum [Flt F] (x : F) : Num F → Bool
  | .int n => Flt.ltInt x n
  | .flt y => Flt.lt x y

/-- `bisect(cum_weights, x, 0, hi)`, Lib/random.py:494: the `internal_bisect_right`
loop on a float `x`. -/
def bisectNum [Flt F] (a : List (Num F)) (x : F) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if ltNum x (a.getD mid default) then bisectNum a x fuel lo mid
      else bisectNum a x fuel (mid + 1) hi
    else lo

/-- The argument `weights`. -/
inductive WeightsArg (F : Type) where
  | seq (xs : List (Num F))
  /-- Not iterable and an `int` (`choices(pop, 3)`). -/
  | intArg (k : IntArg)
  /-- Not iterable and not an `int`. -/
  | notIterable (tyName : String)

/-- `[population[floor(random() * n)] for i in _repeat(None, k)]`, Lib/random.py:473. -/
def choicesPlain [Flt F] (g : Gen σ F) (pop : SeqObj α) (n : F) : Nat → RM σ (List α)
  | 0 => pure []
  | k + 1 => do
    let r ← rnd g
    let j ← lift (mathFloor (r * n))
    let x ← lift (pop.getItem j.toNat)
    let rest ← choicesPlain g pop n k
    return x :: rest

/-- `[population[bisect(cum_weights, random() * total, 0, hi)] for i in _repeat(None, k)]`,
Lib/random.py:494-495. -/
def choicesWeighted [Flt F] (g : Gen σ F) (pop : SeqObj α) (cum : List (Num F)) (total : F) (hi : Nat) :
    Nat → RM σ (List α)
  | 0 => pure []
  | k + 1 => do
    let r ← rnd g
    let j := bisectNum cum (r * total) (hi + 1) 0 hi
    let x ← lift (pop.getItem j)
    let rest ← choicesWeighted g pop cum total hi k
    return x :: rest

/-- From `if len(cum_weights) != n` on, Lib/random.py:485-495. -/
def choicesCum [Flt F] (g : Gen σ F) (pop : SeqObj α) (n : Nat) (cum : List (Num F)) (k : Int) :
    RM σ (List α) := do
  if cum.length ≠ n then
    raise (.valueError "The number of weights does not match the population")
  else
    match cum.getLast? with
    | none => raise (.indexError "list index out of range")
    | some last =>
      let total ← lift (show Py F from
        match last with
        | .int a => do
          let x ← pyFloat a
          return x + 0.0
        | .flt x => .ok (x + 0.0))
      if Flt.le total 0.0 then
        raise (.valueError "Total of weights must be greater than zero")
      else if !isFinite total then
        raise (.valueError "Total of weights must be finite")
      else
        choicesWeighted g pop cum total (n - 1) k.toNat

/-- `Random.choices`, Lib/random.py:460-495. `k` is an `int`; `_repeat(None, k)`
with `k < 0` repeats nothing, which `Int.toNat` gives. -/
def choices [Flt F] (g : Gen σ F) (pop : SeqObj α) (weights : Option (WeightsArg F))
    (cumWeights : Option (List (Num F))) (k : Int) : RM σ (List α) := do
  let n ← lift pop.len
  match cumWeights with
  | none =>
    match weights with
    | none =>
      let nf : F ← lift (pyFloat (n : Int))
      choicesPlain g pop (nf + 0.0) k.toNat
    | some (.seq xs) =>
      let cum ← lift (accumulateNums xs)
      choicesCum g pop n cum k
    | some (.intArg w) =>
      let s ← lift (argStr w)
      raise (.typeError s!"The number of choices must be a keyword argument: k={s}")
    | some (.notIterable ty) => raise (.typeError s!"'{ty}' object is not iterable")
  | some cum =>
    match weights with
    | some _ => raise (.typeError "Cannot specify both weights and cumulative weights")
    | none => choicesCum g pop n cum k

end PyLean.CoreLibs.Rand
