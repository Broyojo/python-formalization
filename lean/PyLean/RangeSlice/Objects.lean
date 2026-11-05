import PyLean.RangeSlice.Iter

/-!
The object level of `range`, Objects/rangeobject.c, CPython 3.15.2: what `range(...)`,
`range.__new__`, `r[item]`, `r == other` and `hash(r)` do with the Python objects they are
given. The arguments are not Lean ints but objects whose `__index__` is a callback that may
raise, return an `int` subclass (with its `DeprecationWarning`) or return a non-int, or that
have no `__index__` at all.

Scope: a class is modelled by its behaviour and its name `tp` (`%T` and `%.200s` print the
same text for the top-level `__main__` classes the difftest uses; names longer than 200
characters, which `%.200s` truncates, are out of scope). Memory errors are out of scope.
-/

namespace PyLean.RangeSlice

open PyLean

/-! ## Objects and `PyNumber_Index` -/

/-- What a user-defined `__index__` (`nb_index`) returns when it returns normally. -/
inductive IndexRet where
  /-- an object whose type is exactly `int` -/
  | exact (v : Int)
  /-- an instance of a proper subclass `tp` of `int` (such as `bool`); `warnRaises` says
  whether the warnings filter in force at the call turns the `DeprecationWarning` that
  `_PyNumber_Index` then issues into an exception -/
  | subclass (v : Int) (tp : String) (warnRaises : Bool)
  /-- an object of type `tp` that is not an `int` -/
  | other (tp : String)
  deriving Repr, DecidableEq, Inhabited

/-- A Python object passed to `range(...)` or `r[...]`, or compared with a range. -/
inductive Obj where
  /-- an object whose type is exactly `int` -/
  | int (v : Int)
  /-- `True` or `False` -/
  | bool (b : Bool)
  /-- an instance of a proper subclass `tp` of `int` other than `bool`. Any `__index__` it
  defines is never called (`_PyNumber_Index` checks `PyLong_Check` first). -/
  | intSub (v : Int) (tp : String)
  /-- not an `int`; its type `tp` defines `__index__`, a callback with this outcome -/
  | index (tp : String) (r : Py IndexRet)
  /-- a `slice` object with int-or-`None` parts -/
  | slice (s : Slice)
  /-- not an `int`, not a `slice`, and its type `tp` has no `__index__` (`float`, `str`,
  `NoneType`, `list`, ...) -/
  | other (tp : String)
  deriving Inhabited

/-- `Py_TYPE(o)->tp_name`. -/
def Obj.typeName : Obj → String
  | .int _ => "int"
  | .bool _ => "bool"
  | .intSub _ tp | .index tp _ | .other tp => tp
  | .slice _ => "slice"

/-- `_PyIndex_Check(o)`, Include/internal/pycore_abstract.h:13-17: the type has `nb_index`.
`int` and every subclass of it do; `slice` does not. -/
def Obj.hasIndex : Obj → Bool
  | .int _ | .bool _ | .intSub _ _ | .index _ _ => true
  | .slice _ | .other _ => false

/-- The `DeprecationWarning` of `_PyNumber_Index`, Objects/abstract.c:1440-1446, when the
warnings filter makes it an exception. -/
def indexSubclassWarning (tp rtp : String) : PyExc :=
  .named "DeprecationWarning" (tp ++ ".__index__() must return an int, not " ++ rtp ++
    ".  The ability to return an instance of a strict subclass of int is deprecated, " ++
    "and may be removed in a future version of Python.")

/-- `PyNumber_Index(o)`, Objects/abstract.c:1456-1463, over `_PyNumber_Index` (:1410-1449):
an `int` of any subclass is taken as is (:1416-1418) and then copied to an exact `int`
(:1460-1461); no `nb_index` is a `TypeError` (:1419-1424); otherwise `__index__` is called
(:1426): its exception propagates, an exact `int` is returned (:1428-1430), a non-int is a
`TypeError` (:1432-1437), and an `int` subclass first issues the `DeprecationWarning`
(:1440-1447). -/
def numberIndex : Obj → Py Int
  | .int v => .ok v
  | .bool b => .ok (if b then 1 else 0)
  | .intSub v _ => .ok v
  | .slice _ => .error (.typeError "'slice' object cannot be interpreted as an integer")
  | .other tp => .error (.typeError ("'" ++ tp ++ "' object cannot be interpreted as an integer"))
  | .index tp r =>
    match r with
    | .error e => .error e
    | .ok (.exact v) => .ok v
    | .ok (.other rtp) => .error (.typeError (tp ++ ".__index__() must return an int, not " ++ rtp))
    | .ok (.subclass v rtp warnRaises) =>
      if warnRaises then .error (indexSubclassWarning tp rtp) else .ok v

/-! ## `range(...)`: `validate_step`, `range_from_array`, `range_new`, `range_vectorcall` -/

/-- `validate_step`, rangeobject.c:47-61: an omitted step is 1 (:50-51); otherwise
`PyNumber_Index(step)` (:53), and a zero result is the `ValueError` (:54-58). -/
def validateStepObj : Option Obj → Py Int
  | none => .ok 1
  | some o => do
    let s ← numberIndex o
    if s = 0 then throw (.valueError "range() arg 3 must not be zero") else pure s

/-- `range_from_array` cases 3 and 2, rangeobject.c:102-122 then :141: `PyNumber_Index` of
the start (:107), then of the stop (:111), then `validate_step` (:116), each failure
returning at once; then `make_range_object`. -/
def rangeFrom23 (a b : Obj) (step : Option Obj) : Py Range := do
  let start ← numberIndex a
  let stop ← numberIndex b
  let step ← validateStepObj step
  pure (makeRangeObject start stop step)

/-- `range_from_array`, rangeobject.c:96-151, by argument count: 3 and 2 (:102-122), 1
(:123-130: `PyNumber_Index` of the stop, start 0, step 1), 0 (:131-134) and more than 3
(:135-139); then `make_range_object` (:141). -/
def rangeFromArray : List Obj → Py Range
  | [] => .error (.typeError "range expected at least 1 argument, got 0")
  | [b] => do
    let stop ← numberIndex b
    pure (makeRangeObject 0 stop 1)
  | [a, b] => rangeFrom23 a b none
  | [a, b, c] => rangeFrom23 a b (some c)
  | l => .error (.typeError ("range expected at most 3 arguments, got " ++ toString l.length))

/-- The `TypeError` of `_PyArg_NoKeywords` (Python/getargs.c:2956-2957) and
`_PyArg_NoKwnames` (:2991). -/
def noKwError : PyExc := .typeError "range() takes no keyword arguments"

/-- `_PyArg_NoKeywords("range", kw)`, Python/getargs.c:2942-2959. `kw` is `NULL` (`none`) or
the dict of keyword arguments, given by its keys (`tp_new` always passes a dict, so the
`PyDict_CheckExact` internal-error branch at :2948-2951 cannot be reached from Python). -/
def noKeywords (kw : Option (List String)) : Py Unit :=
  match kw with
  | none => .ok ()
  | some [] => .ok ()
  | some (_ :: _) => .error noKwError

/-- `_PyArg_NoKwnames("range", kwnames)`, Python/getargs.c:2978-2993: `kwnames` is `NULL`
or the tuple of keyword names. -/
def noKwnames (kwnames : Option (List String)) : Py Unit :=
  match kwnames with
  | none => .ok ()
  | some [] => .ok ()
  | some (_ :: _) => .error noKwError

/-- `range.__new__(range, *args, **kw)`: `range_new`, rangeobject.c:154-160. -/
def rangeNewTp (args : List Obj) (kw : Option (List String)) : Py Range := do
  noKeywords kw
  rangeFromArray args

/-- `range(*args, **kw)`: `range_vectorcall`, rangeobject.c:164-172 (`PyVectorcall_NARGS`
strips the offset flag, so the argument count is `args.length`). -/
def rangeVectorcall (args : List Obj) (kwnames : Option (List String)) : Py Range := do
  noKwnames kwnames
  rangeFromArray args

/-- `res` is a range object with these fields and its mathematical length (which `IsLen`
fixes uniquely, `isLen_unique`). -/
def Builds (res : Py Range) (start stop step : Int) : Prop :=
  ∃ r, res = .ok r ∧ r.start = start ∧ r.stop = stop ∧ r.step = step ∧ r.Len r.length

/-- **`range(...)` on arbitrary objects**, for both entry points. `range_new` and
`range_vectorcall` agree on every argument list and keyword set (twins); any keyword is a
`TypeError`, and an empty keyword set is no keyword. With no keywords: 0 arguments and more
than 3 are `TypeError`s with the source's messages; one argument is `range(0, stop, 1)`
where `stop = PyNumber_Index(arg)`, its error propagating; for two or three arguments the
start is converted first, then the stop, then the step (omitted means 1), the first failure
wins, a zero step is the `ValueError` only after both conversions succeeded
(`range(1, 'x', 0)` raises the `TypeError`), and otherwise the result stores the converted
values and the mathematical length. Quantified over all objects. -/
def RangeCallObj : Prop :=
  (∀ args kw, rangeNewTp args kw = rangeVectorcall args kw) ∧
  (∀ args (k : String) (ks : List String), rangeVectorcall args (some (k :: ks)) = .error noKwError) ∧
  (∀ args, rangeVectorcall args (some []) = rangeVectorcall args none) ∧
  rangeVectorcall [] none = .error (.typeError "range expected at least 1 argument, got 0") ∧
  (∀ args : List Obj, 3 < args.length →
    rangeVectorcall args none =
      .error (.typeError ("range expected at most 3 arguments, got " ++ toString args.length))) ∧
  (∀ b e, numberIndex b = .error e → rangeVectorcall [b] none = .error e) ∧
  (∀ b v, numberIndex b = .ok v → Builds (rangeVectorcall [b] none) 0 v 1) ∧
  (∀ (a b : Obj) (c : Option Obj),
    let res := rangeVectorcall (a :: b :: c.toList) none
    (∀ e, numberIndex a = .error e → res = .error e) ∧
    (∀ x e, numberIndex a = .ok x → numberIndex b = .error e → res = .error e) ∧
    (∀ x y, numberIndex a = .ok x → numberIndex b = .ok y →
      (c = none → Builds res x y 1) ∧
      (∀ o e, c = some o → numberIndex o = .error e → res = .error e) ∧
      (∀ o, c = some o → numberIndex o = .ok 0 →
        res = .error (.valueError "range() arg 3 must not be zero")) ∧
      (∀ o s, c = some o → numberIndex o = .ok s → s ≠ 0 → Builds res x y s)))

theorem builds_mk (a b s : Int) (h : s ≠ 0) : Builds (.ok (makeRangeObject a b s)) a b s :=
  ⟨_, rfl, rfl, rfl, rfl, (makeRangeObject_wf a b s h).len⟩

theorem rangeCallObj_proven : RangeCallObj := by
  refine ⟨fun args kw => ?_, fun args k ks => rfl, fun args => rfl, rfl, fun args h => ?_,
    fun b e h => ?_, fun b v h => ?_, fun a b c => ?_⟩
  · unfold rangeNewTp rangeVectorcall noKeywords noKwnames
    cases kw with
    | none => rfl
    | some l => cases l <;> rfl
  · rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
    all_goals simp only [List.length_cons, List.length_nil] at h
    all_goals first | omega | rfl
  · simp [rangeVectorcall, noKwnames, rangeFromArray, h, bind, Except.bind]
  · simp only [rangeVectorcall, noKwnames, rangeFromArray, h, bind, Except.bind, pure, Except.pure]
    exact builds_mk 0 v 1 (by decide)
  · intro res
    have hres : res = rangeFrom23 a b c := by
      cases c <;> rfl
    rw [hres]
    refine ⟨fun e h => ?_, fun x e h1 h2 => ?_, fun x y h1 h2 => ⟨fun hc => ?_, fun o e hc h3 => ?_,
      fun o hc h3 => ?_, fun o s hc h3 hs => ?_⟩⟩
    · simp [rangeFrom23, h, bind, Except.bind]
    · simp [rangeFrom23, h1, h2, bind, Except.bind]
    · subst hc
      simp only [rangeFrom23, h1, h2, validateStepObj, bind, Except.bind, pure, Except.pure]
      exact builds_mk x y 1 (by decide)
    · subst hc; simp [rangeFrom23, h1, h2, h3, validateStepObj, bind, Except.bind]
    · subst hc; simp [rangeFrom23, h1, h2, h3, validateStepObj, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw]
    · subst hc
      simp only [rangeFrom23, h1, h2, h3, validateStepObj, hs, bind, Except.bind, pure, Except.pure,
        ite_false]
      exact builds_mk x y s hs

/-! ## `r[item]`: `range_subscript` -/

/-- What `r[item]` returns. -/
inductive SubRes where
  | item (v : Int)
  | range (r : Range)
  deriving Repr, DecidableEq, Inhabited

/-- `r[item]`: `range_subscript`, rangeobject.c:729-748. An object with `nb_index` is
converted by `PyNumber_Index` (:732-736) and indexed by `compute_range_item` (:737); a
slice goes to `compute_slice` (:741-743); anything else is the `TypeError` (:744-747). -/
def rangeSubscript (r : Range) (item : Obj) : Py SubRes :=
  if item.hasIndex then do
    let i ← numberIndex item
    let v ← computeRangeItem r i
    pure (.item v)
  else
    match item with
    | .slice s => do
      let r' ← computeSlice r s
      pure (.range r')
    | _ => .error (.typeError ("range indices must be integers or slices, not " ++ item.typeName))

/-- **`r[item]` for every object.** An object with `__index__` (an `int` of any subclass, or
a class defining `__index__`) is converted by `PyNumber_Index`, whose error propagates
(`range(5)[Ix()]` with a raising `__index__`), and the int then indexes the sequence:
element `i` (`i + L` for negative `i`) for `-L <= i < L`, `IndexError` otherwise. A slice
gives exactly what `compute_slice` gives (pinned by `RangeSliceSeq` and `SliceErrors`), and
every other object is the `TypeError` naming its type. For every range (`r.WF`, mathematical
length `L`). -/
def SubscriptObj : Prop :=
  ∀ (r : Range) (L : Int), r.WF → r.Len L →
    (∀ item : Obj, item.hasIndex = true →
      rangeSubscript r item =
        match numberIndex item with
        | .error e => .error e
        | .ok i =>
          if 0 ≤ i ∧ i < L then .ok (.item (r.elem i))
          else if -L ≤ i ∧ i < 0 then .ok (.item (r.elem (i + L)))
          else .error (.indexError "range object index out of range")) ∧
    (∀ s : Slice,
      rangeSubscript r (.slice s) =
        match computeSlice r s with
        | .ok r' => .ok (.range r')
        | .error e => .error e) ∧
    (∀ tp : String,
      rangeSubscript r (.other tp) =
        .error (.typeError ("range indices must be integers or slices, not " ++ tp)))

theorem subscriptObj_proven : SubscriptObj := by
  intro r L hw hL
  refine ⟨fun item hi => ?_, fun s => ?_, fun tp => rfl⟩
  · unfold rangeSubscript
    rw [ite_t hi]
    cases h : numberIndex item with
    | error e => rfl
    | ok i =>
      simp only [bind, Except.bind]
      rw [getItemSeq_proven r L i hw hL]
      by_cases h1 : 0 ≤ i ∧ i < L
      · simp [h1, pure, Except.pure]
      · by_cases h2 : -L ≤ i ∧ i < 0
        · simp [h1, h2, pure, Except.pure]
        · simp [h1, h2]
  · unfold rangeSubscript
    simp only [Obj.hasIndex, Bool.false_eq_true, ite_false, bind, Except.bind, pure, Except.pure]
    cases computeSlice r s <;> rfl

/-! ## `r == other`: `range_richcompare` -/

/-- The six rich comparison operators (`Py_LT` ... `Py_GE`). -/
inductive CmpOp where
  | lt | le | eq | ne | gt | ge
  deriving Repr, DecidableEq, Inhabited

/-- The other operand of `range_richcompare`. -/
inductive CmpOther where
  /-- the same range object as `self` -/
  | self
  /-- a different range object -/
  | range (r : Range)
  /-- an object that is not a range (`PyRange_Check` is an exact type test; `range` cannot
  be subclassed) -/
  | notRange (tp : String)
  deriving Inhabited

/-- What a rich comparison slot returns: `NotImplemented` or a `bool`. -/
inductive CmpRes where
  | notImplemented
  | bool (b : Bool)
  deriving Repr, DecidableEq, Inhabited

/-- `range_equals`, rangeobject.c:530-553, with the `r0 == r1` identity test of :534 (`same`)
before the field comparisons (`rangeEquals`). On exact-int fields no comparison raises. -/
def rangeEqualsObj (r0 r1 : Range) (same : Bool) : Bool :=
  if same then true else rangeEquals r0 r1

/-- `range_richcompare`, rangeobject.c:556-583: `NotImplemented` for a non-range (:560-561);
`==` and `!=` through `range_equals`, `!=` negating it (:563-573); `NotImplemented` for the
four orderings (:574-578). (The `default` `PyErr_BadArgument` of :579-581 is unreachable:
`op` is always one of the six.) -/
def rangeRichcompare (self : Range) (other : CmpOther) (op : CmpOp) : Py CmpRes :=
  match other with
  | .notRange _ => .ok .notImplemented
  | .self => onRange self true
  | .range o => onRange o false
where
  onRange (o : Range) (same : Bool) : Py CmpRes :=
    match op with
    | .eq => .ok (.bool (rangeEqualsObj self o same))
    | .ne => .ok (.bool !(rangeEqualsObj self o same))
    | .lt | .le | .gt | .ge => .ok .notImplemented

/-- **`range.__eq__` and friends, every branch.** Against a non-range every operator returns
`NotImplemented` (so `range(3) == 3` falls back to identity); the four orderings return
`NotImplemented` against anything (so `range(3) < range(4)` is a `TypeError`); a range is
equal to itself; and against another range `==` returns `True` exactly when both have the
same length and the same elements, `!=` returning the negation. For every pair of ranges. -/
def RichcompareObj : Prop :=
  ∀ (r0 r1 : Range) (L0 L1 : Int), r0.WF → r1.WF → r0.Len L0 → r1.Len L1 →
    (∀ tp op, rangeRichcompare r0 (.notRange tp) op = .ok .notImplemented) ∧
    (∀ other op, op ≠ .eq → op ≠ .ne → rangeRichcompare r0 other op = .ok .notImplemented) ∧
    rangeRichcompare r0 .self .eq = .ok (.bool true) ∧
    rangeRichcompare r0 .self .ne = .ok (.bool false) ∧
    ∃ b : Bool,
      rangeRichcompare r0 (.range r1) .eq = .ok (.bool b) ∧
      rangeRichcompare r0 (.range r1) .ne = .ok (.bool !b) ∧
      (b = true ↔ (L0 = L1 ∧ ∀ k, 0 ≤ k → k < L0 → r0.elem k = r1.elem k))

theorem richcompareObj_proven : RichcompareObj := by
  intro r0 r1 L0 L1 hw0 hw1 hL0 hL1
  refine ⟨fun tp op => rfl, fun other op h1 h2 => ?_, rfl, rfl,
    rangeEquals r0 r1, rfl, rfl, eqSameSeq_proven r0 r1 L0 L1 hw0 hw1 hL0 hL1⟩
  cases other <;> cases op <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2

/-! ## `hash(r)`: `range_hash` -/

/-- The tuple `range_hash` hashes: `(len, start or None, step or None)`. -/
abbrev HashKey := Int × Option Int × Option Int

/-- `hash(r)`: `range_hash`, rangeobject.c:594-628: `PyObject_Hash` (:624) of the tuple built
at :601-623 (`rangeHashKey`). `tupleHash` is `hash` on such tuples (Objects/tupleobject.c),
left abstract. `PyObject_Not` and `PyObject_RichCompareBool` on the exact-int length cannot
fail. -/
def rangeHash (tupleHash : HashKey → Py Int) (r : Range) : Py Int := tupleHash (rangeHashKey r)

/-- **`hash(r)` is the hash of one tuple, and that tuple determines equality.** For every
range of mathematical length `L` and every tuple hash, `hash(r)` is the hash of
`(L, None, None)` when `L == 0`, `(L, r[0], None)` when `L == 1` and `(L, r[0], step)`
otherwise (`hash(range(1, 9, 2)) == hash((4, 1, 2))`), and two ranges hash the same tuple
exactly when they compare equal, so a constant key or the raw `(start, stop, step)` fails. -/
def RangeHashObj : Prop :=
  (∀ (h : HashKey → Py Int) (r : Range) (L : Int), r.WF → r.Len L →
    rangeHash h r =
      h (L, (if L = 0 then none else some (r.elem 0)), (if L ≤ 1 then none else some r.step))) ∧
  (∀ r0 r1 : Range, r0.WF → r1.WF → (rangeHashKey r0 = rangeHashKey r1 ↔ rangeEquals r0 r1 = true))

theorem rangeHashObj_proven : RangeHashObj := by
  refine ⟨fun h r L hw hL => ?_, fun r0 r1 hw0 hw1 => ⟨fun hk => ?_, eqHashConsistent_proven r0 r1 hw0 hw1⟩⟩
  · have hl := hw.length_eq hL
    have h0 := hL.1
    unfold rangeHash rangeHashKey Range.elem
    rw [hl]
    by_cases hz : L = 0
    · simp [hz]
    · by_cases h1 : L = 1
      · simp [h1]
      · simp [hz, h1, show ¬ L ≤ 1 by omega]
  · unfold rangeHashKey at hk
    unfold rangeEquals
    by_cases hz0 : r0.length = 0 <;> by_cases hz1 : r1.length = 0 <;>
    by_cases ho0 : r0.length = 1 <;> by_cases ho1 : r1.length = 1 <;>
      simp_all

end PyLean.RangeSlice
