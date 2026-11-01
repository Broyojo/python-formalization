import PyLean.Itertools.GroupbyProps

/-!
`groupby` with everything that can fail: this is the mirror of `groupby_step`
(Modules/itertoolsmodule.c:507-531), `groupby_next` (:533-579) and
`_grouper_next` (:665-700), with their `NULL` returns. The input may raise after
its items and the key function may raise on any item.

`GroupbyTee.lean` has the same three functions without those branches, which
is what the simulation of the doc's generators in `GroupbyProps.lean` runs on.
`gbOps_pure` shows the two coincide when nothing raises, so that proof applies
to this model.

Key comparison stays `DecidableEq κ`: `PyObject_RichCompareBool` failing (the
`rcmp == -1` of :560 and the `rcmp <= 0` of :691) needs a raising `__eq__`,
which is excluded by that assumption on the key type. `_grouper_create` running
out of memory is not modelled.
-/

namespace PyLean.Itertools

open PyLean

variable {α κ : Type} [Inhabited α] [Inhabited κ] [DecidableEq κ]

/-- A `groupbyobject` and the exception its input raises after its items (once,
then the input is exhausted, as with a generator). -/
structure GbState (α κ : Type) where
  g : CGroupby α κ
  err : Option PyExc

/-- The return of `groupby_step`: `0`, or `-1` with exception `e` set (`none`:
the input ended, nothing is set). -/
inductive GbStep where
  | ok
  | fail (e : Option PyExc)

/-- `groupby_step` (:507-531). `PyIter_Next` has taken the item before the key
function runs, so a raising key loses that item (:519-523); `currvalue` and
`currkey` are assigned only after both calls succeeded (:526-529). -/
def gbStep (key : α → Py κ) (s : GbState α κ) : GbStep × GbState α κ :=
  match s.g.it with
  | [] =>
    match s.err with
    | none => (.fail none, s)
    | some e => (.fail (some e), { s with err := none })
  | v :: rest =>
    match key v with
    | .error e => (.fail (some e), { s with g := { s.g with it := rest } })
    | .ok k => (.ok, { s with g := { s.g with it := rest, currvalue := some v, currkey := some k } })

/-- The `for (;;)` loop of `groupby_next` (:541-568): `none` is the `break`, and
`some e` the `return NULL` after a failed `groupby_step` (:566-567). Fuel as in
`cGroupbySkip`. -/
def gbSkip (key : α → Py κ) : Nat → GbState α κ → Option (Option PyExc) × GbState α κ
  | 0, s => (some none, s)
  | fuel + 1, s =>
    if !gbAdvance s.g.currkey s.g.tgtkey then (none, s)
    else match gbStep key s with
      | (.fail e, s) => (some e, s)
      | (.ok, s) => gbSkip key fuel s

/-- A `NULL` return: `StopIteration` when no exception is set. -/
def gbFail {β : Type} : Option PyExc → NextRes β
  | none => .stop
  | some e => .exc e

/-- `groupby_next` (:533-579). `currgrouper` is cleared first (:539), so the
current group is invalidated even when this call then fails. -/
def gbNext (key : α → Py κ) (s : GbState α κ) : NextRes κ × GbState α κ :=
  let s := { s with g := { s.g with currgrouper := none } }
  match gbSkip key (s.g.it.length + 1) s with
  | (some e, s) => (gbFail e, s)
  | (none, s) =>
    let ck := s.g.currkey.getD default
    (.val ck, { s with g := cGrouperCreate { s.g with tgtkey := some ck } ck })

/-- `gbo->currvalue` as a result. -/
def gbValue {β : Type} : Option β → NextRes β
  | none => .stop
  | some v => .val v

/-- `_grouper_next` (:665-700). -/
def gbGrouperNext (key : α → Py κ) (s : GbState α κ) (j : Nat) : NextRes α × GbState α κ :=
  if s.g.currgrouper != some j then (.stop, s)
  else
    match (if s.g.currvalue.isNone then gbStep key s else (.ok, s)) with
    | (.fail e, s) => (gbFail e, s)
    | (.ok, s) =>
      if s.g.groupers.getD j default == s.g.currkey.getD default then
        (gbValue s.g.currvalue, { s with g := { s.g with currvalue := none, currkey := none } })
      else (.stop, s)

def gbOps (key : α → Py κ) : GbState α κ → List (GbOp κ) → List (NextRes κ ⊕ NextRes α)
  | _, [] => []
  | s, .outer :: ops => let (r, s) := gbNext key s; .inl r :: gbOps key s ops
  | s, .group j :: ops =>
    if j < s.g.groupers.length then
      let (r, s) := gbGrouperNext key s j; .inr r :: gbOps key s ops
    else gbOps key s ops
  | s, .direct k :: ops => gbOps key { s with g := cGrouperDirect s.g k } ops

/-- `itertools_groupby_impl` (:458-477), then the operations. -/
def cGroupbyR (key : α → Py κ) (iterable : Obj α) (ops : List (GbOp κ)) :
    Py (List (NextRes κ ⊕ NextRes α)) :=
  match getIter iterable with
  | .error e => .error e
  | .ok ⟨l, err⟩ =>
    .ok (gbOps key ⟨{ it := l, tgtkey := none, currkey := none, currvalue := none,
                      currgrouper := none, groupers := [] }, err⟩ ops)

/-! ## When nothing raises this is the model of `GroupbyTee.lean` -/

/-- A key function that does not raise. -/
def pureKey (key : α → κ) : α → Py κ := fun x => .ok (key x)

def liftRes : Option κ ⊕ Option α → NextRes κ ⊕ NextRes α
  | .inl r => .inl (gbValue r)
  | .inr r => .inr (gbValue r)

theorem gbStep_pure (key : α → κ) (g : CGroupby α κ) :
    gbStep (pureKey key) ⟨g, none⟩ =
      match cGroupbyStep key g with
      | none => (.fail none, ⟨g, none⟩)
      | some g' => (.ok, ⟨g', none⟩) := by
  cases h : g.it with
  | nil => simp [gbStep, cGroupbyStep, h]
  | cons v rest => simp [gbStep, cGroupbyStep, h, pureKey]

theorem gbSkip_pure (key : α → κ) : ∀ (fuel : Nat) (g : CGroupby α κ),
    gbSkip (pureKey key) fuel ⟨g, none⟩ =
      (if (cGroupbySkip key fuel g).1 then none else some none, ⟨(cGroupbySkip key fuel g).2, none⟩)
  | 0, g => by simp [gbSkip, cGroupbySkip]
  | fuel + 1, g => by
    simp only [gbSkip, cGroupbySkip]
    by_cases ha : gbAdvance g.currkey g.tgtkey = true
    · simp only [ha, Bool.not_true, Bool.false_eq_true, if_false, gbStep_pure]
      cases hs : cGroupbyStep key g with
      | none => simp
      | some g' => simp only; exact gbSkip_pure key fuel g'
    · simp [ha]

theorem gbNext_pure (key : α → κ) (g : CGroupby α κ) :
    gbNext (pureKey key) ⟨g, none⟩ =
      (gbValue (cGroupbyNext key g).1, ⟨(cGroupbyNext key g).2, none⟩) := by
  simp only [gbNext, cGroupbyNext, gbSkip_pure]
  cases h : (cGroupbySkip key (g.it.length + 1) { g with currgrouper := none }).1 with
  | false =>
    cases hs : cGroupbySkip key (g.it.length + 1) { g with currgrouper := none } with
    | mk f g' =>
      rw [hs] at h
      simp only at h
      subst h
      simp [gbFail, gbValue]
  | true =>
    cases hs : cGroupbySkip key (g.it.length + 1) { g with currgrouper := none } with
    | mk f g' =>
      rw [hs] at h
      simp only at h
      subst h
      simp [gbValue]

theorem gbGrouperNext_pure (key : α → κ) (g : CGroupby α κ) (j : Nat) :
    gbGrouperNext (pureKey key) ⟨g, none⟩ j =
      (gbValue (cGrouperNext key g j).1, ⟨(cGrouperNext key g j).2, none⟩) := by
  simp only [gbGrouperNext, cGrouperNext]
  by_cases hc : (g.currgrouper != some j) = true
  · simp [hc, gbValue]
  · simp only [hc, Bool.false_eq_true, if_false]
    cases hv : g.currvalue.isNone with
    | false =>
      simp only [Bool.false_eq_true, if_false]
      split <;> simp [gbValue]
    | true =>
      simp only [if_true, gbStep_pure]
      cases hs : cGroupbyStep key g with
      | none => simp [gbFail, gbValue]
      | some g' =>
        simp only
        split <;> simp [gbValue]

/-- With a key function and input that do not raise, the two models give the
same answers to every sequence of operations. -/
theorem gbOps_pure (key : α → κ) : ∀ (ops : List (GbOp κ)) (g : CGroupby α κ),
    gbOps (pureKey key) ⟨g, none⟩ ops = (cGroupbyOps key g ops).map liftRes
  | [], _ => rfl
  | .outer :: ops, g => by
    simp only [gbOps, cGroupbyOps, gbNext_pure, List.map_cons, liftRes]
    rw [gbOps_pure key ops]
  | .group j :: ops, g => by
    simp only [gbOps, cGroupbyOps]
    by_cases hj : j < g.groupers.length
    · simp only [hj, if_true, gbGrouperNext_pure, List.map_cons, liftRes]
      rw [gbOps_pure key ops]
    · simp only [hj, if_false]
      exact gbOps_pure key ops g
  | .direct k :: ops, g => by
    simp only [gbOps, cGroupbyOps]
    exact gbOps_pure key ops _

/-! ## Properties -/

/-- For every key function that does not raise, every input object that does
not raise after its items, and every interleaving of `next()` on the groupby
object and on any group it returned (including old groups), the C object answers
exactly as the doc's generators, over any element type and any key type with
decidable equality. A non-iterable input raises in both.

Hypotheses, both preconditions: the key function and the input do not raise.
The doc's generators die at their first exception, the C object does not, so
past an exception there is nothing to agree on; `GroupbyFailedStepKeepsState`
says what C does there. -/
def GroupbyDocAgreeR : Prop :=
  ∀ (α κ : Type) [Inhabited α] [Inhabited κ] [DecidableEq κ] (key : α → κ) (o : Obj α)
    (ops : List (GbOp κ)), (∀ op ∈ ops, op.isPublic = true) →
    (∀ l e, o = .iter l (some e) → False) →
    cGroupbyR (pureKey key) o ops = (docGroupby key o ops).map (·.map liftRes)

theorem groupbyDocAgreeR_proven : GroupbyDocAgreeR := by
  intro α κ _ _ _ key o ops hp hnr
  cases o with
  | notIterable ty => rfl
  | iter l err =>
    cases err with
    | some e => exact (hnr l e rfl).elim
    | none =>
      have h := groupbyDocAgree_proven α κ key (.iter l none) ops hp
      rw [← h]
      simp only [cGroupbyR, cGroupby, cGroupbyNew, getIter]
      exact congrArg Except.ok (gbOps_pure key ops _)

/-- A failed `groupby_step`, for every key function and state: the groupby
object's values are those from before the call, so the object stays usable, and
at most the one item it took is lost. -/
def GroupbyFailedStepKeepsState : Prop :=
  ∀ (α κ : Type) (key : α → Py κ) (s s' : GbState α κ) (e : Option PyExc),
    gbStep key s = (.fail e, s') →
    s'.g.currkey = s.g.currkey ∧ s'.g.currvalue = s.g.currvalue ∧ s'.g.tgtkey = s.g.tgtkey ∧
      s'.g.currgrouper = s.g.currgrouper ∧ s'.g.groupers = s.g.groupers ∧
      s'.g.it = s.g.it.drop 1 ∧ (e = none ↔ s.g.it = [] ∧ s.err = none)

theorem groupbyFailedStepKeepsState_proven : GroupbyFailedStepKeepsState := by
  intro α κ key s s' e h
  simp only [gbStep] at h
  cases hit : s.g.it with
  | nil =>
    rw [hit] at h
    cases hr : s.err with
    | none =>
      simp only [hr, Prod.mk.injEq, GbStep.fail.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [hit, hr]
    | some x =>
      simp only [hr, Prod.mk.injEq, GbStep.fail.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [hit]
  | cons v rest =>
    rw [hit] at h
    cases hk : key v with
    | error x =>
      simp only [hk, Prod.mk.injEq, GbStep.fail.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    | ok k => simp [hk] at h

/-- `itertools._grouper(groupby_obj, k)` makes the new group current: every
group created before it stops at once and leaves the state alone, whatever the
key function and input would do next. -/
def GrouperDirectInvalidates : Prop :=
  ∀ (α κ : Type) [Inhabited α] [Inhabited κ] [DecidableEq κ] (key : α → Py κ) (g : CGroupby α κ)
    (err : Option PyExc) (k : κ) (j : Nat), j < g.groupers.length →
    gbGrouperNext key ⟨cGrouperDirect g k, err⟩ j = (.stop, ⟨cGrouperDirect g k, err⟩)

theorem grouperDirectInvalidates_proven : GrouperDirectInvalidates := by
  intro α κ _ _ _ key g err k j hj
  have h : (cGrouperDirect g k).currgrouper ≠ some j := by
    simp only [cGrouperDirect, cGrouperCreate]
    intro h
    simp only [Option.some.injEq] at h
    omega
  simp [gbGrouperNext, h]

end PyLean.Itertools
