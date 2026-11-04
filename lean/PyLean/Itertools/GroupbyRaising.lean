import PyLean.Itertools.GroupbyProps

/-!
`groupby` with everything that can fail or re-enter: this is the mirror of
`groupby_step` (Modules/itertoolsmodule.c:505-529), `groupby_next` (:532-575)
and `_grouper_next` (:662-696). The input may raise after its items, the key
function may raise on any item, and key comparison is a `KeyEq`: it may raise,
and a `__eq__` it calls may re-enter the groupby object.

Re-entrancy is the real code path, not a state change written by hand: `hooks`
holds, for successive `__eq__` calls, the operations that call performs on the
same object, and they run through `gbRun`, the function that runs top-level
operations. The Python caller catches what those operations raise.

`GroupbyTee.lean` has the same three functions without those branches, which
is what the simulation of the doc's generators in `GroupbyProps.lean` runs on.
`gbFold_pure` shows the two coincide when nothing raises or re-enters, so that
proof applies to this model.

Not modelled: `_grouper_create` running out of memory; a key function or input
that re-enters (`groupby_step` re-reads nothing after them, and the finalizers
of the values it releases).
-/

namespace PyLean.Itertools

open PyLean

variable {α κ : Type}

/-- `PyObject_RichCompareBool(a, b, Py_EQ)` (Objects/object.c:1122-1144): `same`
is `a is b`, which answers true without calling `__eq__`; otherwise `eq` is the
outcome of `__eq__` and its truth test. Both are parameters: nothing is assumed
of them, in particular no equivalence, and `eq` may raise. -/
structure KeyEq (κ : Type) where
  same : κ → κ → Bool
  eq : κ → κ → Py Bool

/-- One outcome of `next()`. `crash` is a NULL dereference: the process dies. -/
inductive GbRes (β : Type) where
  | val (a : β)
  | stop
  | exc (e : PyExc)
  | crash
  deriving Repr, DecidableEq

/-- A `groupbyobject`, the exception its input raises after its items (once,
then the input is exhausted, as with a generator), what successive `__eq__`
calls do, the results so far, and whether the process has died. -/
structure GbState (α κ : Type) where
  g : CGroupby α κ
  err : Option PyExc
  hooks : List (List (GbOp κ)) := []
  log : List (GbRes κ ⊕ GbRes α) := []
  crashed : Bool := false

/-- The return of `groupby_step`: `0`, or `-1` with exception `e` set (`none`:
the input ended, nothing is set). -/
inductive GbStep where
  | ok
  | fail (e : Option PyExc)

/-- `groupby_step` (:505-529). `PyIter_Next` has taken the item before the key
function runs, so a raising key loses that item (:517-521); `currvalue` and
`currkey` are assigned only after both calls succeeded (:524-527). -/
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

/-- `PyObject_RichCompareBool(a, b, Py_EQ)` with `__eq__` running its hook. The
`Py_INCREF`ed snapshots of :549-553 and :681-682 are the arguments `a` and `b`,
which the hook cannot change. -/
def gbEq (K : KeyEq κ) (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ)
    (a b : κ) : Py Bool × GbState α κ :=
  if K.same a b then (.ok true, s)
  else match s.hooks with
    | [] => (K.eq a b, s)
    | h :: hs => (K.eq a b, run h { s with hooks := hs })

/-- `if (groupby_step(gbo) < 0) return NULL;`, then carry on with `k`. -/
def gbThen (k : GbState α κ → Option (Option PyExc) × GbState α κ) :
    GbStep × GbState α κ → Option (Option PyExc) × GbState α κ
  | (.fail e, s) => (some e, s)
  | (.ok, s) => k s

/-- The `for (;;)` loop of `groupby_next` (:539-566): `none` is the `break`, and
`some e` a `return NULL`, after a failed comparison (:558-559) or a failed
`groupby_step` (:564-565). Each iteration but the last takes an item, so
`it.length + 1` iterations are enough, whatever a hook takes. -/
def gbSkip (K : KeyEq κ) (key : α → Py κ) (run : List (GbOp κ) → GbState α κ → GbState α κ) :
    Nat → GbState α κ → Option (Option PyExc) × GbState α κ
  | 0, s => (some none, s)
  | fuel + 1, s =>
    match s.g.currkey, s.g.tgtkey with
    | none, _ => gbThen (fun s => gbSkip K key run fuel s) (gbStep key s)
    | some _, none => (none, s)
    | some ck, some tk =>
      match gbEq K run s tk ck with
      | (.error e, s) => (some (some e), s)
      | (.ok false, s) => (none, s)
      | (.ok true, s) => gbThen (fun s => gbSkip K key run fuel s) (gbStep key s)

/-- A `NULL` return: `StopIteration` when no exception is set. -/
def gbFail {β : Type} : Option PyExc → GbRes β
  | none => .stop
  | some e => .exc e

/-- `_grouper_create` (:625-637): a new grouper becomes the current one. -/
def gbCreate (g : CGroupby α κ) (tgtkey : κ) : CGroupby α κ :=
  { g with groupers := g.groupers ++ [tgtkey], currgrouper := some g.groupers.length }

/-- `groupby_next` (:532-575). `currgrouper` is cleared first (:537), so the
current group is invalidated even when this call then fails.

After the loop's `break` the C code reads `gbo->currkey` unchecked (:567). The
loop re-reads nothing after the comparison, so a hook that cleared it leaves
`Py_INCREF(NULL)`: that is `crash`. -/
def gbNext (K : KeyEq κ) (key : α → Py κ) (run : List (GbOp κ) → GbState α κ → GbState α κ)
    (s : GbState α κ) : GbRes κ × GbState α κ :=
  let s := { s with g := { s.g with currgrouper := none } }
  match gbSkip K key run (s.g.it.length + 1) s with
  | (some e, s) => (gbFail e, s)
  | (none, s) =>
    match s.g.currkey with
    | none => (.crash, { s with crashed := true })
    | some ck => (.val ck, { s with g := gbCreate { s.g with tgtkey := some ck } ck })

/-- `gbo->currvalue` as a result. -/
def gbValue {β : Type} : Option β → GbRes β
  | none => .stop
  | some v => .val v

/-- `_grouper_next` (:662-696). `currkey` is not null at :682 (`assert` at :676):
`groupby_step` sets it with `currvalue`, and :692-693 clear them together.
`rcmp <= 0` is :687-689: `-1` is the exception, `0` the end of the group. The
hook may have taken `currvalue`, and then `r` is `NULL` at :691: a plain stop. -/
def gbGrouperNext [Inhabited κ] (K : KeyEq κ) (key : α → Py κ)
    (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ) (j : Nat) :
    GbRes α × GbState α κ :=
  if s.g.currgrouper != some j then (.stop, s)
  else
    match (if s.g.currvalue.isNone then gbStep key s else (.ok, s)) with
    | (.fail e, s) => (gbFail e, s)
    | (.ok, s) =>
      match gbEq K run s (s.g.groupers.getD j default) (s.g.currkey.getD default) with
      | (.error e, s) => (.exc e, s)
      | (.ok false, s) => (.stop, s)
      | (.ok true, s) =>
        (gbValue s.g.currvalue, { s with g := { s.g with currvalue := none, currkey := none } })

/-- One operation; its result joins the log when it returns, so results of
operations a hook ran come first. -/
def gbOp [Inhabited κ] (K : KeyEq κ) (key : α → Py κ) (run : List (GbOp κ) → GbState α κ → GbState α κ) :
    GbOp κ → GbState α κ → GbState α κ
  | .outer, s => let (r, s) := gbNext K key run s; { s with log := s.log ++ [.inl r] }
  | .group j, s =>
    if j < s.g.groupers.length then
      let (r, s) := gbGrouperNext K key run s j
      { s with log := s.log ++ [.inr r] }
    else s
  | .direct k, s => { s with g := gbCreate s.g k }

def gbFold [Inhabited κ] (K : KeyEq κ) (key : α → Py κ) (run : List (GbOp κ) → GbState α κ → GbState α κ)
    (ops : List (GbOp κ)) (s : GbState α κ) : GbState α κ :=
  ops.foldl (fun s op => gbOp K key run op s) s

/-- Runs operations. Each hook is used once, so `hooks.length + 1` levels are
enough. -/
def gbRun [Inhabited κ] (K : KeyEq κ) (key : α → Py κ) : Nat → List (GbOp κ) → GbState α κ → GbState α κ
  | 0, _, s => s
  | d + 1, ops, s => gbFold K key (gbRun K key d) ops s

/-- `itertools_groupby_impl` (:456-475). -/
def gbInit (iterable : Obj α) (hooks : List (List (GbOp κ))) : Py (GbState α κ) :=
  match getIter iterable with
  | .error e => .error e
  | .ok ⟨l, err⟩ =>
    .ok { g := { it := l, tgtkey := none, currkey := none, currvalue := none,
                 currgrouper := none, groupers := [] }, err := err, hooks := hooks }

/-- `groupby(iterable, key)`, then the operations: the results, and whether the
process died. -/
def cGroupbyR [Inhabited κ] (K : KeyEq κ) (key : α → Py κ) (iterable : Obj α)
    (hooks : List (List (GbOp κ))) (ops : List (GbOp κ)) :
    Py (List (GbRes κ ⊕ GbRes α) × Bool) :=
  match gbInit iterable hooks with
  | .error e => .error e
  | .ok s =>
    let s := gbRun K key (hooks.length + 1) ops s
    .ok (s.log, s.crashed)

/-! ## When nothing raises or re-enters this is the model of `GroupbyTee.lean` -/

/-- A key function that does not raise. -/
def pureKey (key : α → κ) : α → Py κ := fun x => .ok (key x)

/-- Comparison on a key type with decidable equality, which does not raise. -/
def decEq (κ : Type) [DecidableEq κ] : KeyEq κ := ⟨fun a b => a == b, fun a b => .ok (a == b)⟩

def liftRes : Option κ ⊕ Option α → GbRes κ ⊕ GbRes α
  | .inl r => .inl (gbValue r)
  | .inr r => .inr (gbValue r)

theorem gbFold_cons [Inhabited κ] (K : KeyEq κ) (key : α → Py κ)
    (run : List (GbOp κ) → GbState α κ → GbState α κ) (op : GbOp κ) (ops : List (GbOp κ)) (s : GbState α κ) :
    gbFold K key run (op :: ops) s = gbFold K key run ops (gbOp K key run op s) := rfl

section Pure

variable [Inhabited α] [Inhabited κ] [DecidableEq κ]
variable (run : List (GbOp κ) → GbState α κ → GbState α κ)

theorem gbEq_pure (s : GbState α κ) (h : s.hooks = []) (a b : κ) :
    gbEq (decEq κ) run s a b = (.ok (a == b), s) := by
  simp only [gbEq, decEq]
  by_cases hab : (a == b) = true
  · simp [hab]
  · simp [hab, h]

theorem gbStep_pure (key : α → κ) (s : GbState α κ) (he : s.err = none) :
    gbStep (pureKey key) s =
      match cGroupbyStep key s.g with
      | none => (.fail none, s)
      | some g' => (.ok, { s with g := g' }) := by
  simp only [gbStep, cGroupbyStep]
  cases h : s.g.it with
  | nil => simp [he]
  | cons v rest => simp [pureKey]

theorem gbSkip_pure (key : α → κ) : ∀ (fuel : Nat) (s : GbState α κ), s.err = none → s.hooks = [] →
    gbSkip (decEq κ) (pureKey key) run fuel s =
      (if (cGroupbySkip key fuel s.g).1 then none else some none,
        { s with g := (cGroupbySkip key fuel s.g).2 })
  | 0, s, _, _ => by simp [gbSkip, cGroupbySkip]
  | fuel + 1, s, he, hh => by
    have step : gbThen (fun s => gbSkip (decEq κ) (pureKey key) run fuel s) (gbStep (pureKey key) s) =
        match cGroupbyStep key s.g with
        | none => (some none, s)
        | some g' =>
          (if (cGroupbySkip key fuel g').1 then none else some none,
            { s with g := (cGroupbySkip key fuel g').2 }) := by
      rw [gbStep_pure key s he]
      cases hs : cGroupbyStep key s.g with
      | none => rfl
      | some g' => exact gbSkip_pure key fuel { s with g := g' } he hh
    have hcases : s.g.currkey = none ∨ ∃ ck, s.g.currkey = some ck := by
      cases s.g.currkey <;> simp
    have htases : s.g.tgtkey = none ∨ ∃ tk, s.g.tgtkey = some tk := by
      cases s.g.tgtkey <;> simp
    simp only [gbSkip, cGroupbySkip]
    rcases hcases with hc | ⟨ck, hc⟩
    · simp only [hc, gbAdvance, Bool.not_true, Bool.false_eq_true, if_false]
      rw [step]
      cases hs : cGroupbyStep key s.g with
      | none => simp
      | some g' => rfl
    · rcases htases with ht | ⟨tk, ht⟩
      · simp [hc, ht, gbAdvance]
      · simp only [hc, ht, gbEq_pure run s hh tk ck, gbAdvance]
        cases hb : (tk == ck) with
        | false => simp
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, if_false]
          rw [step]
          cases hs : cGroupbyStep key s.g with
          | none => simp
          | some g' => rfl

/-- A `true` from `cGroupbySkip` is the `break`, so `currkey` is set. -/
theorem cGroupbySkip_true_currkey (key : α → κ) : ∀ (fuel : Nat) (g : CGroupby α κ),
    (cGroupbySkip key fuel g).1 = true → (cGroupbySkip key fuel g).2.currkey.isSome = true
  | 0, g, h => by simp [cGroupbySkip] at h
  | fuel + 1, g, h => by
    simp only [cGroupbySkip] at h ⊢
    by_cases ha : gbAdvance g.currkey g.tgtkey = true
    · simp only [ha, Bool.not_true, Bool.false_eq_true, if_false] at h ⊢
      cases hs : cGroupbyStep key g with
      | none => simp [hs] at h
      | some g' =>
        simp only [hs] at h ⊢
        exact cGroupbySkip_true_currkey key fuel g' h
    · have hna : gbAdvance g.currkey g.tgtkey = false := by simpa using ha
      simp only [hna, Bool.not_false, if_true] at h ⊢
      cases hc : g.currkey with
      | none => simp [gbAdvance, hc] at hna
      | some _ => simp

theorem gbNext_pure (key : α → κ) (s : GbState α κ) (he : s.err = none) (hh : s.hooks = []) :
    gbNext (decEq κ) (pureKey key) run s =
      (gbValue (cGroupbyNext key s.g).1, { s with g := (cGroupbyNext key s.g).2 }) := by
  simp only [gbNext, cGroupbyNext]
  rw [gbSkip_pure run key _ { s with g := { s.g with currgrouper := none } } he hh]
  have hkey := cGroupbySkip_true_currkey key (s.g.it.length + 1) { s.g with currgrouper := none }
  cases hs : cGroupbySkip key (s.g.it.length + 1) { s.g with currgrouper := none } with
  | mk f g' =>
    rw [hs] at hkey
    cases f with
    | false => simp [gbFail, gbValue]
    | true =>
      have hc := hkey rfl
      cases hk : g'.currkey with
      | none => simp [hk] at hc
      | some ck =>
        simp [hk, gbValue, cGrouperCreate, gbCreate]

theorem gbGrouperNext_pure (key : α → κ) (s : GbState α κ) (j : Nat) (he : s.err = none) (hh : s.hooks = []) :
    gbGrouperNext (decEq κ) (pureKey key) run s j =
      (gbValue (cGrouperNext key s.g j).1, { s with g := (cGrouperNext key s.g j).2 }) := by
  simp only [gbGrouperNext, cGrouperNext]
  by_cases hc : (s.g.currgrouper != some j) = true
  · simp [hc, gbValue]
  · simp only [hc, Bool.false_eq_true, if_false]
    cases hv : s.g.currvalue.isNone with
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [gbEq_pure run s hh]
      cases hb : (s.g.groupers.getD j default == s.g.currkey.getD default) <;> simp [gbValue]
    | true =>
      simp only [if_true, gbStep_pure key s he]
      cases hs : cGroupbyStep key s.g with
      | none => simp [gbFail, gbValue]
      | some g' =>
        simp only
        rw [gbEq_pure run { s with g := g' } hh]
        cases hb : (g'.groupers.getD j default == g'.currkey.getD default) <;> simp [gbValue]

/-- With a key function, input and comparison that do not raise or re-enter, the
two models give the same answers to every sequence of operations, and the
process does not die. -/
theorem gbFold_pure (key : α → κ) : ∀ (ops : List (GbOp κ)) (s : GbState α κ), s.err = none → s.hooks = [] →
    (gbFold (decEq κ) (pureKey key) run ops s).log = s.log ++ (cGroupbyOps key s.g ops).map liftRes ∧
      (gbFold (decEq κ) (pureKey key) run ops s).crashed = s.crashed
  | [], s, _, _ => by simp [gbFold, cGroupbyOps]
  | .outer :: ops, s, he, hh => by
    rw [gbFold_cons]
    have hs : gbOp (decEq κ) (pureKey key) run .outer s =
        { s with g := (cGroupbyNext key s.g).2, log := s.log ++ [.inl (gbValue (cGroupbyNext key s.g).1)] } := by
      simp only [gbOp, gbNext_pure run key s he hh]
    rw [hs]
    obtain ⟨h1, h2⟩ := gbFold_pure key ops
      { s with g := (cGroupbyNext key s.g).2, log := s.log ++ [.inl (gbValue (cGroupbyNext key s.g).1)] } he hh
    refine ⟨?_, h2⟩
    rw [h1]
    simp [cGroupbyOps, liftRes]
  | .group j :: ops, s, he, hh => by
    rw [gbFold_cons]
    by_cases hj : j < s.g.groupers.length
    · have hs : gbOp (decEq κ) (pureKey key) run (.group j) s =
          { s with g := (cGrouperNext key s.g j).2, log := s.log ++ [.inr (gbValue (cGrouperNext key s.g j).1)] } := by
        simp only [gbOp, hj, if_true, gbGrouperNext_pure run key s j he hh]
      rw [hs]
      obtain ⟨h1, h2⟩ := gbFold_pure key ops
        { s with g := (cGrouperNext key s.g j).2, log := s.log ++ [.inr (gbValue (cGrouperNext key s.g j).1)] } he hh
      refine ⟨?_, h2⟩
      rw [h1]
      simp [cGroupbyOps, hj, liftRes]
    · have hs : gbOp (decEq κ) (pureKey key) run (.group j) s = s := by simp [gbOp, hj]
      rw [hs]
      obtain ⟨h1, h2⟩ := gbFold_pure key ops s he hh
      exact ⟨by rw [h1]; simp [cGroupbyOps, hj], h2⟩
  | .direct k :: ops, s, he, hh => by
    rw [gbFold_cons]
    have hs : gbOp (decEq κ) (pureKey key) run (.direct k) s = { s with g := cGrouperDirect s.g k } := by
      simp [gbOp, gbCreate, cGrouperDirect, cGrouperCreate]
    rw [hs]
    obtain ⟨h1, h2⟩ := gbFold_pure key ops { s with g := cGrouperDirect s.g k } he hh
    exact ⟨by rw [h1]; simp [cGroupbyOps], h2⟩

end Pure

/-! ## Properties -/

/-- For every key function that does not raise, every input object that does
not raise after its items, keys with decidable equality, and every interleaving
of `next()` on the groupby object and on any group it returned (including old
groups), the C object answers exactly as the doc's generators, over any element
and key type. A non-iterable input raises in both. Nothing re-enters.

Hypotheses, all preconditions: the callbacks and the input do not raise and do
not re-enter. The doc's generators die at their first exception and the C
object does not, so past an exception there is nothing to agree on;
`GroupbyEqError` and `GroupbyFailedStepKeepsState` say what C does there. -/
def GroupbyDocAgreeR : Prop :=
  ∀ (α κ : Type) [Inhabited α] [Inhabited κ] [DecidableEq κ] (key : α → κ) (o : Obj α)
    (ops : List (GbOp κ)), (∀ op ∈ ops, op.isPublic = true) →
    (∀ l e, o = .iter l (some e) → False) →
    cGroupbyR (decEq κ) (pureKey key) o [] ops = (docGroupby key o ops).map (fun r => (r.map liftRes, false))

theorem groupbyDocAgreeR_proven : GroupbyDocAgreeR := by
  intro α κ _ _ _ key o ops hp hnr
  cases o with
  | notIterable ty => simp [cGroupbyR, gbInit, getIter, docGroupby, Except.map]
  | iter l err =>
    cases err with
    | some e => exact (hnr l e rfl).elim
    | none =>
      have h := groupbyDocAgree_proven α κ key (.iter l none) ops hp
      rw [← h]
      simp only [cGroupbyR, gbInit, cGroupby, cGroupbyNew, getIter, gbRun]
      obtain ⟨h1, h2⟩ := gbFold_pure (gbRun (decEq κ) (pureKey key) ([] : List (List (GbOp κ))).length) key ops
        { g := { it := l, tgtkey := none, currkey := none, currvalue := none, currgrouper := none,
                 groupers := [] }, err := none } rfl rfl
      rw [h1, h2]
      simp [Except.map]

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

theorem gbGrouperNext_compare [Inhabited κ] (K : KeyEq κ) (key : α → Py κ)
    (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ) (j : Nat) (v : α) (ck : κ)
    (r : Py Bool) (hh : s.hooks = []) (hj : s.g.currgrouper = some j) (hv : s.g.currvalue = some v)
    (hc : s.g.currkey = some ck) (h1 : K.same (s.g.groupers.getD j default) ck = false)
    (h2 : K.eq (s.g.groupers.getD j default) ck = r) :
    gbGrouperNext K key run s j =
      match r with
      | .error e => (.exc e, s)
      | .ok false => (.stop, s)
      | .ok true => (gbValue s.g.currvalue, { s with g := { s.g with currvalue := none, currkey := none } }) := by
  have hq : gbEq K run s (s.g.groupers.getD j default) ck = (r, s) := by
    simp only [gbEq, h1, Bool.false_eq_true, if_false, hh, h2]
  simp only [gbGrouperNext, hj, bne_self_eq_false, Bool.false_eq_true, if_false, hv, Option.isNone_some,
    hc, Option.getD_some, hq]
  cases r with
  | error e => rfl
  | ok b =>
    cases b with
    | false => rfl
    | true => simp [hj, hv]

/-- For every comparison, key function and state: when the keys are not the same
object, nothing re-enters and `__eq__` raises, `groupby_next` and `_grouper_next`
propagate exactly that exception. `groupby_next` leaves every field but
`currgrouper` as it was (:558-559), so the object stays usable; `_grouper_next`
changes nothing at all (:687-689). -/
def GroupbyEqError : Prop :=
  ∀ (α κ : Type) [Inhabited κ] (K : KeyEq κ) (key : α → Py κ)
    (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ) (e : PyExc) (ck tk : κ),
    s.hooks = [] → s.g.tgtkey = some tk → s.g.currkey = some ck →
    (K.same tk ck = false ∧ K.eq tk ck = .error e →
      gbNext K key run s = (.exc e, { s with g := { s.g with currgrouper := none } })) ∧
    (∀ (j : Nat) (v : α), s.g.currgrouper = some j → s.g.currvalue = some v →
      K.same (s.g.groupers.getD j default) ck = false → K.eq (s.g.groupers.getD j default) ck = .error e →
      gbGrouperNext K key run s j = (.exc e, s))

theorem groupbyEqError_proven : GroupbyEqError := by
  intro α κ _ K key run s e ck tk hh ht hc
  constructor
  · rintro ⟨h1, h2⟩
    simp [gbNext, gbSkip, ht, hc, gbEq, h1, h2, hh, gbFail]
  · intro j v hj hv h1 h2
    exact gbGrouperNext_compare K key run s j v ck _ hh hj hv hc h1 h2

/-- `_grouper_next` on a comparison that answers false ends the group and
changes nothing, for every comparison and state (`rcmp == 0`, :687-689). -/
def GrouperEqFalseStops : Prop :=
  ∀ (α κ : Type) [Inhabited κ] (K : KeyEq κ) (key : α → Py κ)
    (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ) (j : Nat) (v : α) (ck : κ),
    s.hooks = [] → s.g.currgrouper = some j → s.g.currvalue = some v → s.g.currkey = some ck →
    K.same (s.g.groupers.getD j default) ck = false → K.eq (s.g.groupers.getD j default) ck = .ok false →
    gbGrouperNext K key run s j = (.stop, s)

theorem grouperEqFalseStops_proven : GrouperEqFalseStops := by
  intro α κ _ K key run s j v ck hh hj hv hc h1 h2
  exact gbGrouperNext_compare K key run s j v ck _ hh hj hv hc h1 h2

/-- `itertools._grouper(groupby_obj, k)` makes the new group current: every
group created before it stops at once and leaves the state alone, whatever the
comparison, key function, input and hooks would do. -/
def GrouperDirectInvalidates : Prop :=
  ∀ (α κ : Type) [Inhabited κ] (K : KeyEq κ) (key : α → Py κ)
    (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ) (k : κ) (j : Nat),
    j < s.g.groupers.length →
    gbGrouperNext K key run { s with g := gbCreate s.g k } j = (.stop, { s with g := gbCreate s.g k })

theorem grouperDirectInvalidates_proven : GrouperDirectInvalidates := by
  intro α κ _ K key run s k j hj
  have h : (gbCreate s.g k).currgrouper ≠ some j := by
    simp only [gbCreate]
    intro h
    simp only [Option.some.injEq] at h
    omega
  simp [gbGrouperNext, h]

/-- Without re-entrancy the process cannot die: for every comparison (which may
raise), key function and input (which may raise) and every sequence of
operations. The `break` of `groupby_next` is only taken with `currkey` set. -/
def GroupbyNoCrashWithoutHooks : Prop :=
  ∀ (α κ : Type) [Inhabited κ] (K : KeyEq κ) (key : α → Py κ) (o : Obj α) (ops : List (GbOp κ))
    (s : GbState α κ), gbInit o [] = .ok s → (gbRun K key 1 ops s).crashed = false

theorem gbStep_keeps (key : α → Py κ) (s : GbState α κ) :
    (gbStep key s).2.hooks = s.hooks ∧ (gbStep key s).2.crashed = s.crashed := by
  simp only [gbStep]
  cases hi : s.g.it with
  | nil => cases he : s.err <;> simp
  | cons v rest => cases hk : key v <;> simp [hk]

theorem gbEq_nohook (K : KeyEq κ) (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ)
    (a b : κ) (hh : s.hooks = []) : (gbEq K run s a b).2 = s := by
  simp only [gbEq]
  split <;> simp [hh]

/-- What the skip loop preserves when nothing re-enters; its `break` has `currkey`. -/
theorem gbSkip_nohook (K : KeyEq κ) (key : α → Py κ) (run : List (GbOp κ) → GbState α κ → GbState α κ) :
    ∀ (fuel : Nat) (s : GbState α κ), s.hooks = [] →
      (gbSkip K key run fuel s).2.hooks = [] ∧ (gbSkip K key run fuel s).2.crashed = s.crashed ∧
        ((gbSkip K key run fuel s).1 = none → (gbSkip K key run fuel s).2.g.currkey.isSome = true)
  | 0, s, hh => by simp [gbSkip, hh]
  | fuel + 1, s, hh => by
    have step : (gbThen (fun s => gbSkip K key run fuel s) (gbStep key s)).2.hooks = [] ∧
        (gbThen (fun s => gbSkip K key run fuel s) (gbStep key s)).2.crashed = s.crashed ∧
        ((gbThen (fun s => gbSkip K key run fuel s) (gbStep key s)).1 = none →
          (gbThen (fun s => gbSkip K key run fuel s) (gbStep key s)).2.g.currkey.isSome = true) := by
      obtain ⟨k1, k2⟩ := gbStep_keeps key s
      cases hs : gbStep key s with
      | mk r s' =>
        rw [hs] at k1 k2
        simp only at k1 k2
        cases r with
        | fail e => simp [gbThen, k1, k2, hh]
        | ok =>
          have := gbSkip_nohook K key run fuel s' (by rw [k1, hh])
          simp only [gbThen]
          exact ⟨this.1, by rw [this.2.1, k2], this.2.2⟩
    simp only [gbSkip]
    cases hc : s.g.currkey with
    | none => exact step
    | some ck =>
      cases ht : s.g.tgtkey with
      | none => simp [hc, hh]
      | some tk =>
        simp only
        have hq := gbEq_nohook K run s tk ck hh
        cases he : gbEq K run s tk ck with
        | mk r s' =>
          rw [he] at hq
          simp only at hq
          subst hq
          cases r with
          | error e => simp [hh]
          | ok b =>
            cases b with
            | false => simp [hc, hh]
            | true => exact step

theorem gbNext_nohook (K : KeyEq κ) (key : α → Py κ) (run : List (GbOp κ) → GbState α κ → GbState α κ)
    (s : GbState α κ) (hh : s.hooks = []) (hc : s.crashed = false) :
    (gbNext K key run s).2.hooks = [] ∧ (gbNext K key run s).2.crashed = false := by
  simp only [gbNext]
  obtain ⟨h1, h2, h3⟩ := gbSkip_nohook K key run (s.g.it.length + 1)
    { s with g := { s.g with currgrouper := none } } hh
  cases hs : gbSkip K key run (s.g.it.length + 1) { s with g := { s.g with currgrouper := none } } with
  | mk r s' =>
    rw [hs] at h1 h2 h3
    simp only at h1 h2 h3
    have h2' : s'.crashed = false := h2.trans hc
    cases r with
    | some e => simpa using ⟨h1, h2'⟩
    | none =>
      have hk := h3 rfl
      cases hk' : s'.g.currkey with
      | none => simp [hk'] at hk
      | some ck => simpa [hk'] using ⟨h1, h2'⟩

theorem gbGrouperNext_nohook [Inhabited κ] (K : KeyEq κ) (key : α → Py κ)
    (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ) (j : Nat)
    (hh : s.hooks = []) (hc : s.crashed = false) :
    (gbGrouperNext K key run s j).2.hooks = [] ∧ (gbGrouperNext K key run s j).2.crashed = false := by
  simp only [gbGrouperNext]
  by_cases h : (s.g.currgrouper != some j) = true
  · simp [h, hh, hc]
  · simp only [h, Bool.false_eq_true, if_false]
    have hr : (if s.g.currvalue.isNone then gbStep key s else (GbStep.ok, s)).2.hooks = [] ∧
        (if s.g.currvalue.isNone then gbStep key s else (GbStep.ok, s)).2.crashed = false := by
      obtain ⟨k1, k2⟩ := gbStep_keeps key s
      split
      · exact ⟨k1.trans hh, k2.trans hc⟩
      · exact ⟨hh, hc⟩
    cases hq : (if s.g.currvalue.isNone then gbStep key s else (GbStep.ok, s)) with
    | mk r s1 =>
      rw [hq] at hr
      simp only at hr
      cases r with
      | fail e => exact hr
      | ok =>
        simp only
        have he := gbEq_nohook K run s1 (s1.g.groupers.getD j default) (s1.g.currkey.getD default) hr.1
        cases hc2 : gbEq K run s1 (s1.g.groupers.getD j default) (s1.g.currkey.getD default) with
        | mk c s2 =>
          rw [hc2] at he
          simp only at he
          subst he
          cases c with
          | error e => exact hr
          | ok b =>
            cases b with
            | false => exact hr
            | true => exact hr

theorem gbOp_nohook [Inhabited κ] (K : KeyEq κ) (key : α → Py κ)
    (run : List (GbOp κ) → GbState α κ → GbState α κ) (op : GbOp κ) (s : GbState α κ)
    (hh : s.hooks = []) (hc : s.crashed = false) :
    (gbOp K key run op s).hooks = [] ∧ (gbOp K key run op s).crashed = false := by
  cases op with
  | outer =>
    have := gbNext_nohook K key run s hh hc
    simp only [gbOp]
    exact this
  | group j =>
    simp only [gbOp]
    split
    · exact gbGrouperNext_nohook K key run s j hh hc
    · exact ⟨hh, hc⟩
  | direct k => exact ⟨hh, hc⟩

theorem gbFold_nohook [Inhabited κ] (K : KeyEq κ) (key : α → Py κ)
    (run : List (GbOp κ) → GbState α κ → GbState α κ) :
    ∀ (ops : List (GbOp κ)) (s : GbState α κ), s.hooks = [] → s.crashed = false →
      (gbFold K key run ops s).crashed = false
  | [], _, _, hc => hc
  | op :: ops, s, hh, hc => by
    rw [gbFold_cons]
    obtain ⟨h1, h2⟩ := gbOp_nohook K key run op s hh hc
    exact gbFold_nohook K key run ops _ h1 h2

theorem groupbyNoCrashWithoutHooks_proven : GroupbyNoCrashWithoutHooks := by
  intro α κ _ K key o ops s hs
  simp only [gbInit] at hs
  cases hi : getIter o with
  | error e => simp [hi] at hs
  | ok src =>
    rw [hi] at hs
    simp only [Except.ok.injEq] at hs
    subst hs
    exact gbFold_nohook K key _ ops _ rfl rfl

/-- Did this run kill the process? -/
def gbCrashes [Inhabited κ] (K : KeyEq κ) (key : α → Py κ) (iterable : Obj α)
    (hooks : List (List (GbOp κ))) (ops : List (GbOp κ)) : Bool :=
  match cGroupbyR K key iterable hooks ops with
  | .ok r => r.2
  | .error _ => false

/-- Invariant: Python code cannot crash the interpreter. For every comparison,
key function, input, re-entrant `__eq__` and sequence of operations, the process
survives. -/
def GroupbyNoCrash : Prop :=
  ∀ (α κ : Type) [Inhabited κ] (K : KeyEq κ) (key : α → Py κ) (o : Obj α)
    (hooks : List (List (GbOp κ))) (ops : List (GbOp κ)), gbCrashes K key o hooks ops = false

/-- Keys are distinct objects that compare unequal. `__eq__` re-enters once: it
starts a new group and reads it, which clears `currkey`, then answers false, and
`groupby_next` takes the `break` onto a null `currkey`. -/
theorem groupbyNoCrash_refuted : ¬GroupbyNoCrash := by
  intro h
  have := h Nat Nat ⟨fun a b => a == b, fun _ _ => .ok false⟩ (fun x => .ok x)
    (.iter [1, 2, 3, 4, 5, 6] none) [[.outer, .group 1]] [.outer, .outer]
  revert this
  decide

end PyLean.Itertools
