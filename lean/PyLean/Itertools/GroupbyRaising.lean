import PyLean.Itertools.GroupbyProps

/-!
`groupby` with everything that can fail or re-enter: this is the mirror of
`groupby_step` (Modules/itertoolsmodule.c:505-529), `groupby_next` (:532-575)
and `_grouper_next` (:662-696). The input may raise after its items, the key
function may raise on any item, and key comparison is a `KeyEq`: it may raise.
The comparison, the key function and the input may each re-enter the groupby
object and its groups.

Re-entrancy is the real code path, not a state change written by hand: `hooks`,
`keyHooks` and `iterHooks` hold, for successive `__eq__` calls, key-function
calls and items of the input, the operations that call performs on the same
object, and they run through `gbRun`, the function that runs top-level
operations. The Python caller catches what those operations raise. The input's
operations run after it has taken its item and before it returns it (as a
`map` function does), so a re-entrant call reads the items after it; the key
function's run before it answers.

`GroupbyTee.lean` has the same three functions without those branches, which
is what the simulation of the doc's generators in `GroupbyProps.lean` runs on.
`gbFold_pure` shows the two coincide when nothing raises or re-enters, so that
proof applies to this model.

`groupby_step` re-reads nothing after the input and the key function return: it
writes `currvalue` and `currkey` (:524-527) over whatever a re-entrant call left
there. `_grouper_next` checks `currgrouper` (:669) and `currvalue` (:670) before
the step and neither after it, so a group whose callback re-entered still
compares and returns the item it pulled, even when the re-entrant call made
another group current, and the value that call left current is released unseen.
`dropped` records those values (the `oldvalue` of :524 and :527 when
`_grouper_next` calls the step); it is ghost state, not a field of the C object.
The same overwrite inside `groupby_next`'s loop releases values by design (they
belong to the group being skipped) and is not recorded.

Not modelled: `_grouper_create` running out of memory; the finalizers of the
values the object releases; a key function `None` with key hooks (it calls no
Python code, so its `keyHooks` must be empty).
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
  keyHooks : List (List (GbOp κ)) := []
  iterHooks : List (List (GbOp κ)) := []
  log : List (GbRes κ ⊕ GbRes α) := []
  dropped : List α := []
  crashed : Bool := false

/-- The return of `groupby_step`: `0`, with the `oldvalue` it released
(:524, :527), or `-1` with exception `e` set (`none`: the input ended, nothing
is set). -/
inductive GbStep (α : Type) where
  | ok (old : Option α)
  | fail (e : Option PyExc)

/-- The Python code the input's `__next__` runs for the item it has taken. -/
def gbIterHook (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ) : GbState α κ :=
  match s.iterHooks with
  | [] => s
  | h :: hs => run h { s with iterHooks := hs }

/-- The Python code a key-function call runs before it answers. -/
def gbKeyHook (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ) : GbState α κ :=
  match s.keyHooks with
  | [] => s
  | h :: hs => run h { s with keyHooks := hs }

/-- `groupby_step` (:505-529). `PyIter_Next` (:510) has taken the item before the
key function runs (:517), so a raising key loses that item (:517-521). Both calls
may run Python code. `currvalue` and `currkey` are assigned only after both
succeeded (:524-527), over whatever is there then, and that old value is
released. -/
def gbStep (key : α → Py κ) (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ) :
    GbStep α × GbState α κ :=
  match s.g.it with
  | [] =>
    match s.err with
    | none => (.fail none, s)
    | some e => (.fail (some e), { s with err := none })
  | v :: rest =>
    let s := gbKeyHook run (gbIterHook run { s with g := { s.g with it := rest } })
    match key v with
    | .error e => (.fail (some e), s)
    | .ok k => (.ok s.g.currvalue, { s with g := { s.g with currvalue := some v, currkey := some k } })

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
    GbStep α × GbState α κ → Option (Option PyExc) × GbState α κ
  | (.fail e, s) => (some e, s)
  | (.ok _, s) => k s

/-- The `for (;;)` loop of `groupby_next` (:539-566): `none` is the `break`, and
`some e` a `return NULL`, after a failed comparison (:558-559) or a failed
`groupby_step` (:564-565). Each iteration but the last takes an item, so
`it.length + 1` iterations are enough, whatever a hook takes. The loop re-reads
`currkey` and `tgtkey` on every iteration (:540, :542, :549-550). -/
def gbSkip (K : KeyEq κ) (key : α → Py κ) (run : List (GbOp κ) → GbState α κ → GbState α κ) :
    Nat → GbState α κ → Option (Option PyExc) × GbState α κ
  | 0, s => (some none, s)
  | fuel + 1, s =>
    match s.g.currkey, s.g.tgtkey with
    | none, _ => gbThen (fun s => gbSkip K key run fuel s) (gbStep key run s)
    | some _, none => (none, s)
    | some ck, some tk =>
      match gbEq K run s tk ck with
      | (.error e, s) => (some (some e), s)
      | (.ok false, s) => (none, s)
      | (.ok true, s) => gbThen (fun s => gbSkip K key run fuel s) (gbStep key run s)

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

/-- :674-695 of `_grouper_next`: compare the group's key with `currkey` (:681-683),
then on a match return `currvalue` and clear it with `currkey` (:691-693). -/
def gbGrouperCmp [Inhabited κ] (K : KeyEq κ) (run : List (GbOp κ) → GbState α κ → GbState α κ)
    (s : GbState α κ) (j : Nat) : GbRes α × GbState α κ :=
  match gbEq K run s (s.g.groupers.getD j default) (s.g.currkey.getD default) with
  | (.error e, s) => (.exc e, s)
  | (.ok false, s) => (.stop, s)
  | (.ok true, s) => (gbValue s.g.currvalue, { s with g := { s.g with currvalue := none, currkey := none } })

/-- `_grouper_next` (:662-696). `currgrouper` (:669) and `currvalue` (:670) are
checked before `groupby_step` (:671-672) and not after it, so what its callbacks
did is not looked at: the comparison reads the group's own key and the live
`currkey` (:681-682). The value the step released is `dropped`. `currkey` is not
null at :682 (`assert` at :676): `groupby_step` sets it with `currvalue`, and
:692-693 clear them together. `rcmp <= 0` is :687-689: `-1` is the exception,
`0` the end of the group. A comparison hook may have taken `currvalue`, and then
`r` is `NULL` at :691: a plain stop. -/
def gbGrouperNext [Inhabited κ] (K : KeyEq κ) (key : α → Py κ)
    (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ) (j : Nat) :
    GbRes α × GbState α κ :=
  if s.g.currgrouper != some j then (.stop, s)
  else
    match (if s.g.currvalue.isNone then gbStep key run s else (.ok none, s)) with
    | (.fail e, s) => (gbFail e, s)
    | (.ok none, s) => gbGrouperCmp K run s j
    | (.ok (some o), s) => gbGrouperCmp K run { s with dropped := s.dropped ++ [o] } j

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

/-- Runs operations. Each hook is used once, so one level more than there are
hooks is enough. -/
def gbRun [Inhabited κ] (K : KeyEq κ) (key : α → Py κ) : Nat → List (GbOp κ) → GbState α κ → GbState α κ
  | 0, _, s => s
  | d + 1, ops, s => gbFold K key (gbRun K key d) ops s

/-- `itertools_groupby_impl` (:456-475). -/
def gbInit (iterable : Obj α) (hooks : List (List (GbOp κ)))
    (keyHooks : List (List (GbOp κ)) := []) (iterHooks : List (List (GbOp κ)) := []) :
    Py (GbState α κ) :=
  match getIter iterable with
  | .error e => .error e
  | .ok ⟨l, err⟩ =>
    .ok { g := { it := l, tgtkey := none, currkey := none, currvalue := none,
                 currgrouper := none, groupers := [] }, err := err, hooks := hooks,
          keyHooks := keyHooks, iterHooks := iterHooks }

/-- `groupby(iterable, key)`, then the operations: the final state. -/
def cGroupbyS [Inhabited κ] (K : KeyEq κ) (key : α → Py κ) (iterable : Obj α)
    (hooks : List (List (GbOp κ))) (ops : List (GbOp κ))
    (keyHooks : List (List (GbOp κ)) := []) (iterHooks : List (List (GbOp κ)) := []) :
    Py (GbState α κ) :=
  match gbInit iterable hooks keyHooks iterHooks with
  | .error e => .error e
  | .ok s => .ok (gbRun K key (hooks.length + keyHooks.length + iterHooks.length + 1) ops s)

/-- `groupby(iterable, key)`, then the operations: the results, and whether the
process died. -/
def cGroupbyR [Inhabited κ] (K : KeyEq κ) (key : α → Py κ) (iterable : Obj α)
    (hooks : List (List (GbOp κ))) (ops : List (GbOp κ))
    (keyHooks : List (List (GbOp κ)) := []) (iterHooks : List (List (GbOp κ)) := []) :
    Py (List (GbRes κ ⊕ GbRes α) × Bool) :=
  match cGroupbyS K key iterable hooks ops keyHooks iterHooks with
  | .error e => .error e
  | .ok s => .ok (s.log, s.crashed)

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

theorem gbStep_pure (key : α → κ) (s : GbState α κ) (he : s.err = none) (hk : s.keyHooks = [])
    (hi : s.iterHooks = []) :
    gbStep (pureKey key) run s =
      match cGroupbyStep key s.g with
      | none => (.fail none, s)
      | some g' => (.ok s.g.currvalue, { s with g := g' }) := by
  simp only [gbStep, cGroupbyStep]
  cases h : s.g.it with
  | nil => simp [he]
  | cons v rest => simp [pureKey, gbIterHook, gbKeyHook, hk, hi]

theorem gbSkip_pure (key : α → κ) : ∀ (fuel : Nat) (s : GbState α κ), s.err = none → s.hooks = [] →
    s.keyHooks = [] → s.iterHooks = [] →
    gbSkip (decEq κ) (pureKey key) run fuel s =
      (if (cGroupbySkip key fuel s.g).1 then none else some none,
        { s with g := (cGroupbySkip key fuel s.g).2 })
  | 0, s, _, _, _, _ => by simp [gbSkip, cGroupbySkip]
  | fuel + 1, s, he, hh, hk, hi => by
    have step : gbThen (fun s => gbSkip (decEq κ) (pureKey key) run fuel s) (gbStep (pureKey key) run s) =
        match cGroupbyStep key s.g with
        | none => (some none, s)
        | some g' =>
          (if (cGroupbySkip key fuel g').1 then none else some none,
            { s with g := (cGroupbySkip key fuel g').2 }) := by
      rw [gbStep_pure run key s he hk hi]
      cases hs : cGroupbyStep key s.g with
      | none => rfl
      | some g' => exact gbSkip_pure key fuel { s with g := g' } he hh hk hi
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

theorem gbNext_pure (key : α → κ) (s : GbState α κ) (he : s.err = none) (hh : s.hooks = [])
    (hk : s.keyHooks = []) (hi : s.iterHooks = []) :
    gbNext (decEq κ) (pureKey key) run s =
      (gbValue (cGroupbyNext key s.g).1, { s with g := (cGroupbyNext key s.g).2 }) := by
  simp only [gbNext, cGroupbyNext]
  rw [gbSkip_pure run key _ { s with g := { s.g with currgrouper := none } } he hh hk hi]
  have hkey := cGroupbySkip_true_currkey key (s.g.it.length + 1) { s.g with currgrouper := none }
  cases hs : cGroupbySkip key (s.g.it.length + 1) { s.g with currgrouper := none } with
  | mk f g' =>
    rw [hs] at hkey
    cases f with
    | false => simp [gbFail, gbValue]
    | true =>
      have hc := hkey rfl
      cases hck : g'.currkey with
      | none => simp [hck] at hc
      | some ck =>
        simp [hck, gbValue, cGrouperCreate, gbCreate]

theorem gbGrouperNext_pure (key : α → κ) (s : GbState α κ) (j : Nat) (he : s.err = none) (hh : s.hooks = [])
    (hk : s.keyHooks = []) (hi : s.iterHooks = []) :
    gbGrouperNext (decEq κ) (pureKey key) run s j =
      (gbValue (cGrouperNext key s.g j).1, { s with g := (cGrouperNext key s.g j).2 }) := by
  simp only [gbGrouperNext, gbGrouperCmp, cGrouperNext]
  by_cases hc : (s.g.currgrouper != some j) = true
  · simp [hc, gbValue]
  · simp only [hc, Bool.false_eq_true, if_false]
    cases hv : s.g.currvalue.isNone with
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [gbEq_pure run s hh]
      cases hb : (s.g.groupers.getD j default == s.g.currkey.getD default) <;> simp [gbValue]
    | true =>
      have hv' : s.g.currvalue = none := Option.isNone_iff_eq_none.mp hv
      simp only [if_true, gbStep_pure run key s he hk hi, hv']
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
    s.keyHooks = [] → s.iterHooks = [] →
    (gbFold (decEq κ) (pureKey key) run ops s).log = s.log ++ (cGroupbyOps key s.g ops).map liftRes ∧
      (gbFold (decEq κ) (pureKey key) run ops s).crashed = s.crashed
  | [], s, _, _, _, _ => by simp [gbFold, cGroupbyOps]
  | .outer :: ops, s, he, hh, hk, hi => by
    rw [gbFold_cons]
    have hs : gbOp (decEq κ) (pureKey key) run .outer s =
        { s with g := (cGroupbyNext key s.g).2, log := s.log ++ [.inl (gbValue (cGroupbyNext key s.g).1)] } := by
      simp only [gbOp, gbNext_pure run key s he hh hk hi]
    rw [hs]
    obtain ⟨h1, h2⟩ := gbFold_pure key ops
      { s with g := (cGroupbyNext key s.g).2, log := s.log ++ [.inl (gbValue (cGroupbyNext key s.g).1)] }
      he hh hk hi
    refine ⟨?_, h2⟩
    rw [h1]
    simp [cGroupbyOps, liftRes]
  | .group j :: ops, s, he, hh, hk, hi => by
    rw [gbFold_cons]
    by_cases hj : j < s.g.groupers.length
    · have hs : gbOp (decEq κ) (pureKey key) run (.group j) s =
          { s with g := (cGrouperNext key s.g j).2, log := s.log ++ [.inr (gbValue (cGrouperNext key s.g j).1)] } := by
        simp only [gbOp, hj, if_true, gbGrouperNext_pure run key s j he hh hk hi]
      rw [hs]
      obtain ⟨h1, h2⟩ := gbFold_pure key ops
        { s with g := (cGrouperNext key s.g j).2, log := s.log ++ [.inr (gbValue (cGrouperNext key s.g j).1)] }
        he hh hk hi
      refine ⟨?_, h2⟩
      rw [h1]
      simp [cGroupbyOps, hj, liftRes]
    · have hs : gbOp (decEq κ) (pureKey key) run (.group j) s = s := by simp [gbOp, hj]
      rw [hs]
      obtain ⟨h1, h2⟩ := gbFold_pure key ops s he hh hk hi
      exact ⟨by rw [h1]; simp [cGroupbyOps, hj], h2⟩
  | .direct k :: ops, s, he, hh, hk, hi => by
    rw [gbFold_cons]
    have hs : gbOp (decEq κ) (pureKey key) run (.direct k) s = { s with g := cGrouperDirect s.g k } := by
      simp [gbOp, gbCreate, cGrouperDirect, cGrouperCreate]
    rw [hs]
    obtain ⟨h1, h2⟩ := gbFold_pure key ops { s with g := cGrouperDirect s.g k } he hh hk hi
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
`GroupbyEqError` and `GroupbyFailedStepKeepsState` say what C does there. A
re-entrant call is refused by the doc's generators (`ValueError: generator
already executing`), so there is nothing to agree on there either;
`GrouperReentrantStep` says what C does. -/
def GroupbyDocAgreeR : Prop :=
  ∀ (α κ : Type) [Inhabited α] [Inhabited κ] [DecidableEq κ] (key : α → κ) (o : Obj α)
    (ops : List (GbOp κ)), (∀ op ∈ ops, op.isPublic = true) →
    (∀ l e, o = .iter l (some e) → False) →
    cGroupbyR (decEq κ) (pureKey key) o [] ops = (docGroupby key o ops).map (fun r => (r.map liftRes, false))

theorem groupbyDocAgreeR_proven : GroupbyDocAgreeR := by
  intro α κ _ _ _ key o ops hp hnr
  cases o with
  | notIterable ty => simp [cGroupbyR, cGroupbyS, gbInit, getIter, docGroupby, Except.map]
  | iter l err =>
    cases err with
    | some e => exact (hnr l e rfl).elim
    | none =>
      have h := groupbyDocAgree_proven α κ key (.iter l none) ops hp
      rw [← h]
      simp only [cGroupbyR, cGroupbyS, gbInit, cGroupby, cGroupbyNew, getIter, gbRun]
      obtain ⟨h1, h2⟩ := gbFold_pure (gbRun (decEq κ) (pureKey key)
          (([] : List (List (GbOp κ))).length + ([] : List (List (GbOp κ))).length +
            ([] : List (List (GbOp κ))).length)) key ops
        { g := { it := l, tgtkey := none, currkey := none, currvalue := none, currgrouper := none,
                 groupers := [] }, err := none } rfl rfl rfl rfl
      rw [h1, h2]
      simp [Except.map]

/-- A failed `groupby_step`, for every key function and state, with an input and
key function that do not re-enter: the groupby object's values are those from
before the call, so the object stays usable, and at most the one item it took is
lost. With re-entry the values are whatever the re-entrant calls left
(`GrouperReentrantStep` for the successful step). -/
def GroupbyFailedStepKeepsState : Prop :=
  ∀ (α κ : Type) (key : α → Py κ) (run : List (GbOp κ) → GbState α κ → GbState α κ)
    (s s' : GbState α κ) (e : Option PyExc), s.iterHooks = [] → s.keyHooks = [] →
    gbStep key run s = (.fail e, s') →
    s'.g.currkey = s.g.currkey ∧ s'.g.currvalue = s.g.currvalue ∧ s'.g.tgtkey = s.g.tgtkey ∧
      s'.g.currgrouper = s.g.currgrouper ∧ s'.g.groupers = s.g.groupers ∧
      s'.g.it = s.g.it.drop 1 ∧ (e = none ↔ s.g.it = [] ∧ s.err = none)

theorem groupbyFailedStepKeepsState_proven : GroupbyFailedStepKeepsState := by
  intro α κ key run s s' e hi hk h
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
    simp only [gbIterHook, gbKeyHook, hi, hk] at h
    cases hkv : key v with
    | error x =>
      simp only [hkv, Prod.mk.injEq, GbStep.fail.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    | ok k => simp [hkv] at h

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
  simp only [gbGrouperNext, gbGrouperCmp, hj, bne_self_eq_false, Bool.false_eq_true, if_false, hv,
    Option.isNone_some, hc, Option.getD_some, hq]
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

/-- `itertools._grouper(groupby_obj, k)` (:617-622, `_grouper_create` :625-637) makes the
new group current: every group created before it stops at once and leaves the state alone,
whatever the comparison, key function, input and hooks would do; and `next()` on the new
group compares `k` with `currkey` (:681-683): with a current value `v`, when they are not
the same object and nothing re-enters, it returns `v` and clears the value if `__eq__`
answers true, stops if false, and raises what `__eq__` raises, changing nothing in those two
cases. For every comparison, key function and state. -/
def GrouperDirectInvalidates : Prop :=
  ∀ (α κ : Type) [Inhabited κ] (K : KeyEq κ) (key : α → Py κ)
    (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ) (k : κ),
    (∀ j, j < s.g.groupers.length →
      gbGrouperNext K key run { s with g := gbCreate s.g k } j = (.stop, { s with g := gbCreate s.g k })) ∧
    (∀ (v : α) (ck : κ), s.hooks = [] → s.g.currvalue = some v → s.g.currkey = some ck →
      K.same k ck = false →
      gbGrouperNext K key run { s with g := gbCreate s.g k } s.g.groupers.length =
        match K.eq k ck with
        | .error e => (.exc e, { s with g := gbCreate s.g k })
        | .ok false => (.stop, { s with g := gbCreate s.g k })
        | .ok true => (.val v, { s with g := { gbCreate s.g k with currvalue := none, currkey := none } }))

theorem grouperDirectInvalidates_proven : GrouperDirectInvalidates := by
  intro α κ _ K key run s k
  refine ⟨fun j hj => ?_, fun v ck hh hv hc hs => ?_⟩
  · have h : (gbCreate s.g k).currgrouper ≠ some j := by
      simp only [gbCreate]
      intro h
      simp only [Option.some.injEq] at h
      omega
    simp [gbGrouperNext, h]
  · have hg : (gbCreate s.g k).groupers.getD s.g.groupers.length default = k := by
      simp [gbCreate]
    have key_lemma := fun (r : Py Bool) (h2 : K.eq k ck = r) =>
      gbGrouperNext_compare K key run { s with g := gbCreate s.g k } s.g.groupers.length v ck
        r hh (by simp [gbCreate]) (by simp [gbCreate, hv]) (by simp [gbCreate, hc])
        (by rw [hg]; exact hs) (by rw [hg]; exact h2)
    cases hr : K.eq k ck with
    | error e => rw [key_lemma _ hr]
    | ok b => cases b <;> rw [key_lemma _ hr] <;> simp [gbValue, gbCreate, hv]

/-- `groupby_step` failing inside `groupby_next` (:564-565), for every comparison, key
function and state where the loop reaches it: no current key (:540-541), or a current key
that compares equal to the target (:554-562) with nothing re-entering. When the key function
raises on the next item `v`, `groupby_next` raises that exception; the item is consumed,
`currgrouper` is cleared (:537), and every other field keeps its old value, so the next call
carries on from the following item. When the input raises, that exception propagates and the
input is used up. The input and the key function do not re-enter here; what a re-entrant one
does is `GrouperReentrantStep`. -/
def GroupbyNextStepError : Prop :=
  ∀ (α κ : Type) [Inhabited κ] (K : KeyEq κ) (key : α → Py κ)
    (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ) (e : PyExc),
    s.iterHooks = [] → s.keyHooks = [] →
    (s.g.currkey = none ∨ ∃ ck tk, s.g.currkey = some ck ∧ s.g.tgtkey = some tk ∧ s.hooks = [] ∧
      (K.same tk ck = true ∨ K.eq tk ck = .ok true)) →
    (∀ v rest, s.g.it = v :: rest → key v = .error e →
      gbNext K key run s = (.exc e, { s with g := { s.g with currgrouper := none, it := rest } })) ∧
    (s.g.it = [] → s.err = some e →
      gbNext K key run s = (.exc e, { s with g := { s.g with currgrouper := none }, err := none }))

theorem groupbyNextStepError_proven : GroupbyNextStepError := by
  intro α κ _ K key run s e hi hk hpath
  refine ⟨fun v rest hit hkv => ?_, fun hit he => ?_⟩
  · rcases hpath with hn | ⟨ck, tk, hc, ht, hh, hq⟩
    · simp [gbNext, gbSkip, hn, gbThen, gbStep, hit, hkv, gbFail, gbIterHook, gbKeyHook, hi, hk]
    · by_cases hs : K.same tk ck = true
      · simp [gbNext, gbSkip, hc, ht, gbEq, hs, gbThen, gbStep, hit, hkv, gbFail, gbIterHook, gbKeyHook, hi, hk]
      · have hq' : K.eq tk ck = .ok true := by simpa [hs] using hq
        simp [gbNext, gbSkip, hc, ht, gbEq, hs, hh, hq', gbThen, gbStep, hit, hkv, gbFail, gbIterHook,
          gbKeyHook, hi, hk]
  · rcases hpath with hn | ⟨ck, tk, hc, ht, hh, hq⟩
    · simp [gbNext, gbSkip, hn, gbThen, gbStep, hit, he, gbFail]
    · by_cases hs : K.same tk ck = true
      · simp [gbNext, gbSkip, hc, ht, gbEq, hs, gbThen, gbStep, hit, he, gbFail]
      · have hq' : K.eq tk ck = .ok true := by simpa [hs] using hq
        simp [gbNext, gbSkip, hc, ht, gbEq, hs, hh, hq', gbThen, gbStep, hit, he, gbFail]

/-- `groupby_step` failing inside `_grouper_next` (:671-673): for every comparison, key
function and state, on the current group with no current value, with an input and key
function that do not re-enter. When the key function raises on the next item `v`, `next()`
on the group raises that exception, the item is consumed and nothing else changes: the group
stays current, so a later `next()` on it reads the following item `w` and returns it when its
key compares equal to the group's (here with nothing re-entering). When the input raises,
that exception propagates and the group then stops. -/
def GrouperStepError : Prop :=
  ∀ (α κ : Type) [Inhabited κ] (K : KeyEq κ) (key : α → Py κ)
    (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ) (j : Nat) (e : PyExc),
    s.iterHooks = [] → s.keyHooks = [] →
    s.g.currgrouper = some j → s.g.currvalue = none →
    (∀ v rest, s.g.it = v :: rest → key v = .error e →
      gbGrouperNext K key run s j = (.exc e, { s with g := { s.g with it := rest } }) ∧
      ∀ w rest' kw, rest = w :: rest' → key w = .ok kw → s.hooks = [] →
        (K.same (s.g.groupers.getD j default) kw = true ∨ K.eq (s.g.groupers.getD j default) kw = .ok true) →
        gbGrouperNext K key run { s with g := { s.g with it := rest } } j =
          (.val w, { s with g := { s.g with it := rest', currvalue := none, currkey := none } })) ∧
    (s.g.it = [] → s.err = some e →
      gbGrouperNext K key run s j = (.exc e, { s with err := none }) ∧
      gbGrouperNext K key run { s with err := none } j = (.stop, { s with err := none }))

theorem grouperStepError_proven : GrouperStepError := by
  intro α κ _ K key run s j e hi hk hj hv
  refine ⟨fun v rest hit hkv => ⟨?_, fun w rest' kw hr hkw hh hq => ?_⟩, fun hit he => ⟨?_, ?_⟩⟩
  · simp [gbGrouperNext, hj, hv, gbStep, hit, hkv, gbFail, gbIterHook, gbKeyHook, hi, hk]
  · subst hr
    generalize hT0 : s.g.groupers.getD j default = T at hq
    have hT : s.g.groupers[j]?.getD default = T := by simpa using hT0
    by_cases hs : K.same T kw = true
    · simp [gbGrouperNext, hj, hv, gbStep, hkw, gbEq, hT, hs, gbValue, gbIterHook, gbKeyHook, hi, hk,
        gbGrouperCmp]
    · have hq' : K.eq T kw = .ok true := by simpa [hs] using hq
      simp [gbGrouperNext, hj, hv, gbStep, hkw, gbEq, hT, hs, hh, hq', gbValue, gbIterHook, gbKeyHook,
        hi, hk, gbGrouperCmp]
  · simp [gbGrouperNext, hj, hv, gbStep, hit, he, gbFail]
  · simp [gbGrouperNext, hj, hv, gbStep, hit, gbFail]

/-! ## No crash without re-entry -/

/-- No callback has anything left to run. -/
def GbQuiet (s : GbState α κ) : Prop := s.hooks = [] ∧ s.keyHooks = [] ∧ s.iterHooks = []

/-- Without re-entrancy the process cannot die: for every comparison (which may
raise), key function and input (which may raise) and every sequence of
operations. The `break` of `groupby_next` is only taken with `currkey` set. -/
def GroupbyNoCrashWithoutHooks : Prop :=
  ∀ (α κ : Type) [Inhabited κ] (K : KeyEq κ) (key : α → Py κ) (o : Obj α) (ops : List (GbOp κ))
    (s : GbState α κ), gbInit o [] = .ok s → (gbRun K key 1 ops s).crashed = false

theorem gbStep_keeps (key : α → Py κ) (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ)
    (hq : GbQuiet s) : GbQuiet (gbStep key run s).2 ∧ (gbStep key run s).2.crashed = s.crashed := by
  obtain ⟨hh, hk, hi⟩ := hq
  simp only [gbStep]
  cases hit : s.g.it with
  | nil => cases he : s.err <;> simp [GbQuiet, hh, hk, hi]
  | cons v rest => cases hkv : key v <;> simp [hkv, gbIterHook, gbKeyHook, GbQuiet, hh, hk, hi]

theorem gbEq_nohook (K : KeyEq κ) (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ)
    (a b : κ) (hh : s.hooks = []) : (gbEq K run s a b).2 = s := by
  simp only [gbEq]
  split <;> simp [hh]

/-- What the skip loop preserves when nothing re-enters; its `break` has `currkey`. -/
theorem gbSkip_nohook (K : KeyEq κ) (key : α → Py κ) (run : List (GbOp κ) → GbState α κ → GbState α κ) :
    ∀ (fuel : Nat) (s : GbState α κ), GbQuiet s →
      GbQuiet (gbSkip K key run fuel s).2 ∧ (gbSkip K key run fuel s).2.crashed = s.crashed ∧
        ((gbSkip K key run fuel s).1 = none → (gbSkip K key run fuel s).2.g.currkey.isSome = true)
  | 0, s, hq => ⟨hq, rfl, by simp [gbSkip]⟩
  | fuel + 1, s, hq => by
    have step : ∀ t : GbState α κ, GbQuiet t → t.crashed = s.crashed →
        GbQuiet (gbThen (fun s => gbSkip K key run fuel s) (gbStep key run t)).2 ∧
        (gbThen (fun s => gbSkip K key run fuel s) (gbStep key run t)).2.crashed = s.crashed ∧
        ((gbThen (fun s => gbSkip K key run fuel s) (gbStep key run t)).1 = none →
          (gbThen (fun s => gbSkip K key run fuel s) (gbStep key run t)).2.g.currkey.isSome = true) := by
      intro t ht htc
      obtain ⟨k1, k2⟩ := gbStep_keeps key run t ht
      cases hs : gbStep key run t with
      | mk r s' =>
        rw [hs] at k1 k2
        simp only at k1 k2
        cases r with
        | fail e => exact ⟨k1, k2.trans htc, by simp [gbThen]⟩
        | ok o =>
          have := gbSkip_nohook K key run fuel s' k1
          simp only [gbThen]
          exact ⟨this.1, this.2.1.trans (k2.trans htc), this.2.2⟩
    simp only [gbSkip]
    cases hc : s.g.currkey with
    | none => exact step s hq rfl
    | some ck =>
      cases ht : s.g.tgtkey with
      | none => exact ⟨hq, rfl, by simp [hc]⟩
      | some tk =>
        simp only
        have hqe := gbEq_nohook K run s tk ck hq.1
        cases he : gbEq K run s tk ck with
        | mk r s' =>
          rw [he] at hqe
          simp only at hqe
          subst s'
          cases r with
          | error e => exact ⟨hq, rfl, by simp⟩
          | ok b =>
            cases b with
            | false => exact ⟨hq, rfl, by simp [hc]⟩
            | true => exact step s hq rfl

theorem gbNext_nohook (K : KeyEq κ) (key : α → Py κ) (run : List (GbOp κ) → GbState α κ → GbState α κ)
    (s : GbState α κ) (hq : GbQuiet s) (hc : s.crashed = false) :
    GbQuiet (gbNext K key run s).2 ∧ (gbNext K key run s).2.crashed = false := by
  simp only [gbNext]
  obtain ⟨h1, h2, h3⟩ := gbSkip_nohook K key run (s.g.it.length + 1)
    { s with g := { s.g with currgrouper := none } } hq
  cases hs : gbSkip K key run (s.g.it.length + 1) { s with g := { s.g with currgrouper := none } } with
  | mk r s' =>
    rw [hs] at h1 h2 h3
    simp only at h1 h2 h3
    have h2' : s'.crashed = false := h2.trans hc
    cases r with
    | some e =>
      simp only
      exact ⟨h1, h2'⟩
    | none =>
      have hk := h3 rfl
      simp only
      split
      · next hk' => simp [hk'] at hk
      · exact ⟨h1, h2'⟩

theorem gbGrouperCmp_nohook [Inhabited κ] (K : KeyEq κ) (run : List (GbOp κ) → GbState α κ → GbState α κ)
    (s : GbState α κ) (j : Nat) (hq : GbQuiet s) (hc : s.crashed = false) :
    GbQuiet (gbGrouperCmp K run s j : GbRes α × GbState α κ).2 ∧
      (gbGrouperCmp K run s j : GbRes α × GbState α κ).2.crashed = false := by
  simp only [gbGrouperCmp]
  have he := gbEq_nohook K run s (s.g.groupers.getD j default) (s.g.currkey.getD default) hq.1
  cases hc2 : gbEq K run s (s.g.groupers.getD j default) (s.g.currkey.getD default) with
  | mk c s3 =>
    rw [hc2] at he
    simp only at he
    subst he
    cases c with
    | error e => exact ⟨hq, hc⟩
    | ok b => cases b <;> exact ⟨hq, hc⟩

theorem gbGrouperNext_nohook [Inhabited κ] (K : KeyEq κ) (key : α → Py κ)
    (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ) (j : Nat)
    (hq : GbQuiet s) (hc : s.crashed = false) :
    GbQuiet (gbGrouperNext K key run s j).2 ∧ (gbGrouperNext K key run s j).2.crashed = false := by
  unfold gbGrouperNext
  by_cases h : (s.g.currgrouper != some j) = true
  · rw [if_pos h]
    exact ⟨hq, hc⟩
  · rw [if_neg h]
    have hr : GbQuiet (if s.g.currvalue.isNone then gbStep key run s else (GbStep.ok none, s)).2 ∧
        (if s.g.currvalue.isNone then gbStep key run s else (GbStep.ok none, s)).2.crashed = false := by
      obtain ⟨k1, k2⟩ := gbStep_keeps key run s hq
      split
      · exact ⟨k1, k2.trans hc⟩
      · exact ⟨hq, hc⟩
    cases hq2 : (if s.g.currvalue.isNone then gbStep key run s else (GbStep.ok none, s)) with
    | mk r s1 =>
      rw [hq2] at hr
      simp only at hr
      cases r with
      | fail e => exact hr
      | ok old =>
        cases old with
        | none => exact gbGrouperCmp_nohook K run s1 j hr.1 hr.2
        | some o => exact gbGrouperCmp_nohook K run { s1 with dropped := s1.dropped ++ [o] } j hr.1 hr.2

theorem gbOp_nohook [Inhabited κ] (K : KeyEq κ) (key : α → Py κ)
    (run : List (GbOp κ) → GbState α κ → GbState α κ) (op : GbOp κ) (s : GbState α κ)
    (hq : GbQuiet s) (hc : s.crashed = false) :
    GbQuiet (gbOp K key run op s) ∧ (gbOp K key run op s).crashed = false := by
  cases op with
  | outer =>
    have := gbNext_nohook K key run s hq hc
    simp only [gbOp]
    exact this
  | group j =>
    simp only [gbOp]
    split
    · exact gbGrouperNext_nohook K key run s j hq hc
    · exact ⟨hq, hc⟩
  | direct k => exact ⟨hq, hc⟩

theorem gbFold_nohook [Inhabited κ] (K : KeyEq κ) (key : α → Py κ)
    (run : List (GbOp κ) → GbState α κ → GbState α κ) :
    ∀ (ops : List (GbOp κ)) (s : GbState α κ), GbQuiet s → s.crashed = false →
      (gbFold K key run ops s).crashed = false
  | [], _, _, hc => hc
  | op :: ops, s, hq, hc => by
    rw [gbFold_cons]
    obtain ⟨h1, h2⟩ := gbOp_nohook K key run op s hq hc
    exact gbFold_nohook K key run ops _ h1 h2

theorem groupbyNoCrashWithoutHooks_proven : GroupbyNoCrashWithoutHooks := by
  intro α κ _ K key o ops s hs
  simp only [gbInit] at hs
  cases hi : getIter o with
  | error e => simp [hi] at hs
  | ok src =>
    obtain ⟨l, err⟩ := src
    rw [hi] at hs
    simp only [Except.ok.injEq] at hs
    subst hs
    exact gbFold_nohook K key _ ops _ ⟨rfl, rfl, rfl⟩ rfl

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

/-! ## A re-entrant input or key function inside `_grouper_next` -/

/-- `_grouper_next` on the current group `j` with no current value, for every
comparison, key function, state and re-entrant code. It takes the next item `v`,
whose key is `k`; `T` is the state once the input's and the key function's code
for that item has run, whatever that code did: it may have made another group
current, left another value current, or used up the input. The group does not
look at `currgrouper` again (:669 is before the step, :672): it stores `v` and `k`
over what `T` holds (:524-527), releasing `T`'s current value into `dropped`, and
compares its own key with `k` (:681-683). With nothing re-entering that
comparison it returns `v` and clears the value when `__eq__` answers true, and
stops, keeping `v` current, when it answers false.

And the run CPython 3.15.2 gives: input `[1, 1, 1, 2, 2, 3, 3]`, key `id`, the
second key call running `next()` on the groupby object. That call skips the third
`1` and returns key `2`, making its group current with the first `2` as the
current value; the first group then stores its second `1` over that `2` and
returns it; the new group gives the second `2` and stops at `3`. -/
def GrouperReentrantStep : Prop :=
  (∀ (α κ : Type) [Inhabited κ] (K : KeyEq κ) (key : α → Py κ)
    (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ) (j : Nat) (v : α)
    (rest : List α) (k : κ),
    s.g.currgrouper = some j → s.g.currvalue = none → s.g.it = v :: rest → key v = .ok k →
    ∀ T, T = gbKeyHook run (gbIterHook run { s with g := { s.g with it := rest } }) → T.hooks = [] →
    ((K.same (T.g.groupers.getD j default) k = true ∨ K.eq (T.g.groupers.getD j default) k = .ok true) →
      gbGrouperNext K key run s j =
        (.val v, { T with g := { T.g with currvalue := none, currkey := none },
                          dropped := T.dropped ++ T.g.currvalue.toList })) ∧
    (K.same (T.g.groupers.getD j default) k = false → K.eq (T.g.groupers.getD j default) k = .ok false →
      gbGrouperNext K key run s j =
        (.stop, { T with g := { T.g with currvalue := some v, currkey := some k },
                         dropped := T.dropped ++ T.g.currvalue.toList }))) ∧
  cGroupbyR (decEq Nat) (pureKey id) (.iter [1, 1, 1, 2, 2, 3, 3] none) []
      [.outer, .group 0, .group 0, .group 1, .group 1] [[], [.outer]] [] =
    .ok ([.inl (.val 1), .inr (.val 1), .inl (.val 2), .inr (.val 1), .inr (.val 2), .inr .stop], false)

theorem grouperReentrantStep_proven : GrouperReentrantStep := by
  refine ⟨?_, by decide⟩
  intro α κ _ K key run s j v rest k hj hv hit hk T hT hth
  have hstep : gbStep key run s =
      (.ok T.g.currvalue, { T with g := { T.g with currvalue := some v, currkey := some k } }) := by
    subst hT
    simp only [gbStep, hit, hk]
  have h1 : ¬((s.g.currgrouper != some j) = true) := by simp [hj]
  have h2 : s.g.currvalue.isNone = true := by simp [hv]
  generalize hG : T.g.groupers.getD j default = G
  have hG' : T.g.groupers[j]?.getD default = G := by simpa using hG
  constructor
  · intro hq
    unfold gbGrouperNext
    rw [if_neg h1, if_pos h2, hstep]
    cases hcv : T.g.currvalue with
    | none =>
      simp only [gbGrouperCmp, gbEq, hth, Option.getD_some]
      rcases hq with hs | hq
      · simp [hG', hs, gbValue]
      · by_cases hs : K.same G k = true
        · simp [hG', hs, gbValue]
        · simp [hG', hs, hq, gbValue]
    | some o =>
      simp only [gbGrouperCmp, gbEq, hth, Option.getD_some]
      rcases hq with hs | hq
      · simp [hG', hs, gbValue]
      · by_cases hs : K.same G k = true
        · simp [hG', hs, gbValue]
        · simp [hG', hs, hq, gbValue]
  · intro hs hq
    unfold gbGrouperNext
    rw [if_neg h1, if_pos h2, hstep]
    cases hcv : T.g.currvalue with
    | none => simp [gbGrouperCmp, gbEq, hth, hG', hs, hq]
    | some o => simp [gbGrouperCmp, gbEq, hth, hG', hs, hq]

/-- The values `_grouper_next`'s step released, after `groupby(iterable, key)`
and the operations. -/
def gbDrops [Inhabited κ] (K : KeyEq κ) (key : α → Py κ) (iterable : Obj α)
    (hooks keyHooks iterHooks : List (List (GbOp κ))) (ops : List (GbOp κ)) : List α :=
  match cGroupbyS K key iterable hooks ops keyHooks iterHooks with
  | .ok s => s.dropped
  | .error _ => []

/-- `_grouper_next` steps only when there is no current value (:670), to fill the
slot: for every comparison, key function, input, re-entrant code and sequence of
operations, its `groupby_step` never releases a value, so no item that was made
current is lost without being returned. -/
def GrouperStepKeepsItems : Prop :=
  ∀ (α κ : Type) [Inhabited κ] (K : KeyEq κ) (key : α → Py κ) (o : Obj α)
    (hooks keyHooks iterHooks : List (List (GbOp κ))) (ops : List (GbOp κ)),
    gbDrops K key o hooks keyHooks iterHooks ops = []

/-- Input `[1, 1, 1, 2, 2, 3, 3]`, key `id`; the second key call runs `next()` on
the groupby object. That call skips the third `1`, makes the group of `2` current
and leaves its first `2` as the current value; the first group then stores its
second `1` over it, and the new group starts at the second `2`. The log is what
CPython 3.15.2 prints: the first group gives `1, 1`, the re-entrant `next()`
gives key `2`, the new group gives `2` and stops at `3`. -/
theorem grouperStepKeepsItems_refuted : ¬GrouperStepKeepsItems := by
  intro h
  have h1 := h Nat Nat (decEq Nat) (pureKey id) (.iter [1, 1, 1, 2, 2, 3, 3] none) [] [[], [.outer]] []
    [.outer, .group 0, .group 0, .group 1, .group 1]
  have h2 : gbDrops (decEq Nat) (pureKey id) (.iter [1, 1, 1, 2, 2, 3, 3] none) [] [[], [.outer]] []
      [.outer, .group 0, .group 0, .group 1, .group 1] = [2] := by decide
  rw [h2] at h1
  exact absurd h1 (by decide)

/-- Nothing for the input and the key function to run, and nothing dropped yet. -/
def GbCalm (s : GbState α κ) : Prop := s.keyHooks = [] ∧ s.iterHooks = [] ∧ s.dropped = []

theorem gbStep_calm (key : α → Py κ) (run : List (GbOp κ) → GbState α κ → GbState α κ) (s : GbState α κ)
    (hq : GbCalm s) : GbCalm (gbStep key run s).2 ∧
      ∀ o, (gbStep key run s).1 = .ok o → o = s.g.currvalue := by
  obtain ⟨hk, hi, hd⟩ := hq
  simp only [gbStep]
  cases hit : s.g.it with
  | nil => cases he : s.err <;> simp [GbCalm, hk, hi, hd]
  | cons v rest => cases hkv : key v <;> simp [hkv, gbIterHook, gbKeyHook, GbCalm, hk, hi, hd]

section Calm

variable [Inhabited κ] (K : KeyEq κ) (key : α → Py κ) (run : List (GbOp κ) → GbState α κ → GbState α κ)
  (hrun : ∀ ops t, GbCalm t → GbCalm (run ops t))
include hrun

theorem gbEq_calm (s : GbState α κ) (a b : κ) (hq : GbCalm s) : GbCalm (gbEq K run s a b).2 := by
  simp only [gbEq]
  split
  · exact hq
  · split
    · exact hq
    · exact hrun _ _ hq

theorem gbSkip_calm : ∀ (fuel : Nat) (s : GbState α κ), GbCalm s → GbCalm (gbSkip K key run fuel s).2
  | 0, _, hq => hq
  | fuel + 1, s, hq => by
    have step : ∀ t : GbState α κ, GbCalm t →
        GbCalm (gbThen (fun s => gbSkip K key run fuel s) (gbStep key run t)).2 := by
      intro t ht
      have k := (gbStep_calm key run t ht).1
      cases hs : gbStep key run t with
      | mk r s' =>
        rw [hs] at k
        cases r with
        | fail e => exact k
        | ok o => exact gbSkip_calm fuel s' k
    simp only [gbSkip]
    cases hc : s.g.currkey with
    | none => exact step s hq
    | some ck =>
      cases ht : s.g.tgtkey with
      | none => exact hq
      | some tk =>
        simp only
        have he := gbEq_calm K run hrun s tk ck hq
        cases hq2 : gbEq K run s tk ck with
        | mk r s' =>
          rw [hq2] at he
          cases r with
          | error e => exact he
          | ok b =>
            cases b with
            | false => exact he
            | true => exact step s' he

theorem gbNext_calm (s : GbState α κ) (hq : GbCalm s) : GbCalm (gbNext K key run s).2 := by
  simp only [gbNext]
  have h := gbSkip_calm K key run hrun (s.g.it.length + 1) { s with g := { s.g with currgrouper := none } } hq
  cases hs : gbSkip K key run (s.g.it.length + 1) { s with g := { s.g with currgrouper := none } } with
  | mk r s' =>
    rw [hs] at h
    cases r with
    | some e => exact h
    | none =>
      simp only
      split
      · exact h
      · exact h

theorem gbGrouperCmp_calm (s : GbState α κ) (j : Nat) (hq : GbCalm s) :
    GbCalm (gbGrouperCmp K run s j : GbRes α × GbState α κ).2 := by
  simp only [gbGrouperCmp]
  have he := gbEq_calm K run hrun s (s.g.groupers.getD j default) (s.g.currkey.getD default) hq
  cases hc2 : gbEq K run s (s.g.groupers.getD j default) (s.g.currkey.getD default) with
  | mk c s3 =>
    rw [hc2] at he
    cases c with
    | error e => exact he
    | ok b => cases b <;> exact he

theorem gbGrouperNext_calm (s : GbState α κ) (j : Nat) (hq : GbCalm s) :
    GbCalm (gbGrouperNext K key run s j).2 := by
  unfold gbGrouperNext
  by_cases h : (s.g.currgrouper != some j) = true
  · rw [if_pos h]
    exact hq
  · rw [if_neg h]
    by_cases hv : s.g.currvalue.isNone = true
    · rw [if_pos hv]
      obtain ⟨k1, k2⟩ := gbStep_calm key run s hq
      cases hs : gbStep key run s with
      | mk r s1 =>
        rw [hs] at k1 k2
        cases r with
        | fail e => exact k1
        | ok old =>
          have hold : old = none := by
            rw [k2 old rfl]
            exact Option.isNone_iff_eq_none.mp hv
          subst hold
          exact gbGrouperCmp_calm K run hrun s1 j k1
    · rw [if_neg hv]
      exact gbGrouperCmp_calm K run hrun s j hq

theorem gbOp_calm (op : GbOp κ) (s : GbState α κ) (hq : GbCalm s) : GbCalm (gbOp K key run op s) := by
  cases op with
  | outer =>
    have := gbNext_calm K key run hrun s hq
    simp only [gbOp]
    exact this
  | group j =>
    simp only [gbOp]
    split
    · exact gbGrouperNext_calm K key run hrun s j hq
    · exact hq
  | direct k => exact hq

theorem gbFold_calm : ∀ (ops : List (GbOp κ)) (s : GbState α κ), GbCalm s → GbCalm (gbFold K key run ops s)
  | [], _, hq => hq
  | op :: ops, s, hq => by
    rw [gbFold_cons]
    exact gbFold_calm ops _ (gbOp_calm K key run hrun op s hq)

end Calm

theorem gbRun_calm [Inhabited κ] (K : KeyEq κ) (key : α → Py κ) :
    ∀ (d : Nat) (ops : List (GbOp κ)) (s : GbState α κ), GbCalm s → GbCalm (gbRun K key d ops s)
  | 0, _, _, hq => hq
  | d + 1, ops, s, hq => gbFold_calm K key (gbRun K key d) (fun ops t ht => gbRun_calm K key d ops t ht) ops s hq

/-- With an input and a key function that do not re-enter, `_grouper_next`'s step
never releases a value: for every comparison (whose `__eq__` may raise and
re-enter, `hooks`), key function and input (which may raise) and every sequence
of operations. So the refutation of `GrouperStepKeepsItems` needs the input or
the key function to re-enter. -/
def GrouperStepKeepsItemsNoReentry : Prop :=
  ∀ (α κ : Type) [Inhabited κ] (K : KeyEq κ) (key : α → Py κ) (o : Obj α)
    (hooks : List (List (GbOp κ))) (ops : List (GbOp κ)),
    gbDrops K key o hooks [] [] ops = []

theorem grouperStepKeepsItemsNoReentry_proven : GrouperStepKeepsItemsNoReentry := by
  intro α κ _ K key o hooks ops
  simp only [gbDrops, cGroupbyS, gbInit]
  cases hi : getIter o with
  | error e => rfl
  | ok src =>
    obtain ⟨l, err⟩ := src
    exact (gbRun_calm K key _ ops _ ⟨rfl, rfl, rfl⟩).2.2

end PyLean.Itertools
