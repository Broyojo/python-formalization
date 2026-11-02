import PyLean.Itertools.SimpleProps
import PyLean.Itertools.GroupbyTee

/-!
`pairwise_next` (Modules/itertoolsmodule.c:346-399) with the input able to call
`next()` on the same pairwise object: that is what makes the re-check of `po->it`
at :364-368 reachable, and what the plain model `cPairwiseNext` in `Simple.lean`
cannot express. `hooks` holds, for successive items, how many `next()` calls are
made after the item is taken and before it is returned, as a function given to
`map` does: an input that re-entered before taking its item would have none left
for the outer call once the inner calls had exhausted it. They run through
`pwRun`, the function that runs top-level calls. The caller catches what they
raise.

`pwSteps_pure` shows the two models coincide when nothing re-enters, so the doc
comparison in `SimpleProps.lean` applies.
-/

namespace PyLean.Itertools

open PyLean

variable {α : Type}

/-- A `pairwiseobject`. `src` is the iterator: it stays alive after `po->it` is
cleared, since the outer call still holds it. `live` is `po->it != NULL`. -/
structure PwS (α : Type) where
  src : Src α
  live : Bool
  old : Option α
  hooks : List Nat := []
  log : List (NextRes (α × α)) := []

/-- What a pull of the input gave. -/
inductive PwPull (α : Type) where
  | item (v : α)
  | done
  | fail (e : PyExc)

/-- `(*Py_TYPE(it)->tp_iternext)(it)`: the item is taken, then the hook runs. -/
def pwPull (run : Nat → PwS α → PwS α) (s : PwS α) : PwPull α × PwS α :=
  match s.src.next with
  | .done => (.done, s)
  | .fail e rest => (.fail e, { s with src := rest })
  | .item v rest =>
    (.item v, match s.hooks with
      | [] => { s with src := rest }
      | h :: hs => run h { s with src := rest, hooks := hs })

/-- A failed pull: `NULL`, with the exception if one is set. -/
def pwFail {β : Type} : Option PyExc → NextRes β
  | none => .stop
  | some e => .exc e

/-- :370-398: pull `new`. On failure `it` and `old` are cleared (:372-377). On
success the local `old` is paired with `new`, and `po->old` becomes `new`
(:396), overwriting whatever a hook left there. `it` is the local copy, so this
pull happens even if a hook cleared `po->it` meanwhile. -/
def pwSecond (run : Nat → PwS α → PwS α) (old : α) (s : PwS α) : NextRes (α × α) × PwS α :=
  match pwPull run s with
  | (.done, s) => (.stop, { s with live := false, old := none })
  | (.fail e, s) => (.exc e, { s with live := false, old := none })
  | (.item new, s) => (.val (old, new), { s with old := some new })

/-- `pairwise_next` (:347-399). -/
def pwNext (run : Nat → PwS α → PwS α) (s : PwS α) : NextRes (α × α) × PwS α :=
  if !s.live then (.stop, s)
  else
    match s.old with
    | some old => pwSecond run old s
    | none =>
      match pwPull run s with
      -- :359-363: `Py_XSETREF(po->old, NULL)`, then `Py_CLEAR(po->it)`
      | (.done, s) => (.stop, { s with live := false, old := none })
      | (.fail e, s) => (.exc e, { s with live := false, old := none })
      | (.item old, s) =>
        -- :359 stores it; :364-368 re-read `po->it`, which a hook may have cleared
        if !s.live then (.stop, { s with old := none })
        else pwSecond run old { s with old := some old }

/-- `n` calls of `next()`; a result joins the log when its call returns. -/
def pwTimes (run : Nat → PwS α → PwS α) : Nat → PwS α → PwS α
  | 0, s => s
  | n + 1, s =>
    let (r, s) := pwNext run s
    pwTimes run n { s with log := s.log ++ [r] }

/-- Runs `n` calls. Each hook is used once, so `hooks.length + 1` levels are
enough. -/
def pwRun : Nat → Nat → PwS α → PwS α
  | 0, _, s => s
  | d + 1, n, s => pwTimes (pwRun d) n s

/-- `pairwise(iterable)` (`pairwise_new_impl`, :297-320), then `n` calls of `next()`. -/
def cPairwiseR (iterable : Obj α) (hooks : List Nat) (n : Nat) : Py (List (NextRes (α × α))) :=
  match getIter iterable with
  | .error e => .error e
  | .ok it => .ok (pwRun (hooks.length + 1) n { src := it, live := true, old := none, hooks := hooks }).log

/-! ## When nothing re-enters this is `cPairwiseNext` -/

/-- A `Step` as the result of `next()`. -/
def stepRes {σ β : Type} : Step σ β → NextRes β × σ
  | .yield a s => (.val a, s)
  | .stop s => (.stop, s)
  | .raise e s => (.exc e, s)

/-- `n` calls of `next()` on the plain model. -/
def pwPureTimes : Nat → PairwiseState α → List (NextRes (α × α))
  | 0, _ => []
  | n + 1, s => let (r, s) := stepRes (cPairwiseNext s); r :: pwPureTimes n s

/-- How a `PwS` with nothing re-entering matches a `PairwiseState`; `L` is its log. -/
def PwRel (L : List (NextRes (α × α))) (p : PwS α) (c : PairwiseState α) : Prop :=
  p.hooks = [] ∧ p.log = L ∧ p.old = c.old ∧
    (match c.it with
     | some src => p.live = true ∧ p.src = src
     | none => p.live = false)

theorem pwPull_pure (run : Nat → PwS α → PwS α) (s : PwS α) (hh : s.hooks = []) :
    pwPull run s = match s.src.next with
      | .done => (.done, s)
      | .fail e rest => (.fail e, { s with src := rest })
      | .item v rest => (.item v, { s with src := rest }) := by
  simp only [pwPull, hh]

theorem pwNext_pure (run : Nat → PwS α → PwS α) (L : List (NextRes (α × α))) (p : PwS α)
    (c : PairwiseState α) (h : PwRel L p c) :
    (pwNext run p).1 = (stepRes (cPairwiseNext c)).1 ∧
      PwRel L (pwNext run p).2 (stepRes (cPairwiseNext c)).2 := by
  obtain ⟨hh, hL, ho, hm⟩ := h
  have second : ∀ (old : α) (p' : PwS α) (src : Src α), p'.hooks = [] → p'.log = L → p'.src = src →
      p'.live = true → (pwSecond run old p').1 = (stepRes (cPairwiseNew2 old src)).1 ∧
        PwRel L (pwSecond run old p').2 (stepRes (cPairwiseNew2 old src)).2 := by
    intro old p' src h1 h3 h2 h4
    subst h2
    simp only [pwSecond, cPairwiseNew2, pwPull_pure run p' h1]
    cases hn : p'.src.next with
    | done => simp [stepRes, PwRel, h1, h3]
    | fail e rest => simp [stepRes, PwRel, h1, h3]
    | item v rest => simp [stepRes, PwRel, h1, h3, h4]
  cases hc : c.it with
  | none =>
    rw [hc] at hm
    have hl : p.live = false := hm
    simp only [pwNext, hl, Bool.not_false, if_true, cPairwiseNext, hc, stepRes]
    exact ⟨trivial, hh, hL, ho, by simp [hc, hl]⟩
  | some src =>
    rw [hc] at hm
    obtain ⟨hl, hs⟩ := hm
    simp only [pwNext, hl, Bool.not_true, Bool.false_eq_true, if_false, cPairwiseNext, hc]
    cases hold : c.old with
    | some old =>
      rw [hold] at ho
      simp only [ho]
      exact second old p src hh hL hs hl
    | none =>
      rw [hold] at ho
      simp only [ho, pwPull_pure run p hh, hs]
      cases hn : src.next with
      | done => simp [stepRes, PwRel, hh, hL]
      | fail e rest => simp [stepRes, PwRel, hh, hL]
      | item v rest =>
        simp only [hl, Bool.not_true, Bool.false_eq_true, if_false]
        exact second v _ rest hh hL rfl rfl

theorem pwTimes_pure (run : Nat → PwS α → PwS α) : ∀ (n : Nat) (L : List (NextRes (α × α))) (p : PwS α)
    (c : PairwiseState α), PwRel L p c → (pwTimes run n p).log = L ++ pwPureTimes n c
  | 0, L, p, _, h => by simp [pwTimes, pwPureTimes, h.2.1]
  | n + 1, L, p, c, h => by
    have hs := pwNext_pure run L p c h
    simp only [pwTimes, pwPureTimes]
    cases hq : pwNext run p with
    | mk r s =>
      cases hq2 : stepRes (cPairwiseNext c) with
      | mk r2 c2 =>
        rw [hq, hq2] at hs
        obtain ⟨h1, h2⟩ := hs
        simp only at h1 h2
        subst h1
        have hrel : PwRel (L ++ [r]) { s with log := s.log ++ [r] } c2 := by
          obtain ⟨a, b, c', d⟩ := h2
          exact ⟨a, by simp [b], c', d⟩
        simp only
        rw [pwTimes_pure run n (L ++ [r]) _ c2 hrel]
        simp

/-- The items of a sequence of `next()` results, as `list()` would see them. -/
def runOf {β : Type} : List (NextRes β) → Run β
  | [] => ([], some .modelFuel)
  | .val a :: l => let r := runOf l; (a :: r.1, r.2)
  | .stop :: _ => ([], none)
  | .exc e :: _ => ([], some e)

theorem runOf_pure : ∀ (n : Nat) (s : PairwiseState α), runOf (pwPureTimes n s) = drain cPairwiseNext n s
  | 0, _ => rfl
  | n + 1, s => by
    simp only [pwPureTimes, drain]
    cases hs : cPairwiseNext s with
    | «yield» a s' => simp [stepRes, runOf, runOf_pure n s']
    | stop s' => simp [stepRes, runOf]
    | raise e s' => simp [stepRes, runOf]

/-! ## Properties -/

/-- With an input that does not re-enter, `n` calls of `next()` give the doc
generator's pairs and its end, for every input object (not iterable, or raising
after its items) and every element type. The hypothesis is a precondition: the
doc's generator raises `ValueError` when re-entered, so there is nothing to
compare. -/
def PairwiseDocAgreeR : Prop :=
  ∀ (α : Type) (o : Obj α),
    (match cPairwiseR o [] (o.len + 2) with
     | .ok rs => runOf rs
     | .error e => Run.err e) = docPairwise o

theorem pairwiseDocAgreeR_proven : PairwiseDocAgreeR := by
  intro α o
  rw [← pairwise_eq o]
  simp only [cPairwiseR, cPairwise, cPairwiseNew]
  cases hi : getIter o with
  | error e => rfl
  | ok it =>
    simp only [List.length_nil, pwRun]
    rw [pwTimes_pure _ (o.len + 2) [] { src := it, live := true, old := none } { it := some it, old := none }
      ⟨rfl, rfl, rfl, rfl, rfl⟩]
    simp [runOf_pure]

/-- For every hook and state. Once `po->it` is cleared, `next()` stops and changes
nothing (:354-356). And the re-check after the first pull (:364-368): if the hook
cleared `po->it` while the outer call was taking its first item, the outer call
stops, clearing `old`, and that item is dropped. It is reached: with `map(f, [0, 1,
2])` where `f(0)` drains the pairwise object, the inner calls see `(1, 2)` and the
end, and the outer call stops. -/
def PairwiseReentryStops : Prop :=
  (∀ (α : Type) (run : Nat → PwS α → PwS α) (s : PwS α), s.live = false → pwNext run s = (.stop, s)) ∧
  (∀ (α : Type) (run : Nat → PwS α → PwS α) (s : PwS α) (v : α) (rest : Src α) (h : Nat) (hs : List Nat),
    s.live = true → s.old = none → s.src.next = .item v rest → s.hooks = h :: hs →
    (run h { s with src := rest, hooks := hs }).live = false →
    pwNext run s = (.stop, { run h { s with src := rest, hooks := hs } with old := none })) ∧
  (∀ (a b c : Nat), cPairwiseR (.iter [a, b, c] none) [4] 1 =
    .ok [.val (b, c), .stop, .stop, .stop, .stop])

theorem pairwiseReentryStops_proven : PairwiseReentryStops := by
  refine ⟨?_, ?_, ?_⟩
  · intro α run s h
    simp [pwNext, h]
  · intro α run s v rest h hs h1 h2 h3 h4 h5
    generalize hS : run h { s with src := rest, hooks := hs } = S at h5 ⊢
    have hp : pwPull run s = (.item v, S) := by
      simp only [pwPull, h3, h4]
      exact congrArg _ hS
    simp only [pwNext, h1, Bool.not_true, Bool.false_eq_true, if_false, h2, hp, h5, Bool.not_false, if_true]
  · intro a b c
    rfl

end PyLean.Itertools
