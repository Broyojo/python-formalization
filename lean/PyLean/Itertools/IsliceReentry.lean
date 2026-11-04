import PyLean.Itertools.IsliceProps
import PyLean.Itertools.PairwiseReentry

/-!
`islice_next` (Modules/itertoolsmodule.c:1697-1734) with an input that may raise
and may call `next()` on the same islice object; `cIsliceNext` in `Islice.lean`
reads a plain list and cannot express that.

`islice_next` reads `lz->it` once into a local (:1701), checks it (:1706-1707) and
caches its `tp_iternext` (:1709); every pull goes through that local, which holds
no reference of its own. `lz->cnt` and `lz->next` are re-read after every pull
(:1710, :1715, :1717, :1722-1728), so the outer call carries on from whatever a
re-entrant call left there. `hooks` holds, for successive items the input hands
out, how many `next()` calls on the islice its `__next__` makes after taking the
item and before returning it (as a `map` function does). They run through
`isRun`, the function that runs top-level calls; the caller catches what they
raise.

A call that reaches `empty` (:1731-1733) clears `lz->it`, dropping the islice's
reference, while an outer call may still be using the local `it`. `sole` says that
reference was the only one besides the running `__next__` calls (whose `self`
keeps the iterator alive; `active` counts them): then the iterator is freed when
the last of those calls returns, and the outer call's next pull reads freed
memory. That is `crash`. On CPython 3.15.2 and main it is a segfault
(python/cpython#142732). With other references (`sole = false`), the outer call
keeps pulling from an iterator the islice has let go.

Scope: the input is a Python-level iterator (a class with `__next__`), so a
running `__next__` holds `self`; `islice_next` re-entering itself through a C
iterator that drops its own state is not modelled.

`isTimes_pure` shows that with nothing re-entering this is `cIsliceNext`, so the
theorems of `IsliceProps.lean` hold for this mirror.
-/

namespace PyLean.Itertools

open PyLean

variable {α : Type}

/-- An `isliceobject` and its input. `src` is the iterator itself, which outlives
`lz->it`; `live` is `lz->it != NULL`. -/
structure IsS (α : Type) where
  src : Src α
  live : Bool
  next : Int
  stop : Int
  step : Int
  cnt : Int
  sole : Bool := false
  active : Nat := 0
  freed : Bool := false
  hooks : List Nat := []
  log : List (NextRes α) := []
  crashed : Bool := false

/-- What a pull through the local `it` gave. -/
inductive IsPull (α : Type) where
  | item (v : α)
  | done
  | fail (e : PyExc)
  | crash

/-- `iternext(it)` (:1711, :1719) through the local `it`. On a freed iterator the
process dies. Otherwise the input takes its item, then runs its hook with one
more `__next__` active; when that `__next__` returns and no other is running,
an iterator the islice has let go and nobody else holds is freed. -/
def isPull (run : Nat → IsS α → IsS α) (s : IsS α) : IsPull α × IsS α :=
  if s.freed then (.crash, { s with crashed := true })
  else match s.src.next with
    | .done => (.done, s)
    | .fail e rest => (.fail e, { s with src := rest })
    | .item v rest =>
      let s := match s.hooks with
        | [] => { s with src := rest }
        | h :: hs =>
          let t := run h { s with src := rest, hooks := hs, active := s.active + 1 }
          { t with active := t.active - 1 }
      (.item v, if !s.live && s.sole && s.active == 0 then { s with freed := true } else s)

/-- How the skip loop ended. -/
inductive IsSk where
  | cont
  | empty (e : Option PyExc)
  | crash

/-- The `while (lz->cnt < lz->next)` loop (:1710-1716), re-reading both fields on
every iteration. Each iteration but the last takes an item, so
`src.items.length + 1` iterations are enough. -/
def isSkip (run : Nat → IsS α → IsS α) : Nat → IsS α → IsSk × IsS α
  | 0, s => (.empty (some .modelFuel), s)
  | fuel + 1, s =>
    if s.cnt < s.next then
      match isPull run s with
      | (.item _, s) => isSkip run fuel { s with cnt := s.cnt + 1 }
      | (.done, s) => (.empty none, s)
      | (.fail e, s) => (.empty (some e), s)
      | (.crash, s) => (.crash, s)
    else (.cont, s)

/-- :1723-1728: `lz->next += step` in `size_t` (two's complement wraparound), then
`next = stop` if that wrapped below the old value or passed `stop`. -/
def isAdvance (next stop step : Int) : Int :=
  if wrapSsize (next + step) < next || (stop != -1 && wrapSsize (next + step) > stop) then stop
  else wrapSsize (next + step)

/-- A `NULL` return: `StopIteration` when no exception is set. -/
def isFail {β : Type} : Option PyExc → NextRes β
  | none => .stop
  | some e => .exc e

/-- `islice_next` (:1697-1734). `stop` is the local copy of :1702 (`lz->stop`
never changes); `goto empty` clears `lz->it` (:1731-1733). A dead process
answers nothing more. -/
def isNext (run : Nat → IsS α → IsS α) (s : IsS α) : NextRes α × IsS α :=
  if s.crashed then (.stop, s)
  else if !s.live then (.stop, s)
  else
    match isSkip run (s.src.items.length + 1) s with
    | (.crash, s) => (.stop, s)
    | (.empty e, s) => (isFail e, { s with live := false })
    | (.cont, s) =>
      if s.stop != -1 && s.cnt >= s.stop then (.stop, { s with live := false })
      else match isPull run s with
        | (.crash, s) => (.stop, s)
        | (.done, s) => (.stop, { s with live := false })
        | (.fail e, s) => (.exc e, { s with live := false })
        | (.item v, s) => (.val v, { s with cnt := s.cnt + 1, next := isAdvance s.next s.stop s.step })

/-- `n` calls of `next()`; a result joins the log when its call returns, so the
results of re-entrant calls come first. Nothing is logged once the process died. -/
def isTimes (run : Nat → IsS α → IsS α) : Nat → IsS α → IsS α
  | 0, s => s
  | n + 1, s =>
    if s.crashed then s
    else
      let (r, s) := isNext run s
      isTimes run n (if s.crashed then s else { s with log := s.log ++ [r] })

/-- Runs `n` calls. Each hook is used once, so `hooks.length + 1` levels are
enough. -/
def isRun : Nat → Nat → IsS α → IsS α
  | 0, _, s => s
  | d + 1, n, s => isTimes (isRun d) n s

/-- The state `islice_new` (:1590-1674) builds, around the input iterator. -/
def isInit (src : Src α) (st : IsliceState α) (sole : Bool) (hooks : List Nat) : IsS α :=
  { src := src, live := true, next := st.next, stop := st.stop, step := st.step, cnt := st.cnt,
    sole := sole, hooks := hooks }

/-- `islice(seq, *args)`, then `n` calls of `next()`: the results, whether the
process died, and how many items the input handed out. -/
def cIsliceR (seq : Obj α) (args : List (Option Int)) (sole : Bool) (hooks : List Nat) (n : Nat) :
    Py (List (NextRes α) × Bool × Nat) :=
  match cIsliceNew seq args with
  | .error e => .error e
  | .ok st =>
    match st.it with
    | none => .ok ([], false, 0)
    | some src =>
      let s := isRun (hooks.length + 1) n (isInit src st sole hooks)
      .ok (s.log, s.crashed, src.items.length - s.src.items.length)

/-! ## When nothing re-enters this is `cIsliceNext` -/

/-- `n` calls of `next()` on the plain model. -/
def isPureTimes : Nat → IsliceState α → List (NextRes α)
  | 0, _ => []
  | n + 1, s => let (r, s) := stepRes (cIsliceNext s); r :: isPureTimes n s

theorem runOf_isPure : ∀ (n : Nat) (s : IsliceState α), runOf (isPureTimes n s) = drain cIsliceNext n s
  | 0, _ => rfl
  | n + 1, s => by
    simp only [isPureTimes, drain]
    cases hs : cIsliceNext s with
    | «yield» a s' => simp [stepRes, runOf, runOf_isPure n s']
    | stop s' => simp [stepRes, runOf]
    | raise e s' => simp [stepRes, runOf]

theorem drainSt_fst {σ β : Type} (f : σ → Step σ β) : ∀ (n : Nat) (s : σ), (drainSt f n s).1 = drain f n s
  | 0, _ => rfl
  | n + 1, s => by
    simp only [drainSt, drain]
    cases f s with
    | «yield» a s' => simp [drainSt_fst f n s']
    | stop _ => rfl
    | raise _ _ => rfl

/-- How an `IsS` with nothing re-entering matches an `IsliceState`; `L` is its log. -/
def IsRel (L : List (NextRes α)) (p : IsS α) (c : IsliceState α) : Prop :=
  p.hooks = [] ∧ p.freed = false ∧ p.crashed = false ∧ p.log = L ∧ p.next = c.next ∧ p.stop = c.stop ∧
    p.step = c.step ∧ p.cnt = c.cnt ∧
    (match c.it with
     | some src => p.live = true ∧ p.src = src
     | none => p.live = false)

theorem isSkip_pure (run : Nat → IsS α → IsS α) : ∀ (fuel : Nat) (p : IsS α),
    p.hooks = [] → p.freed = false → p.live = true → p.src.items.length < fuel →
    isSkip run fuel p = match cIsliceSkip p.next p.src.items p.cnt with
      | (none, cnt) => (.empty p.src.err, { p with src := ⟨[], none⟩, cnt := cnt })
      | (some l, cnt) => (.cont, { p with src := ⟨l, p.src.err⟩, cnt := cnt })
  | 0, _, _, _, _, h => by simp at h
  | fuel + 1, p, hh, hf, hl, hlen => by
    obtain ⟨⟨items, err⟩, live, next, stop, step, cnt, sole, active, freed, hooks, log, crashed⟩ := p
    simp only at hh hf hl hlen
    subst hh hf hl
    cases items with
    | nil =>
      simp only [isSkip, cIsliceSkip]
      by_cases hc : cnt < next
      · cases err <;> simp [hc, isPull, Src.next]
      · simp [hc]
    | cons x xs =>
      simp only [isSkip, cIsliceSkip]
      by_cases hc : cnt < next
      · simp only [hc, if_true, isPull, Src.next, Bool.false_eq_true, if_false, Bool.not_true,
          Bool.false_and]
        exact isSkip_pure run fuel _ rfl rfl rfl (by simp at hlen ⊢; omega)
      · simp [hc]

theorem isNext_pure (run : Nat → IsS α → IsS α) (L : List (NextRes α)) (p : IsS α)
    (c : IsliceState α) (h : IsRel L p c) :
    (isNext run p).1 = (stepRes (cIsliceNext c)).1 ∧ IsRel L (isNext run p).2 (stepRes (cIsliceNext c)).2 := by
  obtain ⟨hh, hf, hc, hL, hn, hs, hst, hcnt, hm⟩ := h
  obtain ⟨psrc, live, next, stop, step, cnt, sole, active, freed, hooks, log, crashed⟩ := p
  simp only at hh hf hc hL hn hs hst hcnt hm
  subst hh hf hc hL hn hs hst hcnt
  cases hit : c.it with
  | none =>
    rw [hit] at hm
    subst hm
    simp [isNext, cIsliceNext, hit, stepRes, IsRel]
  | some src =>
    rw [hit] at hm
    obtain ⟨hl, hsrc⟩ := hm
    subst hl hsrc
    obtain ⟨l, err⟩ := psrc
    have hsk := isSkip_pure run (l.length + 1)
      ⟨⟨l, err⟩, true, c.next, c.stop, c.step, c.cnt, sole, active, false, [], log, false⟩ rfl rfl rfl (by simp)
    simp only at hsk
    simp only [isNext, Bool.false_eq_true, if_false, Bool.not_true, hsk, cIsliceNext, hit]
    cases hk : cIsliceSkip c.next l c.cnt with
    | mk r cnt =>
      cases r with
      | none =>
        cases err <;> simp [isFail, cIsliceEnded, stepRes, IsRel]
      | some l' =>
        simp only
        by_cases hstop : (c.stop != -1 && decide (cnt ≥ c.stop)) = true
        · simp [hstop, stepRes, IsRel]
        · simp only [hstop, Bool.false_eq_true, if_false]
          cases l' with
          | nil =>
            cases err <;> simp [isPull, Src.next, cIsliceEnded, stepRes, IsRel]
          | cons v rest =>
            simp [isPull, Src.next, stepRes, IsRel, isAdvance]

theorem isTimes_pure (run : Nat → IsS α → IsS α) : ∀ (n : Nat) (L : List (NextRes α)) (p : IsS α)
    (c : IsliceState α), IsRel L p c → (isTimes run n p).log = L ++ isPureTimes n c ∧
      (isTimes run n p).crashed = false
  | 0, L, p, _, h => by simp [isTimes, isPureTimes, h.2.2.2.1, h.2.2.1]
  | n + 1, L, p, c, h => by
    have hs := isNext_pure run L p c h
    simp only [isTimes, isPureTimes]
    rw [if_neg (by simp [h.2.2.1])]
    cases hq : isNext run p with
    | mk r s =>
      cases hq2 : stepRes (cIsliceNext c) with
      | mk r2 c2 =>
        rw [hq, hq2] at hs
        obtain ⟨h1, h2⟩ := hs
        simp only at h1 h2
        subst h1
        have hcr : s.crashed = false := h2.2.2.1
        have hrel : IsRel (L ++ [r]) { s with log := s.log ++ [r] } c2 := by
          obtain ⟨a, b, c', d, e⟩ := h2
          exact ⟨a, b, c', by simp [d], e⟩
        simp only
        rw [if_neg (by simp [hcr])]
        obtain ⟨k1, k2⟩ := isTimes_pure run n (L ++ [r]) _ c2 hrel
        exact ⟨by rw [k1]; simp, k2⟩

/-! ## Properties -/

/-- With an input that does not re-enter, for every element type, input object
(not iterable, or raising after its items), arguments, and whether or not the
islice holds the only reference: `len + 1` calls of `next()` on this mirror give
exactly the run of `cIsliceNext` (so the theorems of `IsliceProps.lean` hold for
it), and the process survives. -/
def IsliceReentryPure : Prop :=
  ∀ (α : Type) (seq : Obj α) (args : List (Option Int)) (sole : Bool),
    (match cIsliceR seq args sole [] (seq.len + 1) with
     | .ok (rs, crashed, _) => (runOf rs, crashed)
     | .error e => (Run.err e, false)) = ((cIslice seq args).1, false)

theorem cIsliceNew_it (seq : Obj α) (args : List (Option Int)) (st : IsliceState α)
    (h : cIsliceNew seq args = .ok st) : ∃ src, st.it = some src := by
  simp only [cIsliceNew] at h
  cases ha : cIsliceArgs args with
  | error e => simp [ha] at h
  | ok v =>
    obtain ⟨start, stop, step⟩ := v
    cases hg : getIter seq with
    | error e => simp [ha, hg] at h
    | ok it =>
      simp only [ha, hg, Except.ok.injEq] at h
      exact ⟨it, by rw [← h]⟩

theorem isliceReentryPure_proven : IsliceReentryPure := by
  intro α seq args sole
  simp only [cIsliceR, cIslice]
  cases hn : cIsliceNew seq args with
  | error e => rfl
  | ok st =>
    obtain ⟨src, hsrc⟩ := cIsliceNew_it seq args st hn
    simp only [hsrc, List.length_nil, isRun]
    obtain ⟨k1, k2⟩ := isTimes_pure (isRun 0) (seq.len + 1) [] (isInit src st sole []) st
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [hsrc, isInit]⟩
    simp only [isRun] at k1 k2
    rw [k1, k2, drainSt_fst, ← runOf_isPure]
    rfl

/-- The re-entrant path, for every state and re-entrant code: a call with nothing
to skip (`cnt >= next`) and below `stop` takes the input's next item `v`, whose
`__next__` then runs `h` calls of `next()` on the islice; `R` is the state they
leave, whatever they did (consumed items, advanced `cnt` and `next`, or reached
`empty` and cleared `lz->it`). Unless that freed the iterator, the outer call
returns `v` and advances the counters `R` holds (:1722-1728), not the ones it
started with. Concretely, on 3.15.2, `islice(it, 5)` over 0..9 where taking `0`
calls `next()` once gives `1` to the inner call and then `0, 2, 3, 4` and the
end; `islice(it, 2, None)` gives `3` to the inner call and then `4, 5, ..., 9`. -/
def IsliceReentryRereads : Prop :=
  (∀ (α : Type) (run : Nat → IsS α → IsS α) (s : IsS α) (v : α) (rest : Src α) (h : Nat) (hs : List Nat),
    s.crashed = false → s.live = true → s.freed = false → s.next ≤ s.cnt →
    ¬(s.stop != -1 && decide (s.cnt ≥ s.stop)) = true →
    s.src.next = .item v rest → s.hooks = h :: hs →
    ∀ R, R = run h { s with src := rest, hooks := hs, active := s.active + 1 } →
    ¬(!R.live && R.sole && R.active - 1 == 0) = true →
    isNext run s =
      (.val v, { R with active := R.active - 1, cnt := R.cnt + 1, next := isAdvance R.next R.stop R.step })) ∧
  cIsliceR (.iter (List.range 10) none) [some 5] false [1] 6 =
    .ok ([.val 1, .val 0, .val 2, .val 3, .val 4, .stop, .stop], false, 5) ∧
  cIsliceR (.iter (List.range 10) none) [some 2, none] false [1] 8 =
    .ok ([.val 3, .val 4, .val 5, .val 6, .val 7, .val 8, .val 9, .stop, .stop], false, 10)

theorem isliceReentryRereads_proven : IsliceReentryRereads := by
  refine ⟨?_, rfl, rfl⟩
  intro α run s v rest h hs hc hl hf hle hstop hsrc hh R hR hfree
  subst hR
  have hsk : isSkip run (s.src.items.length + 1) s = (.cont, s) := by
    simp only [isSkip]
    rw [if_neg (by omega)]
  have hp : isPull run s = (.item v, { run h { s with src := rest, hooks := hs, active := s.active + 1 } with
      active := (run h { s with src := rest, hooks := hs, active := s.active + 1 }).active - 1 }) := by
    rw [isPull, if_neg (by simp [hf]), hsrc]
    simp only [hh, hfree, Bool.false_eq_true, ↓reduceIte]
  simp only [isNext, hc, hl, Bool.false_eq_true, ↓reduceIte, Bool.not_true, hsk, hstop, hp]

/-- Did the process die? -/
def isCrashes (seq : Obj α) (args : List (Option Int)) (sole : Bool) (hooks : List Nat) (n : Nat) : Bool :=
  match cIsliceR seq args sole hooks n with
  | .ok (_, crashed, _) => crashed
  | .error _ => false

/-- Invariant: Python code cannot make the interpreter use freed memory. For every
input, arguments, re-entrant `__next__` and number of calls, the process survives. -/
def IsliceNoUseAfterFree : Prop :=
  ∀ (α : Type) (seq : Obj α) (args : List (Option Int)) (sole : Bool) (hooks : List Nat) (n : Nat),
    isCrashes seq args sole hooks n = false

/-- `islice(it, 2, None)` holding the only reference to `it`, which yields one
item; taking it, `__next__` calls `next()` on the islice once. That call pulls,
finds the input exhausted and clears `lz->it`; when `__next__` returns, the
iterator is freed, and the outer call, still skipping (`cnt = 1 < next = 2`),
pulls through its stale local `it`. CPython 3.15.2 and main segfault. -/
theorem isliceNoUseAfterFree_refuted : ¬IsliceNoUseAfterFree := by
  intro h
  have := h Nat (.iter [7] none) [some 2, none] true [1] 1
  revert this
  decide

/-- Nothing can be freed: the islice does not hold the only reference. -/
def IsShared (s : IsS α) : Prop := s.sole = false ∧ s.freed = false ∧ s.crashed = false

section Shared

variable (run : Nat → IsS α → IsS α) (hrun : ∀ n t, IsShared t → IsShared (run n t))
include hrun

theorem isPull_shared (s : IsS α) (hq : IsShared s) :
    IsShared (isPull run s).2 ∧ (isPull run s).1 ≠ .crash := by
  obtain ⟨src, live, next, stop, step, cnt, sole, active, freed, hooks, log, crashed⟩ := s
  obtain ⟨h1, h2, h3⟩ := hq
  simp only at h1 h2 h3
  subst h1 h2 h3
  simp only [isPull, Bool.false_eq_true, if_false]
  cases hn : src.next with
  | done => simp [IsShared]
  | fail e rest => simp [IsShared]
  | item v rest =>
    cases hooks with
    | nil => simp [IsShared]
    | cons k ks =>
      obtain ⟨g1, g2, g3⟩ :=
        hrun k ⟨rest, live, next, stop, step, cnt, false, active + 1, false, ks, log, false⟩ ⟨rfl, rfl, rfl⟩
      simp [IsShared, g1, g2, g3]

theorem isSkip_shared : ∀ (fuel : Nat) (s : IsS α), IsShared s →
    IsShared (isSkip run fuel s).2 ∧ (isSkip run fuel s).1 ≠ .crash
  | 0, s, hq => ⟨hq, by simp [isSkip]⟩
  | fuel + 1, s, hq => by
    simp only [isSkip]
    split
    · obtain ⟨k1, k2⟩ := isPull_shared run hrun s hq
      cases hp : isPull run s with
      | mk r s' =>
        rw [hp] at k1 k2
        cases r with
        | item v => exact isSkip_shared fuel _ k1
        | done => exact ⟨k1, by simp⟩
        | fail e => exact ⟨k1, by simp⟩
        | crash => exact absurd rfl k2
    · exact ⟨hq, by simp⟩

theorem isNext_shared (s : IsS α) (hq : IsShared s) : IsShared (isNext run s).2 := by
  have hc := hq.2.2
  simp only [isNext, hc, Bool.false_eq_true, if_false]
  split
  · exact hq
  · obtain ⟨k1, k2⟩ := isSkip_shared run hrun (s.src.items.length + 1) s hq
    cases hk : isSkip run (s.src.items.length + 1) s with
    | mk r s' =>
      rw [hk] at k1 k2
      cases r with
      | crash => exact absurd rfl k2
      | empty e => exact k1
      | cont =>
        simp only
        split
        · exact k1
        · obtain ⟨p1, p2⟩ := isPull_shared run hrun s' k1
          cases hp : isPull run s' with
          | mk r2 s2 =>
            rw [hp] at p1 p2
            cases r2 with
            | crash => exact absurd rfl p2
            | done => exact p1
            | fail e => exact p1
            | item v => exact p1

theorem isTimes_shared : ∀ (n : Nat) (s : IsS α), IsShared s → IsShared (isTimes run n s)
  | 0, _, hq => hq
  | n + 1, s, hq => by
    simp only [isTimes]
    rw [if_neg (by simp [hq.2.2])]
    have k := isNext_shared run hrun s hq
    cases hq2 : isNext run s with
    | mk r s' =>
      rw [hq2] at k
      simp only at k ⊢
      apply isTimes_shared n
      split
      · exact k
      · exact k

end Shared

theorem isRun_shared : ∀ (d n : Nat) (s : IsS α), IsShared s → IsShared (isRun d n s)
  | 0, _, _, hq => hq
  | d + 1, n, s, hq => isTimes_shared (isRun d) (fun n t ht => isRun_shared d n t ht) n s hq

/-- When something else holds the input (`sole = false`), nothing is freed and
the process survives, for every input, arguments, re-entrant `__next__` and
number of calls; the refutation above needs the islice to hold the only
reference. -/
def IsliceNoCrashShared : Prop :=
  ∀ (α : Type) (seq : Obj α) (args : List (Option Int)) (hooks : List Nat) (n : Nat),
    isCrashes seq args false hooks n = false

theorem isliceNoCrashShared_proven : IsliceNoCrashShared := by
  intro α seq args hooks n
  simp only [isCrashes, cIsliceR]
  cases hn : cIsliceNew seq args with
  | error e => rfl
  | ok st =>
    simp only
    cases hit : st.it with
    | none => rfl
    | some src => exact (isRun_shared _ n _ ⟨rfl, rfl, rfl⟩).2.2

end PyLean.Itertools
