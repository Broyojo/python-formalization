import PyLean.TypeObj.ExcSetstateC

/-!
Properties of the `__setstate__` loop over the real dict table (`ExcSetstateC`).
-/

namespace PyLean.TypeObj.SetstateC

open PyLean PyLean.DictSet

/-- `PyDict_Next`'s walk from `pos` of a dict that does not change: the items it yields. -/
inductive Visits (d : SD) : Int → List (Nat × Nat) → Prop where
  | done {pos : Int} : dictNext d pos = none → Visits d pos []
  | step {pos pos' : Int} {k v : Nat} {h : Int} {L : List (Nat × Nat)} :
      dictNext d pos = some (pos', k, v, h) → Visits d pos' L → Visits d pos ((k, v) :: L)

/-- **The `__setstate__` loop, step by step, on the real table.** Each turn calls `PyDict_Next`
on the dict as it is now, from the position the last turn left (`:246`): at the end of the
table the loop stops; otherwise the attribute is set through `__setattr__`, whose effects on the
dict (insertions, which may resize and compact it, and deletions, which leave dummy slots) are
seen by the next turn, and a raise is the result (`:252-254`). With a `__setattr__` that leaves
the dict alone, the loop sets exactly the items of the walk, in order. The fuel bound
`L.length < f` is the model's, not Python's. -/
def SetstateTableSteps : Prop :=
  (∀ (script : Nat → List DAct) (pos : Int) (s : St) (f : Nat),
    dictNext s.d pos = none → setstateLoop script (f + 1) pos s = (.ok (), s)) ∧
  (∀ (script : Nat → List DAct) (pos pos' : Int) (k v : Nat) (h : Int) (s s' : St) (f : Nat),
    dictNext s.d pos = some (pos', k, v, h) → setAttr script k v s = (.ok (), s') →
    setstateLoop script (f + 1) pos s = setstateLoop script f pos' s') ∧
  (∀ (script : Nat → List DAct) (pos pos' : Int) (k v : Nat) (h : Int) (s s' : St) (e : PyExc)
      (f : Nat),
    dictNext s.d pos = some (pos', k, v, h) → setAttr script k v s = (.error e, s') →
    setstateLoop script (f + 1) pos s = (.error e, s')) ∧
  (∀ (script : Nat → List DAct) (k v : Nat) (s : St) (d' : SD),
    runActs (script k) s.d = (.ok (), d') →
    setAttr script k v s = (.ok (), { d := d', log := s.log ++ [(k, v)] })) ∧
  (∀ (script : Nat → List DAct) (s : St) (pos : Int) (L : List (Nat × Nat)) (f : Nat),
    (∀ k, script k = []) → Visits s.d pos L → L.length < f →
    setstateLoop script f pos s = (.ok (), { s with log := s.log ++ L }))

theorem visits_loop (script : Nat → List DAct) (hs : ∀ k, script k = []) :
    ∀ (d : SD) (pos : Int) (L : List (Nat × Nat)), Visits d pos L →
      ∀ (s : St) (f : Nat), s.d = d → L.length < f →
        setstateLoop script f pos s = (.ok (), { s with log := s.log ++ L }) := by
  intro d pos L hv
  induction hv with
  | done hn =>
    intro s f hd hl
    subst hd
    cases f with
    | zero => simp at hl
    | succ f => simp [setstateLoop, hn]
  | @step pos pos' k v h L hn _ ih =>
    intro s f hd hl
    subst hd
    cases f with
    | zero => simp at hl
    | succ f =>
      simp only [List.length_cons] at hl
      have ha : setAttr script k v s = (.ok (), { d := s.d, log := s.log ++ [(k, v)] }) := by
        simp [setAttr, hs k, runActs]
      simp only [setstateLoop, hn, ha]
      rw [ih { d := s.d, log := s.log ++ [(k, v)] } f rfl (by omega)]
      simp

theorem setstateTableSteps_proven : SetstateTableSteps := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro script pos s f h
    simp [setstateLoop, h]
  · intro script pos pos' k v h s s' f hn ha
    simp [setstateLoop, hn, ha]
  · intro script pos pos' k v h s s' e f hn ha
    simp [setstateLoop, hn, ha]
  · intro script k v s d' h
    simp [setAttr, h]
  · intro script s pos L f hs hv hl
    exact visits_loop script hs s.d pos L hv s f rfl hl

/-- **What 3.15.2 does when `__setattr__` changes the state.** Both cases run on CPython 3.15.2
with the same results:
* `st = {'a': 1, 'b': 2, 'c': 3}` and a `__setattr__` that runs `del st['a']` when setting `a`:
  the deletion leaves a dummy, nothing moves, and `a`, `b` and `c` are all set. A loop over a list
  that closes the gap (the interpreter's `setstateLoop`) skips `b`.
* `st` with `k0`..`k4`, then `del st['k0'], st['k1']`, and a `__setattr__` that adds `n1` when
  setting `k2`: the insertion finds no usable slot and resizes, which compacts the table under
  the iteration position, so `k3` and `k4` are skipped although they stay in the dict; only `k2`
  and `n1` are set. Behaviour on record, not a bug report: mutating a dict while `PyDict_Next`
  walks it has no promised result. -/
def SetstateTableExamples : Prop :=
  (setstateLoop (fun k => if k = 1 then [.del 1] else []) 10 0
      { d := build [(1, 1), (2, 2), (3, 3)] }).2.log = [(1, 1), (2, 2), (3, 3)] ∧
  (match (setstateLoop (fun k => if k = 2 then [.set 10 9] else []) 10 0
      { d := delAll [0, 1] (build [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4)]) }).1 with
   | .ok _ => true
   | .error _ => false) = true ∧
  (setstateLoop (fun k => if k = 2 then [.set 10 9] else []) 10 0
      { d := delAll [0, 1] (build [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4)]) }).2.log =
    [(2, 2), (10, 9)] ∧
  dictKeysList (setstateLoop (fun k => if k = 2 then [.set 10 9] else []) 10 0
      { d := delAll [0, 1] (build [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4)]) }).2.d = [2, 3, 4, 10]

theorem setstateTableExamples_proven : SetstateTableExamples := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end PyLean.TypeObj.SetstateC
