import PyLean.DictSet.SetAlgebra

/-!
The branches of the set algebra that an arbitrary iterable takes, for every key protocol and every
iterator: `__iter__` and `__next__` may raise and may change what the state holds, and each turn
sees what the last one left.
-/

namespace PyLean.DictSet

open PyLean

/-- `while ((key = PyIter_Next(it)) != NULL)`, turn by turn: the end of the script and exhaustion stop
it, an exception from the step or the body is the result in the state it left, the body can stop it,
and otherwise the next step runs on the state this turn left. -/
def ForIterBody : Prop :=
  ∀ (K : Type) (body : K → SM K Bool) (step : SM K (Option K)) (rest : List (SM K (Option K)))
    (s s' s'' : SetObj K) (key : K) (e : PyExc),
    forIter body [] s = (.ok false, s) ∧
    (step s = (.error e, s') → forIter body (step :: rest) s = (.error e, s')) ∧
    (step s = (.ok none, s') → forIter body (step :: rest) s = (.ok false, s')) ∧
    (step s = (.ok (some key), s') →
      (body key s' = (.error e, s'') → forIter body (step :: rest) s = (.error e, s'')) ∧
      (body key s' = (.ok true, s'') → forIter body (step :: rest) s = (.ok true, s'')) ∧
      (body key s' = (.ok false, s'') → forIter body (step :: rest) s = forIter body rest s''))
theorem forIterBody_proven : ForIterBody := by
  intro K body step rest s s' s'' key e
  refine ⟨rfl, fun h => ?_, fun h => ?_, fun h => ⟨fun hb => ?_, fun hb => ?_, fun hb => ?_⟩⟩
  all_goals simp_all [forIter, M.bind_run]

/-- One turn of the generic loop of `set_intersection` (:1763-1776), for every key protocol:
`PyObject_Hash` runs `__hash__`, whose failure is the result in the state it left (no
`set_unhashable_type` here); a failed lookup is the result; a key `so` does not hold does nothing;
and a key it holds goes in, and stops the loop when the result has caught up with `so` as `so` is
now. -/
def InterIterBody : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (soId : Nat) (key : K) (hash : Int)
    (s s1 s' s'' : SetObj K) (e : PyExc),
    (P.hashM key s = (.error e, s1) → interIterStep P soId key s = (.error e, s1)) ∧
    (P.hashM key s = (.ok hash, s1) →
      (onSet soId (setContainsEntry P key hash) s1 = (.error e, s') →
        interIterStep P soId key s = (.error e, s')) ∧
      (onSet soId (setContainsEntry P key hash) s1 = (.ok false, s') →
        interIterStep P soId key s = (.ok false, s')) ∧
      (onSet soId (setContainsEntry P key hash) s1 = (.ok true, s') →
        (setAddEntry P key hash s' = (.error e, s'') →
          interIterStep P soId key s = (.error e, s'')) ∧
        (setAddEntry P key hash s' = (.ok (), s'') →
          interIterStep P soId key s =
            (.ok (decide (s''.used ≥ (s''.live soId).used)), s''))))
theorem interIterBody_proven : InterIterBody := by
  intro K _ P soId key hash s s1 s' s'' e
  refine ⟨fun h => ?_, fun h => ⟨fun h1 => ?_, fun h1 => ?_, fun h1 => ⟨fun h2 => ?_, fun h2 => ?_⟩⟩⟩
  · simp [interIterStep, h, M.bind_run]
  · simp [interIterStep, h, h1, M.bind_run]
  · simp [interIterStep, h, h1, M.bind_run]
  · simp [interIterStep, h, h1, h2, M.bind_run]
  · by_cases hc : s''.used ≥ (s''.live soId).used <;>
      simp [interIterStep, h, h1, h2, hc, M.bind_run, M.get_run]

/-- The routes of the set methods on what is not a set, for every key protocol and iterator: each
opens with `PyObject_GetIter`, whose failure is the result, in the focus the C code has at that
point, and then runs the loop of its own. -/
def SetIterRoutes : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (it : ReIter (SetObj K) K) (id : Nat)
    (so s' : SetObj K) (e : PyExc),
    (setUpdate P (.live it) so = setUpdateIterable P it so) ∧
    (it.getIter so = (.error e, s') →
      setUpdateIterable P it so = (.error e, s') ∧
      setIsdisjoint P (.live it) so = (.error e, s') ∧
      setIssuperset P (.live it) id so = (.error e, s') ∧
      setDifferenceUpdateInternal P (.live it) id so = (.error e, s')) ∧
    (it.getIter so = (.ok (), s') →
      setIsdisjoint P (.live it) so =
        (match forIter (setContainsKey P) it.steps s' with
         | (.ok hit, s) => (.ok (!hit), s)
         | (.error e, s) => (.error e, s)) ∧
      setIssuperset P (.live it) id so =
        (match forIter (fun key => do
            let rv ← setContainsKey P key
            return !rv) it.steps s' with
         | (.ok miss, s) => (.ok (!miss), s)
         | (.error e, s) => (.error e, s)))
theorem setIterRoutes_proven : SetIterRoutes := by
  intro K _ P it id so s' e
  refine ⟨rfl, fun h => ⟨?_, ?_, ?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · simp [setUpdateIterable, M.bind_run, h]
  · simp [setIsdisjoint, setDisjointIter, SetArg.toReIter, M.bind_run, M.get_run, h]
  · simp [setIssuperset, SetArg.toReIter, M.bind_run, M.get_run, h]
  · simp [setDifferenceUpdateInternal, SetArg.toReIter, M.bind_run, M.get_run, h]
  · have h1 : setIsdisjoint P (.live it) so =
        (do it.getIter; let hit ← forIter (setContainsKey P) it.steps; pure (!hit)) so := by
      simp [setIsdisjoint, setDisjointIter, SetArg.toReIter, M.bind_run, M.get_run]
    rw [h1, M.bind_run, h]
    simp only [M.bind_run]
    cases forIter (setContainsKey P) it.steps s' with
    | mk r s => cases r <;> rfl
  · have h1 : setIssuperset P (.live it) id so =
        (do it.getIter
            let miss ← forIter (fun key => do
              let rv ← setContainsKey P key
              return !rv) it.steps
            pure (!miss)) so := by
      simp [setIssuperset, SetArg.toReIter, M.bind_run, M.get_run]
    rw [h1, M.bind_run, h]
    simp only [M.bind_run]
    cases forIter (fun key => do
        let rv ← setContainsKey P key
        return !rv) it.steps s' with
    | mk r s => cases r <;> rfl

end PyLean.DictSet
