import PyLean.TypeObj.Reduce

/-!
Properties of the pickling support in `Objects/typeobject.c:7286-7835`. They quantify over every
`Rt`, so over every `__getstate__`, `__getattribute__` and `__slotnames__` a class can define.
-/

namespace PyLean.TypeObj

/-- **`__getnewargs_ex__` passes only a tuple and a dict.** Whatever `__getnewargs_ex__` returned,
if `_PyObject_GetNewArguments` accepts it, then the result was a pair whose first item is a tuple
and whose second is a dict, and nothing else happened. So `reduce_newobj` can read both directly,
which it does at `Objects/typeobject.c:7687` and `:7676`. -/
def NewargsExValidated : Prop :=
  ∀ (v a k : Val) (w w' : World), checkNewargsEx v w = .ok (a, k) w' →
    w' = w ∧ tupleOf w v = some [a, k] ∧ (tupleOf w a).isSome = true ∧ (dictOf w k).isSome = true

theorem newargsExValidated_proven : NewargsExValidated := by
  intro v a k w w' h
  unfold checkNewargsEx at h
  simp only [M.bind_app, getW_app] at h
  cases hv : tupleOf w v with
  | none => simp [hv, typeErr, raiseC] at h
  | some xs =>
    rw [hv] at h
    match xs, h with
    | [], h => simp [valueErr, raiseC] at h
    | [_], h => simp [valueErr, raiseC] at h
    | _ :: _ :: _ :: _, h => simp [valueErr, raiseC] at h
    | [a', k'], h =>
      simp only at h
      by_cases h1 : (tupleOf w a').isNone = true
      · simp [h1, typeErr, raiseC] at h
      · by_cases h2 : (dictOf w k').isNone = true
        · simp [h1, h2, typeErr, raiseC] at h
        · simp [h1, h2] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          have h3 : (tupleOf w a').isSome = true := by
            cases hh : tupleOf w a' <;> simp_all
          have h4 : (dictOf w k').isSome = true := by
            cases hh : dictOf w k' <;> simp_all
          exact ⟨rfl, rfl, h3, h4⟩

/-- **The slot names are `None` or a list.** For every class and every `Rt`, whatever a class
stored in `__slotnames__` and whatever `copyreg._slotnames` returned, a value that
`_PyType_GetSlotNames` hands back is `None` or a list. This is what the `assert` at
`Objects/typeobject.c:7381` relies on before `PyList_GET_SIZE`. -/
def SlotNamesWellTyped : Prop :=
  ∀ (rt : Rt) (cls : Addr) (s : Val) (w w' : World), typeGetSlotNames rt cls w = .ok s w' →
    s.is .none = true ∨ (listOf w' s).isSome = true

theorem slotNamesWellTyped_proven : SlotNamesWellTyped := by
  intro rt cls s w w' h
  unfold typeGetSlotNames at h
  simp only [M.bind_app, getW_app] at h
  cases hd : NameDict.get? (tdata w cls).dict "__slotnames__" with
  | some c =>
    rw [hd] at h
    by_cases h1 : (c.is .none || (listOf w c).isSome) = true
    · simp [h1] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa using h1
    · simp [h1, typeErr, raiseC] at h
  | none =>
    cases hc : copyregSlotnames rt cls w with
    | err e w1 => simp [hd, hc] at h
    | ok r w1 =>
      by_cases h1 : r.is .none = true ∨ (listOf w1 r).isSome = true
      · simp [hd, hc, h1] at h
        obtain ⟨rfl, rfl⟩ := h
        exact h1
      · simp [hd, hc, h1, typeErr, raiseC] at h

/-- **The guard on `__slotnames__` holds.** If the loop of `object_getstate_default` completes and
visited anything, the list has its original size at the end, for every getter. A getter that
changed it either raised `RuntimeError` at `Objects/typeobject.c:7440` or put it back before the
check. -/
def GetstateSlotsGuard : Prop :=
  ∀ (rt : Rt) (obj names : Val) (size : Nat) (slots : Addr) (fuel i : Nat) (w w' : World),
    i < size → getstateSlotsLoop rt obj names size slots fuel i w = .ok () w' →
    ((listOf w' names).getD []).length = size

theorem getstateSlotsGuard_proven : GetstateSlotsGuard := by
  intro rt obj names size slots fuel
  induction fuel with
  | zero =>
    intro i w w' _ h
    simp [getstateSlotsLoop, raise] at h
  | succ fuel ih =>
    intro i w w' hi h
    rw [getstateSlotsLoop] at h
    have hni : ¬ i ≥ size := by omega
    simp only [hni, ite_false, M.bind_app] at h
    cases hs : getstateSlotStep rt obj names slots i w with
    | err e w1 => simp [hs] at h
    | ok u w1 =>
      simp only [hs, getW_app] at h
      by_cases hlen : ((listOf w1 names).getD []).length = size
      · simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ite_false] at h
        by_cases hnext : i + 1 < size
        · exact ih (i + 1) w1 w' hnext h
        · have hge : i + 1 ≥ size := by omega
          cases fuel with
          | zero => simp [getstateSlotsLoop, raise] at h
          | succ f =>
            rw [getstateSlotsLoop] at h
            simp [hge] at h
            subst h
            exact hlen
      · have hb : (((listOf w1 names).getD []).length != size) = true := by
          simpa using hlen
        simp [hb, runtimeErr, raiseC] at h

end PyLean.TypeObj
