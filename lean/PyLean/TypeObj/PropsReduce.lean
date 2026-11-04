import PyLean.TypeObj.Reduce

/-!
Properties of the pickling support in `Objects/typeobject.c:7912-8461`. They quantify over every
`Rt`, so over every `__getstate__`, `__getattribute__` and `__slotnames__` a class can define.
-/

namespace PyLean.TypeObj

/-- **`__getnewargs_ex__` passes a tuple and a dict, and nothing else.** `checkNewargsEx` succeeds
on exactly the pairs whose first item is a tuple and whose second is a dict, and returns those
two, with the world unchanged. So `reduce_newobj` can read both directly, which it does at
`Objects/typeobject.c:8313` and `:8302`. -/
def NewargsExValidated : Prop :=
  ∀ (v a k : Val) (w : World),
    (∃ w', checkNewargsEx v w = .ok (a, k) w') ↔
      (tupleOf w v = some [a, k] ∧ (tupleOf w a).isSome = true ∧ (dictOf w k).isSome = true)

theorem newargsExValidated_proven : NewargsExValidated := by
  intro v a k w
  constructor
  · rintro ⟨w', h⟩
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
            exact ⟨rfl, h3, h4⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨w, ?_⟩
    have h5 : ¬ tupleOf w a = none := by intro hh; simp [hh] at h2
    have h6 : ¬ dictOf w k = none := by intro hh; simp [hh] at h3
    simp [checkNewargsEx, h1, h5, h6]

/-- **`__getnewargs_ex__` comes first, and a missing method is not an error.** For every `Rt`:
`_PyObject_GetNewArguments` checks what `__getnewargs_ex__` returned, tries `__getnewargs__` only
if the first is absent, rejects a result of that which is no tuple, and gives two NULLs if both are
absent. So an object without either pickles as having no arguments. -/
def GetNewArgumentsOrder : Prop :=
  (∀ (rt : Rt) (obj m v : Val) (w w1 w2 : World),
    lookupSpecial rt obj "__getnewargs_ex__" w = .ok (some m) w1 → rt.call m [] [] w1 = .ok v w2 →
    getNewArguments rt obj w =
      ((do let (a, k) ← checkNewargsEx v; pure (some a, some k)) : M _) w2) ∧
  (∀ (rt : Rt) (obj m v : Val) (w w1 w2 w3 : World),
    lookupSpecial rt obj "__getnewargs_ex__" w = .ok none w1 →
    lookupSpecial rt obj "__getnewargs__" w1 = .ok (some m) w2 → rt.call m [] [] w2 = .ok v w3 →
    (tupleOf w3 v).isSome = true → getNewArguments rt obj w = .ok (some v, none) w3) ∧
  (∀ (rt : Rt) (obj m v : Val) (w w1 w2 w3 : World),
    lookupSpecial rt obj "__getnewargs_ex__" w = .ok none w1 →
    lookupSpecial rt obj "__getnewargs__" w1 = .ok (some m) w2 → rt.call m [] [] w2 = .ok v w3 →
    (tupleOf w3 v).isSome = false → getNewArguments rt obj w =
      (typeErr s!"__getnewargs__ should return a tuple, not '{trunc 200 (typeName w3 v)}'" :
        M (Option Val × Option Val)) w3) ∧
  (∀ (rt : Rt) (obj : Val) (w w1 w2 : World),
    lookupSpecial rt obj "__getnewargs_ex__" w = .ok none w1 →
    lookupSpecial rt obj "__getnewargs__" w1 = .ok none w2 →
    getNewArguments rt obj w = .ok (none, none) w2)

theorem getNewArgumentsOrder_proven : GetNewArgumentsOrder := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro rt obj m v w w1 w2 h1 h2
    simp [getNewArguments, h1, h2]
  · intro rt obj m v w w1 w2 w3 h1 h2 h3 h4
    have h5 : ¬ tupleOf w3 v = none := by intro hh; simp [hh] at h4
    simp [getNewArguments, h1, h2, h3, h5]
  · intro rt obj m v w w1 w2 w3 h1 h2 h3 h4
    have h5 : tupleOf w3 v = none := by
      cases hh : tupleOf w3 v <;> simp_all
    simp [getNewArguments, h1, h2, h3, h5, typeErr, raiseC]
  · intro rt obj w w1 w2 h1 h2
    simp [getNewArguments, h1, h2]

/-- **The slot names are `None` or a list.** For every class and every `Rt`, a value that
`_PyType_GetSlotNames` hands back is `None` or a list, which the `assert` at
`Objects/typeobject.c:8007` relies on before `PyList_GET_SIZE`. A cached value of that kind is
returned as it is, with no call of `copyreg`, and a cached value of any other type is the exact
`TypeError`. -/
def SlotNamesWellTyped : Prop :=
  (∀ (rt : Rt) (cls : Addr) (s : Val) (w w' : World), typeGetSlotNames rt cls w = .ok s w' →
    s.is .none = true ∨ (listOf w' s).isSome = true) ∧
  (∀ (rt : Rt) (cls : Addr) (s : Val) (w : World),
    NameDict.get? (tdata w cls).dict "__slotnames__" = some s →
    (s.is .none = true ∨ (listOf w s).isSome = true) → typeGetSlotNames rt cls w = .ok s w) ∧
  (∀ (rt : Rt) (cls : Addr) (s : Val) (w : World),
    NameDict.get? (tdata w cls).dict "__slotnames__" = some s →
    s.is .none = false → (listOf w s).isSome = false →
    typeGetSlotNames rt cls w =
      (typeErr s!"{trunc 200 (tpName w cls)}.__slotnames__ should be a list or None, not {trunc 200 (typeName w s)}" : M Val) w)

theorem slotNamesWellTyped_proven : SlotNamesWellTyped := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · intro rt cls s w hd h1
    simp [typeGetSlotNames, hd, h1]
  · intro rt cls s w hd h1 h2
    simp [typeGetSlotNames, hd, h1, h2]
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
    cases hcr : w.copyregSlotnames with
    | none =>
      cases hc : copyregSlotnames rt cls w with
      | err e w1 => simp [hd, hcr, hc] at h
      | ok r w1 =>
        by_cases h1 : r.is .none = true ∨ (listOf w1 r).isSome = true
        · simp [hd, hcr, hc, h1] at h
          obtain ⟨rfl, rfl⟩ := h
          exact h1
        · simp [hd, hcr, hc, h1, typeErr, raiseC] at h
    | some f =>
      cases hc : rt.call f [.obj cls] [] w with
      | err e w1 => simp [hd, hcr, hc] at h
      | ok r w1 =>
        by_cases h1 : r.is .none = true ∨ (listOf w1 r).isSome = true
        · simp [hd, hcr, hc, h1] at h
          obtain ⟨rfl, rfl⟩ := h
          exact h1
        · simp [hd, hcr, hc, h1, typeErr, raiseC] at h

/-- **The guard on `__slotnames__` holds.** After a round of the loop of
`object_getstate_default` at `i`, for every getter: a list of another size is the exact
`RuntimeError` (`Objects/typeobject.c:8066`), the same size ends the loop at the last index, and
if the loop completes at all, the list has its original size. -/
def GetstateSlotsGuard : Prop :=
  (∀ (rt : Rt) (obj names : Val) (size : Nat) (slots : Addr) (fuel i : Nat) (w w' : World),
    i < size → getstateSlotsLoop rt obj names size slots fuel i w = .ok () w' →
    ((listOf w' names).getD []).length = size) ∧
  (∀ (rt : Rt) (obj names : Val) (size : Nat) (slots : Addr) (fuel i : Nat) (w w1 : World),
    i < size → getstateSlotStep rt obj names slots i w = .ok () w1 →
    ((listOf w1 names).getD []).length ≠ size →
    getstateSlotsLoop rt obj names size slots (fuel + 1) i w =
      (runtimeErr "__slotnames__ changed size during iteration" : M Unit) w1) ∧
  (∀ (rt : Rt) (obj names : Val) (size : Nat) (slots : Addr) (fuel i : Nat) (w w1 : World),
    i + 1 = size → getstateSlotStep rt obj names slots i w = .ok () w1 →
    ((listOf w1 names).getD []).length = size →
    getstateSlotsLoop rt obj names size slots (fuel + 2) i w = .ok () w1)

theorem getstateSlotsGuard_proven : GetstateSlotsGuard := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · intro rt obj names size slots fuel i w w1 hi hs hlen
    have hni : ¬ i ≥ size := by omega
    have hb : (((listOf w1 names).getD []).length != size) = true := by simpa using hlen
    rw [getstateSlotsLoop]
    simp only [hni, ite_false, M.bind_app, hs, getW_app]
    rw [if_pos hb]
    simp [runtimeErr, raiseC]
  · intro rt obj names size slots fuel i w w1 hi hs hlen
    have hni : ¬ i ≥ size := by omega
    have hge : i + 1 ≥ size := by omega
    rw [getstateSlotsLoop]
    simp only [hni, ite_false, M.bind_app, hs, getW_app, hlen, bne_self_eq_false,
      Bool.false_eq_true]
    rw [getstateSlotsLoop]
    simp [hge]
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
