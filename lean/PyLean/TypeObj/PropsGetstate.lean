import PyLean.TypeObj.PropsAttrExact

/-!
`object_getstate_default` (`Objects/typeobject.c:7979-8101`, CPython 3.15.2) on every branch, for
an object that is not a class.
-/

namespace PyLean.TypeObj

/-- The number of slot names `object_getstate_default` sees: `PyList_GET_SIZE(slotnames)`. -/
def slotCount (w : World) (names : Val) : Nat := ((listOf w names).getD []).length

/-- **`object_getstate_default`, every branch, for an instance.**
`Objects/typeobject.c:7979-8101`:
* with `required`, a variable-size type raises "cannot pickle %.200s objects" before anything
  else (`:7984-7989`);
* the state is `None` for an empty instance dict and the `__dict__` otherwise (an exception
  getting it propagates), then `_PyType_GetSlotNames` runs and its exception propagates;
* with `required`, a `tp_basicsize` larger than `object`'s plus a dict pointer (unless the dict is
  managed), a weakref pointer and one pointer per slot name raises "cannot pickle '%.200s' object"
  (`:8008-8028`);
* with no slot names (or `None`), the state alone is the result;
* otherwise each slot name's attribute is collected into a new dict (`getstateSlotsLoop`, whose
  exceptions propagate, `GetstateSlotsGuard`), and the result is the state alone if none was set
  and `(state, slots)` if some were (`:8084-8095`). -/
def GetstateDefaultExact : Prop :=
  ∀ (rt : Rt) (obj : Val) (required : Bool) (w : World),
    asType w obj = none →
    let d := tdata w (typeOf w obj)
    (required = true → d.itemsize ≠ 0 →
      objectGetstateDefault rt obj required w =
        (typeErr s!"cannot pickle {trunc 200 (typeName w obj)} objects" : M Val) w) ∧
    ((required = false ∨ d.itemsize = 0) →
      ∀ (st : Val) (w0 : World),
        ((instanceDictEmpty w obj = true ∧ st = .none ∧ w0 = w) ∨
          (instanceDictEmpty w obj = false ∧ genericGetDict obj w = .ok st w0)) →
        (∀ e w1, typeGetSlotNames rt (typeOf w obj) w0 = .err e w1 →
          objectGetstateDefault rt obj required w = .err e w1) ∧
        (∀ names w1, typeGetSlotNames rt (typeOf w obj) w0 = .ok names w1 →
          let base : Int := (tdata w1 B.object).basicsize
          let base := if d.dictoffset != 0 && d.dictoffset != -1 then base + 8 else base
          let base := if d.weaklistoffset > 0 then base + 8 else base
          let base := if !names.is .none then base + 8 * slotCount w1 names else base
          (required = true → (d.basicsize : Int) > base →
            objectGetstateDefault rt obj required w =
              (typeErr s!"cannot pickle '{trunc 200 (typeName w1 obj)}' object" : M Val) w1) ∧
          ((required = false ∨ (d.basicsize : Int) ≤ base) →
            ((names.is .none = true ∨ slotCount w1 names = 0) →
              objectGetstateDefault rt obj required w = .ok st w1) ∧
            (names.is .none = false → slotCount w1 names > 0 →
              let a := w1.heap.size
              let w2 : World := { w1 with heap := w1.heap.push (.val { cls := B.dict, body := .dict [] }) }
              (∀ e w3, getstateSlotsLoop rt obj names (slotCount w1 names) a iterFuel 0 w2 = .err e w3 →
                objectGetstateDefault rt obj required w = .err e w3) ∧
              (∀ w3, getstateSlotsLoop rt obj names (slotCount w1 names) a iterFuel 0 w2 = .ok () w3 →
                objectGetstateDefault rt obj required w =
                  .ok (if (dictEntries w3 a).isEmpty then st else .tuple [st, .obj a]) w3)))))

theorem getstateDefaultExact_proven : GetstateDefaultExact := by
  intro rt obj required w ha
  dsimp only
  refine ⟨fun hr hi => ?_, fun hri st w0 hst => ?_⟩
  · have : (required && (tdata w (typeOf w obj)).itemsize != 0) = true := by simp [hr] at hi ⊢; exact hi
    simp only [objectGetstateDefault, M.bind_app, getW_app, this, ite_true]
    simp [typeErr, raiseC]
  have hpre : (required && (tdata w (typeOf w obj)).itemsize != 0) = false := by
    rcases hri with h | h
    · simp [h]
    · simp [h]
  have hinit : getstateInitial obj w = .ok st w0 := by
    rcases hst with ⟨he1, rfl, rfl⟩ | ⟨he1, hg⟩
    · simp [getstateInitial, ha, he1]
    · simp [getstateInitial, ha, he1, hg]
  refine ⟨fun e w1 he => ?_, fun names w1 hn => ?_⟩
  · simp only [objectGetstateDefault, M.bind_app, getW_app, hpre, Bool.false_eq_true, ite_false,
      M.pure_app, hinit, he]
  have htail : objectGetstateDefault rt obj required w =
      getstateTail rt obj required (tdata w (typeOf w obj)) st names w1 := by
    simp only [objectGetstateDefault, M.bind_app, getW_app, hpre, Bool.false_eq_true, ite_false,
      M.pure_app, hinit, hn]
  rw [htail]
  refine ⟨fun hr hb => ?_, fun hok => ⟨fun hz => ?_, fun hn0 hc => ⟨fun e w3 hl => ?_, fun w3 hl => ?_⟩⟩⟩
  · subst hr
    simp only [slotCount] at hb
    simp only [getstateTail, M.bind_app, getW_app, ite_true]
    rw [if_pos hb]
    simp [typeErr, raiseC]
  all_goals simp only [slotCount] at *
  · have hz' : (!names.is .none && decide (((listOf w1 names).getD []).length > 0)) = false := by
      rcases hz with h | h <;> simp [h]
    rcases hok with h | h
    · subst h; simp only [getstateTail, M.bind_app, getW_app, Bool.false_eq_true, ite_false]
      simp only [hz', Bool.false_eq_true, ite_false, M.pure_app]
    · cases required
      · simp only [getstateTail, M.bind_app, getW_app, Bool.false_eq_true, ite_false]
        simp only [hz', Bool.false_eq_true, ite_false, M.pure_app]
      · simp only [getstateTail, M.bind_app, getW_app, ite_true]
        rw [if_neg (Int.not_lt.mpr h)]
        simp only [hz', Bool.false_eq_true, ite_false, M.pure_app]
  · have hz' : (!names.is .none && decide (((listOf w1 names).getD []).length > 0)) = true := by
      simp [hn0, hc]
    have hal : allocCell (.val { cls := B.dict, body := .dict [] }) w1 =
        .ok w1.heap.size { w1 with heap := w1.heap.push (.val { cls := B.dict, body := .dict [] }) } := rfl
    rcases hok with h | h
    · subst h; simp only [getstateTail, M.bind_app, getW_app, Bool.false_eq_true, ite_false]
      simp only [hz', ite_true, M.bind_app, hal, hl]; try (simp only [getW_app]; by_cases hE : (dictEntries w3 w1.heap.size).isEmpty = true <;> simp [hE])
    · cases required
      · simp only [getstateTail, M.bind_app, getW_app, Bool.false_eq_true, ite_false]
        simp only [hz', ite_true, M.bind_app, hal, hl]; try (simp only [getW_app]; by_cases hE : (dictEntries w3 w1.heap.size).isEmpty = true <;> simp [hE])
      · simp only [getstateTail, M.bind_app, getW_app, ite_true]
        rw [if_neg (Int.not_lt.mpr h)]
        simp only [hz', ite_true, M.bind_app, hal, hl]; try (simp only [getW_app]; by_cases hE : (dictEntries w3 w1.heap.size).isEmpty = true <;> simp [hE])
  · have hz' : (!names.is .none && decide (((listOf w1 names).getD []).length > 0)) = true := by
      simp [hn0, hc]
    have hal : allocCell (.val { cls := B.dict, body := .dict [] }) w1 =
        .ok w1.heap.size { w1 with heap := w1.heap.push (.val { cls := B.dict, body := .dict [] }) } := rfl
    rcases hok with h | h
    · subst h; simp only [getstateTail, M.bind_app, getW_app, Bool.false_eq_true, ite_false]
      simp only [hz', ite_true, M.bind_app, hal, hl]; try (simp only [getW_app]; by_cases hE : (dictEntries w3 w1.heap.size).isEmpty = true <;> simp [hE])
    · cases required
      · simp only [getstateTail, M.bind_app, getW_app, Bool.false_eq_true, ite_false]
        simp only [hz', ite_true, M.bind_app, hal, hl]; try (simp only [getW_app]; by_cases hE : (dictEntries w3 w1.heap.size).isEmpty = true <;> simp [hE])
      · simp only [getstateTail, M.bind_app, getW_app, ite_true]
        rw [if_neg (Int.not_lt.mpr h)]
        simp only [hz', ite_true, M.bind_app, hal, hl]; try (simp only [getW_app]; by_cases hE : (dictEntries w3 w1.heap.size).isEmpty = true <;> simp [hE])

end PyLean.TypeObj
