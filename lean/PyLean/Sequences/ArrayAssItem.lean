import PyLean.Sequences.ArrayItems
import PyLean.Sequences.ArraySubscr

/-!
`array_ass_item` (the `sq_ass_item` slot, arraymodule.c:1208-1219) and `setarrayitem`
(:1222-1229), through which `array_new` fills an array from a list or tuple (:3083-3098).
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

/-- The loop of `array_new` for a list or tuple initializer (arraymodule.c:3083-3098):
`setarrayitem(a, i, v)` for `i` from 0, the first failure ending it (the array is discarded,
:3091-3095). -/
def newFill (a : Arr) (i : Int) : List PyVal → Py Arr
  | [] => .ok a
  | v :: vs =>
    match arrAssItem a i (some v) with
    | .error e => .error e
    | .ok a' => newFill a' (i + 1) vs

/-- `array_ass_item` for every array, index and value: an index outside `0 <= i < len(a)`
raises `IndexError("array assignment index out of range")` for a store and a deletion alike
(:1211-1215), before the value is looked at; inside, a deletion is `array_del_slice(a, i, i+1)`
(:1216-1217) and a store is the typecode's `setitem` (:1218): its conversion error (`TypeError`,
`OverflowError`, ...) is the result, otherwise item `i` becomes the converted value and nothing
else changes. -/
def ArrayAssItem : Prop :=
  ∀ (a : Arr) (i : Int),
    ((i < 0 ∨ (a.items.length : Int) ≤ i) → ∀ v,
      arrAssItem a i v = .error (.indexError "array assignment index out of range")) ∧
    (0 ≤ i → i < a.items.length →
      arrAssItem a i none = arrDelSlice a i (i + 1) ∧
      ∀ v, arrAssItem a i (some v) =
        match tcSetitem a.tc true v with
        | .error e => .error e
        | .ok x => .ok { a with items := a.items.set i.toNat x })

theorem arrayAssItem_proven : ArrayAssItem := by
  intro a i
  refine ⟨fun h v => ?_, fun h0 h1 => ⟨?_, fun v => ?_⟩⟩
  · unfold arrAssItem
    simp only [bind, Except.bind, throwE]
    rw [iteT (by omega)]
  · unfold arrAssItem
    simp only [bind, Except.bind, pure, Except.pure]
    rw [iteF (by omega)]
  · unfold arrAssItem
    simp only [bind, Except.bind, pure, Except.pure]
    rw [iteF (by omega)]
    cases tcSetitem a.tc true v <;> rfl

theorem newFill_spec (tc : TC) (vs : List PyVal) :
    ∀ (a : Arr) (pre : List Int), a.tc = tc → a.items = pre ++ List.replicate vs.length 0 →
      newFill a pre.length vs = (vs.mapM (tcSetitem tc true)).map (fun ys => { a with items := pre ++ ys }) := by
  induction vs with
  | nil =>
    intro a pre _ h
    simp only [List.length_nil, List.replicate_zero, List.append_nil] at h
    simp only [newFill, List.mapM_nil]
    cases a
    simp_all [Except.map, pure, Except.pure]
  | cons v vs ih =>
    intro a pre ht h
    subst ht
    have hl : a.items.length = pre.length + vs.length + 1 := by rw [h]; simp; omega
    unfold newFill
    rw [(arrayAssItem_proven a pre.length).2 (by omega) (by omega) |>.2 v]
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure, Int.toNat_natCast]
    cases tcSetitem a.tc true v with
    | error e => rfl
    | ok x =>
      simp only
      have h2 := ih { a with items := a.items.set pre.length x } (pre ++ [x]) rfl (by
        rw [h]; simp [List.replicate_succ, List.set_append_right])
      rw [show (pre.length : Int) + 1 = ((pre ++ [x]).length : Int) by simp, h2]
      cases vs.mapM (tcSetitem a.tc true) with
      | error e => rfl
      | ok ys => simp [Except.map]

/-- `array(typecode, list)` and `array(typecode, tuple)` fill the new array with
`setarrayitem` item by item (arraymodule.c:3083-3098): for every typecode, every list or tuple
whose length `newarrayobject` accepts, the result is `newFill` from index 0 over the new
zeroed array, so the first item `array_ass_item`'s setitem refuses raises its exception
(`array('b', [1000])` raises `OverflowError("signed char is greater than maximum")`), and
otherwise the items are the converted values in order. -/
def ArrayNewFill : Prop :=
  ∀ (t : String) (tc : TC) (vs : List PyVal) (a : Arr), newArr t tc vs.length = .ok a →
    arrNew t tc.code (.list vs) = newFill a 0 vs ∧ arrNew t tc.code (.tuple vs) = newFill a 0 vs ∧
    (∀ e, vs.mapM (tcSetitem tc true) = .error e → arrNew t tc.code (.list vs) = .error e) ∧
    arrNew "array" "b" (.list [.int 1000]) = .error (.overflowError "signed char is greater than maximum")

theorem arrayNewFill_proven : ArrayNewFill := by
  intro t tc vs a ha
  have hf : (vs.length : Int) ≤ ssizeMax / tc.itemsize := by
    unfold newArr at ha; split at ha
    · simp at ha
    · omega
  have ha' := newArr_ok t tc vs.length hf
  rw [ha] at ha'
  injection ha' with ha'
  subst ha'
  have hspec := newFill_spec tc vs ⟨tc, List.replicate (vs.length : Int).toNat 0, vs.length,
    decide ((vs.length : Int) > 0), 0, t⟩ [] rfl (by simp)
  simp only [List.length_nil, Int.natCast_zero, List.nil_append] at hspec
  have hl : arrNew t tc.code (.list vs) = newFill ⟨tc, List.replicate (vs.length : Int).toNat 0, vs.length,
      decide ((vs.length : Int) > 0), 0, t⟩ 0 vs := by
    rw [hspec]
    unfold arrNew
    simp only [arrNewBad_list, find_code, Option.isSome_none, Bool.false_eq_true, ite_false, newArr_ok t tc vs.length hf]
    cases vs.mapM (tcSetitem tc true) <;> rfl
  refine ⟨hl, ?_, fun e he => ?_, by decide⟩
  · have hb : arrNewBad tc.code (.tuple vs) = .ok () := by unfold arrNewBad; split <;> rfl
    rw [hspec]
    unfold arrNew
    simp only [hb, find_code, Option.isSome_none, Bool.false_eq_true, ite_false, newArr_ok t tc vs.length hf]
    cases vs.mapM (tcSetitem tc true) <;> rfl
  · rw [hl]
    rw [hspec, he]
    rfl

end PyLean.Sequences
