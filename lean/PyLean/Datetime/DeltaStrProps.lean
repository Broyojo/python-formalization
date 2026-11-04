import PyLean.Datetime.OpenProps
import PyLean.Datetime.TwinsProps

/-!
`str(timedelta)` and `repr(timedelta)`: the list concatenation of `_pydatetime` against the
`PyUnicode_FromFormat` calls of C `delta_str` and `delta_repr`.
-/

namespace PyLean.Datetime

open PyLean

theorem day_lit (X : String) : " " ++ ("d" ++ ("a" ++ ("y" ++ X))) = " day" ++ X := by
  rw [← String.append_assoc, ← String.append_assoc, ← String.append_assoc]
  have : " " ++ "d" ++ "a" ++ "y" = " day" := by decide
  rw [this]

theorem comma_lit (X : String) : "," ++ (" " ++ X) = ", " ++ X := by
  rw [← String.append_assoc]
  have : "," ++ " " = ", " := by decide
  rw [this]

theorem us_lit (X : String) : ", " ++ ("microseconds=" ++ X) = ", microseconds=" ++ X := by
  rw [← String.append_assoc]
  have : ", " ++ "microseconds=" = ", microseconds=" := by decide
  rw [this]

theorem s_lit (X : String) : ", " ++ ("seconds=" ++ X) = ", seconds=" ++ X := by
  rw [← String.append_assoc]
  have : ", " ++ "seconds=" = ", seconds=" := by decide
  rw [this]

theorem ofList_append' (a b : List Char) : String.ofList (a ++ b) = String.ofList a ++ String.ofList b := by
  simp

theorem delta_str_eq (t : Delta) : t.str = t.strC := by
  have hp : (t.days.natAbs = 1) ↔ (t.days = 1 ∨ t.days = -1) := by omega
  unfold Delta.str Delta.strC fmtD fmt0
  by_cases hd : t.days = 0 <;> by_cases hu : t.us = 0 <;> by_cases h1 : t.days.natAbs = 1 <;>
    simp [hd, hu, h1, hp.mp, ofList_append', String.append_assoc, toString, day_lit, comma_lit] <;>
    simp_all <;>
    (simp only [← String.append_assoc]; repeat' (first | rfl | decide | congr 1))

theorem delta_repr_eq (t : Delta) : t.repr = t.reprC := by
  unfold Delta.repr Delta.reprC fmtD
  by_cases hd : t.days = 0 <;> by_cases hs : t.seconds = 0 <;> by_cases hu : t.us = 0 <;>
    simp [hd, hs, hu, toString, String.append_assoc, us_lit, s_lit]

theorem delta_reprArgs_eq (t : Delta) : t.reprArgsPy = t.reprArgsC := by
  unfold Delta.reprArgsPy Delta.reprArgsC fmtD
  by_cases hd : t.days = 0 <;> by_cases hs : t.seconds = 0 <;> by_cases hu : t.us = 0 <;>
    simp [hd, hs, hu, toString, String.append_assoc, us_lit, s_lit]

theorem timedeltaStrRepr_proven : TimedeltaStrRepr := fun t _ => ⟨delta_str_eq t, delta_repr_eq t⟩

/-- `repr(t)` for `timedelta` and for every subclass whose `__qualname__` is its `__name__`
and whose module is not named `datetime`: the twins give the same text, and for the base class
it is `repr(t)` of `TimedeltaStrRepr` (`datetime.timedelta(days=..., seconds=...,
microseconds=...)`, only the nonzero fields, `0` for none). -/
def TimedeltaReprCls : Prop :=
  ∀ (c : ReprCls) (t : Delta),
    (c = .base ∨ ∃ mod name, c = .sub mod name name ∧ mod ≠ "datetime") →
    t.reprClsPy c = t.reprClsC c ∧ t.reprClsPy .base = t.repr

theorem timedeltaReprCls_proven : TimedeltaReprCls := by
  intro c t h
  refine ⟨?_, ?_⟩
  · rcases h with rfl | ⟨mod, name, rfl, hm⟩
    · simp only [Delta.reprClsPy, Delta.reprClsC, delta_reprArgs_eq, getClassModule, ReprCls.module,
        ReprCls.tdQualname, ReprCls.tdTpName, ↓reduceIte, toString]
      have : "datetime." ++ "timedelta" = "datetime.timedelta" := by decide
      rw [this]
    · simp [Delta.reprClsPy, Delta.reprClsC, delta_reprArgs_eq, getClassModule, ReprCls.module,
        ReprCls.tdQualname, ReprCls.tdTpName, hm, toString]
  · unfold Delta.reprClsPy Delta.repr Delta.reprArgsPy fmtD
    simp only [getClassModule, ReprCls.module, ReprCls.tdQualname, ↓reduceIte, toString]
    have : "datetime." ++ "timedelta" ++ "(" = "datetime.timedelta(" := by decide
    rw [this]
    try simp only [String.append_assoc]

/-- `repr(t)` agrees between the twins for every class. -/
def TimedeltaReprTwins : Prop := ∀ (c : ReprCls) (t : Delta), t.reprClsPy c = t.reprClsC c

/-- `class Outer: class TSub(timedelta): pass`: `repr(Outer.TSub(1))` is
`Outer.TSub(days=1)` in Python (`__qualname__`) and `TSub(days=1)` in C (`tp_name`). -/
theorem timedeltaReprTwins_refuted : ¬TimedeltaReprTwins := by
  intro h
  have := h (.sub "__main__" "Outer.TSub" "TSub") ⟨1, 0, 0⟩
  revert this; decide

end PyLean.Datetime
