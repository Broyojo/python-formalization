import PyLean.ListSort.FallibleSteps

/-! # `count_run`'s failure exits, each reached by its own clause -/

namespace PyLean.ListSort

open PyLean

variable {α : Type}

/-- `count_run(ms, slo, nremaining)` (listobject.c:1972-2064) on every slice and any comparison, at each of
its later failure points: after an ascending scan that stopped at a smaller item,

* the `IFLT(lo[0], lo[n-1])` test (:2020) that raises returns `-1` with the slice untouched;
* an error in the descending loop (:2031-2041) is returned with the slice as that loop leaves it
  (the all-equal prefix reversed, finished groups reversed, the current group not);
* an error in the ascending extension (:2052-2055) is returned with the descending run already reversed
  into ascending order (:2045-2046), the extension's items so far and the rest in place.

None of them is turned into a success or a restored input. -/
def CountRunFailSteps : Prop :=
  ∀ (α : Type) (lt : PLt α) (e : PyExc) (er : Option PyExc) (x0 y w : α) (rest t r' pre r2 ws ext r3 : List α)
    (ms ms1 ms2 ms3 ms4 : MS) (e' : PyExc),
    ascTakeF lt x0 rest ms = (t, y :: r', ms1, none) →
    ((x0 :: t).length > 1 → isltF lt ms1 x0 ((x0 :: t).getLast (by simp)) = (.error e, ms2) →
      countRunF lt (x0 :: rest) ms = (0, x0 :: rest, ms2, some e)) ∧
    ((if (x0 :: t).length > 1 then isltF lt ms1 x0 ((x0 :: t).getLast (by simp)) else (.ok false, ms1)) =
        (.ok false, ms2) →
      descLoopF lt (x0 :: t).reverse [y] y r' ms2 = (pre, r2, ms3, some e) →
      countRunF lt (x0 :: rest) ms = (0, pre ++ r2, ms3, some e)) ∧
    ((if (x0 :: t).length > 1 then isltF lt ms1 x0 ((x0 :: t).getLast (by simp)) else (.ok false, ms1)) =
        (.ok false, ms2) →
      descLoopF lt (x0 :: t).reverse [y] y r' ms2 = ((w :: ws).reverse, r2, ms3, none) →
      ascTakeF lt ((w :: ws).getLast (by simp)) r2 ms3 = (ext, r3, ms4, some e') →
      countRunF lt (x0 :: rest) ms = (0, (w :: ws) ++ ext ++ r3, ms4, some e'))

theorem countRunFailSteps_proven : CountRunFailSteps := by
  intro α lt e er x0 y w rest t r' pre r2 ws ext r3 ms ms1 ms2 ms3 ms4 e' hA
  refine ⟨fun hl h => ?_, fun hE hD => ?_, fun hE hD hX => ?_⟩
  · simp only [countRunF, hA]
    rw [if_pos hl, h]
  · simp only [countRunF, hA]
    rw [hE]
    simp only [hD]
  · simp only [countRunF, hA]
    rw [hE]
    simp only [hD, List.reverse_reverse, hX]

end PyLean.ListSort
