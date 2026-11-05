import PyLean.RangeSlice.Iter

/-!
Which iterator `iter(r)` and `reversed(r)` return. The choice is visible from Python: the type
name differs, and `range_iterator.__setstate__` accepts `True` and `__index__` objects where
`longrange_iterator.__setstate__` raises `TypeError` (`SetstateStateTypes`). These theorems pin
the exact conditions of `range_iter` and `range_reverse`, and the fields of the iterator.
-/

namespace PyLean.RangeSlice

open PyLean

theorem asLong_some {x : Int} (h : IsLong x) : asLong x = some x := by simp [asLong, h]
theorem asLong_none {x : Int} (h : ¬ IsLong x) : asLong x = none := by simp [asLong, h]

/-- **`iter(r)`, the iterator chosen.** For every range of mathematical length `L`,
`range_iter` (rangeobject.c:1227-1279) returns the C `long` `range_iterator` over
`(start, step, L)` exactly when start, stop and step fit a C `long` (:1238-1252), `L` is at
most `LONG_MAX` (:1253-1256), and, for a non-empty range, `stop + step - 1 <= LONG_MAX` for a
positive step and `stop + step + 1 >= LONG_MIN` for a negative one (:1257-1267, the
`lstart + ulen * lstep` overflow check); otherwise it returns `longrange_iterator` over
`(start, step, L)` (:1269-1278). When `range_iterator` is chosen, the end value
`start + L*step` fits a C `long`, which is what that check is for. -/
def IterChoice : Prop :=
  ∀ (r : Range) (L : Int), r.WF → r.Len L →
    rangeIter r =
      (if IsLong r.start ∧ IsLong r.stop ∧ IsLong r.step ∧ L ≤ longMax ∧
          (L = 0 ∨ (if r.step > 0 then r.stop + r.step - 1 ≤ longMax
                    else longMin ≤ r.stop + r.step + 1))
       then .fast r.start r.step L else .long r.start r.step L) ∧
    ((rangeIter r).typeName = "range_iterator" → IsLong (r.start + L * r.step))

theorem rangeIter_eq (r : Range) (L : Int) (hw : r.WF) (hL : r.Len L) :
    rangeIter r =
      (if IsLong r.start ∧ IsLong r.stop ∧ IsLong r.step ∧ L ≤ longMax ∧
          (L = 0 ∨ (if r.step > 0 then r.stop + r.step - 1 ≤ longMax
                    else longMin ≤ r.stop + r.step + 1))
       then .fast r.start r.step L else .long r.start r.step L) := by
  have hlen := hw.length_eq hL
  unfold rangeIter
  rw [hlen]
  by_cases h1 : IsLong r.start
  case neg =>
    rw [asLong_none h1, ite_f (fun h => h1 h.1)]
  by_cases h2 : IsLong r.stop
  case neg =>
    rw [asLong_some h1, asLong_none h2, ite_f (fun h => h2 h.2.1)]
  by_cases h3 : IsLong r.step
  case neg =>
    rw [asLong_some h1, asLong_some h2, asLong_none h3, ite_f (fun h => h3 h.2.2.1)]
  rw [asLong_some h1, asLong_some h2, asLong_some h3]
  simp only
  rw [fast_len hw hL h1 h2 h3]
  unfold IsLong longMin longMax at *
  by_cases hb : L > 9223372036854775807
  · rw [ite_t hb, ite_f (fun h => absurd h.2.2.2.1 (by omega))]
  rw [ite_f hb]
  by_cases hp : r.step > 0
  · simp only [hp, ↓reduceIte]
    by_cases hc : L ≠ 0 ∧ r.stop > 9223372036854775807 - (r.step - 1)
    · rw [ite_t hc]
      refine (ite_f ?_).symm
      intro h; rcases h.2.2.2.2 with h' | h' <;> omega
    · rw [ite_f hc, ite_t ⟨h1, h2, h3, by omega, by omega⟩]
  · simp only [hp, ↓reduceIte]
    by_cases hc : L ≠ 0 ∧ r.stop < -9223372036854775808 + (-1 - r.step)
    · rw [ite_t hc]
      refine (ite_f ?_).symm
      intro h; rcases h.2.2.2.2 with h' | h' <;> omega
    · rw [ite_f hc, ite_t ⟨h1, h2, h3, by omega, by omega⟩]

theorem iterChoice_proven : IterChoice := by
  intro r L hw hL
  refine ⟨rangeIter_eq r L hw hL, fun hname => ?_⟩
  rw [rangeIter_eq r L hw hL] at hname
  by_cases hc : IsLong r.start ∧ IsLong r.stop ∧ IsLong r.step ∧ L ≤ longMax ∧
          (L = 0 ∨ (if r.step > 0 then r.stop + r.step - 1 ≤ longMax
                    else longMin ≤ r.stop + r.step + 1))
  case neg =>
    rw [ite_f hc] at hname; simp [RIter.typeName] at hname
  obtain ⟨h1, h2, h3, _, hz⟩ := hc
  have hL0 := hL.1
  have hs := hw.1
  rcases hz with hz | hz
  · subst hz; simp only [Int.zero_mul, Int.add_zero]; exact h1
  by_cases hL1 : L = 0
  · subst hL1; simp only [Int.zero_mul, Int.add_zero]; exact h1
  have hin := (hL.2 (L - 1) (by omega)).1 (by omega)
  unfold InSeq at hin
  have e : r.start + L * r.step = r.start + (L - 1) * r.step + r.step := by
    rw [Int.sub_mul, Int.one_mul]; omega
  rw [e]
  unfold IsLong longMin longMax at *
  by_cases hp : r.step > 0
  · rw [ite_t (show (0 : Int) < r.step from hp)] at hin
    rw [ite_t hp] at hz
    have := Int.mul_nonneg (show 0 ≤ L - 1 by omega) (Int.le_of_lt hp)
    omega
  · rw [ite_f (show ¬ (0 : Int) < r.step by omega)] at hin
    rw [ite_f hp] at hz
    have := Int.mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ L - 1 by omega) (show r.step ≤ 0 by omega)
    omega

/-- **`reversed(r)`, the iterator chosen.** For every range of mathematical length `L`,
`range_reverse` (rangeobject.c:1282-1384) returns the C `long` `range_iterator` exactly when
start, stop and step fit a C `long` (:1302-1316), the step is not `LONG_MIN` (:1318-1319),
`start - step` fits a C `long` (:1321-1342, computed in unsigned arithmetic) and `L` is at
most `LONG_MAX` (:1344-1346); otherwise `longrange_iterator` (:1352-1377). Either way the
iterator starts at `start + (L - 1)*step` (the last element, or `start - step` when empty),
steps by `-step` and holds `L` values (:1348-1350 and :1357-1374). -/
def ReverseChoice : Prop :=
  ∀ (r : Range) (L : Int), r.WF → r.Len L →
    rangeReverse r =
      if IsLong r.start ∧ IsLong r.stop ∧ IsLong r.step ∧ r.step ≠ longMin ∧
          IsLong (r.start - r.step) ∧ L ≤ longMax
      then .fast (r.start + (L - 1) * r.step) (-r.step) L
      else .long (r.start + (L - 1) * r.step) (-r.step) L

theorem reverseChoice_proven : ReverseChoice := by
  intro r L hw hL
  have hlen := hw.length_eq hL
  have hL0 := hL.1
  unfold rangeReverse
  rw [hlen]
  by_cases h1 : IsLong r.start
  case neg =>
    rw [asLong_none h1, ite_f (fun h => h1 h.1)]
  by_cases h2 : IsLong r.stop
  case neg =>
    rw [asLong_some h1, asLong_none h2, ite_f (fun h => h2 h.2.1)]
  by_cases h3 : IsLong r.step
  case neg =>
    rw [asLong_some h1, asLong_some h2, asLong_none h3, ite_f (fun h => h3 h.2.2.1)]
  rw [asLong_some h1, asLong_some h2, asLong_some h3]
  simp only
  by_cases hm : r.step = longMin
  · rw [ite_t hm, ite_f (fun h => h.2.2.2.1 hm)]
  rw [ite_f hm]
  have hchk : (if r.step > 0 then usub (toU r.start) (toU longMin) < toU r.step
               else usub (toU longMax) (toU r.start) < usub 0 (toU r.step)) ↔
      ¬ IsLong (r.start - r.step) := by
    unfold IsLong longMin longMax at *
    by_cases hp : r.step > 0
    · rw [ite_t hp]; unfold usub toU two64; omega
    · rw [ite_f hp]; unfold usub toU two64; omega
  by_cases hc : (if r.step > 0 then usub (toU r.start) (toU longMin) < toU r.step
                 else usub (toU longMax) (toU r.start) < usub 0 (toU r.step))
  · rw [ite_t hc, ite_f (fun h => (hchk.1 hc) h.2.2.2.2.1)]
  rw [ite_f hc, fast_len hw hL h1 h2 h3]
  have h4 : IsLong (r.start - r.step) := Decidable.byContradiction fun hn => hc (hchk.2 hn)
  by_cases hb : L > longMax
  · rw [ite_t hb, ite_f (fun h => absurd h.2.2.2.2.2 (by omega))]
  rw [ite_f hb, ite_t ⟨h1, h2, h3, hm, h4, by omega⟩]
  have hneg : IsLong (-r.step) := by unfold IsLong longMin longMax at *; omega
  have hlast : IsLong (r.start + (L - 1) * r.step) := by
    by_cases hz : L = 0
    · rw [hz, Int.sub_mul, Int.zero_mul, Int.one_mul]
      have e : r.start + (0 - r.step) = r.start - r.step := by omega
      rw [e]; exact h4
    · exact elem_long hL h1 h2 (k := L - 1) (by omega) (by omega)
  rw [rev_newStart, wrap_long hneg, wrap_long hlast]

end PyLean.RangeSlice
