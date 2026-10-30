import PyLean.Sequences.SliceAssign

/-!
`array.array` slice assignment against `list` slice assignment.
-/

namespace PyLean.Sequences

open PyLean
open PyLean.RangeSlice (Slice sliceIndices sliceUnpack adjustIndices IsLen)

/-- Same value, or exceptions of the same class (messages may differ). -/
def SameUpToMsg {α : Type} : Py α → Py α → Prop
  | .ok a, .ok b => a = b
  | .error e1, .error e2 => e1.className = e2.className
  | _, _ => False

/-- `a[s] = array(tc, t)` agrees with `list(a)[s] = t` (value, or exception
class), for every array (any typecode, `len <= sys.maxsize`), every slice
with int/None parts and every `t` (the items of an array of the same
typecode). -/
def ArraySliceAssignAgree : Prop :=
  ∀ (tc : TC) (l t : List Int) (s : Slice), (l.length : Int) ≤ ssizeMax →
    SameUpToMsg ((arrAssSubscr ⟨tc, l⟩ (.inr s) (some t)).map (·.items)) (listAssSubscript l s (some t))

/-- The same when the assigned array is not empty (the refuted case above
needs an empty right-hand side). -/
def ArraySliceAssignAgreeNonempty : Prop :=
  ∀ (tc : TC) (l t : List Int) (s : Slice), (l.length : Int) ≤ ssizeMax → t ≠ [] →
    SameUpToMsg ((arrAssSubscr ⟨tc, l⟩ (.inr s) (some t)).map (·.items)) (listAssSubscript l s (some t))

theorem arraySliceAssignAgree_refuted : ¬ ArraySliceAssignAgree := by
  intro h
  have := h .b [1, 2, 3] [] ⟨none, none, some 2⟩ (by decide)
  have e1 : (arrAssSubscr ⟨.b, [1, 2, 3]⟩ (.inr ⟨none, none, some 2⟩) (some [])).map (·.items) = .ok [2] := by
    decide
  have e2 : listAssSubscript [1, 2, 3] ⟨none, none, some 2⟩ (some []) =
      .error (.valueError "attempt to assign sequence of size 0 to extended slice of size 2") := by decide
  rw [e1, e2] at this
  exact this

theorem arraySliceAssignAgreeNonempty_proven : ArraySliceAssignAgreeNonempty := by
  intro tc l t s hlen hne
  have hn : 0 ≤ (l.length : Int) := by omega
  have htlen : t.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
  by_cases h0 : s.step = some 0
  · obtain ⟨e1, _⟩ := zero_step_errors l t s h0
    rw [e1]
    obtain ⟨st, sp, ss⟩ := s
    simp only at h0; subst h0
    simp [arrAssSubscr, sliceUnpack, RangeSlice.clampSsize, bind, Except.bind, ssizeMin, ssizeMax,
      SameUpToMsg, Except.map]
    rfl
  obtain ⟨a, b, c, L, st, sp, c', hsi, hL, hb, hLdef, hsu, hadj, h1, hsg, hc, hc'0, hpos⟩ :=
    adjust_spec s l.length hn hlen h0
  unfold arrAssSubscr listAssSubscript adjustSlice
  simp only [hsu, bind, Except.bind, pure, Except.pure]
  rw [hadj]
  dsimp only
  rw [iteF hc'0]
  by_cases hc1 : c' = 1
  · subst hc1
    have hcc : c = 1 := h1.mp rfl
    have hb1 := hb.1 (by omega)
    rw [iteT rfl, iteT rfl]
    unfold listAssSlice
    dsimp only
    simp only [SameUpToMsg, Except.map, Option.getD_some]
    have e1 : (if a < 0 then 0 else if a > (l.length : Int) then (l.length : Int) else a) = a := by
      split <;> (try split) <;> omega
    rw [e1]
    congr 2
    split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega
  · rw [iteF hc1, iteF hc1]
    rw [iteF (show ¬ ((t.length : Int) = 0) by omega)]
    by_cases ht : (t.length : Int) ≠ L
    · rw [iteT ht, iteT ht]; rfl
    · rw [iteF ht, iteF ht]
      rw [iteF (show ¬ L = 0 by omega)]
      simp only [SameUpToMsg, Except.map, Option.getD_some]

end PyLean.Sequences
