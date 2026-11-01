import PyLean.Sequences.SliceAssign
import PyLean.Sequences.ArrayBasic

/-!
`array.array` slice assignment against `list` slice assignment.
-/

namespace PyLean.Sequences

open PyLean
open PyLean.RangeSlice (Slice sliceIndices sliceUnpack adjustIndices IsLen)

set_option linter.unusedSectionVars false

/-- Same value, or exceptions of the same class (messages may differ). -/
def SameUpToMsg {α : Type} : Py α → Py α → Prop
  | .ok a, .ok b => a = b
  | .error e1, .error e2 => e1.className = e2.className
  | _, _ => False

theorem fits_shrink (a : Arr) (n m : Int) (h : n ≤ m) (hm : a.Fits m) : a.Fits n := by
  unfold Arr.Fits at *; omega

theorem arrAssCore_none (a : Arr) (start stop step len : Int) :
    arrAssCore a start stop step len none = arrAssCore a start stop step len (some []) := by
  simp only [arrAssCore, List.length_nil, Option.getD_some, Option.getD_none, Int.natCast_zero]

theorem shrink_list (l src : List Int) (s e : Nat) (h1 : s + src.length < e) (h2 : e ≤ l.length) :
    let m := l.take (s + src.length) ++ (l.drop e).take (l.length - e) ++ l.drop (s + src.length + (l.length - e))
    m.take (l.length + src.length - (e - s)) = l.take (s + src.length) ++ l.drop e := by
  intro m
  simp only [m]
  list_ext

theorem take_part (l src tail : List Int) (s : Nat) (h : s + src.length ≤ l.length) :
    (l.take (s + src.length) ++ tail).take s ++ src ++ (l.take (s + src.length) ++ tail).drop (s + src.length)
      = l.take s ++ src ++ tail := by
  have e1 : (l.take (s + src.length) ++ tail).take s = l.take s := by
    rw [List.take_append_of_le_length (by simp; omega), List.take_take]
    congr 1
    omega
  have e2 : (l.take (s + src.length) ++ tail).drop (s + src.length) = tail := by
    rw [List.drop_left' (by simp; omega)]
  rw [e1, e2]

theorem grow_list (l src : List Int) (s e : Nat) (h1 : e - s < src.length) (h2 : e ≤ l.length) (h3 : s ≤ e) :
    let z := l ++ List.replicate (src.length - (e - s)) 0
    let m := z.take (s + src.length) ++ (z.drop e).take (l.length - e) ++ z.drop (s + src.length + (l.length - e))
    m.take s ++ src ++ m.drop (s + src.length) = l.take s ++ src ++ l.drop e := by
  intro z m
  have hz : z.length = s + src.length + (l.length - e) := by
    simp only [z, List.length_append, List.length_replicate]; omega
  have e1 : z.drop (s + src.length + (l.length - e)) = [] := List.drop_eq_nil_of_le (by omega)
  have e2 : (z.drop e).take (l.length - e) = l.drop e := by
    simp only [z]
    rw [List.drop_append_of_le_length (by omega), List.take_left' (by simp)]
  have e3 : m = z.take (s + src.length) ++ l.drop e := by
    simp only [m]; rw [e1, e2, List.append_nil]
  rw [e3]
  have e4 : (z.take (s + src.length) ++ l.drop e).take s = l.take s := by
    rw [List.take_append_of_le_length (by simp only [List.length_take]; omega), List.take_take,
      show min s (s + src.length) = s by omega]
    simp only [z]
    rw [List.take_append_of_le_length (by omega)]
  have e5 : (z.take (s + src.length) ++ l.drop e).drop (s + src.length) = l.drop e :=
    List.drop_left' (by simp only [List.length_take]; omega)
  rw [e4, e5]

/-- The `step == 1` branches of `array_ass_subscr`: the items `start:stop` are
replaced by `src`, through whichever of the two `memmove` orders applies. -/
theorem arrAssCore_step1 (a : Arr) (start stop len : Int) (src : List Int) (hx : a.exports = 0)
    (h0 : 0 ≤ start) (he : max start stop ≤ a.items.length) (hlen : len = max start stop - start)
    (hf : a.Fits (a.items.length + src.length - len)) :
    ∃ a', arrAssCore a start stop 1 len (some src) = .ok a' ∧
      a'.items = a.items.take start.toNat ++ src ++ a.items.drop (max start stop).toNat ∧
      a'.tc = a.tc ∧ a'.exports = 0 ∧ a'.tname = a.tname := by
  have hstop : (if ((1 : Int) > 0 ∧ stop < start) ∨ ((1 : Int) < 0 ∧ stop > start) then start else stop)
      = max start stop := by
    split <;> omega
  unfold arrAssCore
  simp only [bind, Except.bind, pure, Except.pure, Option.getD_some, throwE, hstop]
  rw [iteF (show ¬ (((src.length : Int) = 0 ∨ len ≠ src.length) ∧ a.exports > 0) by omega), iteT trivial]
  have hse : start ≤ max start stop := by omega
  generalize max start stop = e at he hlen hse ⊢
  by_cases hgt : len > src.length
  · rw [iteT hgt, memmove_ok _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only
    obtain ⟨a', hr, hi', ht, he', htn⟩ := arrResize_ok
      { a with items := a.items.take (start + src.length).toNat ++ (a.items.drop e.toNat).take ((a.items.length : Int) - e).toNat ++ a.items.drop (start + src.length + ((a.items.length : Int) - e)).toNat }
      ((a.items.length : Int) + src.length - len) hx (by omega) (by unfold Arr.Fits at *; simp only; omega)
    rw [hr]
    simp only
    by_cases hs : (src.length : Int) > 0
    · rw [iteT hs]
      refine ⟨_, rfl, ?_, ht, he', htn⟩
      show memcpy a'.items start src = _
      rw [hi', resized_le _ _ (by omega) (by simp only [List.length_append, List.length_take, List.length_drop]; omega)]
      unfold memcpy
      have hk := shrink_list a.items src start.toNat e.toNat (by omega) (by omega)
      simp only at hk
      rw [show (start + (src.length : Int)).toNat = start.toNat + src.length by omega,
        show ((a.items.length : Int) - e).toNat = a.items.length - e.toNat by omega,
        show (start + (src.length : Int) + ((a.items.length : Int) - e)).toNat = start.toNat + src.length + (a.items.length - e.toNat) by omega,
        show ((a.items.length : Int) + src.length - len).toNat = a.items.length + src.length - (e.toNat - start.toNat) by omega,
        hk]
      exact take_part a.items src _ _ (by omega)
    · rw [iteF hs]
      refine ⟨a', rfl, ?_, ht, he', htn⟩
      rw [hi', resized_le _ _ (by omega) (by simp only [List.length_append, List.length_take, List.length_drop]; omega)]
      have : src = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      list_ext
  · rw [iteF hgt]
    by_cases hlt : len < src.length
    · rw [iteT hlt]
      obtain ⟨a', hr, hi', ht, he', htn⟩ := arrResize_ok a ((a.items.length : Int) + src.length - len) hx (by omega) hf
      have hl' : (a'.items.length : Int) = (a.items.length : Int) + src.length - len := by
        rw [hi', length_resized _ _ (by omega)]
      rw [hr]
      simp only
      rw [memmove_ok _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp only
      rw [iteT (show (src.length : Int) > 0 by omega)]
      refine ⟨_, rfl, ?_, ht, he', htn⟩
      show memcpy _ start src = _
      rw [hi', resized_gt _ _ (by omega)]
      unfold memcpy
      have hk := grow_list a.items src start.toNat e.toNat (by omega) (by omega) (by omega)
      simp only at hk
      rw [show (start + (src.length : Int)).toNat = start.toNat + src.length by omega,
        show ((a.items.length : Int) + src.length - len - ((a.items.length : Int))).toNat = src.length - (e.toNat - start.toNat) by omega,
        show ((a.items.length : Int) + src.length - len - start - src.length).toNat = a.items.length - e.toNat by omega,
        show (start + (src.length : Int) + ((a.items.length : Int) + src.length - len - start - src.length)).toNat = start.toNat + src.length + (a.items.length - e.toNat) by omega,
        show e.toNat = e.toNat from rfl]
      exact hk
    · rw [iteF hlt]
      have hk : len = src.length := by omega
      by_cases hs : (src.length : Int) > 0
      · rw [iteT hs]
        refine ⟨_, rfl, ?_, rfl, hx, rfl⟩
        show memcpy a.items start src = _
        unfold memcpy
        rw [show (start + (src.length : Int)).toNat = e.toNat by omega]
      · rw [iteF hs]
        refine ⟨a, rfl, ?_, rfl, hx, rfl⟩
        have : src = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst this
        have : e = start := by simp at hk; omega
        subst this
        simp

/-- `a[s] = t` for an array `t` of the same typecode agrees with `list(a)[s] = list(t)`
(the same items, or an exception of the same class), for every array `a` (no buffer
exported; the type invariant that `len(a) + len(t)` items fit the address space) and
every slice with int/None parts. -/
def ArraySliceAssignAgree : Prop :=
  ∀ (a o : Arr) (s : Slice), a.tc = o.tc → a.exports = 0 →
    a.Fits (a.items.length + o.items.length) →
    SameUpToMsg ((arrAssSlice a s (.arr o false)).map (·.items)) (listAssSubscript a.items s (some o.items))

/-- The same when the assigned array is not empty (the refuted case above
needs an empty right-hand side). -/
def ArraySliceAssignAgreeNonempty : Prop :=
  ∀ (a o : Arr) (s : Slice), a.tc = o.tc → a.exports = 0 →
    a.Fits (a.items.length + o.items.length) → o.items ≠ [] →
    SameUpToMsg ((arrAssSlice a s (.arr o false)).map (·.items)) (listAssSubscript a.items s (some o.items))

theorem arraySliceAssignAgree_refuted : ¬ ArraySliceAssignAgree := by
  intro h
  have := h ⟨.b, [1, 2, 3], 3, true, 0, "array"⟩ ⟨.b, [], 0, false, 0, "array"⟩ ⟨none, none, some 2⟩ rfl rfl
    (by unfold Arr.Fits ssizeMax TC.itemsize; simp)
  have e1 : (arrAssSlice ⟨.b, [1, 2, 3], 3, true, 0, "array"⟩ ⟨none, none, some 2⟩
      (.arr ⟨.b, [], 0, false, 0, "array"⟩ false)).map (·.items) = .ok [2] := by decide
  have e2 : listAssSubscript ([1, 2, 3] : List Int) ⟨none, none, some 2⟩ (some []) =
      .error (.valueError "attempt to assign sequence of size 0 to extended slice of size 2") := by decide
  rw [e1] at this
  simp only at this
  rw [e2] at this
  exact this

theorem arraySliceAssignAgreeNonempty_proven : ArraySliceAssignAgreeNonempty := by
  intro a o s htc hx hf hne
  have hn : 0 ≤ (a.items.length : Int) := by omega
  have hsz : a.Fits a.items.length := fits_shrink a _ _ (by omega) hf
  have hmax : (a.items.length : Int) ≤ ssizeMax := by
    unfold Arr.Fits at hsz
    have : ssizeMax / a.tc.itemsize ≤ ssizeMax := Int.ediv_le_self _ (by unfold ssizeMax; omega)
    omega
  have htlen : o.items.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
  by_cases h0 : s.step = some 0
  · obtain ⟨e1, _⟩ := zero_step_errors a.items o.items s h0
    rw [e1]
    obtain ⟨st, sp, ss⟩ := s
    simp only at h0; subst h0
    simp [arrAssSlice, sliceUnpack, RangeSlice.clampSsize, bind, Except.bind, ssizeMin, ssizeMax,
      SameUpToMsg, Except.map, throwE]
  obtain ⟨b, e, c, L, st, sp, c', hsi, hL, hb, hLdef, hsu, hadj, h1, hsg, hc, hc'0, hpos⟩ :=
    adjust_spec s a.items.length hn hmax h0
  have hL0 : 0 ≤ L := by
    have := adjust_len_nonneg a.items.length st sp c'
    rw [hadj] at this
    exact this
  unfold arrAssSlice listAssSubscript adjustSlice
  simp only [hsu, bind, Except.bind, pure, Except.pure]
  rw [hadj]
  dsimp only
  have htc' : ¬ ((!false) = true ∧ o.tc ≠ a.tc) := by
    intro h; exact h.2 htc.symm
  rw [iteF htc']
  by_cases hc1 : c' = 1
  · subst hc1
    have hcc : c = 1 := h1.mp rfl
    have hb1 := hb.1 (by omega)
    rw [iteT rfl]
    have hmaxb : max b e ≤ a.items.length := by omega
    have hLm : L = max b e - b := by
      rw [hLdef, hcc]
      unfold RangeSlice.computeRangeLengthSlow
      rw [iteT (by decide)]
      split <;> omega
    obtain ⟨a', hr, hi, _⟩ := arrAssCore_step1 a b e L o.items hx (by omega) hmaxb hLm
      (fits_shrink a _ _ (by omega) hf)
    rw [hr]
    unfold listAssSlice
    dsimp only
    simp only [SameUpToMsg, Except.map, Option.getD_some]
    have e1 : (if b < 0 then 0 else if b > (a.items.length : Int) then (a.items.length : Int) else b) = b := by
      split <;> (try split) <;> omega
    rw [e1, hi]
    congr 2
    split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega
  · rw [iteF hc1]
    unfold arrAssCore
    simp only [bind, Except.bind, pure, Except.pure, throwE, Option.getD_some]
    rw [iteF (show ¬ (((o.items.length : Int) = 0 ∨ L ≠ o.items.length) ∧ a.exports > 0) by omega), iteF hc1,
      iteF (show ¬ ((o.items.length : Int) = 0) by omega)]
    by_cases ht : (o.items.length : Int) ≠ L
    · rw [iteT ht, iteT ht]; rfl
    · rw [iteF ht, iteF ht]
      rw [iteF (show ¬ L = 0 by omega)]
      simp only [SameUpToMsg, Except.map]

end PyLean.Sequences
