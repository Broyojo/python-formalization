import PyLean.Sequences.ArrayModel
import PyLean.RangeSlice.Slice

/-!
Slice assignment `s[i:j:k] = t` for `list` against the language reference,
and `array.array` against `list`.
-/

namespace PyLean.Sequences

open PyLean
open PyLean.RangeSlice (Slice sliceIndices sliceUnpack adjustIndices IsLen listSlicePositions
  listSliceIndices_proven toU)

set_option linter.unusedSectionVars false

variable {α : Type} [Inhabited α]

/-- Replace position `ps[i]` by `t[i]`, for `i = 0, 1, ...` in order. -/
def assignAt (l : List α) (ps : List Int) (t : List α) : List α :=
  (List.range t.length).foldl (fun m (i : Nat) => m.set (ix ps i).toNat (ix t i)) l

/-- `s[i:j:k] = t` as the language reference and the mutable-sequence table
describe it (Doc/reference/simple_stmts.rst "If the target is a slicing",
Doc/library/stdtypes.rst:1244-1269 with note (1)): with
`(a, b, c) = slice.indices(len(s))` and `L = len(range(a, b, c))`, a step of 1
replaces `s[a:max(a, b)]` by `t` (changing the length), any other step needs
`len(t) == L` (else `ValueError`) and replaces `s[a + k*c]` by `t[k]`. -/
def sliceAssignSpec (l t : List α) (s : Slice) : Py (List α) :=
  match sliceIndices s l.length with
  | .error e => .error e
  | .ok (a, b, c) =>
    let L := RangeSlice.computeRangeLengthSlow a b c
    if c = 1 then .ok (l.take a.toNat ++ t ++ l.drop (max a b).toNat)
    else if (t.length : Int) ≠ L then
      .error (.valueError s!"attempt to assign sequence of size {t.length} to extended slice of size {L}")
    else .ok (assignAt l ((List.range L.toNat).map (fun (k : Nat) => a + k * c)) t)

/-- `l[s] = t` for every list `l` (`len(l) <= sys.maxsize`, a type
invariant), every iterable's items `t` and every slice with int/None parts —
including steps and bounds far outside `Py_ssize_t` — is `sliceAssignSpec`. -/
def ListSliceAssign : Prop :=
  ∀ (α : Type) [Inhabited α] (l t : List α) (s : Slice), (l.length : Int) ≤ ssizeMax →
    listAssSubscript l s (some t) = sliceAssignSpec l t s

theorem foldl_range_congr (n : Nat) (f g : List α → Nat → List α)
    (h : ∀ m i, i < n → f m i = g m i) (m : List α) :
    (List.range n).foldl f m = (List.range n).foldl g m := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih (fun m i hi => h m i (by omega))]
    simp only [List.foldl_cons, List.foldl_nil]
    exact h _ _ (by omega)

theorem adjust_len_nonneg (n st sp se : Int) : 0 ≤ (adjustIndices n st sp se).2.2 := by
  unfold adjustIndices
  dsimp only
  split
  · split
    · have := Int.tdiv_nonneg (a := (RangeSlice.adjustOne st n se - RangeSlice.adjustOne sp n se - 1))
        (b := -se) (by omega) (by omega)
      omega
    · omega
  · split
    · rename_i h1 h2
      have := Int.tdiv_nonneg (a := (RangeSlice.adjustOne sp n se - RangeSlice.adjustOne st n se - 1))
        (b := se) (by omega) (by omega)
      omega
    · omega


open PyLean.RangeSlice in
/-- The C slice arithmetic (`PySlice_Unpack` + `PySlice_AdjustIndices`)
against `slice.indices`: start, stop and length agree, and for step != 1 the
`size_t` cursor visits `a + k*c`. -/
theorem adjust_spec (s : Slice) (n : Int) (hn : 0 ≤ n) (hn' : n ≤ ssizeMax) (h0 : s.step ≠ some 0) :
    ∃ a b c L st sp c', sliceIndices s n = .ok (a, b, c) ∧ IsLen a b c L ∧ Bnds a b c n ∧
      L = computeRangeLengthSlow a b c ∧
      sliceUnpack s = .ok (st, sp, c') ∧ adjustIndices n st sp c' = (a, b, L) ∧
      (c' = 1 ↔ c = 1) ∧ (c' < 0 ↔ c < 0) ∧ c ≠ 0 ∧ c' ≠ 0 ∧
      (∀ k : Int, 0 ≤ k → k < L → toU (toU a + k * toU c') = a + k * c) := by
  have hc := step_getD_ne h0
  have ⟨hsgn, hc'0, hlo, hhi, hid⟩ := clampStep_sign _ hc
  generalize hcdef : s.step.getD 1 = c at hc hsgn hc'0 hlo hhi hid
  have hb := clip_bnds s.start s.stop c n hn
  generalize hc'def : clampStep c = c' at hsgn hc'0 hlo hhi hid
  generalize hadef : clipLong s.start (startDflt c n) (lowerOf c) (upperOf c n) n = a at hb
  generalize hbdef : clipLong s.stop (stopDflt c n) (lowerOf c) (upperOf c n) n = b at hb
  have hL := slow_isLen a b c hc
  have hbig : c' = c ∨ (c' = ssizeMax ∨ c' = -ssizeMax) := by
    by_cases h1 : -ssizeMax ≤ c ∧ c ≤ ssizeMax
    · exact Or.inl (hid h1.1 h1.2)
    · right; rw [← hc'def]; unfold clampStep clampSsize ssizeMin ssizeMax at *
      split <;> (try split) <;> (try split) <;> omega
  obtain ⟨hL', hsmall⟩ := len_clamped a b c c' n _ hn' hc hsgn hc'0 hbig hid hb hL
  have hlen' : computeRangeLengthSlow a b c' = computeRangeLengthSlow a b c :=
    isLen_unique (slow_isLen a b c' hc'0) hL'
  refine ⟨a, b, c, computeRangeLengthSlow a b c, _, _, c', ?_, hL, hb, rfl,
    (by rw [sliceUnpack_eq s h0, hcdef, hc'def]), ?_, ?_, hsgn,
    hc, hc'0, ?_⟩
  · unfold sliceIndices
    rw [iteF (show ¬ n < 0 by omega), getLongIndices_eq s n h0, hcdef, hadef, hbdef]
  · unfold adjustIndices
    simp only
    rw [adjust_start s.start c c' n hn hn' hsgn, adjust_stop s.stop c c' n hn hn' hsgn, hadef, hbdef,
      adjust_len a b c' hc'0, hlen']
  · constructor
    · intro h1; rcases hbig with h | h
      · rw [← h, h1]
      · unfold ssizeMax at h; omega
    · intro h1; subst h1; rcases hbig with h | h
      · exact h
      · unfold ssizeMax at h; omega
  · intro k hk hkL
    have hin := indices_in_bounds a b c n _ hL hb k hk hkL
    rw [toU_lin]
    have hsame : a + k * c' = a + k * c := by
      by_cases hcc : c' = c
      · rw [hcc]
      · have := hsmall hcc
        rw [show k = 0 by omega]; simp
    rw [hsame]
    unfold two64
    unfold ssizeMax at hn'
    omega

theorem ix_map_range (L : Nat) (f : Nat → α) (i : Nat) (hi : i < L) :
    ix ((List.range L).map f) i = f i := by
  unfold ix
  rw [List.getD_eq_getElem?_getD, show ((i : Int)).toNat = i by omega, List.getElem?_map,
    List.getElem?_range hi]
  rfl

theorem zero_step_errors (l t : List α) (s : Slice) (h0 : s.step = some 0) :
    listAssSubscript l s (some t) = .error (.valueError "slice step cannot be zero") ∧
    sliceIndices s l.length = .error (.valueError "slice step cannot be zero") := by
  obtain ⟨st, sp, ss⟩ := s
  simp only at h0; subst h0
  constructor
  · simp [listAssSubscript, adjustSlice, sliceUnpack, RangeSlice.clampSsize, bind, Except.bind, ssizeMin,
      ssizeMax]; rfl
  · simp [sliceIndices, RangeSlice.getLongIndices, bind, Except.bind]; rfl

theorem listSliceAssign_proven : ListSliceAssign := by
  intro α _ l t s hlen
  have hn : 0 ≤ (l.length : Int) := by omega
  by_cases h0 : s.step = some 0
  · obtain ⟨e1, e2⟩ := zero_step_errors l t s h0
    rw [e1]; unfold sliceAssignSpec; rw [e2]
  obtain ⟨a, b, c, L, st, sp, c', hsi, hL, hb, hLdef, hsu, hadj, h1, hsg, hc, _, hpos⟩ :=
    adjust_spec s l.length hn hlen h0
  unfold listAssSubscript adjustSlice sliceAssignSpec
  rw [hsi, hsu]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [hadj]
  dsimp only
  rw [← hLdef]
  by_cases hc1 : c = 1
  · have hc'1 : c' = 1 := h1.mpr hc1
    rw [hc'1, iteT rfl, iteT hc1]
    have hb1 := hb.1 (by omega)
    unfold listAssSlice
    dsimp only
    have e1 : (if a < 0 then 0 else if a > (l.length : Int) then (l.length : Int) else a) = a := by
      split <;> (try split) <;> omega
    rw [e1]
    have e2 : (if (if (1:Int) < 0 ∧ a < b ∨ (1:Int) > 0 ∧ a > b then a else b) < a then a
        else if (if (1:Int) < 0 ∧ a < b ∨ (1:Int) > 0 ∧ a > b then a else b) > (l.length : Int) then (l.length : Int)
        else if (1:Int) < 0 ∧ a < b ∨ (1:Int) > 0 ∧ a > b then a else b) = max a b := by
      split <;> (try split) <;> (try split) <;> (try split) <;> omega
    rw [e2]
  · have hc'1 : ¬ c' = 1 := fun h => hc1 (h1.mp h)
    rw [iteF hc'1, iteF hc1]
    by_cases ht : (t.length : Int) ≠ L
    · rw [iteT ht, iteT ht]; rfl
    · rw [iteF ht, iteF ht]
      have htL : (t.length : Int) = L := by omega
      by_cases hL0 : L = 0
      · rw [iteT hL0]
        have : t = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst this; rfl
      · rw [iteF hL0]
        congr 1
        unfold storeLoop assignAt
        apply foldl_range_congr
        intro m i hi
        rw [ix_map_range _ _ _ (by omega), hpos i (by omega) (by omega)]

end PyLean.Sequences

