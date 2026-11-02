import PyLean.TextLibs.EtreeModel
import PyLean.Sequences.SliceAssign

/-!
Properties of `Element` as a sequence of children (`EtreeModel.lean`).

The reference for a slice store is `list`: the pure-Python twin stores through
`self._children[index] = element`, and `list_ass_subscript` is proven equal to the language
reference (`Sequences.ListSliceAssign`). The C accelerator agrees with it on every slice except a
backward step-1 slice (`e[5:2] = [x]`), where it duplicates one child pointer without a new
reference and drops another (`setSliceCIsList_refuted`, bug `textlibs-etree-slice-backward-dup`).
-/

namespace PyLean.TextLibs.Etree

open PyLean PyLean.Sequences
open PyLean.RangeSlice (Slice sliceUnpack adjustIndices adjustOne toU two64 listSlicePositions)

set_option linter.unusedSectionVars false

variable {α : Type} [Inhabited α]

/-! ## C slice assignment against `list` -/

/-- `e[s] = xs` in the C accelerator leaves the children `list` would hold after `l[s] = xs`,
and raises what `list` raises, for every slice with int/None parts, every element and every
list or tuple `xs` of Elements. `len(kids) <= sys.maxsize` is a type invariant. -/
def SetSliceCIsList : Prop :=
  ∀ (α : Type) [Inhabited α] (T : Ty α) (kids xs : List α) (s : Slice),
    (kids.length : Int) ≤ ssizeMax → (xs.length : Int) ≤ ssizeMax → (∀ x ∈ xs, T.isElem x) →
    setSliceC T kids s (.seq xs) = ofList kids (listAssSubscript kids s (some xs))

/-- `e[5:2] = [X]` on seven children: C leaves `a0 a1 a2 a2 a3 X a5 a6` (a2 twice, a4 gone), where
`list` leaves `a0 a1 a2 a3 a4 X a5 a6`. -/
theorem setSliceCIsList_refuted : ¬ SetSliceCIsList := by
  intro h
  have := congrArg Prod.fst (h Nat caseTy [0, 1, 2, 3, 4, 5, 6] [7] ⟨some 5, some 2, none⟩
    (by decide) (by decide) (by decide))
  revert this
  decide

/-- What the bug does to the children, as an equation the model computes. -/
theorem setSliceC_backward_example :
    (setSliceC caseTy [0, 1, 2, 3, 4, 5, 6] ⟨some 5, some 2, none⟩ (.seq [7])).1 =
      [0, 1, 2, 2, 3, 7, 5, 6] := by decide

/-! ## The two twins on iterators -/

/-- The C accelerator and the pure-Python twin leave the same children after every slice store,
whatever iterable is assigned. -/
def SetSliceTwins : Prop :=
  ∀ (α : Type) [Inhabited α] (T : Ty α) (kids : List α) (s : Slice) (a : Arg α),
    (kids.length : Int) ≤ ssizeMax →
    (setSliceC T kids s a).1 = (setSlicePy T kids s a).1

/-- `e[1:1] = (x for x in [X0, X1])`: C inserts both, the Python twin inserts nothing, because its
type-check loop exhausts the generator before `list.__setitem__` iterates it. -/
theorem setSliceTwins_refuted : ¬ SetSliceTwins := by
  intro h
  have := h Nat caseTy [0, 1, 2] ⟨some 1, some 1, none⟩ (.iter [60, 61] none id) (by decide)
  revert this
  decide

/-! ## Loop lemmas -/

theorem set_getElem? (l : List α) (i p : Nat) (v : α) :
    (l.set i v)[p]? = if p = i ∧ i < l.length then some v else l[p]? := by
  by_cases h : p = i
  · subst h
    by_cases h2 : p < l.length
    · rw [if_pos ⟨rfl, h2⟩]; simp [h2]
    · rw [if_neg (fun h => h2 h.2), List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
  · rw [if_neg (fun h' => h h'.1), List.getElem?_set_ne (Ne.symm h)]

theorem foldl_set_length (n : Nat) (f : List α → Nat → Nat) (g : List α → Nat → α) (m : List α) :
    ((List.range n).foldl (fun m k => m.set (f m k) (g m k)) m).length = m.length := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append]; simp [ih]

/-- The `newlen < slicelen` shift: after `k` moves, the slots `[e, e+k)` hold what sat `δ`
further right. -/
theorem shiftDown_nat (mem : List α) (e δ k : Nat) (hk : e + δ + k ≤ mem.length) (p : Nat) :
    ((List.range k).foldl (fun m (j : Nat) => m.set (e + j) (m.getD (e + δ + j) default)) mem)[p]? =
      if e ≤ p ∧ p < e + k then mem[p + δ]? else mem[p]? := by
  induction k generalizing p with
  | zero => simp; omega
  | succ k ih =>
    have ih' := ih (by omega)
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [set_getElem?, foldl_set_length, List.getD_eq_getElem?_getD, ih' (e + δ + k),
      if_neg (show ¬(e ≤ e + δ + k ∧ e + δ + k < e + k) by omega),
      List.getElem?_eq_getElem (show e + δ + k < mem.length by omega), Option.getD_some, ih' p]
    by_cases hp : p = e + k
    · subst hp
      rw [if_pos (show e + k = e + k ∧ e + k < mem.length from ⟨rfl, by omega⟩),
        if_pos (show e ≤ e + k ∧ e + k < e + (k + 1) by omega), show e + k + δ = e + δ + k by omega,
        List.getElem?_eq_getElem (show e + δ + k < mem.length by omega)]
    · rw [if_neg (fun h => hp h.1)]
      by_cases hin : e ≤ p ∧ p < e + k
      · rw [if_pos hin, if_pos (show e ≤ p ∧ p < e + (k + 1) by omega)]
      · rw [if_neg hin, if_neg (show ¬(e ≤ p ∧ p < e + (k + 1)) by omega)]

/-- The `newlen > slicelen` shift, walking down from the last child: after `k` moves, the top
`k` slots of the grown buffer hold what sat `D` further left. -/
theorem shiftUp_nat (mem : List α) (n D k : Nat) (hk : k ≤ n) (hlen : mem.length = n + D) (p : Nat) :
    ((List.range k).foldl (fun m (j : Nat) => m.set (n - 1 - j + D) (m.getD (n - 1 - j) default)) mem)[p]? =
      if n + D - k ≤ p ∧ p < n + D then mem[p - D]? else mem[p]? := by
  induction k generalizing p with
  | zero => simp; omega
  | succ k ih =>
    have ih' := ih (by omega)
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [set_getElem?, foldl_set_length, List.getD_eq_getElem?_getD, ih' (n - 1 - k),
      if_neg (show ¬(n + D - k ≤ n - 1 - k ∧ n - 1 - k < n + D) by omega),
      List.getElem?_eq_getElem (show n - 1 - k < mem.length by omega), Option.getD_some, ih' p]
    by_cases hp : p = n - 1 - k + D
    · subst hp
      rw [if_pos (show n - 1 - k + D = n - 1 - k + D ∧ n - 1 - k + D < mem.length from ⟨rfl, by omega⟩),
        if_pos (show n + D - (k + 1) ≤ n - 1 - k + D ∧ n - 1 - k + D < n + D by omega),
        show n - 1 - k + D - D = n - 1 - k by omega,
        List.getElem?_eq_getElem (show n - 1 - k < mem.length by omega)]
    · rw [if_neg (fun h => hp h.1)]
      by_cases hin : n + D - k ≤ p ∧ p < n + D
      · rw [if_pos hin, if_pos (show n + D - (k + 1) ≤ p ∧ p < n + D by omega)]
      · rw [if_neg hin, if_neg (show ¬(n + D - (k + 1) ≤ p ∧ p < n + D) by omega)]

/-- The replace loop with step 1: after `k` stores, `[a, a+k)` holds `xs[0:k]`. -/
theorem store_nat (mem xs : List α) (a k : Nat) (hk : k ≤ xs.length) (hlen : a + k ≤ mem.length) (p : Nat) :
    ((List.range k).foldl (fun m (i : Nat) => m.set (a + i) (xs.getD i default)) mem)[p]? =
      if a ≤ p ∧ p < a + k then xs[p - a]? else mem[p]? := by
  induction k generalizing p with
  | zero => simp; omega
  | succ k ih =>
    have ih' := ih (by omega) (by omega)
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [set_getElem?, foldl_set_length, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show k < xs.length by omega), Option.getD_some, ih' p]
    by_cases hp : p = a + k
    · subst hp
      rw [if_pos (show a + k = a + k ∧ a + k < mem.length from ⟨rfl, by omega⟩),
        if_pos (show a ≤ a + k ∧ a + k < a + (k + 1) by omega), show a + k - a = k by omega,
        List.getElem?_eq_getElem (show k < xs.length by omega)]
    · rw [if_neg (fun h => hp h.1)]
      by_cases hin : a ≤ p ∧ p < a + k
      · rw [if_pos hin, if_pos (show a ≤ p ∧ p < a + (k + 1) by omega)]
      · rw [if_neg hin, if_neg (show ¬(a ≤ p ∧ p < a + (k + 1)) by omega)]

/-! ## Bridges from the C loops to the lemmas above -/

theorem shiftDown_eq (mem : List α) (b n e : Nat) (heb : e ≤ b) (d : Int) (hd : d = (e : Int) - b) :
    shiftDown mem b n d =
      (List.range (n - b)).foldl (fun m (j : Nat) => m.set (e + j) (m.getD (e + (b - e) + j) default)) mem := by
  unfold shiftDown
  rw [show ((n : Int) - (b : Int)).toNat = n - b by omega]
  apply foldl_range_congr
  intro m j _
  simp only [ix]
  rw [show ((b : Int) + (j : Int) + d).toNat = e + j by omega,
    show ((b : Int) + (j : Int)).toNat = e + (b - e) + j by omega]

theorem shiftUp_eq (mem : List α) (b n D : Nat) (hb : b ≤ n) :
    shiftUp mem b n D =
      (List.range (n - b)).foldl (fun m (j : Nat) => m.set (n - 1 - j + D) (m.getD (n - 1 - j) default)) mem := by
  unfold shiftUp
  rw [show ((n : Int) - (b : Int)).toNat = n - b by omega]
  apply foldl_range_congr
  intro m j hj
  simp only [ix]
  rw [show ((n : Int) - 1 - (j : Int) + (D : Int)).toNat = n - 1 - j + D by omega,
    show ((n : Int) - 1 - (j : Int)).toNat = n - 1 - j by omega]

theorem storeLoop_one (mem xs : List α) (a : Nat) (hsmall : (a : Int) + xs.length < two64) :
    storeLoop mem a 1 xs =
      (List.range xs.length).foldl (fun m (i : Nat) => m.set (a + i) (xs.getD i default)) mem := by
  unfold storeLoop
  apply foldl_range_congr
  intro m i hi
  simp only [ix, toU]
  unfold two64 at hsmall ⊢
  rw [show ((((a : Int) % 18446744073709551616 + (i : Int) * (1 % 18446744073709551616)) %
      18446744073709551616)).toNat = a + i by omega, show ((i : Int)).toNat = i by omega]

theorem storeLoop_length (mem xs : List α) (a step : Int) : (storeLoop mem a step xs).length = mem.length := by
  unfold storeLoop
  exact foldl_set_length _ (fun _ i => (toU (toU a + (i : Int) * toU step)).toNat) (fun _ i => ix xs i) mem

theorem storeLoop_nil (mem : List α) (a step : Int) : storeLoop mem a step [] = mem := rfl

theorem take_get (l : List α) (t p : Nat) : (l.take t)[p]? = if p < t then l[p]? else none := by
  rw [List.getElem?_take]

theorem pad_get (kids : List α) (D p : Nat) :
    (kids ++ List.replicate D default)[p]? =
      if p < kids.length then kids[p]? else if p < kids.length + D then some default else none := by
  by_cases h : p < kids.length
  · rw [if_pos h, List.getElem?_append_left h]
  · rw [if_neg h, List.getElem?_append_right (by omega), List.getElem?_replicate]
    by_cases h2 : p < kids.length + D
    · rw [if_pos (by omega), if_pos h2]
    · rw [if_neg (by omega), if_neg h2]

/-- The list result, slot by slot. -/
theorem splice_get (kids xs : List α) (a b p : Nat) (ha : a ≤ b) (hb : b ≤ kids.length) :
    (kids.take a ++ xs ++ kids.drop b)[p]? =
      if p < a then kids[p]? else if p < a + xs.length then xs[p - a]? else kids[p - a - xs.length + b]? := by
  have hta : (kids.take a).length = a := by simp; omega
  by_cases h1 : p < a
  · rw [if_pos h1, List.append_assoc, List.getElem?_append_left (by omega), List.getElem?_take_of_lt h1]
  · rw [if_neg h1, List.append_assoc, List.getElem?_append_right (by omega), hta]
    by_cases h2 : p < a + xs.length
    · rw [if_pos h2, List.getElem?_append_left (by omega)]
    · rw [if_neg h2, List.getElem?_append_right (by omega), List.getElem?_drop]
      congr 1; omega

/-- The step-1 store, `a ≤ b`: C's resize, shift, replace and truncate is the splice. -/
theorem splice_c (kids xs : List α) (a b : Nat) (ha : a ≤ b) (hb : b ≤ kids.length)
    (hsmall : (b : Int) + xs.length < two64) (L : Int) (hL : L = (b : Int) - a) :
    let n : Int := kids.length
    let newlen : Int := xs.length
    let mem := if newlen > L then kids ++ List.replicate (newlen - L).toNat default else kids
    let d := newlen - L
    let mem := if newlen < L then shiftDown mem b n d else if newlen > L then shiftUp mem b n d else mem
    (storeLoop mem a 1 xs).take (n + d).toNat = kids.take a ++ xs ++ kids.drop b := by
  intro n newlen mem d mem'
  have hst : (a : Int) + xs.length < two64 := by omega
  apply List.ext_getElem?
  intro p
  rw [take_get, storeLoop_one _ _ _ hst, splice_get kids xs a b p ha hb]
  by_cases hlt : newlen < L
  · -- shrink: the tail moves left by `b - (a + len xs)`
    have hm : mem' = (List.range (kids.length - b)).foldl
        (fun m (j : Nat) => m.set (a + xs.length + j) (m.getD (a + xs.length + (b - (a + xs.length)) + j) default)) kids := by
      simp only [mem', mem, if_pos hlt, if_neg (show ¬ newlen > L by omega)]
      exact shiftDown_eq kids b kids.length (a + xs.length) (by omega) d (by omega)
    have hlen : mem'.length = kids.length := by rw [hm]; exact foldl_set_length _ _ _ _
    rw [store_nat _ _ _ _ (Nat.le_refl _) (by omega), hm,
      shiftDown_nat _ _ _ _ (by omega)]
    rw [show (n + d).toNat = kids.length - (b - (a + xs.length)) by omega]
    by_cases h1 : p < a
    · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos h1]
    · rw [if_neg h1]
      by_cases h2 : p < a + xs.length
      · rw [if_pos (by omega), if_pos (show a ≤ p ∧ p < a + xs.length by omega), if_pos h2]
      · rw [if_neg h2, if_neg (show ¬(a ≤ p ∧ p < a + xs.length) by omega)]
        by_cases h3 : p < kids.length - (b - (a + xs.length))
        · rw [if_pos h3, if_pos (by omega)]; congr 1; omega
        · rw [if_neg h3, List.getElem?_eq_none (by omega)]
  · by_cases hgt : newlen > L
    · -- grow: the tail moves right by `len xs - (b - a)` into the padded buffer
      have hm : mem' = (List.range (kids.length - b)).foldl
          (fun m (j : Nat) => m.set (kids.length - 1 - j + (xs.length - (b - a)))
            (m.getD (kids.length - 1 - j) default)) (kids ++ List.replicate (xs.length - (b - a)) default) := by
        simp only [mem', mem, if_neg hlt, if_pos hgt]
        rw [show (newlen - L).toNat = xs.length - (b - a) by omega,
          show d = ((xs.length - (b - a) : Nat) : Int) by omega]
        exact shiftUp_eq _ b kids.length _ hb
      have hpad : (kids ++ List.replicate (xs.length - (b - a)) default).length =
          kids.length + (xs.length - (b - a)) := by simp
      have hlen : mem'.length = kids.length + (xs.length - (b - a)) := by
        rw [hm, foldl_set_length _ _ _ _, hpad]
      rw [store_nat _ _ _ _ (Nat.le_refl _) (by omega), hm,
        shiftUp_nat _ _ _ _ (by omega) hpad, pad_get, pad_get]
      rw [show (n + d).toNat = kids.length + (xs.length - (b - a)) by omega]
      by_cases h1 : p < a
      · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos h1]
      · rw [if_neg h1]
        by_cases h2 : p < a + xs.length
        · rw [if_pos (by omega), if_pos (show a ≤ p ∧ p < a + xs.length by omega), if_pos h2]
        · rw [if_neg h2, if_neg (show ¬(a ≤ p ∧ p < a + xs.length) by omega)]
          by_cases h3 : p < kids.length + (xs.length - (b - a))
          · rw [if_pos h3, if_pos (show kids.length + (xs.length - (b - a)) - (kids.length - b) ≤ p ∧
              p < kids.length + (xs.length - (b - a)) by omega), if_pos (by omega)]
            congr 1; omega
          · rw [if_neg h3, List.getElem?_eq_none (by omega)]
    · -- same length: no shift
      have hm : mem' = kids := by simp only [mem', mem, if_neg hlt, if_neg hgt]
      have hlen : (xs.length : Int) = (b : Int) - a := by omega
      rw [hm, store_nat _ _ _ _ (Nat.le_refl _) (by omega),
        show (n + d).toNat = kids.length by omega]
      by_cases h1 : p < a
      · rw [if_pos (by omega), if_neg (by omega), if_pos h1]
      · rw [if_neg h1]
        by_cases h2 : p < a + xs.length
        · rw [if_pos (by omega), if_pos (show a ≤ p ∧ p < a + xs.length by omega), if_pos h2]
        · rw [if_neg h2, if_neg (show ¬(a ≤ p ∧ p < a + xs.length) by omega)]
          by_cases h3 : p < kids.length
          · rw [if_pos h3]; congr 1; omega
          · rw [if_neg h3, List.getElem?_eq_none (by omega)]

/-! ## The forward theorem -/

/-- The slice is not a backward step-1 slice: when the step is 1, the clipped start does not lie
past the clipped stop. Every slice with another step, and every step-1 slice with
`start <= stop` after clipping, qualifies. -/
def Forward (n : Int) (s : Slice) : Prop :=
  ∀ start stop, sliceUnpack s = .ok (start, stop, 1) →
    (adjustIndices n start stop 1).1 ≤ (adjustIndices n start stop 1).2.1

/-- `SetSliceCIsList` on every forward slice: the C store and `list` agree there, on the children
left behind and on every exception (`PySlice_Unpack` errors and the extended-slice size check). -/
def SetSliceCForwardIsList : Prop :=
  ∀ (α : Type) [Inhabited α] (T : Ty α) (kids xs : List α) (s : Slice),
    (kids.length : Int) ≤ ssizeMax → (xs.length : Int) ≤ ssizeMax → (∀ x ∈ xs, T.isElem x) →
    Forward kids.length s →
    setSliceC T kids s (.seq xs) = ofList kids (listAssSubscript kids s (some xs))

theorem adjOne_bounds (x n : Int) (hn : 0 ≤ n) : 0 ≤ adjustOne x n 1 ∧ adjustOne x n 1 ≤ n := by
  unfold adjustOne; dsimp only; (repeat' split) <;> omega

theorem setSliceCForwardIsList_proven : SetSliceCForwardIsList := by
  intro α _ T kids xs s hn hm hel hfw
  have hbad : firstBad T xs = none := by
    unfold firstBad; rw [List.find?_eq_none]; intro x hx; simp [hel x hx]
  unfold setSliceC listAssSubscript adjustSlice
  cases hu : sliceUnpack s with
  | error e => simp [ofList, bind, Except.bind]
  | ok v =>
    obtain ⟨start, stop, step⟩ := v
    rw [show fastC kids (Arg.seq xs) = (kids, Except.ok xs) from rfl]
    simp only [bind, Except.bind, pure, Except.pure, hbad]
    by_cases hs : step = 1
    · subst hs
      have hf := hfw start stop hu
      simp only [adjustIndices, show ¬ ((1 : Int) < 0) by decide, if_false, Int.tdiv_one] at hf ⊢
      obtain ⟨ha0, han⟩ := adjOne_bounds start kids.length (by omega)
      obtain ⟨hb0, hbn⟩ := adjOne_bounds stop kids.length (by omega)
      generalize adjustOne start (kids.length : Int) 1 = A at *
      generalize adjustOne stop (kids.length : Int) 1 = B at *
      obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
      obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hb0
      have hab : a ≤ b := by omega
      have hstop : (if ((1 : Int) < 0 ∧ (a : Int) < b) ∨ ((1 : Int) > 0 ∧ (a : Int) > b) then (a : Int) else b) = b := by
        rw [if_neg (by omega)]
      simp only [hstop, show ((1 : Int) ≠ 1) = False by simp, false_and, if_false, ite_true, ofList]
      
      unfold listAssSlice
      simp only [if_neg (show ¬ ((a : Int) < 0) by omega), if_neg (show ¬ ((a : Int) > kids.length) by omega),
        if_neg (show ¬ ((b : Int) < a) by omega), if_neg (show ¬ ((b : Int) > kids.length) by omega)]
      try rw [show ((a : Int)).toNat = a by omega]
      try rw [show ((b : Int)).toNat = b by omega]
      have h := splice_c kids xs a b hab (by omega) (by unfold two64 ssizeMax at *; omega)
        (if (a : Int) < (b : Int) then (b : Int) - a - 1 + 1 else 0) (by split <;> omega)
      simp only [] at h
      rw [h]
      (repeat' split) <;> (try simp only [false_or] at *) <;> first | omega | simp
    · simp only [hs, ne_eq, not_false_eq_true, true_and, if_false]
      by_cases hl : (xs.length : Int) = (adjustIndices (kids.length : Int) start stop step).2.2
      · simp only [← hl, Int.lt_irrefl, gt_iff_lt, not_true_eq_false, ite_false, if_false, Int.sub_self,
          Int.add_zero]
        rw [show ((kids.length : Int)).toNat = kids.length by omega,
          List.take_of_length_le (by rw [storeLoop_length]; exact Nat.le_refl _)]
        by_cases h0 : (xs.length : Int) = 0
        · rw [if_pos h0]
          have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst this
          rfl
        · rw [if_neg h0]; rfl
      · rw [if_pos hl, if_pos hl]; rfl

/-! ## Slice deletion against `list` -/

/-- `del e[s]` in the C accelerator leaves the children the Python twin's `del self._children[s]`
leaves, and raises what it raises, for every slice with int/None parts. -/
def DelSliceCIsList : Prop :=
  ∀ (α : Type) [Inhabited α] (kids : List α) (s : Slice), (kids.length : Int) ≤ ssizeMax →
    delSliceC kids s = delSlicePy kids s

/-- With step 1 every `num_moved` is 0, so the compaction loop moves nothing. -/
theorem delLoop_one (fuel : Nat) (mem : List α) (stop cur i : Int)
    (hstop : stop ≤ mem.length) (hi : 0 ≤ i) (hic : i ≤ cur) (hf : stop - cur < fuel) (hf0 : 0 < fuel) :
    delLoop (mem.length : Int) 1 stop fuel mem cur i = .ok mem := by
  induction fuel generalizing cur i with
  | zero => omega
  | succ fuel ih =>
    unfold delLoop
    by_cases hc : cur < stop
    · rw [if_pos hc]
      have hlim : (if cur + 1 ≥ (mem.length : Int) then (mem.length : Int) - cur - 1 else 1 - 1) = 0 := by
        split <;> omega
      simp only [hlim]
      have hmv : memmove mem (cur - i) (cur + 1) 0 = .ok mem := by
        unfold memmove
        rw [if_pos (by omega)]
        simp only [Int.toNat_zero, List.take_zero, List.append_nil, Int.add_zero]
        rw [List.take_append_drop]
      rw [hmv]
      exact ih (cur + 1) (i + 1) (by omega) (by omega) (by omega) (by omega)
    · rw [if_neg hc]

/-- Step-1 deletion of `[a, b)`, `a < b`: the tail move and the shrink leave the splice. -/
theorem delExtended_one (kids : List α) (a b : Nat) (hab : a < b) (hb : b ≤ kids.length) :
    delExtended kids a b 1 ((b : Int) - a - 1 + 1) = .ok (kids.take a ++ kids.drop b) := by
  unfold delExtended
  simp only [show ¬ ((1 : Int) < 0) by decide, if_false, ite_false]
  rw [show ((b : Int) - a - 1 + 1).toNat + 1 = (b - a) + 1 by omega]
  simp only [bind, Except.bind]
  rw [delLoop_one _ kids b a 0 (by omega) (by omega) (by omega) (by omega) (by omega)]
  simp only [show (a : Int) + ((b : Int) - a - 1 + 1) * 1 = b by omega,
    show (b : Int) - ((b : Int) - a - 1 + 1) = a by omega, pure, Except.pure]
  by_cases hlt : (b : Int) < kids.length
  · rw [if_pos hlt]
    unfold memmove
    rw [if_pos (by omega)]
    simp only []
    congr 1
    apply List.ext_getElem?
    intro p
    rw [take_get]
    simp only [List.getElem?_append, List.getElem?_take, List.getElem?_drop, List.length_append,
      List.length_take, List.length_drop]
    rw [show ((kids.length : Int) - ((b : Int) - a - 1 + 1)).toNat = kids.length - (b - a) by omega,
      show ((a : Int)).toNat = a by omega, show ((b : Int)).toNat = b by omega,
      show ((kids.length : Int) - b).toNat = kids.length - b by omega,
      show ((a : Int) + ((kids.length : Int) - b)).toNat = a + (kids.length - b) by omega]
    (repeat' split) <;> (try rw [Nat.min_eq_left (show a ≤ kids.length by omega)] at *) <;>
      (first | omega | rfl | (congr 1; omega) | (simp_all <;> omega))
  · rw [if_neg hlt]
    congr 1
    rw [show b = kids.length by omega, List.drop_length, List.append_nil]
    congr 1
    omega

/-- A nonempty adjusted slice is never backward, so `list`'s clip of `stop` does nothing. -/
theorem adj_noclamp (n st sp step : Int) (h : 0 < (adjustIndices n st sp step).2.2) :
    ¬ ((step < 0 ∧ (adjustIndices n st sp step).1 < (adjustIndices n st sp step).2.1) ∨
      (step > 0 ∧ (adjustIndices n st sp step).1 > (adjustIndices n st sp step).2.1)) := by
  unfold adjustIndices at *
  dsimp only at *
  (repeat' split at h) <;> omega

theorem delSliceCIsList_proven : DelSliceCIsList := by
  intro α _ kids s hn
  unfold delSliceC delSlicePy listAssSubscript adjustSlice
  cases hu : sliceUnpack s with
  | error e => simp [ofList, bind, Except.bind]
  | ok v =>
    obtain ⟨start, stop, step⟩ := v
    simp only [bind, Except.bind, pure, Except.pure]
    by_cases hs : step = 1
    · subst hs
      simp only [adjustIndices, show ¬ ((1 : Int) < 0) by decide, if_false, Int.tdiv_one, if_true]
      obtain ⟨ha0, han⟩ := adjOne_bounds start kids.length (by omega)
      obtain ⟨hb0, hbn⟩ := adjOne_bounds stop kids.length (by omega)
      generalize adjustOne start (kids.length : Int) 1 = A at *
      generalize adjustOne stop (kids.length : Int) 1 = B at *
      obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
      obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hb0
      unfold listAssSlice
      by_cases hab : a < b
      · have hab' : (a : Int) < b := by omega
        try simp only [hab', if_true, ite_true]
        rw [if_neg (show ¬ ((b : Int) - a - 1 + 1 ≤ 0) by omega), delExtended_one kids a b hab (by omega)]
        simp only [ofList, Prod.mk.injEq, and_true]
        (repeat' split) <;> (try simp only [false_or, false_and] at *) <;> first | omega | simp
      · have hab' : ¬ (a : Int) < b := by omega
        try simp only [hab', if_false, ite_false]
        rw [if_pos (show (0 : Int) ≤ 0 by omega)]
        simp only [ofList, Prod.mk.injEq, and_true]
        (repeat' split) <;> (try simp only [false_or, false_and] at *) <;>
          first | omega | (have : a = b := by omega
                           subst this; simp) | simp
    · simp only [hs, if_false, ite_false]
      by_cases hl : (adjustIndices (kids.length : Int) start stop step).2.2 ≤ 0
      · simp only [hl, if_true, ite_true, ofList]
      · simp only [hl, if_false, ite_false]
        rw [if_neg (adj_noclamp _ _ _ _ (by omega))]
        cases delExtended kids (adjustIndices (kids.length : Int) start stop step).1
          (adjustIndices (kids.length : Int) start stop step).2.1 step
          (adjustIndices (kids.length : Int) start stop step).2.2 <;> rfl

/-! ## Index paths: C against the Python twin -/

/-- Two outcomes agree: equal values, or exceptions of the same class. The twins word their
`IndexError`s differently ("child index out of range" against "list index out of range"). -/
def Agree {β : Type} : Py β → Py β → Prop
  | .ok x, .ok y => x = y
  | .error e, .error f => e.className = f.className
  | _, _ => False

/-- `e[i]`, `del e[i]` and `e[i] = x` for an Element `x` give the same children, values and
exception classes in both twins, for every int `i`. `x` being an Element is the documented
precondition of item assignment; `itemStoreTwins_refuted` covers the rest. -/
def ItemTwins : Prop :=
  ∀ (α : Type) [Inhabited α] (T : Ty α) (kids : List α) (i : Int),
    Agree (getItemC kids i) (getItemPy kids i) ∧
    (assItemC T kids i none).1 = (delItemPy kids i).1 ∧ Agree (assItemC T kids i none).2 (delItemPy kids i).2 ∧
    ∀ x, T.isElem x →
      (assItemC T kids i (some x)).1 = (setItemPy T kids i x).1 ∧
      Agree (assItemC T kids i (some x)).2 (setItemPy T kids i x).2

theorem itemTwins_proven : ItemTwins := by
  intro α _ T kids i
  unfold getItemC getItemPy listGetItem assItemC setItemC delItemPy setItemPy listAssItem ofList
  cases h : subIndex i with
  | error e =>
    refine ⟨by simp [bind, Except.bind, Agree], by simp [bind, Except.bind], by simp [bind, Except.bind, Agree],
      fun x hx => by simp [hx, bind, Except.bind, Agree]⟩
  | ok j =>
    simp only [bind, Except.bind, pure, Except.pure]
    by_cases hb : (if j < 0 then j + kids.length else j) < 0 ∨
        (if j < 0 then j + kids.length else j) ≥ kids.length
    · have hv : validIndex (if j < 0 then j + kids.length else j) kids.length = false := by
        unfold validIndex; simp only [decide_eq_false_iff_not]; omega
      simp only [hb, hv, if_true, ite_true, Bool.not_false]
      refine ⟨rfl, rfl, rfl, fun x hx => ?_⟩
      simp [hx, Agree, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw, PyExc.className]
    · have hv : validIndex (if j < 0 then j + kids.length else j) kids.length = true := by
        unfold validIndex; simp only [decide_eq_true_eq]; omega
      simp only [hb, hv, if_false, ite_false, Bool.not_true]
      refine ⟨rfl, rfl, rfl, fun x hx => ?_⟩
      simp [hx, Agree]

/-- `ItemTwins`' store clause for every value, Element or not. -/
def ItemStoreTwins : Prop :=
  ∀ (α : Type) [Inhabited α] (T : Ty α) (kids : List α) (i : Int) (x : α),
    Agree (assItemC T kids i (some x)).2 (setItemPy T kids i x).2

/-- `e[100] = 1000` on an empty element: C checks the index first (`IndexError`), the Python
twin the value first (`TypeError`). -/
theorem itemStoreTwins_refuted : ¬ ItemStoreTwins := by
  intro h
  have := h Nat caseTy [] 100 1000
  have h1 : (assItemC caseTy [] 100 (some 1000)).2 = .error (.indexError "child assignment index out of range") := rfl
  have h2 : (setItemPy caseTy [] 100 1000).2 = .error (typeErrPy caseTy 1000) := rfl
  rw [h1, h2] at this
  simp [Agree, PyExc.className, typeErrPy] at this

/-! ## Slice reads -/

/-- `e[s]` gives the same children, or the same exception, in both twins, for every slice with
int/None parts. -/
def GetSliceTwins : Prop :=
  ∀ (α : Type) [Inhabited α] (kids : List α) (s : Slice), (kids.length : Int) ≤ ssizeMax →
    getSliceC kids s = getSlicePy kids s

theorem getSliceTwins_proven : GetSliceTwins := by
  intro α _ kids s hn
  unfold getSliceC getSlicePy listSlicePositions
  cases hu : sliceUnpack s with
  | error e => rfl
  | ok v =>
    obtain ⟨start, stop, step⟩ := v
    simp only [bind, Except.bind, pure, Except.pure]
    by_cases hl : (adjustIndices (kids.length : Int) start stop step).2.2 ≤ 0
    · simp only [hl, if_true, ite_true, List.map_nil]
    · simp only [hl, if_false, ite_false]
      by_cases hs : step = 1
      · subst hs
        simp only [if_true, ite_true]
        simp only [adjustIndices, show ¬ ((1 : Int) < 0) by decide, if_false, Int.tdiv_one] at hl ⊢
        obtain ⟨ha0, han⟩ := adjOne_bounds start kids.length (by omega)
        obtain ⟨hb0, hbn⟩ := adjOne_bounds stop kids.length (by omega)
        generalize adjustOne start (kids.length : Int) 1 = A at *
        generalize adjustOne stop (kids.length : Int) 1 = B at *
        have hab : A < B := by split at hl <;> omega
        rw [if_pos hab, List.map_map]
        rw [show (B - A - 1 + 1).toNat = (B - A).toNat by omega]
        congr 1
        apply List.map_congr_left
        intro i hi
        simp only [Function.comp, toU, two64]
        rw [List.mem_range] at hi
        congr 1
        unfold ssizeMax at hn
        omega
      · simp only [hs, if_false, ite_false, List.map_map]
        rfl

/-! ## Slice stores of a list or tuple: the twins -/

/-- For a list or tuple of Elements and a forward slice, both twins leave the same children and
raise the same exception. -/
def SetSliceTwinsSeq : Prop :=
  ∀ (α : Type) [Inhabited α] (T : Ty α) (kids xs : List α) (s : Slice),
    (kids.length : Int) ≤ ssizeMax → (xs.length : Int) ≤ ssizeMax → (∀ x ∈ xs, T.isElem x) →
    Forward kids.length s → setSliceC T kids s (.seq xs) = setSlicePy T kids s (.seq xs)

theorem setSliceTwinsSeq_proven : SetSliceTwinsSeq := by
  intro α _ T kids xs s hn hm hel hfw
  have hbad : firstBad T xs = none := by
    unfold firstBad; rw [List.find?_eq_none]; intro x hx; simp [hel x hx]
  rw [setSliceCForwardIsList_proven α T kids xs s hn hm hel hfw]
  simp only [setSlicePy, hbad]

end PyLean.TextLibs.Etree
