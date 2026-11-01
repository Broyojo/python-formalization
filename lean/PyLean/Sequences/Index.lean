import PyLean.Sequences.DequeOps

/-!
`index(x, start, stop)` agrees across `list`, `array.array` and
`collections.deque`, and returns the first match in `s[start:stop]`.
-/

namespace PyLean.Sequences

open PyLean
open PyLean.RangeSlice (Slice sliceIndices)

set_option linter.unusedSectionVars false

variable {α : Type} [Inhabited α]

/-- `r` is the first position `i` in `[a, b)` (and in the list) whose item
satisfies `p`, or `none` when there is no such position. -/
def IsFirst (p : α → Bool) (l : List α) (a b : Int) : Option Int → Prop
  | some i => a ≤ i ∧ i < b ∧ 0 ≤ i ∧ i < l.length ∧ p (ix l i) = true ∧
      ∀ j, a ≤ j → j < i → 0 ≤ j → p (ix l j) = false
  | none => ∀ j, a ≤ j → j < b → 0 ≤ j → j < l.length → p (ix l j) = false

theorem isFirst_congr (p : α → Bool) (l : List α) (a b a' b' : Int) (r : Option Int)
    (hab : ∀ j : Int, 0 ≤ j → j < l.length → (a ≤ j ∧ j < b ↔ a' ≤ j ∧ j < b'))
    (h : IsFirst p l a b r) : IsFirst p l a' b' r := by
  cases r with
  | none =>
    intro j h1 h2 h3 h4
    have := (hab j h3 h4).mpr ⟨h1, h2⟩
    exact h j this.1 this.2 h3 h4
  | some i =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    have hi := (hab i h3 h4).mp ⟨h1, h2⟩
    refine ⟨hi.1, hi.2, h3, h4, h5, fun j hj1 hj2 hj3 => ?_⟩
    have := (hab j hj3 (by omega)).mpr ⟨hj1, by omega⟩
    exact h6 j this.1 hj2 hj3

/-- Step a search loop: if position `i` is not a match, the first match from
`i + 1` is the first match from `i`. -/
theorem isFirst_step (p : α → Bool) (l : List α) (i b : Int) (r : Option Int) (hne : p (ix l i) = false)
    (h : IsFirst p l (i + 1) b r) : IsFirst p l i b r := by
  cases r with
  | none =>
    intro j h1 h2 h3 h4
    by_cases hj : j = i
    · subst hj; exact hne
    · exact h j (by omega) h2 h3 h4
  | some k =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨by omega, h2, h3, h4, h5, fun j hj1 hj2 hj3 => ?_⟩
    by_cases hj : j = i
    · subst hj; exact hne
    · exact h6 j (by omega) hj2 hj3

theorem isFirst_here (p : α → Bool) (l : List α) (i b : Int) (h0 : 0 ≤ i) (hb : i < b) (hl : i < l.length)
    (hx : p (ix l i) = true) : IsFirst p l i b (some i) :=
  ⟨Int.le_refl _, hb, h0, hl, hx, fun j h1 h2 _ => by omega⟩

theorem isFirst_empty (p : α → Bool) (l : List α) (i b : Int) (h : ¬ (i < b ∧ i < l.length)) :
    IsFirst p l i b none := by
  intro j h1 h2 _ h4; omega

theorem listIndexLoop_spec (f : α → α → Bool) (l : List α) (x : α) (stop : Int) : ∀ (fuel : Nat) (i : Int), 0 ≤ i →
    (l.length : Int) - i < fuel → IsFirst (f · x) l i stop (listIndexLoop f l x stop i fuel)
  | 0, i, _, h => isFirst_empty _ l i stop (by omega)
  | fuel + 1, i, h0, hf => by
    unfold listIndexLoop
    by_cases h1 : i < stop
    · rw [iteT h1]
      by_cases h2 : i < l.length
      · rw [iteT h2]
        by_cases h3 : f (ix l i) x = true
        · simp only [h3, ite_true]; exact isFirst_here _ l i stop h0 h1 h2 h3
        · have h3' : f (ix l i) x = false := by simpa using h3
          simp only [h3', Bool.false_eq_true, ite_false]
          exact isFirst_step _ l i stop _ h3' (listIndexLoop_spec f l x stop fuel (i + 1) (by omega) (by omega))
      · rw [iteF h2]; exact isFirst_empty _ l i stop (by omega)
    · rw [iteF h1]; exact isFirst_empty _ l i stop (by omega)

namespace Deque

theorem scanLoop_spec (d : Deque α) (hL : d.Layout) (f : α → α → Bool) (v : α) (cf : Bool) (me : PyExc) :
    ∀ (k : Nat) (p b j : Int),
    b * 64 + j - d.left = p → 0 ≤ j → j < 64 → 0 ≤ p → p + k ≤ d.size →
    ∃ r, scanLoop (pureCmp f) v d.state cf me k p b j d = (.ok r, d) ∧
      IsFirst (f · v) d.items p (p + k) r := by
  have h' := hL
  rw [layout_iff] at h'
  intro k
  induction k with
  | zero =>
    intro p b j _ _ _ _ _
    exact ⟨none, rfl, fun j h1 h2 _ _ => by omega⟩
  | succ k ih =>
    intro p b j hp h0 h1 hp0 hk
    simp only [scanLoop]
    rw [read_ok d hL b j (by dq_omega) (by dq_omega) h0 h1 (by omega) (by dq_omega)]
    simp only [hp, pureCmp]
    obtain ⟨c1, c2, c3⟩ := step1_pos d b j p hp h0 h1
    by_cases hx : f (ix d.items p) v = true
    · cases cf <;> simp only [hx, Bool.not_false, Bool.not_true, Bool.and_true, Bool.true_and,
        Bool.false_and, ite_true, ite_false, ne_eq, not_true_eq_false, Bool.false_eq_true]
      all_goals exact ⟨some p, rfl, isFirst_here _ _ _ _ hp0 (by omega) (by dq_omega) hx⟩
    · have hx' : f (ix d.items p) v = false := by simpa using hx
      obtain ⟨r, hr, hf⟩ := ih (p + 1) _ _ c1 c2 c3 (by omega) (by omega)
      refine ⟨r, ?_, ?_⟩
      · cases cf <;> simp only [hx', Bool.and_false, Bool.false_eq_true, ite_false, ne_eq,
          not_true_eq_false] <;> exact hr
      · apply isFirst_step _ _ _ _ _ hx'
        rw [show p + 1 + (k : Int) = p + ((k + 1 : Nat) : Int) by omega] at hf
        exact hf

end Deque

def toRes (msg : String) : Option Int → Py Int
  | some i => .ok i
  | none => .error (.valueError msg)

/-- `index(x[, start[, stop]])` returns the first position of `x` in
`s[start:stop]` and agrees across `list` and `deque`: for every element type,
every `__eq__` that is a pure function `f` returning a truth value (the
assumption on the element type), every list `l` (`len(l) <= sys.maxsize`, a type
invariant), every `x` and every `start`/`stop` given as any Python ints (or
omitted), with `(a, b, 1) = slice(start, stop).indices(len(l))` (the documented
"interpreted as in the slice notation"): there is an `r` that is the first position
in `[a, b)` whose item equals `x` (or `none`), and `list.index` and `deque.index`
(any deque with items `l`, type invariant `WF`) return `r` or raise `ValueError`
with their own message, leaving the deque unchanged, including across the
deque's whole-block skip loop. -/
def IndexAgree : Prop :=
  ∀ (α : Type) [Inhabited α] (f : α → α → Bool) (l : List α) (x : α) (start stop : Option Int),
    (l.length : Int) ≤ ssizeMax →
    ∃ a b r, sliceIndices ⟨start, stop, none⟩ l.length = .ok (a, b, 1) ∧ IsFirst (f · x) l a b r ∧
      listIndex f l x start stop = toRes "list.index(x): x not in list" r ∧
      (∀ d : Deque α, d.WF → d.items = l →
        d.index (pureCmp f) x start stop = (toRes "deque.index(x): x not in deque" r, d))

/-- `clipLong` with the step-1 bounds, as `slice.indices` computes it. -/
def clip1 (v : Option Int) (dflt n : Int) : Int := RangeSlice.clipLong v dflt 0 n n

theorem sliceIndices_step1 (start stop : Option Int) (n : Int) (hn : 0 ≤ n) :
    sliceIndices ⟨start, stop, none⟩ n = .ok (clip1 start 0 n, clip1 stop n n, 1) := by
  unfold sliceIndices RangeSlice.getLongIndices
  rw [iteF (by omega)]
  rfl

theorem clip1_bounds (v : Option Int) (dflt n : Int) (hn : 0 ≤ n) (h0 : 0 ≤ dflt) (h1 : dflt ≤ n) :
    0 ≤ clip1 v dflt n ∧ clip1 v dflt n ≤ n := by
  unfold clip1 RangeSlice.clipLong
  cases v with
  | none => exact ⟨h0, h1⟩
  | some x => simp only; split <;> (try split) <;> omega

/-- The normalisation of a saturated `slice_index` start/stop in
`list_index_impl` (listobject.c:3287-3296): add `len` when negative, clip at 0. -/
def normIdx (v n : Int) : Int := if v < 0 then (if v + n < 0 then 0 else v + n) else v

/-- `array_array_index_impl`'s stop (arraymodule.c:3302-3304): no clip at 0. -/
def normIdxA (v n : Int) : Int := if v < 0 then v + n else v

theorem normIdx_nonneg (v n : Int) (hn : 0 ≤ n) : 0 ≤ normIdx v n := by
  unfold normIdx; split <;> (try split) <;> omega

theorem clip_start (v : Option Int) (n : Int) (hn : 0 ≤ n) (hn' : n ≤ ssizeMax) (j : Int) (hj : 0 ≤ j) (hjn : j < n) :
    (normIdx (sliceIndex (v.getD 0)) n ≤ j ↔ clip1 v 0 n ≤ j) := by
  unfold normIdx sliceIndex clip1 RangeSlice.clipLong RangeSlice.clampSsize
  unfold ssizeMax at hn'
  unfold ssizeMin ssizeMax
  cases v with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    split <;> split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem clip_stop (v : Option Int) (n : Int) (hn : 0 ≤ n) (hn' : n ≤ ssizeMax) (j : Int) (hj : 0 ≤ j) (hjn : j < n) :
    (j < normIdx (sliceIndex (v.getD ssizeMax)) n ↔ j < clip1 v n n) := by
  unfold normIdx sliceIndex clip1 RangeSlice.clipLong RangeSlice.clampSsize
  unfold ssizeMax at hn'
  unfold ssizeMin ssizeMax
  cases v with
  | none => simp only [Option.getD_none]; split <;> (try split) <;> (try split) <;> omega
  | some x =>
    simp only [Option.getD_some]
    split <;> split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem clip_stop_arr (v : Option Int) (n : Int) (hn : 0 ≤ n) (hn' : n ≤ ssizeMax) (j : Int) (hj : 0 ≤ j) (hjn : j < n) :
    (j < normIdxA (sliceIndex (v.getD ssizeMax)) n ↔ j < clip1 v n n) := by
  unfold normIdxA sliceIndex clip1 RangeSlice.clipLong RangeSlice.clampSsize
  unfold ssizeMax at hn'
  unfold ssizeMin ssizeMax
  cases v with
  | none => simp only [Option.getD_none]; split <;> (try split) <;> (try split) <;> omega
  | some x =>
    simp only [Option.getD_some]
    split <;> split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem isFirst_unique (p : α → Bool) (l : List α) (a b : Int) (r r' : Option Int)
    (h : IsFirst p l a b r) (h' : IsFirst p l a b r') : r = r' := by
  cases r with
  | none =>
    cases r' with
    | none => rfl
    | some k =>
      obtain ⟨h1, h2, h3, h4, h5, _⟩ := h'
      have := h k h1 h2 h3 h4
      rw [this] at h5; exact nomatch h5
  | some i =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    cases r' with
    | none =>
      have := h' i h1 h2 h3 h4
      rw [this] at h5; exact nomatch h5
    | some k =>
      obtain ⟨k1, k2, k3, k4, k5, k6⟩ := h'
      by_cases hik : i = k
      · rw [hik]
      · by_cases hlt : i < k
        · have := k6 i h1 hlt h3
          rw [this] at h5; exact nomatch h5
        · have := h6 k k1 (by omega) k3
          rw [this] at k5; exact nomatch k5

theorem listIndex_eq (f : α → α → Bool) (l : List α) (x : α) (start stop : Option Int) :
    listIndex f l x start stop = toRes "list.index(x): x not in list"
      (listIndexLoop f l x (normIdx (sliceIndex (stop.getD ssizeMax)) l.length)
        (normIdx (sliceIndex (start.getD 0)) l.length) (l.length + 1)) := by
  unfold listIndex toRes normIdx
  dsimp only
  split <;> rename_i heq <;> rw [heq]

theorem list_isFirst (f : α → α → Bool) (l : List α) (x : α) (start stop : Option Int)
    (hlen : (l.length : Int) ≤ ssizeMax) :
    ∃ r, listIndex f l x start stop = toRes "list.index(x): x not in list" r ∧
      IsFirst (f · x) l (clip1 start 0 l.length) (clip1 stop l.length l.length) r := by
  have hn : (0 : Int) ≤ l.length := by omega
  rw [listIndex_eq]
  refine ⟨_, rfl, ?_⟩
  have h0 := normIdx_nonneg (sliceIndex (start.getD 0)) l.length hn
  exact isFirst_congr _ _ _ _ _ _ _
    (fun j h0 h1 => and_congr (clip_start start _ hn hlen j h0 h1) (clip_stop stop _ hn hlen j h0 h1))
    (listIndexLoop_spec f l x _ (l.length + 1) _ h0 (by omega))

theorem deque_isFirst (d : Deque α) (h : d.WF) (f : α → α → Bool) (x : α) (start stop : Option Int)
    (hlen : (d.items.length : Int) ≤ ssizeMax) :
    ∃ r, d.index (pureCmp f) x start stop = (toRes "deque.index(x): x not in deque" r, d) ∧
      IsFirst (f · x) d.items (clip1 start 0 d.items.length) (clip1 stop d.items.length d.items.length) r := by
  have hn : (0 : Int) ≤ d.items.length := by omega
  have hL := h.1
  have h' := h.1
  rw [Deque.layout_iff] at h'
  unfold Deque.index Deque.indexC
  dsimp only
  generalize hS : sliceIndex (start.getD 0) = S
  generalize hT : sliceIndex (stop.getD ssizeMax) = T
  -- the clipped start/stop
  generalize hA : (if S < 0 then (if S + d.size < 0 then 0 else S + d.size) else S) = A0
  generalize hB : (if T < 0 then (if T + d.size < 0 then 0 else T + d.size) else T) = B0
  generalize hB1 : (if B0 > d.size then d.size else B0) = B
  generalize hA1 : (if A0 > B then B else A0) = A
  have hsz : 0 ≤ d.size := by rw [Deque.size_eq]; omega
  have hA' : A0 = normIdx S d.items.length := by rw [← hA]; unfold normIdx; rw [Deque.size_eq]
  have hB' : B0 = normIdx T d.items.length := by rw [← hB]; unfold normIdx; rw [Deque.size_eq]
  have hA0 : 0 ≤ A0 := by rw [← hA]; split <;> (try split) <;> omega
  have hB0 : 0 ≤ B0 := by rw [← hB]; split <;> (try split) <;> omega
  have hBb : 0 ≤ B ∧ B ≤ d.size := by rw [← hB1]; split <;> omega
  have hAb : 0 ≤ A ∧ A ≤ B := by rw [← hA1]; split <;> omega
  generalize hnb : (if A - 64 > 0 then (A - 64 + 63) / 64 else 0) = nb
  have hnb1 : 0 ≤ nb ∧ nb * 64 ≤ A ∧ (A > 64 → A - 64 ≤ nb * 64) := by
    rw [← hnb]; split <;> omega
  obtain ⟨c1, c2, c3⟩ := Deque.foldl_step1 d (A - nb * 64).toNat nb d.left (nb * 64) (by omega) h'.1 h'.2.1
  generalize hbj : (List.range (A - nb * 64).toNat).foldl (fun (bj : Int × Int) _ => Deque.step1 bj.1 bj.2)
    (nb, d.left) = bj at c1 c2 c3
  obtain ⟨bb, jj⟩ := bj
  simp only at c1 c2 c3
  have hpos : bb * 64 + jj - d.left = A := by rw [c1]; omega
  have hub : bb ≤ d.rbNum + 1 ∧ nb - 1 ≤ d.rbNum := by
    unfold Deque.rbNum; rw [Deque.size_eq] at hBb ⊢; omega
  simp only
  rw [iteF (by omega)]
  obtain ⟨r, hr, hf⟩ := Deque.scanLoop_spec d hL f x false Deque.mutatedErr (B - A).toNat A bb jj hpos c2 c3 hAb.1 (by omega)
  rw [hr]
  refine ⟨r, by cases r <;> rfl, ?_⟩
  refine isFirst_congr _ _ _ _ _ _ _ (fun j h0 h1 => ?_) hf
  have c1 := clip_start start _ hn hlen j h0 h1
  have c2 := clip_stop stop _ hn hlen j h0 h1
  rw [hS, ← hA'] at c1
  rw [hT, ← hB'] at c2
  rw [← c1, ← c2, ← hA1, ← hB1]
  rw [Deque.size_eq] at *
  constructor
  · intro ⟨k1, k2⟩; split at k1 <;> split at k2 <;> omega
  · intro ⟨k1, k2⟩; constructor <;> split <;> (try split) <;> omega

theorem indexAgree_proven : IndexAgree := by
  intro α _ f l x start stop hlen
  obtain ⟨r, hr, hf⟩ := list_isFirst f l x start stop hlen
  refine ⟨_, _, r, sliceIndices_step1 start stop _ (by omega), hf, hr, fun d hd hl => ?_⟩
  subst hl
  obtain ⟨r', hr', hf'⟩ := deque_isFirst d hd f x start stop hlen
  rw [hr', isFirst_unique _ _ _ _ _ _ hf' hf]

end PyLean.Sequences
