import PyLean.Sequences.DequeOps
import PyLean.Sequences.ArrayModel

/-!
`index(x, start, stop)` agrees across `list`, `array.array` and
`collections.deque`, and returns the first match in `s[start:stop]`.
-/

namespace PyLean.Sequences

open PyLean
open PyLean.RangeSlice (Slice sliceIndices)

/-- `r` is the first position `i` in `[a, b)` (and in the list) with
`l[i] == x`, or `none` when there is no such position. -/
def IsFirst (l : List Int) (x a b : Int) : Option Int → Prop
  | some i => a ≤ i ∧ i < b ∧ 0 ≤ i ∧ i < l.length ∧ ix l i = x ∧
      ∀ j, a ≤ j → j < i → 0 ≤ j → ix l j ≠ x
  | none => ∀ j, a ≤ j → j < b → 0 ≤ j → j < l.length → ix l j ≠ x

theorem isFirst_congr (l : List Int) (x a b a' b' : Int) (r : Option Int)
    (hab : ∀ j : Int, 0 ≤ j → j < l.length → (a ≤ j ∧ j < b ↔ a' ≤ j ∧ j < b'))
    (h : IsFirst l x a b r) : IsFirst l x a' b' r := by
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
theorem isFirst_step (l : List Int) (x i b : Int) (r : Option Int) (hne : ix l i ≠ x)
    (h : IsFirst l x (i + 1) b r) : IsFirst l x i b r := by
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

theorem isFirst_here (l : List Int) (x i b : Int) (h0 : 0 ≤ i) (hb : i < b) (hl : i < l.length)
    (hx : ix l i = x) : IsFirst l x i b (some i) :=
  ⟨Int.le_refl _, hb, h0, hl, hx, fun j h1 h2 _ => by omega⟩

theorem isFirst_empty (l : List Int) (x i b : Int) (h : ¬ (i < b ∧ i < l.length)) :
    IsFirst l x i b none := by
  intro j h1 h2 _ h4; omega

theorem listIndexLoop_spec (l : List Int) (x stop : Int) : ∀ (fuel : Nat) (i : Int), 0 ≤ i →
    (l.length : Int) - i < fuel → IsFirst l x i stop (listIndexLoop l x stop i fuel)
  | 0, i, _, h => isFirst_empty l x i stop (by omega)
  | fuel + 1, i, h0, hf => by
    unfold listIndexLoop
    by_cases h1 : i < stop
    · rw [iteT h1]
      by_cases h2 : i < l.length
      · rw [iteT h2]
        by_cases h3 : ix l i = x
        · rw [iteT h3]; exact isFirst_here l x i stop h0 h1 h2 h3
        · rw [iteF h3]
          exact isFirst_step l x i stop _ h3 (listIndexLoop_spec l x stop fuel (i + 1) (by omega) (by omega))
      · rw [iteF h2]; exact isFirst_empty l x i stop (by omega)
    · rw [iteF h1]; exact isFirst_empty l x i stop (by omega)

theorem arrIndexLoop_spec (l : List Int) (x stop : Int) : ∀ (fuel : Nat) (i : Int), 0 ≤ i →
    (l.length : Int) - i < fuel → IsFirst l x i stop (arrIndexLoop l x stop i fuel)
  | 0, i, _, h => isFirst_empty l x i stop (by omega)
  | fuel + 1, i, h0, hf => by
    unfold arrIndexLoop
    by_cases h1 : i < stop ∧ i < l.length
    · rw [iteT h1]
      by_cases h3 : ix l i = x
      · rw [iteT h3]; exact isFirst_here l x i stop h0 h1.1 h1.2 h3
      · rw [iteF h3]
        exact isFirst_step l x i stop _ h3 (arrIndexLoop_spec l x stop fuel (i + 1) (by omega) (by omega))
    · rw [iteF h1]; exact isFirst_empty l x i stop h1

namespace Deque

theorem step1_pos (d : Deque) (b j p : Int) (hp : b * 64 + j - d.left = p) (hj0 : 0 ≤ j) (hj : j < 64) :
    (step1 b j).1 * 64 + (step1 b j).2 - d.left = p + 1 ∧ 0 ≤ (step1 b j).2 ∧ (step1 b j).2 < 64 := by
  unfold step1
  split
  · simp only; omega
  · simp only; omega

theorem foldl_step1 (d : Deque) (k : Nat) : ∀ (b j p : Int), b * 64 + j - d.left = p → 0 ≤ j → j < 64 →
    let bj := (List.range k).foldl (fun (bj : Int × Int) _ => step1 bj.1 bj.2) (b, j)
    bj.1 * 64 + bj.2 - d.left = p + k ∧ 0 ≤ bj.2 ∧ bj.2 < 64 := by
  induction k with
  | zero => intro b j p hp h0 h1; simp only [List.range_zero, List.foldl_nil]; exact ⟨by omega, h0, h1⟩
  | succ k ih =>
    intro b j p hp h0 h1
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨a1, a2, a3⟩ := ih b j p hp h0 h1
    obtain ⟨c1, c2, c3⟩ := step1_pos d _ _ _ a1 a2 a3
    exact ⟨by rw [c1]; omega, c2, c3⟩

theorem findLoop_spec (d : Deque) (hL : d.Layout) (v : Int) : ∀ (k : Nat) (p b j : Int),
    b * 64 + j - d.left = p → 0 ≤ j → j < 64 → 0 ≤ p → p + k ≤ d.size →
    ∃ r, d.findLoop v k p b j = .ok r ∧ IsFirst d.items v p (p + k) r := by
  have h' := hL
  rw [layout_iff] at h'
  intro k
  induction k with
  | zero =>
    intro p b j _ _ _ _ _
    exact ⟨none, rfl, fun j h1 h2 _ _ => by omega⟩
  | succ k ih =>
    intro p b j hp h0 h1 hp0 hk
    simp only [findLoop, bind, Except.bind]
    rw [read_ok d hL b j (by dq_omega) (by dq_omega) h0 h1 (by omega) (by dq_omega)]
    simp only [hp]
    obtain ⟨c1, c2, c3⟩ := step1_pos d b j p hp h0 h1
    by_cases hx : ix d.items p = v
    · rw [iteT hx]
      exact ⟨some p, rfl, isFirst_here _ _ _ _ hp0 (by omega) (by dq_omega) hx⟩
    · rw [iteF hx]
      obtain ⟨r, hr, hf⟩ := ih (p + 1) _ _ c1 c2 c3 (by omega) (by omega)
      refine ⟨r, hr, ?_⟩
      apply isFirst_step _ _ _ _ _ hx
      rw [show p + 1 + (k : Int) = p + ((k + 1 : Nat) : Int) by omega] at hf
      exact hf

end Deque

/-- `index(x[, start[, stop]])` returns the first position of `x` in
`s[start:stop]` and agrees across the three types: for every list of ints
`l` (`len(l) <= sys.maxsize`, a type invariant), every `x` and every
`start`/`stop` given as any Python ints (or omitted), with `(a, b, 1) =
slice(start, stop).indices(len(l))` (the documented "interpreted as in the
slice notation"): there is an `r` that is the first position in `[a, b)`
holding `x` (or `none`), and `list.index`, `array.index` (any typecode) and
`deque.index` (any deque with items `l`, type invariant `WF`) all return `r`
or raise `ValueError` with their own message — including across the deque's
whole-block skip loop. -/
def IndexAgree : Prop :=
  ∀ (l : List Int) (x : Int) (start stop : Option Int), (l.length : Int) ≤ ssizeMax →
    ∃ a b r, sliceIndices ⟨start, stop, none⟩ l.length = .ok (a, b, 1) ∧ IsFirst l x a b r ∧
      listIndex l x start stop =
        (match r with | some i => .ok i | none => .error (.valueError "list.index(x): x not in list")) ∧
      (∀ tc, arrIndex ⟨tc, l⟩ x start stop =
        (match r with | some i => .ok i | none => .error (.valueError "array.index(x): x not in array"))) ∧
      (∀ d : Deque, d.WF → d.items = l → d.index x start stop =
        (match r with | some i => .ok i | none => .error (.valueError "deque.index(x): x not in deque")))

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

theorem isFirst_unique (l : List Int) (x a b : Int) (r r' : Option Int)
    (h : IsFirst l x a b r) (h' : IsFirst l x a b r') : r = r' := by
  cases r with
  | none =>
    cases r' with
    | none => rfl
    | some k => obtain ⟨h1, h2, h3, h4, h5, _⟩ := h'; exact absurd h5 (h k h1 h2 h3 h4)
  | some i =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    cases r' with
    | none => exact absurd h5 (h' i h1 h2 h3 h4)
    | some k =>
      obtain ⟨k1, k2, k3, k4, k5, k6⟩ := h'
      by_cases hik : i = k
      · rw [hik]
      · by_cases hlt : i < k
        · exact absurd h5 (k6 i h1 hlt h3)
        · exact absurd k5 (h6 k k1 (by omega) k3)

def toRes (msg : String) : Option Int → Py Int
  | some i => .ok i
  | none => .error (.valueError msg)

theorem listIndex_eq (l : List Int) (x : Int) (start stop : Option Int) :
    listIndex l x start stop = toRes "list.index(x): x not in list"
      (listIndexLoop l x (normIdx (sliceIndex (stop.getD ssizeMax)) l.length)
        (normIdx (sliceIndex (start.getD 0)) l.length) (l.length + 1)) := by
  unfold listIndex toRes normIdx
  dsimp only
  split <;> rename_i heq <;> rw [heq]

theorem arrIndex_eq (a : Arr) (x : Int) (start stop : Option Int) :
    arrIndex a x start stop = toRes "array.index(x): x not in array"
      (arrIndexLoop a.items x (normIdxA (sliceIndex (stop.getD ssizeMax)) a.items.length)
        (normIdx (sliceIndex (start.getD 0)) a.items.length) (a.items.length + 1)) := by
  unfold arrIndex toRes normIdx normIdxA
  dsimp only
  split <;> rename_i heq <;> rw [heq]

theorem list_isFirst (l : List Int) (x : Int) (start stop : Option Int) (hlen : (l.length : Int) ≤ ssizeMax) :
    ∃ r, listIndex l x start stop = toRes "list.index(x): x not in list" r ∧
      IsFirst l x (clip1 start 0 l.length) (clip1 stop l.length l.length) r := by
  have hn : (0 : Int) ≤ l.length := by omega
  rw [listIndex_eq]
  refine ⟨_, rfl, ?_⟩
  have h0 := normIdx_nonneg (sliceIndex (start.getD 0)) l.length hn
  exact isFirst_congr _ _ _ _ _ _ _
    (fun j h0 h1 => and_congr (clip_start start _ hn hlen j h0 h1) (clip_stop stop _ hn hlen j h0 h1))
    (listIndexLoop_spec l x _ (l.length + 1) _ h0 (by omega))

theorem arr_isFirst (a : Arr) (x : Int) (start stop : Option Int) (hlen : (a.items.length : Int) ≤ ssizeMax) :
    ∃ r, arrIndex a x start stop = toRes "array.index(x): x not in array" r ∧
      IsFirst a.items x (clip1 start 0 a.items.length) (clip1 stop a.items.length a.items.length) r := by
  have hn : (0 : Int) ≤ a.items.length := by omega
  rw [arrIndex_eq]
  refine ⟨_, rfl, ?_⟩
  have h0 := normIdx_nonneg (sliceIndex (start.getD 0)) a.items.length hn
  exact isFirst_congr _ _ _ _ _ _ _
    (fun j h0 h1 => and_congr (clip_start start _ hn hlen j h0 h1) (clip_stop_arr stop _ hn hlen j h0 h1))
    (arrIndexLoop_spec a.items x _ (a.items.length + 1) _ h0 (by omega))

theorem deque_isFirst (d : Deque) (h : d.WF) (x : Int) (start stop : Option Int)
    (hlen : (d.items.length : Int) ≤ ssizeMax) :
    ∃ r, d.index x start stop = toRes "deque.index(x): x not in deque" r ∧
      IsFirst d.items x (clip1 start 0 d.items.length) (clip1 stop d.items.length d.items.length) r := by
  have hn : (0 : Int) ≤ d.items.length := by omega
  have hL := h.1
  have h' := h.1
  rw [Deque.layout_iff] at h'
  unfold Deque.index Deque.indexC
  simp only [bind, Except.bind, pure, Except.pure]
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
  have hpos : bj.1 * 64 + bj.2 - d.left = A := by rw [c1]; omega
  have hub : bj.1 ≤ d.rbNum + 1 ∧ nb - 1 ≤ d.rbNum := by
    unfold Deque.rbNum; rw [Deque.size_eq] at hBb ⊢; omega
  rw [iteF (by omega)]
  obtain ⟨r, hr, hf⟩ := Deque.findLoop_spec d hL x (B - A).toNat A bj.1 bj.2 hpos c2 c3 hAb.1 (by omega)
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
  intro l x start stop hlen
  obtain ⟨r, hr, hf⟩ := list_isFirst l x start stop hlen
  refine ⟨_, _, r, sliceIndices_step1 start stop _ (by omega), hf, ?_, fun tc => ?_, fun d hd hl => ?_⟩
  · rw [hr]; cases r <;> rfl
  · obtain ⟨r', hr', hf'⟩ := arr_isFirst ⟨tc, l⟩ x start stop hlen
    rw [hr', isFirst_unique _ _ _ _ _ _ hf' hf]; cases r <;> rfl
  · subst hl
    obtain ⟨r', hr', hf'⟩ := deque_isFirst d hd x start stop hlen
    rw [hr', isFirst_unique _ _ _ _ _ _ hf' hf]; cases r <;> rfl

end PyLean.Sequences
