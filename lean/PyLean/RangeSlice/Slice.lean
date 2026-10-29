import PyLean.RangeSlice.Index

/-!
Slices: `slice.indices` (PyLong, `_PySlice_GetLongIndices`), list slicing
(`PySlice_Unpack` + `PySlice_AdjustIndices`, `Py_ssize_t`, saturating) and
range slicing (`compute_slice`).
-/

namespace PyLean.RangeSlice

open PyLean

/-! ### `_PySlice_GetLongIndices` in closed form -/

def lowerOf (c : Int) : Int := if c < 0 then -1 else 0
def upperOf (c n : Int) : Int := if c < 0 then n + -1 else n
def startDflt (c n : Int) : Int := if c < 0 then upperOf c n else lowerOf c
def stopDflt (c n : Int) : Int := if c < 0 then lowerOf c else upperOf c n

theorem getLongIndices_eq (s : Slice) (n : Int) (h0 : s.step ≠ some 0) :
    getLongIndices s n =
      .ok (clipLong s.start (startDflt (s.step.getD 1) n) (lowerOf (s.step.getD 1)) (upperOf (s.step.getD 1) n) n,
           clipLong s.stop (stopDflt (s.step.getD 1) n) (lowerOf (s.step.getD 1)) (upperOf (s.step.getD 1) n) n,
           s.step.getD 1) := by
  obtain ⟨st, sp, ss⟩ := s
  cases ss with
  | none => simp [getLongIndices, startDflt, stopDflt, lowerOf, upperOf, bind, Except.bind, pure, Except.pure]
  | some v =>
    have hv : v ≠ 0 := fun h => h0 (by simp [h])
    by_cases hn : v < 0 <;>
      simp [getLongIndices, startDflt, stopDflt, lowerOf, upperOf, bind, Except.bind, pure,
        Except.pure, hv, hn]

theorem step_getD_ne {s : Slice} (h0 : s.step ≠ some 0) : s.step.getD 1 ≠ 0 := by
  cases h : s.step with
  | none => decide
  | some v => simp only [Option.getD_some]; intro hv; exact h0 (by rw [h, hv])

/-- Clipped values stay within `[lower, upper]`. -/
theorem clipLong_bounds (v : Option Int) (d lower upper n : Int) (hl : lower ≤ 0)
    (hu : n - 1 ≤ upper) (hd1 : lower ≤ d) (hd2 : d ≤ upper) :
    lower ≤ clipLong v d lower upper n ∧ clipLong v d lower upper n ≤ upper := by
  unfold clipLong
  cases v with
  | none => exact ⟨hd1, hd2⟩
  | some x => simp only; split <;> (try split) <;> omega

/-- Bounds of the clipped start and stop: `[0, n]` for a positive step,
`[-1, n-1]` for a negative one. -/
def Bnds (a b c n : Int) : Prop :=
  (0 < c → 0 ≤ a ∧ a ≤ n ∧ 0 ≤ b ∧ b ≤ n) ∧ (c < 0 → -1 ≤ a ∧ a ≤ n - 1 ∧ -1 ≤ b ∧ b ≤ n - 1)

theorem clip_bnds (sa sb : Option Int) (c n : Int) (hn : 0 ≤ n) :
    Bnds (clipLong sa (startDflt c n) (lowerOf c) (upperOf c n) n)
      (clipLong sb (stopDflt c n) (lowerOf c) (upperOf c n) n) c n := by
  constructor
  · intro hc
    have hneg : ¬ c < 0 := by omega
    have h1 := clipLong_bounds sa (startDflt c n) (lowerOf c) (upperOf c n) n
      (by simp [lowerOf, hneg]) (by simp [upperOf, hneg]; omega)
      (by simp [startDflt, lowerOf, hneg]) (by simp [startDflt, lowerOf, upperOf, hneg]; omega)
    have h2 := clipLong_bounds sb (stopDflt c n) (lowerOf c) (upperOf c n) n
      (by simp [lowerOf, hneg]) (by simp [upperOf, hneg]; omega)
      (by simp [stopDflt, lowerOf, upperOf, hneg]; omega) (by simp [stopDflt, upperOf, hneg])
    generalize clipLong sa (startDflt c n) (lowerOf c) (upperOf c n) n = a at h1 ⊢
    generalize clipLong sb (stopDflt c n) (lowerOf c) (upperOf c n) n = b at h2 ⊢
    simp only [lowerOf, upperOf, hneg, ite_false] at h1 h2
    omega
  · intro hc
    have h1 := clipLong_bounds sa (startDflt c n) (lowerOf c) (upperOf c n) n
      (by simp [lowerOf, hc]) (by simp [upperOf, hc]; omega)
      (by simp [startDflt, lowerOf, upperOf, hc]; omega) (by simp [startDflt, upperOf, hc])
    have h2 := clipLong_bounds sb (stopDflt c n) (lowerOf c) (upperOf c n) n
      (by simp [lowerOf, hc]) (by simp [upperOf, hc]; omega)
      (by simp [stopDflt, lowerOf, hc]) (by simp [stopDflt, lowerOf, upperOf, hc]; omega)
    generalize clipLong sa (startDflt c n) (lowerOf c) (upperOf c n) n = a at h1 ⊢
    generalize clipLong sb (stopDflt c n) (lowerOf c) (upperOf c n) n = b at h2 ⊢
    simp only [lowerOf, upperOf, hc, ite_true] at h1 h2
    omega

/-- Every index `a + k*c` of `range(*s.indices(n))` lies in `[0, n)`. -/
theorem indices_in_bounds (a b c n L : Int) (hL : IsLen a b c L)
    (hb : Bnds a b c n)
    (k : Int) (hk : 0 ≤ k) (hkL : k < L) : 0 ≤ a + k * c ∧ a + k * c < n := by
  have hin := (hL.2 k hk).1 hkL
  unfold InSeq at hin
  by_cases hc : 0 < c
  · rw [ite_t hc] at hin
    have := Int.mul_nonneg hk (Int.le_of_lt hc)
    have := hb.1 hc
    omega
  · rw [ite_f hc] at hin
    by_cases hc0 : c = 0
    · subst hc0; simp at hin; have := hL.2 L hL.1; unfold InSeq at this; simp at this; omega
    · have := Int.mul_nonpos_of_nonneg_of_nonpos hk (show c ≤ 0 by omega)
      have := hb.2 (by omega)
      omega

/-! ### Properties of `slice.indices` -/

/-- `slice.indices(n)` returns indices that are all valid for a sequence of
length `n`: for every slice with int/None parts and every `n >= 0`, the step
is the slice's step (1 for `None`), and each element of
`range(*s.indices(n))` is in `[0, n)`. Hypotheses: `n >= 0` and a non-zero
step are the documented preconditions (the other cases raise `ValueError`,
see `SliceErrors`). -/
def IndicesInBounds : Prop :=
  ∀ (s : Slice) (n : Int), 0 ≤ n → s.step ≠ some 0 →
    ∃ a b c, sliceIndices s n = .ok (a, b, c) ∧ c = s.step.getD 1 ∧
      ∀ L, IsLen a b c L → ∀ k, 0 ≤ k → k < L → 0 ≤ a + k * c ∧ a + k * c < n

theorem indicesInBounds_proven : IndicesInBounds := by
  intro s n hn h0
  refine ⟨_, _, _, ?_, rfl, fun L hL k hk hkL =>
    indices_in_bounds _ _ _ n L hL (clip_bnds s.start s.stop _ n hn) k hk hkL⟩
  unfold sliceIndices
  rw [ite_f (show ¬ n < 0 by omega), getLongIndices_eq s n h0]

/-- The documented errors: `slice.indices(n)` raises `ValueError` for a
negative length and for a zero step; list slicing and range slicing raise the
same `ValueError` for a zero step. -/
def SliceErrors : Prop :=
  ∀ (s : Slice) (n : Int) (r : Range),
    (n < 0 → sliceIndices s n = .error (.valueError "length should not be negative")) ∧
    (s.step = some 0 → 0 ≤ n →
      sliceIndices s n = .error (.valueError "slice step cannot be zero") ∧
      listSlicePositions n s = .error (.valueError "slice step cannot be zero") ∧
      computeSlice r s = .error (.valueError "slice step cannot be zero"))

theorem sliceErrors_proven : SliceErrors := by
  intro s n r
  refine ⟨fun h => by unfold sliceIndices; rw [ite_t h], fun h hn => ?_⟩
  obtain ⟨st, sp, ss⟩ := s
  simp only at h
  subst h
  refine ⟨?_, ?_, ?_⟩
  · unfold sliceIndices; rw [ite_f (show ¬ n < 0 by omega)]; rfl
  · rfl
  · rfl

/-! ### List slicing (`PySlice_Unpack` + `PySlice_AdjustIndices`) -/

/-- The step `PySlice_Unpack` produces: saturated to `Py_ssize_t`, then
`-PY_SSIZE_T_MAX` for `PY_SSIZE_T_MIN`. -/
def clampStep (c : Int) : Int :=
  if clampSsize c < -ssizeMax then -ssizeMax else clampSsize c

theorem sliceUnpack_eq (s : Slice) (h0 : s.step ≠ some 0) :
    sliceUnpack s =
      .ok ((match s.start with
            | none => if clampStep (s.step.getD 1) < 0 then ssizeMax else 0
            | some v => clampSsize v),
           (match s.stop with
            | none => if clampStep (s.step.getD 1) < 0 then ssizeMin else ssizeMax
            | some v => clampSsize v),
           clampStep (s.step.getD 1)) := by
  obtain ⟨st, sp, ss⟩ := s
  cases ss with
  | none => rfl
  | some v =>
    have hv : v ≠ 0 := fun h => h0 (by simp [h])
    have hc : clampSsize v ≠ 0 := by unfold clampSsize ssizeMin ssizeMax; split <;> (try split) <;> omega
    simp [sliceUnpack, clampStep, bind, Except.bind, pure, Except.pure, hc]
    exact ⟨rfl, rfl⟩

theorem clampStep_sign (c : Int) (h : c ≠ 0) :
    (clampStep c < 0 ↔ c < 0) ∧ clampStep c ≠ 0 ∧ -ssizeMax ≤ clampStep c ∧ clampStep c ≤ ssizeMax ∧
      (-ssizeMax ≤ c → c ≤ ssizeMax → clampStep c = c) := by
  unfold clampStep clampSsize ssizeMin ssizeMax
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try intros) <;> split <;> (try split) <;> (try split) <;> omega

/-- `PySlice_AdjustIndices` on the saturated start/stop computes the same
start/stop as `_PySlice_GetLongIndices`, for `0 <= n <= PY_SSIZE_T_MAX`. -/
theorem adjust_start (v : Option Int) (c c' n : Int) (hn : 0 ≤ n) (hn' : n ≤ ssizeMax)
    (hs : c' < 0 ↔ c < 0) :
    adjustOne (match v with
               | none => if c' < 0 then ssizeMax else 0
               | some v => clampSsize v) n c' =
      clipLong v (startDflt c n) (lowerOf c) (upperOf c n) n := by
  unfold ssizeMax at hn'
  cases v with
  | none =>
    unfold adjustOne startDflt lowerOf upperOf clipLong ssizeMax
    by_cases h : c < 0
    · simp only [hs.2 h, h, ite_true]; split <;> (try split) <;> omega
    · simp only [show ¬ c' < 0 from fun h' => h (hs.1 h'), h, ite_false]
      split <;> (try split) <;> omega
  | some x =>
    unfold adjustOne clipLong lowerOf upperOf clampSsize ssizeMin ssizeMax
    by_cases h : c < 0
    · simp only [hs.2 h, h, ite_true]
      split <;> (try split) <;> (try split) <;> (try split) <;> omega
    · simp only [show ¬ c' < 0 from fun h' => h (hs.1 h'), h, ite_false]
      split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem adjust_stop (v : Option Int) (c c' n : Int) (hn : 0 ≤ n) (hn' : n ≤ ssizeMax)
    (hs : c' < 0 ↔ c < 0) :
    adjustOne (match v with
               | none => if c' < 0 then ssizeMin else ssizeMax
               | some v => clampSsize v) n c' =
      clipLong v (stopDflt c n) (lowerOf c) (upperOf c n) n := by
  unfold ssizeMax at hn'
  cases v with
  | none =>
    unfold adjustOne stopDflt lowerOf upperOf clipLong ssizeMin ssizeMax
    by_cases h : c < 0
    · simp only [hs.2 h, h, ite_true]; split <;> (try split) <;> omega
    · simp only [show ¬ c' < 0 from fun h' => h (hs.1 h'), h, ite_false]
      split <;> (try split) <;> omega
  | some x =>
    unfold adjustOne clipLong lowerOf upperOf clampSsize ssizeMin ssizeMax
    by_cases h : c < 0
    · simp only [hs.2 h, h, ite_true]
      split <;> (try split) <;> (try split) <;> (try split) <;> omega
    · simp only [show ¬ c' < 0 from fun h' => h (hs.1 h'), h, ite_false]
      split <;> (try split) <;> (try split) <;> (try split) <;> omega

/-- The slice length `PySlice_AdjustIndices` returns is the slow-path formula
(C truncating division of a non-negative numerator is floor division). -/
theorem adjust_len (a b c : Int) (hc : c ≠ 0) :
    (if c < 0 then (if b < a then Int.tdiv (a - b - 1) (-c) + 1 else 0)
     else (if a < b then Int.tdiv (b - a - 1) c + 1 else 0)) = computeRangeLengthSlow a b c := by
  unfold computeRangeLengthSlow
  by_cases h : c < 0
  · rw [ite_t h, ite_f (show ¬ c > 0 by omega)]
    by_cases hab : b < a
    · rw [ite_t hab, ite_f (show ¬ b ≥ a by omega), Int.tdiv_eq_ediv_of_nonneg (by omega)]
    · rw [ite_f hab, ite_t (show b ≥ a by omega)]
  · rw [ite_f h, ite_t (show c > 0 by omega)]
    by_cases hab : a < b
    · rw [ite_t hab, ite_f (show ¬ a ≥ b by omega), Int.tdiv_eq_ediv_of_nonneg (by omega)]
    · rw [ite_f hab, ite_t (show a ≥ b by omega)]

theorem toU_lin (a i b : Int) : toU (toU a + i * toU b) = (a + i * b) % two64 := by
  unfold toU
  rw [Int.add_emod, Int.emod_emod, Int.mul_emod, Int.emod_emod, ← Int.mul_emod, ← Int.add_emod]

/-- If the saturated step differs from the real one, the slice selects at
most one index, and the length is the same for both steps. -/
theorem len_clamped (a b c c' n L : Int) (hn : n ≤ ssizeMax) (hc : c ≠ 0)
    (hs : c' < 0 ↔ c < 0) (hc' : c' ≠ 0) (hbig : c' = c ∨ (c' = ssizeMax ∨ c' = -ssizeMax))
    (hid : -ssizeMax ≤ c → c ≤ ssizeMax → c' = c)
    (hb : Bnds a b c n)
    (hL : IsLen a b c L) : IsLen a b c' L ∧ (c' ≠ c → L ≤ 1) := by
  rcases hbig with h | hbig
  · subst h; exact ⟨hL, fun h => absurd rfl h⟩
  have hL1 : c' ≠ c → L ≤ 1 := by
    intro hne
    apply Int.not_lt.mp
    intro hlt
    have h1 := indices_in_bounds a b c n L hL hb 1 (by decide) hlt
    have h0 := indices_in_bounds a b c n L hL hb 0 (by decide) (by omega)
    simp only [Int.one_mul] at h1
    have : ¬ (-ssizeMax ≤ c ∧ c ≤ ssizeMax) := fun h => hne (hid h.1 h.2)
    unfold ssizeMax at hbig hn this
    by_cases hcc : c < 0 <;> omega
  by_cases hne : c' = c
  · subst hne; exact ⟨hL, fun h => absurd rfl h⟩
  have hL1 := hL1 hne
  refine ⟨⟨hL.1, fun k hk => ?_⟩, fun _ => hL1⟩
  rw [(hL.2 k hk)]
  unfold InSeq
  by_cases hk0 : k = 0
  · subst hk0; simp only [Int.zero_mul, Int.add_zero]
    by_cases hcc : 0 < c
    · rw [ite_t hcc, ite_t (show 0 < c' by omega)]
    · rw [ite_f hcc, ite_f (show ¬ 0 < c' by omega)]
  · -- k >= 1: neither step reaches `b`.
    have hk1 : 1 ≤ k := by omega
    have hkL : ¬ k < L := by omega
    have hn' := (hL.2 k hk)
    have hnot : ¬ InSeq a b c k := fun h => hkL (hn'.2 h)
    unfold InSeq at hnot
    have e : k * c' = (k - 1) * c' + c' := by rw [Int.sub_mul, Int.one_mul]; omega
    unfold ssizeMax at hbig hn
    by_cases hcc : 0 < c
    · rw [ite_t hcc] at hnot
      rw [ite_t hcc, ite_t (show 0 < c' by omega)]
      have := Int.mul_nonneg (show 0 ≤ k - 1 by omega) (show 0 ≤ c' by omega)
      have := hb.1 hcc
      constructor
      · intro h; exact absurd h hnot
      · intro h; omega
    · rw [ite_f hcc] at hnot
      rw [ite_f hcc, ite_f (show ¬ 0 < c' by omega)]
      have := Int.mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ k - 1 by omega) (show c' ≤ 0 by omega)
      have := hb.2 (by omega)
      constructor
      · intro h; exact absurd h hnot
      · intro h; omega

/-- List slicing selects exactly the indices `slice.indices` describes: for
every list length `0 <= n <= sys.maxsize` (a type invariant of Python
sequences) and every slice with int/None parts and a non-zero step, the
positions `list[s]` reads (via the saturating `PySlice_Unpack`, then
`PySlice_AdjustIndices` and the `size_t` cursor of
`list_slice_step_lock_held`) are exactly `range(*s.indices(n))`. Together
with `IndicesInBounds` this also shows that list slicing never reads outside
`[0, n)`. -/
def ListSliceIndices : Prop :=
  ∀ (s : Slice) (n : Int), 0 ≤ n → n ≤ ssizeMax → s.step ≠ some 0 →
    ∃ a b c L, sliceIndices s n = .ok (a, b, c) ∧ IsLen a b c L ∧
      listSlicePositions n s = .ok ((List.range L.toNat).map (fun (k : Nat) => a + (k : Int) * c))

theorem listSliceIndices_proven : ListSliceIndices := by
  intro s n hn hn' h0
  have hc := step_getD_ne h0
  have ⟨hsgn, hc'0, hlo, hhi, hid⟩ := clampStep_sign _ hc
  generalize hcdef : s.step.getD 1 = c at hc hsgn hc'0 hlo hhi hid
  have hb := clip_bnds s.start s.stop c n hn
  generalize hc'def : clampStep c = c' at hsgn hc'0 hlo hhi hid
  generalize hadef : clipLong s.start (startDflt c n) (lowerOf c) (upperOf c n) n = a at hb
  generalize hbdef : clipLong s.stop (stopDflt c n) (lowerOf c) (upperOf c n) n = b at hb
  have hL := slow_isLen a b c hc
  refine ⟨a, b, c, computeRangeLengthSlow a b c, ?_, hL, ?_⟩
  · unfold sliceIndices
    rw [ite_f (show ¬ n < 0 by omega), getLongIndices_eq s n h0, hcdef, hadef, hbdef]
  generalize hLdef : computeRangeLengthSlow a b c = L at hL
  have hbig : c' = c ∨ (c' = ssizeMax ∨ c' = -ssizeMax) := by
    by_cases h1 : -ssizeMax ≤ c ∧ c ≤ ssizeMax
    · exact Or.inl (hid h1.1 h1.2)
    · right; rw [← hc'def]; unfold clampStep clampSsize ssizeMin ssizeMax at *
      split <;> (try split) <;> (try split) <;> omega
  obtain ⟨hL', hsmall⟩ := len_clamped a b c c' n L hn' hc hsgn hc'0 hbig hid hb hL
  have hlen' : computeRangeLengthSlow a b c' = L := isLen_unique (slow_isLen a b c' hc'0) hL'
  unfold listSlicePositions
  rw [sliceUnpack_eq s h0, hcdef, hc'def]
  simp only [bind, Except.bind, pure, Except.pure]
  unfold adjustIndices
  simp only
  rw [adjust_start s.start c c' n hn hn' hsgn, adjust_stop s.stop c c' n hn hn' hsgn, hadef, hbdef,
    adjust_len a b c' hc'0, hlen']
  by_cases hL0 : L ≤ 0
  · rw [ite_t hL0, show L.toNat = 0 by omega]; rfl
  rw [ite_f hL0]
  by_cases h1 : c' = 1
  · rw [ite_t h1]
    have hcc : c = 1 := by
      rcases hbig with h | h
      · rw [← h, h1]
      · unfold ssizeMax at h; omega
    subst hcc
    have hba : b - a = L := by
      rw [← hLdef]; unfold computeRangeLengthSlow
      rw [ite_t (show (1 : Int) > 0 by decide)]
      have := hb.1 (by decide)
      by_cases hab : a ≥ b
      · rw [ite_t hab]; rw [← hLdef] at hL0; unfold computeRangeLengthSlow at hL0
        rw [ite_t (show (1 : Int) > 0 by decide), ite_t hab] at hL0; omega
      · rw [ite_f hab, Int.ediv_one]; omega
    rw [hba]
    congr 1
    apply List.map_congr_left
    intro k _
    rw [Int.mul_one]
  · rw [ite_f h1]
    congr 1
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    have hkL : (k : Int) < L := by omega
    have hin := indices_in_bounds a b c n L hL hb k (by omega) hkL
    rw [toU_lin]
    have hsame : a + (k : Int) * c' = a + (k : Int) * c := by
      by_cases hcc : c' = c
      · rw [hcc]
      · have := hsmall hcc
        rw [show (k : Int) = 0 by omega]; simp
    rw [hsame]
    unfold two64
    unfold ssizeMax at hn'
    omega

/-! ### Range slicing -/

theorem mul_lt_mul_iff_pos {x y s : Int} (hs : 0 < s) : x * s < y * s ↔ x < y :=
  ⟨fun h => (Int.mul_lt_mul_right hs).mp h, fun h => Int.mul_lt_mul_of_pos_right h hs⟩

theorem mul_lt_mul_iff_neg {x y s : Int} (hs : s < 0) : x * s < y * s ↔ y < x :=
  ⟨fun h => by
    apply Int.not_le.mp; intro hle
    have := Int.mul_le_mul_of_nonpos_right hle (Int.le_of_lt hs)
    omega,
   fun h => Int.mul_lt_mul_right_of_neg hs |>.mpr h⟩

/-- `r[s]` selects `r[a + k*c]` for the indices `(a, b, c) = s.indices(len(r))`:
for every range (type invariant `r.WF`, mathematical length `L`) and every slice
with int/None parts and a non-zero step, `compute_slice` returns a valid range
whose k-th element is `r[a + k*c]` and whose length is the length of
`range(a, b, c)`. All arithmetic is on unbounded ints. -/
def RangeSliceSeq : Prop :=
  ∀ (r : Range) (L : Int) (s : Slice), r.WF → r.Len L → s.step ≠ some 0 →
    ∃ a b c r', sliceIndices s L = .ok (a, b, c) ∧ computeSlice r s = .ok r' ∧ r'.WF ∧
      (∀ k, r'.elem k = r.elem (a + k * c)) ∧
      ∀ L', IsLen a b c L' → r'.Len L'

theorem rangeSliceSeq_proven : RangeSliceSeq := by
  intro r L s hw hL h0
  have hlen := hw.length_eq hL
  have hc := step_getD_ne h0
  have hs := hw.1
  generalize hcdef : s.step.getD 1 = c at hc
  generalize hadef : clipLong s.start (startDflt c L) (lowerOf c) (upperOf c L) L = a
  generalize hbdef : clipLong s.stop (stopDflt c L) (lowerOf c) (upperOf c L) L = b
  have hgi : getLongIndices s r.length = .ok (a, b, c) := by
    rw [getLongIndices_eq s _ h0, hlen, hcdef, hadef, hbdef]
  refine ⟨a, b, c, makeRangeObject (computeItem r a) (computeItem r b) (r.step * c), ?_, ?_,
    makeRangeObject_wf _ _ _ (Int.mul_ne_zero hs hc), ?_, ?_⟩
  · unfold sliceIndices; rw [ite_f (show ¬ L < 0 by have := hL.1; omega), ← hlen, hgi]
  · unfold computeSlice; rw [hgi]; rfl
  · intro k
    simp only [makeRangeObject, Range.elem, computeItem_eq]
    rw [Int.add_mul, Int.mul_assoc, Int.mul_comm c r.step, Int.add_assoc]
  · intro L' hL'
    refine ⟨hL'.1, fun k hk => ?_⟩
    rw [hL'.2 k hk]
    simp only [InSeq, makeRangeObject, computeItem_eq, Range.elem]
    have e : r.start + a * r.step + k * (r.step * c) = r.start + (a + k * c) * r.step := by
      rw [Int.add_mul, Int.mul_assoc, Int.mul_comm c r.step, Int.add_assoc]
    rw [e]
    by_cases hp : 0 < r.step
    · by_cases hcp : 0 < c
      · rw [ite_t hcp, ite_t (Int.mul_pos hp hcp)]
        have := @mul_lt_mul_iff_pos (a + k * c) b r.step hp; omega
      · rw [ite_f hcp, ite_f (show ¬ 0 < r.step * c from fun h =>
          absurd h (by have := Int.mul_neg_of_pos_of_neg hp (show c < 0 by omega); omega))]
        have := @mul_lt_mul_iff_pos b (a + k * c) r.step hp; omega
    · have hn : r.step < 0 := by omega
      by_cases hcp : 0 < c
      · rw [ite_t hcp, ite_f (show ¬ 0 < r.step * c from fun h =>
          absurd h (by have := Int.mul_neg_of_neg_of_pos hn hcp; omega))]
        have := @mul_lt_mul_iff_neg b (a + k * c) r.step hn; omega
      · rw [ite_f hcp, ite_t (Int.mul_pos_of_neg_of_neg hn (show c < 0 by omega))]
        have := @mul_lt_mul_iff_neg (a + k * c) b r.step hn; omega

end PyLean.RangeSlice
