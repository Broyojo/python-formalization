import PyLean.RangeSlice.Slice

/-!
Iteration: `iter(r)` and `reversed(r)` choose between the C `long` iterator
(`range_iterator`) and the PyLong one (`longrange_iterator`). Both must yield
the mathematical elements, and pickling (`__reduce__`) at any point must
describe the remaining elements. `__setstate__` is where the two iterator
types disagree.
-/

namespace PyLean.RangeSlice

open PyLean

/-! ### Two's complement lemmas -/

theorem wrap_long {x : Int} (h : IsLong x) : wrap x = x := by
  unfold wrap two64; unfold IsLong longMin longMax at h; unfold longMax; split <;> omega

theorem wrap_isLong (x : Int) : IsLong (wrap x) := by
  unfold wrap IsLong longMin longMax two64; split <;> omega

theorem wrap_add_wrap (x y : Int) : wrap (wrap x + y) = wrap (x + y) := by
  unfold wrap two64 longMax; split <;> split <;> split <;> omega

theorem wrap_add_wrap' (x y : Int) : wrap (x + wrap y) = wrap (x + y) := by
  unfold wrap two64 longMax; split <;> split <;> split <;> omega

theorem wrap_emod (x : Int) : wrap (x % two64) = wrap x := by
  unfold wrap two64 longMax; split <;> split <;> omega

theorem wrap_add_emod (x y : Int) : wrap (x % two64 + y % two64) = wrap (x + y) := by
  unfold wrap two64 longMax; split <;> split <;> omega

/-! ### Running the iterators -/

theorem range_succ_map' {α : Type} (j : Nat) (g : Nat → α) :
    (List.range (j + 1)).map g = g 0 :: (List.range j).map (fun k => g (k + 1)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]; rfl

theorem iterTake_long (n : Nat) (a st m : Int) (hm : 0 ≤ m) :
    iterTake n (.long a st m) =
      ((List.range (min n m.toNat)).map (fun (k : Nat) => a + (k : Int) * st),
       .long (a + ((min n m.toNat : Nat) : Int) * st) st (m - ((min n m.toNat : Nat) : Int))) := by
  induction n generalizing a m with
  | zero => simp [iterTake]
  | succ n ih =>
    by_cases h0 : m = 0
    · subst h0; simp [iterTake, iterNext]
    · have hm1 : 0 ≤ m - 1 := by omega
      have hmin : min (n + 1) m.toNat = min n (m - 1).toNat + 1 := by omega
      simp only [iterTake, iterNext, show m > 0 by omega, ite_true]
      rw [ih (a + st) (m - 1) hm1, hmin, range_succ_map']
      simp only [Prod.mk.injEq, RIter.long.injEq, List.cons.injEq, true_and]
      refine ⟨⟨by simp, ?_⟩, ?_, ?_⟩
      · apply List.map_congr_left; intro k _; push_cast; rw [Int.add_mul, Int.one_mul]; omega
      · push_cast; rw [Int.add_mul, Int.one_mul]; omega
      · push_cast; omega

theorem iterTake_fast (n : Nat) (a st m : Int) (ha : IsLong a) (hm : 0 ≤ m) :
    iterTake n (.fast a st m) =
      ((List.range (min n m.toNat)).map (fun (k : Nat) => wrap (a + (k : Int) * st)),
       .fast (wrap (a + ((min n m.toNat : Nat) : Int) * st)) st (m - ((min n m.toNat : Nat) : Int))) := by
  induction n generalizing a m with
  | zero => simp [iterTake, wrap_long ha]
  | succ n ih =>
    by_cases h0 : m = 0
    · subst h0; simp [iterTake, iterNext, wrap_long ha]
    · have hm1 : 0 ≤ m - 1 := by omega
      have hmin : min (n + 1) m.toNat = min n (m - 1).toNat + 1 := by omega
      simp only [iterTake, iterNext, show m > 0 by omega, ite_true]
      rw [ih (wrap (a + st)) (m - 1) (wrap_isLong _) hm1, hmin, range_succ_map']
      simp only [Prod.mk.injEq, RIter.fast.injEq, List.cons.injEq, true_and, wrap_add_wrap]
      refine ⟨⟨by simp [wrap_long ha], ?_⟩, ?_, ?_⟩
      · apply List.map_congr_left; intro k _; push_cast; rw [Int.add_mul, Int.one_mul]; congr 1; omega
      · push_cast; rw [Int.add_mul, Int.one_mul]; congr 1; omega
      · push_cast; omega

/-! ### Facts about the elements -/

/-- Elements `0 <= k < L` lie between `start` (inclusive) and `stop`
(exclusive) in the direction of the step. -/
theorem elem_between {r : Range} {L k : Int} (hL : r.Len L) (hk : 0 ≤ k) (hkL : k < L) :
    (0 < r.step → r.start ≤ r.elem k ∧ r.elem k < r.stop) ∧
    (¬ 0 < r.step → r.elem k ≤ r.start ∧ r.stop < r.elem k) := by
  have hin := (hL.2 k hk).1 hkL
  unfold InSeq at hin
  unfold Range.elem
  constructor
  · intro hp; rw [ite_t hp] at hin
    have := Int.mul_nonneg hk (Int.le_of_lt hp); omega
  · intro hp; rw [ite_f hp] at hin
    have := Int.mul_nonpos_of_nonneg_of_nonpos hk (show r.step ≤ 0 by omega); omega

theorem elem_long {r : Range} {L k : Int} (hL : r.Len L) (h1 : IsLong r.start) (h2 : IsLong r.stop)
    (hk : 0 ≤ k) (hkL : k < L) : IsLong (r.elem k) := by
  have := elem_between hL hk hkL
  unfold IsLong at *
  by_cases hp : 0 < r.step
  · have := this.1 hp; omega
  · have := this.2 hp; omega

/-- The fast path's length is the stored length. -/
theorem fast_len {r : Range} {L : Int} (hw : r.WF) (hL : r.Len L) (h1 : IsLong r.start)
    (h2 : IsLong r.stop) (h3 : IsLong r.step) : getLenOfRange r.start r.stop r.step = L := by
  rw [getLenOfRange_eq _ _ _ h1 h2 h3 hw.1, ← computeRangeLength_eq_slow _ _ _ hw.1, ← hw.2,
    hw.length_eq hL]

/-- `range(a + j*st, a + m*st, st)` has `m - j` elements, the k-th being
`a + (j+k)*st`. -/
theorem arith_len (a st j m : Int) (hst : st ≠ 0) (hj : j ≤ m) :
    IsLen (a + j * st) (a + m * st) st (m - j) := by
  refine ⟨by omega, fun k _ => ?_⟩
  unfold InSeq
  have e : a + j * st + k * st = a + (j + k) * st := by rw [Int.add_mul]; omega
  rw [e]
  by_cases hp : 0 < st
  · rw [ite_t hp]; have := @mul_lt_mul_iff_pos (j + k) m st hp; omega
  · rw [ite_f hp]; have := @mul_lt_mul_iff_neg m (j + k) st (by omega); omega

/-! ### Properties -/

/-- `iter(r)` yields exactly the elements of `r` in order: for every range
(type invariant `r.WF`, mathematical length `L`) and every `n`, the first `n`
values produced are `r[0], r[1], ...` and the iterator stops after `L`
values, whichever of the C `long` or PyLong iterators `range_iter` picks. -/
def IterForward : Prop :=
  ∀ (r : Range) (L : Int) (n : Nat), r.WF → r.Len L →
    (iterTake n (rangeIter r)).1 = (List.range (min n L.toNat)).map (fun (k : Nat) => r.elem k)

theorem iterForward_proven : IterForward := by
  intro r L n hw hL
  have hlen := hw.length_eq hL
  have hL0 := hL.1
  have hslow : (iterTake n (RIter.long r.start r.step r.length)).1 =
      (List.range (min n L.toNat)).map (fun (k : Nat) => r.elem k) := by
    rw [iterTake_long n _ _ _ (by omega), hlen]; rfl
  unfold rangeIter
  cases h1 : asLong r.start <;> cases h2 : asLong r.stop <;> cases h3 : asLong r.step <;>
    simp only [hslow]
  rename_i lstart lstop lstep
  unfold asLong at h1 h2 h3
  split at h1 <;> split at h2 <;> split at h3 <;> simp only [Option.some.injEq, reduceCtorEq] at h1 h2 h3
  subst h1 h2 h3
  rename_i hs1 hs2 hs3
  rw [fast_len hw hL hs1 hs2 hs3]
  by_cases hbig : L > longMax
  · rw [ite_t hbig]; exact hslow
  rw [ite_f hbig]
  by_cases hchk : L ≠ 0 ∧ (if r.step > 0 then r.stop > longMax - (r.step - 1)
                           else r.stop < longMin + (-1 - r.step))
  · rw [ite_t hchk]; exact hslow
  rw [ite_f hchk, iterTake_fast n _ _ _ hs1 hL0]
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  exact wrap_long (elem_long hL hs1 hs2 (by omega) (by omega))

/-- The reverse fast path's start: `new_stop + ulen * lstep` in unsigned
long, converted back to `long`, is `start + (len - 1)*step` modulo `2^64`. -/
theorem rev_newStart (lstart lstep L : Int) :
    wrap (uadd (toU (wrap (lstart - lstep))) (umul L (toU lstep))) =
      wrap (lstart + (L - 1) * lstep) := by
  unfold uadd umul toU
  rw [wrap_emod, Int.mul_emod, Int.emod_emod, ← Int.mul_emod, wrap_add_emod, wrap_add_wrap,
    Int.sub_mul, Int.one_mul]
  congr 1; omega

/-- `reversed(r)` yields exactly the elements of `r` in reverse order, for
every range and every `n`, whichever iterator `range_reverse` picks (the C
`long` one computes its start in unsigned arithmetic). -/
def IterReversed : Prop :=
  ∀ (r : Range) (L : Int) (n : Nat), r.WF → r.Len L →
    (iterTake n (rangeReverse r)).1 = (List.range (min n L.toNat)).map (fun (k : Nat) => r.elem (L - 1 - k))

theorem iterReversed_proven : IterReversed := by
  intro r L n hw hL
  have hlen := hw.length_eq hL
  have hL0 := hL.1
  have hslow : (iterTake n (RIter.long (r.start + (r.length - 1) * r.step) (-r.step) r.length)).1 =
      (List.range (min n L.toNat)).map (fun (k : Nat) => r.elem (L - 1 - k)) := by
    rw [iterTake_long n _ _ _ (by omega), hlen]
    apply List.map_congr_left
    intro k _
    unfold Range.elem
    rw [Int.mul_neg, Int.sub_mul, Int.sub_mul, Int.sub_mul]
    omega
  unfold rangeReverse
  cases h1 : asLong r.start <;> cases h2 : asLong r.stop <;> cases h3 : asLong r.step <;>
    simp only [hslow]
  rename_i lstart lstop lstep
  unfold asLong at h1 h2 h3
  split at h1 <;> split at h2 <;> split at h3 <;> simp only [Option.some.injEq, reduceCtorEq] at h1 h2 h3
  subst h1 h2 h3
  rename_i hs1 hs2 hs3
  by_cases hmin : r.step = longMin
  · rw [ite_t hmin]; exact hslow
  rw [ite_f hmin]
  by_cases hchk : (if r.step > 0 then usub (toU r.start) (toU longMin) < toU r.step
                   else usub (toU longMax) (toU r.start) < usub 0 (toU r.step))
  · rw [ite_t hchk]; exact hslow
  rw [ite_f hchk, fast_len hw hL hs1 hs2 hs3]
  by_cases hbig : L > longMax
  · rw [ite_t hbig]; exact hslow
  rw [ite_f hbig]
  have hneg : wrap (-r.step) = -r.step := wrap_long (by unfold IsLong longMin longMax at *; omega)
  rw [iterTake_fast n _ _ _ (wrap_isLong _) hL0, rev_newStart, hneg]
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  rw [wrap_add_wrap]
  have e : r.start + (L - 1) * r.step + (k : Int) * -r.step = r.elem (L - 1 - k) := by
    unfold Range.elem; rw [Int.mul_neg, Int.sub_mul, Int.sub_mul, Int.sub_mul]; omega
  rw [e]
  exact wrap_long (elem_long hL hs1 hs2 (by omega) (by omega))

/-- After `j` values, `it` has `L - j` left (`__length_hint__`) and
`it.__reduce__()` describes a valid range of exactly the remaining values
`f j, f (j+1), ...`. -/
def ResumesAt (it : RIter) (L j : Int) (f : Int → Int) : Prop :=
  it.lengthHint = L - j ∧ (iterReduce it).WF ∧ (iterReduce it).Len (L - j) ∧
    ∀ k, (iterReduce it).elem k = f (j + k)

/-- Pickling an iterator at any point resumes it correctly: for every range,
after any number `n` of `next()` calls on `iter(r)` or `reversed(r)`, the
length hint is the number of remaining values and the range in
`__reduce__()` yields exactly those values. For the C `long` iterator this
relies on `range_iter`'s and `range_reverse`'s overflow checks, which keep
the end value `start + len*step` representable (the intermediate
`len * step` in `rangeiter_reduce` may wrap, harmlessly under
`-fno-strict-overflow`). -/
def IterReduceResumes : Prop :=
  ∀ (r : Range) (L : Int) (n : Nat), r.WF → r.Len L →
    ResumesAt (iterTake n (rangeIter r)).2 L (min n L.toNat : Nat) r.elem ∧
    ResumesAt (iterTake n (rangeReverse r)).2 L (min n L.toNat : Nat) (fun k => r.elem (L - 1 - k))

/-- The arithmetic core: the iterator state `(a + j*st, st, m - j)` reduces to
the range `(a + j*st, a + m*st, st)`. -/
theorem resumes_of (a st m j : Int) (hst : st ≠ 0) (hj : j ≤ m) (f : Int → Int)
    (hf : ∀ k, a + k * st = f k) (it : RIter)
    (hit : it.lengthHint = m - j ∧ iterReduce it = makeRangeObject (a + j * st) (a + m * st) st) :
    ResumesAt it m j f := by
  refine ⟨hit.1, ?_, ?_, ?_⟩
  · rw [hit.2]; exact makeRangeObject_wf _ _ _ hst
  · rw [hit.2]; exact arith_len a st j m hst hj
  · intro k; rw [hit.2, ← hf]; unfold Range.elem makeRangeObject; simp only
    rw [Int.add_mul]; omega

theorem iterReduceResumes_proven : IterReduceResumes := by
  intro r L n hw hL
  have hlen := hw.length_eq hL
  have hL0 := hL.1
  have hs := hw.1
  generalize hjdef : ((min n L.toNat : Nat) : Int) = j
  have hjL : j ≤ L := by omega
  have hj0 : 0 ≤ j := by omega
  refine ⟨?_, ?_⟩
  · have hslow : ResumesAt (iterTake n (RIter.long r.start r.step r.length)).2 L j r.elem := by
      rw [iterTake_long n _ _ _ (by omega), hlen, hjdef]
      refine resumes_of r.start r.step L j hs hjL r.elem (fun _ => rfl) _ ⟨rfl, ?_⟩
      simp only [iterReduce]
      congr 1; rw [Int.add_assoc, ← Int.add_mul]; congr 2; omega
    unfold rangeIter
    cases h1 : asLong r.start <;> cases h2 : asLong r.stop <;> cases h3 : asLong r.step <;>
      simp only [hslow]
    rename_i lstart lstop lstep
    unfold asLong at h1 h2 h3
    split at h1 <;> split at h2 <;> split at h3 <;> simp only [Option.some.injEq, reduceCtorEq] at h1 h2 h3
    subst h1 h2 h3
    rename_i hs1 hs2 hs3
    rw [fast_len hw hL hs1 hs2 hs3]
    by_cases hbig : L > longMax
    · rw [ite_t hbig]; exact hslow
    rw [ite_f hbig]
    by_cases hchk : L ≠ 0 ∧ (if r.step > 0 then r.stop > longMax - (r.step - 1)
                             else r.stop < longMin + (-1 - r.step))
    · rw [ite_t hchk]; exact hslow
    rw [ite_f hchk, iterTake_fast n _ _ _ hs1 hL0, hjdef]
    -- The end value `start + L*step` is a C long thanks to the overflow check.
    have hend : IsLong (r.start + L * r.step) := by
      by_cases hLz : L = 0
      · subst hLz; simp only [Int.zero_mul, Int.add_zero]; exact hs1
      have hlast := elem_between hL (k := L - 1) (by omega) (by omega)
      unfold Range.elem at hlast
      have e : r.start + L * r.step = r.start + (L - 1) * r.step + r.step := by
        rw [Int.sub_mul, Int.one_mul]; omega
      rw [e]
      by_cases hp : 0 < r.step
      · have := hlast.1 hp
        rw [ite_t (show r.step > 0 from hp)] at hchk
        unfold IsLong longMin longMax at *
        omega
      · have := hlast.2 hp
        rw [ite_f (show ¬ r.step > 0 from hp)] at hchk
        unfold IsLong longMin longMax at *
        omega
    have hcur : IsLong (r.start + j * r.step) := by
      by_cases hj : j = L
      · rw [hj]; exact hend
      · exact elem_long hL hs1 hs2 hj0 (by omega)
    refine resumes_of r.start r.step L j hs hjL r.elem (fun _ => rfl) _ ⟨rfl, ?_⟩
    have e : wrap (r.start + j * r.step + (L - j) * r.step) = r.start + L * r.step := by
      rw [Int.add_assoc, ← Int.add_mul, show j + (L - j) = L by omega]; exact wrap_long hend
    simp only [iterReduce]
    rw [wrap_long hcur, wrap_add_wrap', e]
  · have hrev : ∀ k, r.start + (L - 1) * r.step + k * -r.step = r.elem (L - 1 - k) := by
      intro k; unfold Range.elem; rw [Int.mul_neg, Int.sub_mul, Int.sub_mul, Int.sub_mul]; omega
    have hslow : ResumesAt (iterTake n (RIter.long (r.start + (r.length - 1) * r.step) (-r.step)
        r.length)).2 L j (fun k => r.elem (L - 1 - k)) := by
      rw [iterTake_long n _ _ _ (by omega), hlen, hjdef]
      refine resumes_of _ (-r.step) L j (by omega) hjL _ hrev _ ⟨rfl, ?_⟩
      simp only [iterReduce]
      congr 1; rw [Int.add_assoc, ← Int.add_mul]; congr 2; omega
    unfold rangeReverse
    cases h1 : asLong r.start <;> cases h2 : asLong r.stop <;> cases h3 : asLong r.step <;>
      simp only [hslow]
    rename_i lstart lstop lstep
    unfold asLong at h1 h2 h3
    split at h1 <;> split at h2 <;> split at h3 <;> simp only [Option.some.injEq, reduceCtorEq] at h1 h2 h3
    subst h1 h2 h3
    rename_i hs1 hs2 hs3
    by_cases hmin : r.step = longMin
    · rw [ite_t hmin]; exact hslow
    rw [ite_f hmin]
    by_cases hchk : (if r.step > 0 then usub (toU r.start) (toU longMin) < toU r.step
                     else usub (toU longMax) (toU r.start) < usub 0 (toU r.step))
    · rw [ite_t hchk]; exact hslow
    rw [ite_f hchk, fast_len hw hL hs1 hs2 hs3]
    by_cases hbig : L > longMax
    · rw [ite_t hbig]; exact hslow
    rw [ite_f hbig]
    have hneg : wrap (-r.step) = -r.step := wrap_long (by unfold IsLong longMin longMax at *; omega)
    rw [iterTake_fast n _ _ _ (wrap_isLong _) hL0, rev_newStart, hneg, hjdef]
    -- The end value `start - step` is a C long thanks to the overflow check.
    have hend : IsLong (r.start + (L - 1) * r.step + L * -r.step) := by
      rw [show r.start + (L - 1) * r.step + L * -r.step = r.start - r.step by
        rw [Int.mul_neg, Int.sub_mul, Int.one_mul]; omega]
      by_cases hp : r.step > 0
      · rw [ite_t hp] at hchk
        unfold usub toU two64 at hchk
        unfold IsLong longMin longMax at *
        omega
      · rw [ite_f hp] at hchk
        unfold usub toU two64 at hchk
        unfold IsLong longMin longMax at *
        omega
    have hcur : IsLong (r.start + (L - 1) * r.step + j * -r.step) := by
      by_cases hj : j = L
      · rw [hj]; exact hend
      · rw [hrev]; exact elem_long hL hs1 hs2 (by omega) (by omega)
    refine resumes_of _ (-r.step) L j (by omega) hjL _ hrev _ ⟨rfl, ?_⟩
    have e : wrap (r.start + (L - 1) * r.step + j * -r.step + (L - j) * -r.step) =
        r.start + (L - 1) * r.step + L * -r.step := by
      rw [Int.add_assoc _ (j * -r.step), ← Int.add_mul, show j + (L - j) = L by omega]
      exact wrap_long hend
    simp only [iterReduce]
    rw [wrap_add_wrap, wrap_long hcur, wrap_add_wrap', e]

/-- `it.__setstate__(state)` clips the state into `[0, len]` for every
range iterator and every int state: it succeeds and leaves
`L - clip(state)` values. `longrangeiter_setstate` (rangeobject.c:1042-1085)
does exactly that; `rangeiter_setstate` (:884-899) first converts with
`PyLong_AsLong` and raises `OverflowError` for states outside the C `long`
range. -/
def SetstateClips : Prop :=
  ∀ (r : Range) (L state : Int), r.WF → r.Len L →
    ∃ it', iterSetstate (rangeIter r) state = .ok it' ∧
      it'.lengthHint = L - max 0 (min state L)

/-- `it = iter(range(10)); it.__setstate__(2**64)` raises `OverflowError`,
while the same call on `iter(range(2**64, 2**64 + 10))` clips to the end. -/
theorem setstateClips_refuted : ¬SetstateClips := by
  intro h
  obtain ⟨it', hit, -⟩ := h (range1 10) 10 (2 ^ 64) (range1_wf 10)
    (by have := (range1_wf 10).len; rwa [show (range1 10).length = 10 by decide] at this)
  have : iterSetstate (rangeIter (range1 10)) (2 ^ 64) = .error longOverflow := by decide
  rw [this] at hit
  cases hit

/-- The long-iterator half of `SetstateClips` does hold: `longrange_iterator`
clips every int state. -/
theorem setstate_long_clips (a st m state : Int) :
    ∃ it', iterSetstate (.long a st m) state = .ok it' ∧
      it'.lengthHint = m - (if state < 0 then 0 else if m < state then m else state) :=
  ⟨_, rfl, rfl⟩

end PyLean.RangeSlice
