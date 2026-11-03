import PyLean.BytesObj.Seq.ListRows9

/-!
`del l[s]` for every slice (Objects/listobject.c `list_ass_subscript_lock_held`, the deletion arm
:3773-3837, CPython 3.15.2): the extended-slice compaction loop removes exactly the items at the
positions of `range(*s.indices(len(l)))`.
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α : Type}

/-- The items of a list whose position `j` (the first item being at `j0`) has `p j` false, in order. -/
def dropIdx (p : Nat → Bool) : List α → Nat → List α
  | [], _ => []
  | x :: xs, j => if p j then dropIdx p xs (j + 1) else x :: dropIdx p xs (j + 1)

theorem dropIdx_append (p : Nat → Bool) : ∀ (xs ys : List α) (j : Nat),
    dropIdx p (xs ++ ys) j = dropIdx p xs j ++ dropIdx p ys (j + xs.length)
  | [], ys, j => by simp [dropIdx]
  | x :: xs, ys, j => by
    have ih := dropIdx_append p xs ys (j + 1)
    rw [show j + 1 + xs.length = j + (x :: xs).length by simp only [List.length_cons]; omega] at ih
    simp only [List.cons_append, dropIdx, ih]
    split <;> rfl

theorem dropIdx_keep (p : Nat → Bool) : ∀ (xs : List α) (j : Nat),
    (∀ t, t < xs.length → p (j + t) = false) → dropIdx p xs j = xs
  | [], _, _ => rfl
  | x :: xs, j, h => by
    have h0 : p j = false := by simpa using h 0 (by simp)
    have ih := dropIdx_keep p xs (j + 1) (fun t ht => by
      rw [show j + 1 + t = j + (t + 1) by omega]
      exact h (t + 1) (by simp only [List.length_cons]; omega))
    simp only [dropIdx, h0, Bool.false_eq_true, if_false, ih]

theorem dropIdx_all (p : Nat → Bool) : ∀ (xs : List α) (j : Nat),
    (∀ t, t < xs.length → p (j + t) = true) → dropIdx p xs j = []
  | [], _, _ => rfl
  | x :: xs, j, h => by
    have h0 : p j = true := by simpa using h 0 (by simp)
    have ih := dropIdx_all p xs (j + 1) (fun t ht => by
      rw [show j + 1 + t = j + (t + 1) by omega]
      exact h (t + 1) (by simp only [List.length_cons]; omega))
    simp only [dropIdx, h0, if_true, ih]

theorem kept_noP (p : Nat → Bool) (l : List α) (m d : Nat) (hmd : m + d ≤ l.length)
    (h : ∀ t, t < d → p (m + t) = false) :
    dropIdx p (l.take (m + d)) 0 = dropIdx p (l.take m) 0 ++ (l.drop m).take d := by
  rw [List.take_add, dropIdx_append]
  have hm : (l.take m).length = m := by simp only [List.length_take]; omega
  rw [hm, Nat.zero_add]
  congr 1
  apply dropIdx_keep
  intro t ht
  have : ((l.drop m).take d).length = d := by simp only [List.length_take, List.length_drop]; omega
  exact h t (by omega)

theorem kept_P (p : Nat → Bool) (l : List α) (m : Nat) (hm : m < l.length) (h : p m = true) :
    dropIdx p (l.take (m + 1)) 0 = dropIdx p (l.take m) 0 := by
  rw [List.take_add, dropIdx_append]
  have hm' : (l.take m).length = m := by simp only [List.length_take]; omega
  rw [hm', Nat.zero_add]
  have : dropIdx p ((l.drop m).take 1) m = [] := by
    apply dropIdx_all
    intro t ht
    have : t = 0 := by simp only [List.length_take, List.length_drop] at ht; omega
    subst this
    simpa using h
  rw [this, List.append_nil]

theorem memmoveL_nat (mem : List α) (d s c : Nat) (h1 : d + c ≤ mem.length) (h2 : s + c ≤ mem.length) :
    memmoveL mem (d : Int) (s : Int) (c : Int) =
      .ok (mem.take d ++ (mem.drop s).take c ++ mem.drop (d + c)) := by
  unfold memmoveL
  rw [if_pos (by omega)]
  simp only [Int.toNat_natCast]
  rw [show ((d : Int) + (c : Int)).toNat = d + c by omega]

theorem blit_facts (mem : List α) (D S C : Nat) (h1 : D + C ≤ mem.length) (h2 : S + C ≤ mem.length) :
    (mem.take D ++ (mem.drop S).take C ++ mem.drop (D + C)).length = mem.length ∧
    (mem.take D ++ (mem.drop S).take C ++ mem.drop (D + C)).take (D + C) =
      mem.take D ++ (mem.drop S).take C ∧
    (∀ t, D + C ≤ t → (mem.take D ++ (mem.drop S).take C ++ mem.drop (D + C)).drop t = mem.drop t) := by
  have hA : (mem.take D ++ (mem.drop S).take C).length = D + C := by
    simp only [List.length_append, List.length_take, List.length_drop]; omega
  refine ⟨by simp only [List.length_append, List.length_take, List.length_drop]; omega,
    List.take_left' hA, fun t ht => ?_⟩
  rw [List.drop_append, hA, List.drop_eq_nil_of_le (by omega), List.nil_append, List.drop_drop]
  congr 1
  omega

/-- The compaction loop of `list_ass_subscript_lock_held` (listobject.c:3808-3821) with a positive
step, from pass `i` (cursor `cur = start + i*step`) on: the first `cur - i` slots hold the items kept
from the first `cur` positions, and the slots from `cur` on still hold the original items; at the
end the kept items of the first `start + L*step` positions (or of the whole list, when that is past
the end) come first. `p` marks the deleted positions: `start + k*step` for `k < L`. -/
theorem delLoop_spec (orig : List α) (start step L last E : Nat) (stop : Int) (p : Nat → Bool)
    (hstep : 1 ≤ step) (hL : 1 ≤ L) (hlastdef : last = start + (L - 1) * step) (hEdef : E = start + L * step)
    (hlast : last < orig.length) (hs1 : (last : Int) < stop) (hs2 : stop ≤ (E : Int))
    (hPpos : ∀ i, i < L → p (start + i * step) = true)
    (hPgap : ∀ i, i < L → ∀ t, 0 < t → t < step → p (start + i * step + t) = false)
    (hPend : ∀ j, last < j → p j = false) :
    ∀ (r i cur : Nat) (mem : List α) (fuel : Nat), i + r = L → cur = start + i * step → 1 ≤ r → r < fuel →
      mem.length = orig.length →
      mem.take (cur - i) = dropIdx p (orig.take cur) 0 →
      mem.drop cur = orig.drop cur →
      ∃ mem', delLoopL (orig.length : Int) (step : Int) stop fuel mem (cur : Int) (i : Int) = .ok mem' ∧
        mem'.length = orig.length ∧
        (E < orig.length → mem'.take (E - L) = dropIdx p (orig.take E) 0 ∧ mem'.drop E = orig.drop E) ∧
        (orig.length ≤ E → mem'.take (orig.length - L) = dropIdx p orig 0) := by
  intro r
  induction r with
  | zero => intro i cur mem fuel _ _ h; omega
  | succ r ih =>
    intro i cur mem fuel hir hcur _ hf hlen htake hdrop
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hiL : i < L := by omega
    have hmul1 : i * step ≤ (L - 1) * step := Nat.mul_le_mul_right _ (by omega)
    have hmul2 : i ≤ i * step := Nat.le_mul_of_pos_right i hstep
    have hnext : start + (i + 1) * step = cur + step := by rw [Nat.succ_mul]; omega
    have hcl : cur ≤ last := by omega
    have hPc : p cur = true := by rw [hcur]; exact hPpos i hiL
    have hgap : ∀ t, 0 < t → t < step → p (cur + t) = false := by
      intro t h1 h2; rw [hcur]; exact hPgap i hiL t h1 h2
    have hdrop1 : mem.drop (cur + 1) = orig.drop (cur + 1) := by
      rw [← List.drop_drop, hdrop, List.drop_drop]
    have hstopc : (cur : Int) < stop := by omega
    rw [delLoopL, if_pos hstopc]
    simp only
    by_cases hB : (cur : Int) + (step : Int) ≥ (orig.length : Int)
    · -- the last pass: the cursor's next value is past the end
      have hiL1 : i + 1 = L := by
        rcases Nat.lt_or_ge (i + 1) L with hlt | hge
        · have : (i + 1) * step ≤ (L - 1) * step := Nat.mul_le_mul_right _ (by omega)
          omega
        · omega
      have hE : E = cur + step := by rw [hEdef, ← hiL1]; exact hnext
      rw [if_pos hB,
        show (cur : Int) - (i : Int) = ((cur - i : Nat) : Int) by omega,
        show (cur : Int) + 1 = ((cur + 1 : Nat) : Int) by omega,
        show (orig.length : Int) - (cur : Int) - 1 = ((orig.length - cur - 1 : Nat) : Int) by omega,
        memmoveL_nat mem (cur - i) (cur + 1) (orig.length - cur - 1) (by omega) (by omega)]
      simp only
      obtain ⟨b1, b2, -⟩ := blit_facts mem (cur - i) (cur + 1) (orig.length - cur - 1) (by omega) (by omega)
      obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      rw [delLoopL, if_neg (by omega)]
      refine ⟨_, rfl, by rw [b1, hlen], fun h => by omega, fun _ => ?_⟩
      rw [show orig.length - L = cur - i + (orig.length - cur - 1) by omega, b2, htake, hdrop1,
        ← kept_P p orig cur (by omega) hPc]
      have hcl' : cur = last := by rw [hcur, hlastdef, show i = L - 1 by omega]
      rw [← kept_noP p orig (cur + 1) (orig.length - cur - 1) (by omega)
        (fun t ht => hPend _ (by omega))]
      rw [show cur + 1 + (orig.length - cur - 1) = orig.length by omega, List.take_length]
    · -- a middle pass: `step - 1` items move down by `i + 1`
      have hA : cur + step < orig.length := by omega
      rw [if_neg hB,
        show (cur : Int) - (i : Int) = ((cur - i : Nat) : Int) by omega,
        show (cur : Int) + 1 = ((cur + 1 : Nat) : Int) by omega,
        show (step : Int) - 1 = ((step - 1 : Nat) : Int) by omega,
        memmoveL_nat mem (cur - i) (cur + 1) (step - 1) (by omega) (by omega)]
      simp only
      obtain ⟨b1, b2, b3⟩ := blit_facts mem (cur - i) (cur + 1) (step - 1) (by omega) (by omega)
      generalize hnew : mem.take (cur - i) ++ (mem.drop (cur + 1)).take (step - 1) ++
        mem.drop (cur - i + (step - 1)) = new at b1 b2 b3 ⊢
      have hK : dropIdx p (orig.take (cur + step)) 0 =
          dropIdx p (orig.take cur) 0 ++ (orig.drop (cur + 1)).take (step - 1) := by
        rw [show cur + step = cur + 1 + (step - 1) by omega,
          kept_noP p orig (cur + 1) (step - 1) (by omega)
            (fun t ht => by rw [show cur + 1 + t = cur + (t + 1) by omega]; exact hgap _ (by omega) (by omega)),
          kept_P p orig cur (by omega) hPc]
      have nlen : new.length = orig.length := by rw [b1, hlen]
      have ntake : new.take (cur + step - (i + 1)) = dropIdx p (orig.take (cur + step)) 0 := by
        rw [show cur + step - (i + 1) = cur - i + (step - 1) by omega, b2, htake, hdrop1, hK]
      have ndrop : new.drop (cur + step) = orig.drop (cur + step) := by
        rw [b3 (cur + step) (by omega), ← List.drop_drop, hdrop, List.drop_drop]
      rw [show (cur : Int) + (step : Int) = ((cur + step : Nat) : Int) by omega,
        show (i : Int) + 1 = ((i + 1 : Nat) : Int) by omega]
      cases r with
      | zero =>
        have hiL1 : i + 1 = L := by omega
        have hE : E = cur + step := by rw [hEdef, ← hiL1]; exact hnext
        obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        rw [delLoopL, if_neg (by omega)]
        refine ⟨_, rfl, nlen, fun _ => ?_, fun h => by omega⟩
        rw [hE, show cur + step - L = cur + step - (i + 1) by omega]
        exact ⟨ntake, ndrop⟩
      | succ r =>
        exact ih (i + 1) (cur + step) new fuel (by omega) (by rw [hnext]) (by omega) (by omega) nlen
          ntake ndrop

/-- `list_resize(self, newsize)` after a deletion (`newsize` at most the old size) on a well-formed
list succeeds and keeps the invariant. -/
theorem listResize_shrink (o : LObj α) (hw : o.WF) (newsize : Nat) (hle : newsize ≤ o.items.length) :
    ∃ a h, listResize o.allocated o.hasItems (newsize : Int) (newsize : Int) = .ok (a, h) ∧
      (newsize : Int) ≤ a ∧ 0 ≤ a ∧ a ≤ ssizeMax / 8 ∧ (0 < a → h = true) := by
  have hcov := hw.covers
  obtain ⟨-, -, -, -, -, h6, -⟩ := listResizeExact_proven o.allocated o.hasItems newsize newsize
    hw.nonneg (by omega)
  obtain ⟨⟨a, h⟩, hr⟩ := h6 (by omega)
  exact ⟨a, h, hr, listResize_spec _ _ _ _ a h (by omega) hw.nonneg hw.bytes hw.array hr⟩

/-- Facts about the positions `s0 + k*d`, `k < L`, that the compaction loop relies on. -/
theorem posFacts (s0 d L : Nat) (hd : 1 ≤ d) (p : Nat → Bool)
    (hp : ∀ j, p j = true ↔ ∃ k, k < L ∧ j = s0 + k * d) :
    (∀ i, i < L → p (s0 + i * d) = true) ∧
    (∀ i, i < L → ∀ t, 0 < t → t < d → p (s0 + i * d + t) = false) ∧
    (∀ j, s0 + (L - 1) * d < j → p j = false) ∧
    (∀ j, j < s0 → p j = false) := by
  refine ⟨fun i hi => (hp _).mpr ⟨i, hi, rfl⟩, fun i hi t h1 h2 => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · cases hq : p (s0 + i * d + t) with
    | false => rfl
    | true =>
      obtain ⟨k, hk, he⟩ := (hp _).mp hq
      have a1 : i * d < k * d := by omega
      have a2 : k * d < (i + 1) * d := by rw [Nat.succ_mul]; omega
      have b1 := Nat.lt_of_mul_lt_mul_right a1
      have b2 := Nat.lt_of_mul_lt_mul_right a2
      omega
  · cases hq : p j with
    | false => rfl
    | true =>
      obtain ⟨k, hk, he⟩ := (hp _).mp hq
      have : k * d ≤ (L - 1) * d := Nat.mul_le_mul_right _ (by omega)
      omega
  · cases hq : p j with
    | false => rfl
    | true =>
      obtain ⟨k, hk, he⟩ := (hp _).mp hq
      omega

/-- The extended-slice deletion (listobject.c:3789-3837) once the step is positive: the compaction
loop, the tail move (:3822-3826), `Py_SET_SIZE` and the `list_resize` (:3828-3829) leave the items
whose positions are not `start + k*step`, `k < L`. -/
theorem delExtended_pos (o : LObj α) (hw : o.WF) (start step L : Nat) (stop : Int) (p : Nat → Bool)
    (hstep : 1 ≤ step) (hL : 1 ≤ L) (hlast : start + (L - 1) * step < o.items.length)
    (hs1 : ((start + (L - 1) * step : Nat) : Int) < stop) (hs2 : stop ≤ ((start + L * step : Nat) : Int))
    (hp : ∀ j, p j = true ↔ ∃ k, k < L ∧ j = start + k * step) :
    ∃ q, delExtendedL o (start : Int) stop (step : Int) (L : Int) = .ok q ∧ q.WF ∧
      q.items = dropIdx p o.items 0 := by
  obtain ⟨hPpos, hPgap, hPend, hPlow⟩ := posFacts start step L hstep p hp
  have hmulL : L ≤ L * step := Nat.le_mul_of_pos_right L hstep
  obtain ⟨mem, h1, h2, h3, h4⟩ := delLoop_spec o.items start step L (start + (L - 1) * step)
    (start + L * step) stop p hstep hL rfl rfl hlast hs1 hs2 hPpos hPgap hPend L 0 start o.items (L + 1)
    (by omega) (by simp) hL (by omega) rfl
    (by rw [Nat.sub_zero, dropIdx_keep p (o.items.take start) 0 (fun t ht => hPlow _ (by
      simp only [List.length_take] at ht; omega))]) rfl
  push_cast at h1
  unfold delExtendedL
  simp only [show ¬ ((step : Int) < 0) by omega, if_false]
  rw [show ((L : Int)).toNat = L by omega, h1]
  simp only [bind, Except.bind]
  rw [show (start : Int) + (L : Int) * (step : Int) = ((start + L * step : Nat) : Int) by push_cast; rfl]
  have hfinal : ∃ mem2, (if ((start + L * step : Nat) : Int) < (o.items.length : Int) then
      memmoveL mem (((start + L * step : Nat) : Int) - (L : Int)) ((start + L * step : Nat) : Int)
        ((o.items.length : Int) - ((start + L * step : Nat) : Int))
      else pure mem) = .ok mem2 ∧ mem2.take (o.items.length - L) = dropIdx p o.items 0 ∧
      mem2.length = o.items.length := by
    by_cases hE : start + L * step < o.items.length
    · rw [if_pos (by omega),
        show ((start + L * step : Nat) : Int) - (L : Int) = ((start + L * step - L : Nat) : Int) by omega,
        show (o.items.length : Int) - ((start + L * step : Nat) : Int) =
          ((o.items.length - (start + L * step) : Nat) : Int) by omega,
        memmoveL_nat mem _ _ _ (by omega) (by omega)]
      obtain ⟨b1, b2, -⟩ := blit_facts mem (start + L * step - L) (start + L * step)
        (o.items.length - (start + L * step)) (by omega) (by omega)
      obtain ⟨t1, t2⟩ := h3 hE
      refine ⟨_, rfl, ?_, by rw [b1, h2]⟩
      rw [show o.items.length - L = start + L * step - L + (o.items.length - (start + L * step)) by omega,
        b2, t1, t2, ← kept_noP p o.items (start + L * step) (o.items.length - (start + L * step)) (by omega)
          (fun t ht => hPend _ (by
            have : (L - 1) * step + step = L * step := by
              rw [← Nat.succ_mul, show (L - 1).succ = L by omega]
            omega)),
        show start + L * step + (o.items.length - (start + L * step)) = o.items.length by omega,
        List.take_length]
    · rw [if_neg (by omega)]
      exact ⟨mem, rfl, h4 (by omega), h2⟩
  obtain ⟨mem2, e1, e2, e3⟩ := hfinal
  have hLlen : L ≤ o.items.length := by have := Nat.le_mul_of_pos_right (L - 1) hstep; omega
  obtain ⟨a, h, hr, r1, r2, r3, r4⟩ := listResize_shrink o hw (o.items.length - L) (by omega)
  rw [show (o.items.length : Int) - (L : Int) = ((o.items.length - L : Nat) : Int) by omega, hr]
  have hwf : ({ items := mem2.take (o.items.length - L), allocated := a, hasItems := h } : LObj α).WF := by
    refine ⟨r2, ?_, r4, r3⟩
    show ((mem2.take (o.items.length - L)).length : Int) ≤ a
    simp only [List.length_take]
    omega
  by_cases hc : ((start + L * step : Nat) : Int) < (o.items.length : Int)
  · rw [if_pos hc] at e1 ⊢
    rw [e1]
    simp only [Int.toNat_natCast]
    exact ⟨_, rfl, hwf, e2⟩
  · rw [if_neg hc] at e1 ⊢
    rw [e1]
    simp only [Int.toNat_natCast]
    exact ⟨_, rfl, hwf, e2⟩

/-- The deletion with a negative step is the deletion with the step negated, from the lowest
position (listobject.c:3791-3795). -/
theorem delExtended_neg (o : LObj α) (start stop step len : Int) (h : step < 0) :
    delExtendedL o start stop step len =
      delExtendedL o (start + 1 + step * (len - 1) - 1) (start + 1) (-step) len := by
  unfold delExtendedL
  simp only [if_pos h, show ¬ (-step < 0) by omega, if_false]

/-! ## `del l[s]` -/

/-- Is position `j` one of `a + k*c`, `k < L` (the positions of `range(a, b, c)` when `L` is its
length)? -/
def slicePos (a c : Int) (L : Nat) (j : Nat) : Bool :=
  (List.range L).any (fun k => decide ((j : Int) = a + (k : Int) * c))

theorem slicePos_iff (a c : Int) (L j : Nat) :
    slicePos a c L j = true ↔ ∃ k, k < L ∧ (j : Int) = a + (k : Int) * c := by
  simp [slicePos, List.any_eq_true, List.mem_range]

theorem natCast_lin (x y : Int) (k : Nat) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ((x.toNat + k * y.toNat : Nat) : Int) = x + (k : Int) * y := by
  rw [Int.natCast_add, Int.natCast_mul, Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy]

/-- With `a, c ≥ 0`, the positions `a + k*c` as natural numbers. -/
theorem slicePos_nat (a c : Int) (L : Nat) (ha : 0 ≤ a) (hc : 0 ≤ c) (j : Nat) :
    slicePos a c L j = true ↔ ∃ k, k < L ∧ j = a.toNat + k * c.toNat := by
  rw [slicePos_iff]
  constructor
  · rintro ⟨k, hk, he⟩
    have := natCast_lin a c k ha hc
    exact ⟨k, hk, by omega⟩
  · rintro ⟨k, hk, he⟩
    have := natCast_lin a c k ha hc
    exact ⟨k, hk, by rw [he]; exact this⟩

/-- `del l[s]` for every list (well formed, `LObj.WF`, which includes `len(l) <= sys.maxsize`) and
every slice `s` with int/None parts whose `s.indices(len(l))` is `(a, b, c)` (the other slices are
the `ValueError` of `AssSliceErrors`): it succeeds, keeps the list well formed, and leaves exactly
the items whose positions are not in `range(a, b, c)`, in their order
(Doc/library/stdtypes.rst, mutable sequences: `del s[i:j:k]` "removes the elements of `s[i:j:k]`
from the list"). This covers `list_ass_subscript_lock_held`'s deletion arm (listobject.c:3773-3837):
step 1 through `list_ass_slice_lock_held` (:3781-3782), an empty slice (:3784-3785), and the
extended-slice compaction with its negative-step normalisation (:3787-3829). A deletion that removed
the wrong items, or the right number of items at the wrong places, fails this. -/
def DelSlice : Prop :=
  ∀ (α : Type) (o : LObj α) (s : RangeSlice.Slice) (a b c : Int), o.WF →
    RangeSlice.sliceIndices s o.items.length = .ok (a, b, c) →
    ∃ q, listAssSubscriptAny o (.slice s) none = (q, none) ∧ q.WF ∧
      q.items = dropIdx (slicePos a c (RangeSlice.computeRangeLengthSlow a b c).toNat) o.items 0

theorem dropIdx_window (p : Nat → Bool) (l : List α) (A M : Nat) (hAM : A + M ≤ l.length)
    (hp : ∀ j, p j = true ↔ A ≤ j ∧ j < A + M) : dropIdx p l 0 = l.take A ++ l.drop (A + M) := by
  have hpf : ∀ j, ¬ (A ≤ j ∧ j < A + M) → p j = false := by
    intro j hj
    cases h : p j with
    | false => rfl
    | true => exact absurd ((hp j).mp h) hj
  conv => lhs; rw [← List.take_append_drop A l, ← List.take_append_drop M (l.drop A)]
  rw [dropIdx_append, dropIdx_append]
  have hA : (l.take A).length = A := by simp only [List.length_take]; omega
  have hM : ((l.drop A).take M).length = M := by
    simp only [List.length_take, List.length_drop]; omega
  rw [hA, hM, Nat.zero_add,
    dropIdx_keep p (l.take A) 0 (fun t ht => hpf _ (by rw [hA] at ht; omega)),
    dropIdx_all p ((l.drop A).take M) A (fun t ht => (hp _).mpr (by rw [hM] at ht; omega)),
    dropIdx_keep p ((l.drop A).drop M) (A + M) (fun t _ => hpf _ (by omega)),
    List.nil_append, List.drop_drop]

theorem delSlice_proven : DelSlice := by
  intro α o s a b c hw hsi
  have hl := wf_len o hw
  have hn : (0 : Int) ≤ o.items.length := by omega
  have h0 : s.step ≠ some 0 := by
    intro h0
    obtain ⟨st, sp, ss⟩ := s
    simp only at h0; subst h0
    unfold RangeSlice.sliceIndices at hsi
    rw [if_neg (by omega)] at hsi
    simp [RangeSlice.getLongIndices, bind, Except.bind] at hsi
  obtain ⟨a', b', c', L, st, sp, c'', hsi', hL, hb, hLdef, hsu, hadj, h1, hsg, hc, hc'0, -⟩ :=
    PyLean.Sequences.adjust_spec s o.items.length hn hl h0
  rw [hsi] at hsi'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hsi'
  obtain ⟨rfl, rfl, rfl⟩ := hsi'
  -- the C step is the slice's step, clamped to `[-PY_SSIZE_T_MAX, PY_SSIZE_T_MAX]`
  have hstep : c = s.step.getD 1 := by
    have e := RangeSlice.getLongIndices_eq s o.items.length h0
    unfold RangeSlice.sliceIndices at hsi
    rw [if_neg (by omega), e] at hsi
    simp only [Except.ok.injEq, Prod.mk.injEq] at hsi
    exact hsi.2.2.symm
  have hcc : c'' = RangeSlice.clampStep c := by
    rw [RangeSlice.sliceUnpack_eq s h0] at hsu
    simp only [Except.ok.injEq, Prod.mk.injEq] at hsu
    rw [hstep]; exact hsu.2.2.symm
  obtain ⟨-, -, -, -, hid⟩ := RangeSlice.clampStep_sign c hc
  have hbig : c'' = c ∨ (c'' = ssizeMax ∨ c'' = -ssizeMax) := by
    rw [hcc]; unfold RangeSlice.clampStep RangeSlice.clampSsize ssizeMin ssizeMax
    split <;> (try split) <;> (try split) <;> omega
  obtain ⟨hL'', hsmall⟩ := RangeSlice.len_clamped a b c c'' o.items.length L hl hc hsg hc'0 hbig
    (fun h1 h2 => by rw [hcc]; exact hid h1 h2) hb hL
  have hb'' : RangeSlice.Bnds a b c'' o.items.length :=
    ⟨fun h => hb.1 (by omega), fun h => hb.2 (by omega)⟩
  rw [← hLdef]
  have hL0 : 0 ≤ L := hL.1
  -- the positions are the same with the clamped step
  have hPeq : slicePos a c L.toNat = slicePos a c'' L.toNat := by
    by_cases hce : c'' = c
    · rw [hce]
    · have h1L : L ≤ 1 := hsmall hce
      funext j
      rcases (show L.toNat = 0 ∨ L.toNat = 1 by omega) with h | h <;> rw [h] <;> simp [slicePos]
  rw [hPeq]
  unfold listAssSubscriptAny
  by_cases hc1 : c'' = 1
  · -- step 1: `list_ass_slice_lock_held(self, start, stop, NULL)`
    have hc1' : c = 1 := h1.mp hc1
    have hba := hb.1 (by omega)
    have hLa : ∀ k : Int, 0 ≤ k → (k < L ↔ a + k < b) := by
      intro k hk
      have := hL.2 k hk
      unfold RangeSlice.InSeq at this
      rw [hc1', if_pos (by decide), Int.mul_one] at this
      exact this
    have hLv : L = max 0 (b - a) := by
      have e1 := hLa L hL0
      by_cases hab : a < b
      · have e2 := hLa (L - 1)
        by_cases hL1 : 1 ≤ L
        · have := (e2 (by omega)).mp (by omega); omega
        · have := (hLa (b - a - 1) (by omega)).mpr (by omega); omega
      · have := hLa 0 (by omega); omega
    obtain ⟨q, q1, q2, q3⟩ := listAssSlice_del o a
      (if (c'' < 0 ∧ a < b) ∨ (c'' > 0 ∧ a > b) then a else b) hw
    refine ⟨q, ?_, q3, ?_⟩
    · simp only [listAssSubscript, hsu, bind, Except.bind, adjustSliceIndexes, hadj, if_pos hc1, q1,
        liftRes]
    · rw [q2]
      symm
      rw [show max a.toNat (if (c'' < 0 ∧ a < b) ∨ (c'' > 0 ∧ a > b) then a else b).toNat =
        a.toNat + L.toNat by split <;> omega]
      apply dropIdx_window _ _ _ _ (by omega)
      intro j
      rw [slicePos_iff]
      constructor
      · rintro ⟨k, hk, he⟩; rw [hc1] at he; omega
      · intro hj; exact ⟨j - a.toNat, by omega, by rw [hc1]; omega⟩
  · by_cases hLz : L ≤ 0
    · -- an empty extended slice: nothing changes
      refine ⟨o, ?_, hw, ?_⟩
      · simp only [listAssSubscript, hsu, bind, Except.bind, adjustSliceIndexes, hadj, if_neg hc1,
          if_pos hLz, liftRes]
      · rw [show L.toNat = 0 by omega]
        symm
        apply dropIdx_keep
        intro t _
        simp [slicePos]
    · have hL1 : 1 ≤ L := by omega
      have hpos := fun k hk hkL => RangeSlice.indices_in_bounds a b c'' o.items.length L hL'' hb'' k hk hkL
      have hin0 := hpos 0 (by omega) (by omega)
      have hinl := hpos (L - 1) (by omega) (by omega)
      have hlastIn := (hL''.2 (L - 1) (by omega)).mp (by omega)
      have hendOut : ¬ RangeSlice.InSeq a b c'' L := fun h => by
        have := (hL''.2 L hL0).mpr h; omega
      unfold RangeSlice.InSeq at hlastIn hendOut
      have hgoal : ∀ q, delExtendedL o a (if (c'' < 0 ∧ a < b) ∨ (c'' > 0 ∧ a > b) then a else b) c'' L =
          .ok q → listAssSubscriptAny o (.slice s) none = (q, none) := by
        intro q hq
        simp only [listAssSubscriptAny, listAssSubscript, hsu, bind, Except.bind, adjustSliceIndexes, hadj,
          if_neg hc1, if_neg hLz, hq, liftRes]
      by_cases hcp : 0 < c''
      · rw [if_pos hcp] at hlastIn hendOut
        have hab : a < b := by
          have := Int.mul_nonneg (show 0 ≤ L - 1 by omega) (Int.le_of_lt hcp); omega
        have hstop : (if (c'' < 0 ∧ a < b) ∨ (c'' > 0 ∧ a > b) then a else b) = b := by
          rw [if_neg (by omega)]
        have e1 := natCast_lin a c'' (L.toNat - 1) (by omega) (by omega)
        have e2 := natCast_lin a c'' L.toNat (by omega) (by omega)
        rw [show (((L.toNat - 1 : Nat) : Int)) = L - 1 by omega] at e1
        rw [show ((L.toNat : Nat) : Int) = L by omega] at e2
        obtain ⟨q, hq, qw, qi⟩ := delExtended_pos o hw a.toNat c''.toNat L.toNat b (slicePos a c'' L.toNat)
          (by omega) (by omega) (by omega) (by rw [e1]; exact hlastIn) (by rw [e2]; omega)
          (slicePos_nat a c'' L.toNat (by omega) (by omega))
        rw [show ((a.toNat : Nat) : Int) = a by omega, show ((c''.toNat : Nat) : Int) = c'' by omega,
          show ((L.toNat : Nat) : Int) = L by omega, ← hstop] at hq
        exact ⟨q, hgoal q hq, qw, qi⟩
      · have hcn : c'' < 0 := by omega
        rw [if_neg hcp] at hlastIn hendOut
        have hab : b < a := by
          have := Int.mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ L - 1 by omega) (show c'' ≤ 0 by omega)
          omega
        have hstop : (if (c'' < 0 ∧ a < b) ∨ (c'' > 0 ∧ a > b) then a else b) = b := by
          rw [if_neg (by omega)]
        -- normalised: from the lowest position `s0 = a + (L-1)*c` upwards by `-c`
        have hs0 : a + 1 + c'' * (L - 1) - 1 = a + (L - 1) * c'' := by rw [Int.mul_comm]; omega
        have hs0n : 0 ≤ a + (L - 1) * c'' := hinl.1
        have hd : 0 ≤ -c'' := by omega
        have e1 := natCast_lin (a + (L - 1) * c'') (-c'') (L.toNat - 1) hs0n hd
        have e2 := natCast_lin (a + (L - 1) * c'') (-c'') L.toNat hs0n hd
        rw [show (((L.toNat - 1 : Nat) : Int)) = L - 1 by omega, Int.mul_neg] at e1
        rw [show ((L.toNat : Nat) : Int) = L by omega, Int.mul_neg] at e2
        have hP : ∀ j, slicePos a c'' L.toNat j = true ↔
            ∃ k, k < L.toNat ∧ j = (a + (L - 1) * c'').toNat + k * (-c'').toNat := by
          intro j
          rw [slicePos_iff]
          constructor
          · rintro ⟨k, hk, he⟩
            refine ⟨L.toNat - 1 - k, by omega, ?_⟩
            have e3 := natCast_lin (a + (L - 1) * c'') (-c'') (L.toNat - 1 - k) hs0n hd
            rw [show (((L.toNat - 1 - k : Nat) : Int)) = L - 1 - k by omega, Int.mul_neg,
              Int.sub_mul (L - 1) (k : Int) c''] at e3
            omega
          · rintro ⟨k, hk, he⟩
            refine ⟨L.toNat - 1 - k, by omega, ?_⟩
            have e3 := natCast_lin (a + (L - 1) * c'') (-c'') k hs0n hd
            rw [Int.mul_neg] at e3
            rw [show (((L.toNat - 1 - k : Nat) : Int)) = L - 1 - k by omega, Int.sub_mul]
            rw [he]
            omega
        obtain ⟨q, hq, qw, qi⟩ := delExtended_pos o hw (a + (L - 1) * c'').toNat (-c'').toNat L.toNat
          (a + 1) (slicePos a c'' L.toNat) (by omega) (by omega)
          (by have : ((((a + (L - 1) * c'').toNat + (L.toNat - 1) * (-c'').toNat : Nat)) : Int) = a := by
                rw [e1]; rw [Int.sub_mul]; omega
              omega)
          (by rw [e1, Int.sub_mul]; omega) (by rw [e2, Int.sub_mul]; omega) hP
        rw [show (((a + (L - 1) * c'').toNat : Nat) : Int) = a + 1 + c'' * (L - 1) - 1 by omega,
          show (((-c'').toNat : Nat) : Int) = -c'' by omega, show ((L.toNat : Nat) : Int) = L by omega,
          ← delExtended_neg o a b c'' L hcn, ← hstop] at hq
        exact ⟨q, hgoal q hq, qw, qi⟩

end PyLean.BytesObj.Seq
