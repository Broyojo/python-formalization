import PyLean.RangeSlice.Slice
import PyLean.BytesObj.Seq.AllocProps
import PyLean.BytesObj.Seq.SearchProps

/-!
Slicing of tuples and lists. `tuple_subscript` copies with its own `size_t` cursor
for every step, while `list_subscript` has a `memcpy`-like path for step 1 and a
cursor path otherwise. Both read exactly the positions of `listSlicePositions`,
which `RangeSlice` has proved to be `range(*s.indices(n))`, so none of them leaves
the object: the bounds below are derived, not assumed.
-/

namespace PyLean.BytesObj.Seq

open PyLean
open PyLean.RangeSlice (Slice sliceUnpack adjustIndices adjustOne toU listSlicePositions
  sliceIndices IsLen)

variable {α : Type}

theorem toU_toU (x : Int) : toU (toU x) = toU x := by
  simp [toU, Int.emod_emod_of_dvd]

theorem toU_add_left (x y : Int) : toU (toU x + y) = toU (x + y) := by
  simp [toU, Int.emod_add_emod]

/-- The cursor reads position `toU (c + i * u)` at step `i`. -/
theorem sliceLoop_reads (l : List α) (u : Int) (n : Nat) (c : Int)
    (h : ∀ i : Nat, i < n → (slot l (toU (c + (i : Int) * u))).isSome) :
    ∃ r, sliceLoop l u n (toU c) = .ok r ∧
      r.map some = (List.range n).map (fun i : Nat => slot l (toU (c + (i : Int) * u))) := by
  induction n generalizing c with
  | zero => exact ⟨[], rfl, rfl⟩
  | succ n ih =>
    have hz : toU (c + ((0 : Nat) : Int) * u) = toU c := by simp
    have h0 := h 0 (by omega)
    rw [hz] at h0
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h0
    have hstep : ∀ i : Nat, toU (c + u + (i : Int) * u) = toU (c + ((i + 1 : Nat) : Int) * u) := by
      intro i
      congr 1
      rw [Int.natCast_succ, Int.add_mul, Int.one_mul, Int.add_assoc, Int.add_comm u]
    obtain ⟨r, hr, hm⟩ := ih (c + u) (fun i hi => by rw [hstep]; exact h (i + 1) (by omega))
    refine ⟨v :: r, ?_, ?_⟩
    · simp only [sliceLoop, hv, toU_add_left, hr]
    · rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      rw [hm, hz, hv]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, Nat.succ_eq_add_one, hstep]

/-- `listSlicePositions` stays inside the object, by the `RangeSlice` theorems. -/
theorem positions_in_bounds (n : Int) (s : Slice) (hn : 0 ≤ n) (hn' : n ≤ ssizeMax)
    (h0 : s.step ≠ some 0) :
    ∃ ps, listSlicePositions n s = .ok ps ∧ ∀ p ∈ ps, 0 ≤ p ∧ p < n := by
  obtain ⟨a, b, c, L, hsi, hL, hp⟩ := PyLean.RangeSlice.listSliceIndices_proven s n hn hn' h0
  obtain ⟨a', b', c', hsi', _, hb⟩ := PyLean.RangeSlice.indicesInBounds_proven s n hn h0
  rw [hsi] at hsi'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hsi'
  obtain ⟨rfl, rfl, rfl⟩ := hsi'
  refine ⟨_, hp, ?_⟩
  intro p hmem
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hmem
  have hk' : k < L.toNat := List.mem_range.mp hk
  have hLnn := hL.1
  exact hb L hL (k : Int) (by omega) (by omega)

theorem tdiv_le_self (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) : Int.tdiv x y ≤ x := by
  by_cases h : y = 0
  · subst h
    simpa using hx
  · rw [Int.tdiv_eq_ediv_of_nonneg hx]
    exact Int.ediv_le_self y hx

/-- `PySlice_AdjustIndices` never counts more items than the object has. -/
theorem adjust_len_le (n start stop step : Int) (hn : 0 ≤ n) :
    (adjustIndices n start stop step).2.2 ≤ n ∨ (adjustIndices n start stop step).2.2 ≤ 0 := by
  unfold adjustIndices
  simp only
  have hb : ∀ x, step < 0 → -1 ≤ adjustOne x n step ∧ adjustOne x n step ≤ n - 1 := by
    intro x hs
    unfold adjustOne
    simp only
    split <;> (try split) <;> (try split) <;> omega
  have hb' : ∀ x, ¬ step < 0 → 0 ≤ adjustOne x n step ∧ adjustOne x n step ≤ n := by
    intro x hs
    unfold adjustOne
    simp only
    split <;> (try split) <;> (try split) <;> omega
  by_cases hs : step < 0
  · simp only [hs, if_true]
    have h1 := hb start hs
    have h2 := hb stop hs
    generalize adjustOne start n step = a at h1 ⊢
    generalize adjustOne stop n step = b at h2 ⊢
    split
    · have := tdiv_le_self (a - b - 1) (-step) (by omega) (by omega)
      left; omega
    · right; omega
  · simp only [hs, if_false]
    have h1 := hb' start hs
    have h2 := hb' stop hs
    generalize adjustOne start n step = a at h1 ⊢
    generalize adjustOne stop n step = b at h2 ⊢
    split
    · have := tdiv_le_self (b - a - 1) step (by omega) (by omega)
      left; omega
    · right; omega

/-- With step 1 the count is `stop - start`. -/
theorem adjust_step_one (n start stop : Int) (h : 0 < (adjustIndices n start stop 1).2.2) :
    (adjustIndices n start stop 1).2.2 =
      (adjustIndices n start stop 1).2.1 - (adjustIndices n start stop 1).1 := by
  unfold adjustIndices at *
  simp only [show ¬ (1 : Int) < 0 by omega, if_false, Int.tdiv_one] at *
  split
  · omega
  · rename_i hlt
    rw [if_neg hlt] at h
    omega

theorem slot_lt_some (l : List α) (p : Int) (h0 : 0 ≤ p) (h1 : p < l.length) : (slot l p).isSome := by
  have hlt : p.toNat < l.length := by omega
  simp [slot, h0, hlt]

/-- `(l.drop st).take n` read through `slot`. -/
theorem drop_take_slots (l : List α) (st : Nat) (n : Nat) (h : st + n ≤ l.length) :
    ((l.drop st).take n).map some = (List.range n).map (fun i : Nat => slot l ((st : Int) + (i : Int))) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    have hi : i < n := by simpa using h2
    have hlt : st + i < l.length := by omega
    have hc : ((st : Int) + (i : Int)) = ((st + i : Nat) : Int) := by omega
    rw [List.getElem_map, List.getElem_map, List.getElem_take, List.getElem_drop]
    simp only [List.getElem_range]
    rw [hc, slot_nat, List.getElem?_eq_getElem hlt]

/-- For every tuple and list, every slice with int/None parts and a non-zero step, and
any sign and size of the parts: `t[s]` and `l[s]` succeed and read exactly the
positions `listSlicePositions` lists, all inside the object. `len <= (sys.maxsize -
32) // 8` is the type invariant of a tuple (`tuple_alloc` refuses anything longer).
A zero step raises `ValueError` first, as `RangeSlice.SliceErrors` shows for lists. -/
def SliceReads : Prop :=
  ∀ (α : Type) (t : Tup α) (s : Slice),
    (t.items.length : Int) ≤ (ssizeMax - tupleBase) / 8 → s.step ≠ some 0 →
    ∃ ps, listSlicePositions t.items.length s = .ok ps ∧ (∀ p ∈ ps, 0 ≤ p ∧ p < t.items.length) ∧
      (∃ r, tupleGetSlice t s = .ok r ∧ (r.items t.items []).map some = ps.map (slot t.items)) ∧
      (∃ o, listGetSlice t.items s = .ok o ∧ o.items.map some = ps.map (slot t.items))

theorem sliceReads_proven : SliceReads := by
  intro α t s hlen h0
  have hlimit : (ssizeMax - tupleBase) / 8 ≤ ssizeMax := by decide
  have hssize : ssizeMax = 9223372036854775807 := by decide
  obtain ⟨ps, hp, hbd⟩ := positions_in_bounds (t.items.length : Int) s (by omega) (by omega) h0
  refine ⟨ps, hp, hbd, ?_⟩
  unfold listSlicePositions at hp
  unfold tupleGetSlice listGetSlice
  cases hu : sliceUnpack s with
  | error e => simp [hu, bind, Except.bind] at hp
  | ok triple =>
    obtain ⟨start, stop, step⟩ := triple
    simp only [hu, bind, Except.bind] at hp ⊢
    unfold listSliceWrap
    have hle := adjust_len_le (t.items.length : Int) start stop step (by omega)
    have hone := adjust_step_one (t.items.length : Int) start stop
    generalize hadj : adjustIndices (t.items.length : Int) start stop step = adj at hp hle ⊢
    obtain ⟨st, sp, len⟩ := adj
    simp only at hp hle ⊢
    by_cases hlen0 : len ≤ 0
    · simp only [hlen0, if_true, pure, Except.pure] at hp ⊢
      simp only [Except.ok.injEq] at hp
      subst hp
      exact ⟨⟨.empty, rfl, rfl⟩, ⟨LObj.empty, rfl, rfl⟩⟩
    · simp only [hlen0, if_false] at hp ⊢
      have hnle : len ≤ (t.items.length : Int) := by omega
      have halloc : tupleAlloc len = .ok () := by
        unfold tupleAlloc
        rw [if_neg (by omega), if_neg (by omega)]
      by_cases hs1 : step = 1
      · subst hs1
        rw [hadj] at hone
        have hlv : len = sp - st := hone (by simpa using (by omega : 0 < len))
        simp only [if_true, pure, Except.pure, Except.ok.injEq] at hp
        have hL : (sp - st).toNat = len.toNat := by omega
        rw [hL] at hp
        subst hp
        have hLnat : 0 < len.toNat := by omega
        have hst : 0 ≤ st := by
          have := (hbd (st + ((0 : Nat) : Int)) (List.mem_map.mpr ⟨0, List.mem_range.mpr hLnat, rfl⟩)).1
          simpa using this
        have hlast : st + ((len.toNat - 1 : Nat) : Int) < t.items.length :=
          (hbd _ (List.mem_map.mpr ⟨len.toNat - 1, List.mem_range.mpr (by omega), rfl⟩)).2
        obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hst
        have hfit : k + len.toNat ≤ t.items.length := by omega
        have hslots := drop_take_slots t.items k len.toNat hfit
        have hps : ((List.range len.toNat).map (fun i : Nat => (k : Int) + (i : Int))).map (slot t.items) =
            (List.range len.toNat).map (fun i : Nat => slot t.items ((k : Int) + (i : Int))) := by
          simp [List.map_map, Function.comp_def]
        constructor
        · by_cases hwhole : (k : Int) = 0 ∧ (1 : Int) = 1 ∧ len = (t.items.length : Int) ∧ t.exact = true
          · refine ⟨.arg 0, by rw [if_pos hwhole], ?_⟩
            rw [hps]
            have hk0 : k = 0 := by omega
            subst hk0
            have hln : len.toNat = t.items.length := by omega
            have := drop_take_slots t.items 0 t.items.length (by omega)
            rw [hln]
            simpa [TRes.items] using this
          · rw [if_neg hwhole, halloc]
            simp only
            have hr := sliceLoop_reads t.items (toU 1) len.toNat (k : Int) (by
              intro i hi
              have hbound := hbd ((k : Int) + (i : Int))
                (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
              have hu1 : toU 1 = 1 := by decide
              have hsame : toU ((k : Int) + (i : Int) * toU 1) = (k : Int) + (i : Int) := by
                rw [hu1, Int.mul_one]
                unfold toU PyLean.RangeSlice.two64
                apply Int.emod_eq_of_lt <;> omega
              rw [hsame]
              exact slot_lt_some _ _ hbound.1 hbound.2)
            obtain ⟨r, hr1, hr2⟩ := hr
            rw [hr1]
            refine ⟨.fresh { items := r, tracked := true }, rfl, ?_⟩
            rw [hps]
            simp only [TRes.items]
            rw [hr2]
            apply List.map_congr_left
            intro i hi
            have hi' : i < len.toNat := List.mem_range.mp hi
            have hbound := hbd ((k : Int) + (i : Int))
              (List.mem_map.mpr ⟨i, List.mem_range.mpr hi', rfl⟩)
            have hu1 : toU 1 = 1 := by decide
            have hsame : toU ((k : Int) + (i : Int) * toU 1) = (k : Int) + (i : Int) := by
              rw [hu1, Int.mul_one]
              unfold toU PyLean.RangeSlice.two64
              apply Int.emod_eq_of_lt <;> omega
            rw [hsame]
        · simp only [if_true]
          refine ⟨_, rfl, ?_⟩
          rw [hps, ← hslots]
          simp only [listSliceLH]
          have hgt : ¬ sp - (k : Int) ≤ 0 := by omega
          simp only [hgt, if_false, prealloc_items]
          have hk : (k : Int).toNat = k := by omega
          rw [hk, ← hlv]
      · simp only [hs1, if_false, pure, Except.pure, Except.ok.injEq] at hp
        subst hp
        obtain ⟨r, hr1, hr2⟩ := sliceLoop_reads t.items (toU step) len.toNat (toU st) (by
          intro i hi
          have hbound := hbd (toU (toU st + (i : Int) * toU step))
            (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
          exact slot_lt_some _ _ hbound.1 hbound.2)
        rw [toU_toU] at hr1
        have hmap : ((List.range len.toNat).map
              (fun i : Nat => toU (toU st + (i : Int) * toU step))).map (slot t.items) =
            (List.range len.toNat).map (fun i : Nat => slot t.items (toU (toU st + (i : Int) * toU step))) := by
          simp [List.map_map, Function.comp_def]
        rw [hmap, ← hr2]
        have hnw : ¬ (st = 0 ∧ step = 1 ∧ len = (t.items.length : Int) ∧ t.exact = true) :=
          fun h => hs1 h.2.1
        constructor
        · rw [if_neg hnw, halloc]
          simp only [hr1]
          exact ⟨.fresh { items := r, tracked := true }, rfl, rfl⟩
        · simp only [hs1, if_false, hr1]
          exact ⟨LObj.prealloc r, rfl, by simp⟩

/-- `l[a:b]` under `BINARY_SLICE` (`_PyList_BinarySlice`) gives what `l[slice(a, b)]` gives, for every
pair of indices of any size. -/
def ListBinarySlice : Prop :=
  ∀ (α : Type) (l : List α) (a b : Option Int),
    listGetSlice l ⟨a, b, none⟩ = .ok (listBinarySlice l ⟨a, b, none⟩)

theorem listBinarySlice_proven : ListBinarySlice := by
  intro α l a b
  generalize hs : (match a with | none => (0 : Int) | some v => RangeSlice.clampSsize v) = x
  generalize ht : (match b with | none => ssizeMax | some v => RangeSlice.clampSsize v) = y
  have hu : sliceUnpack (⟨a, b, none⟩ : Slice) = .ok (x, y, 1) := by
    subst hs ht
    cases a <;> cases b <;> simp [sliceUnpack, bind, Except.bind, pure, Except.pure]
  have hi : unpackIndices (l.length : Int) (⟨a, b, none⟩ : Slice) =
      ((adjustIndices (l.length : Int) x y 1).1, (adjustIndices (l.length : Int) x y 1).2.1) := by
    subst hs ht
    rfl
  simp only [listGetSlice, hu, bind, Except.bind, listBinarySlice, hi, listSliceWrap]
  have e := adjust_step_one (l.length : Int) x y
  generalize hadj : adjustIndices (l.length : Int) x y 1 = adj at e ⊢
  obtain ⟨st, sp, len⟩ := adj
  simp only at e ⊢
  by_cases h : len ≤ 0
  · have hz : sp - st ≤ 0 := by
      have h1 := congrArg (fun p => p.2.2) hadj
      have h2 := congrArg (fun p => p.1) hadj
      have h3 := congrArg (fun p => p.2.1) hadj
      simp only [adjustIndices, show ¬ (1 : Int) < 0 by omega, if_false, Int.tdiv_one] at h1 h2 h3
      split at h1
      · omega
      · omega
    simp [h, listSliceLH, hz]
  · simp [h]

/-- `t[a:b]` under `BINARY_SLICE` (`_PyTuple_BinarySlice`) has the items of `t[slice(a, b)]`, for an
exact tuple and every pair of indices of any size. The two paths differ only in the GC flag:
`tuple_subscript` always tracks, and `PyTuple_FromArray` tracks by item. Hypothesis: the length of a
tuple that exists. -/
def TupleBinarySlice : Prop :=
  ∀ (α : Type) (mt : α → Bool) (t : Tup α) (a b : Option Int), t.exact = true →
    (t.items.length : Int) ≤ (ssizeMax - tupleBase) / 8 →
    ∃ r r', tupleBinarySlice mt t ⟨a, b, none⟩ = .ok r ∧ tupleGetSlice t ⟨a, b, none⟩ = .ok r' ∧
      r.items t.items [] = r'.items t.items []

theorem map_some_inj {l m : List α} (h : l.map some = m.map some) : l = m := by
  induction l generalizing m with
  | nil => cases m <;> simp_all
  | cons x xs ih =>
    cases m with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at h
      rw [h.1, ih h.2]

theorem tupleBinarySlice_items (mt : α → Bool) (t : Tup α) (s : Slice)
    (hlen : (t.items.length : Int) ≤ (ssizeMax - tupleBase) / 8) :
    ∃ r, tupleBinarySlice mt t s = .ok r ∧
      r.items t.items [] = (listBinarySlice t.items s).items := by
  have hmax : ssizeMax = 9223372036854775807 := by decide
  cases hp : unpackIndices (t.items.length : Int) s with
  | mk x y =>
  have e1 : tupleBinarySlice mt t s = if x = 0 ∧ y = (t.items.length : Int) then .ok (.arg 0)
      else tupleFromArray mt ((t.items.drop x.toNat).take ((if y < x then x else y) - x).toNat) := by
    simp only [tupleBinarySlice, hp]
  have e2 : listBinarySlice t.items s = listSliceLH t.items x y := by
    simp only [listBinarySlice, hp]
  rw [e1, e2]
  by_cases h : x = 0 ∧ y = (t.items.length : Int)
  · obtain ⟨rfl, rfl⟩ := h
    refine ⟨.arg 0, by simp, ?_⟩
    simp only [listSliceLH, TRes.items]
    split
    · have hz : t.items.length = 0 := by omega
      simp [List.length_eq_zero_iff.mp hz, LObj.empty]
    · rename_i hnz
      have hne : t.items ≠ [] := by
        intro e
        rw [e] at hnz
        simp at hnz
      simp [LObj.prealloc, hne]
  · rw [if_neg h]
    by_cases hlt : y < x
    · rw [if_pos hlt]
      refine ⟨.empty, by simp [tupleFromArray], ?_⟩
      simp [listSliceLH, TRes.items, show y - x ≤ 0 by omega, LObj.empty]
    · rw [if_neg hlt]
      generalize hsrc : (t.items.drop x.toNat).take (y - x).toNat = src
      have hsl : (src.length : Int) ≤ t.items.length := by
        rw [← hsrc]
        simp only [List.length_take, List.length_drop]
        omega
      have ha : tupleAlloc (src.length : Int) = .ok () := by
        unfold tupleAlloc
        rw [if_neg (by omega), if_neg (by omega)]
      by_cases he : src.length = 0
      · refine ⟨.empty, by simp [tupleFromArray, he], ?_⟩
        simp only [listSliceLH, TRes.items]
        split
        · rfl
        · rw [hsrc]
          simp [LObj.prealloc, LObj.empty, List.length_eq_zero_iff.mp he]
      · refine ⟨.fresh { items := src, tracked := src.any mt }, by simp [tupleFromArray, he, ha], ?_⟩
        simp only [listSliceLH, TRes.items]
        split
        · rename_i hle
          have : (y - x).toNat = 0 := by omega
          rw [this] at hsrc
          simp at hsrc
          simp [← hsrc] at he
        · rw [hsrc]
          have hne : src ≠ [] := fun e => he (by simp [e])
          simp [LObj.prealloc, hne]

theorem tupleBinarySlice_proven : TupleBinarySlice := by
  intro α mt t a b _ hlen
  obtain ⟨ps, _, _, ⟨r', h1, h2⟩, ⟨o, h3, h4⟩⟩ := sliceReads_proven α t ⟨a, b, none⟩ hlen (by simp)
  obtain ⟨r, hr, he⟩ := tupleBinarySlice_items mt t ⟨a, b, none⟩ hlen
  refine ⟨r, r', hr, h1, ?_⟩
  have hl := listBinarySlice_proven α t.items a b
  rw [h3] at hl
  have ho := Except.ok.inj hl
  rw [he, ← ho]
  exact map_some_inj (h4.trans h2.symm)

/-- `tuple_iteritem` and `list_iteritem` read what the iterators read, and stop at the same place. -/
def IterItemAgrees : Prop :=
  ∀ (α : Type) (l : List α) (i : Int), 0 ≤ i → i ≤ ssizeMax → (l.length : Int) ≤ ssizeMax →
    ((tupleIterItem l i).1 = (tupleIterNext ⟨i, some l⟩).1) ∧
    (i < l.length → (tupleIterItem l i).2 = i + 1) ∧ (i ≥ l.length → (tupleIterItem l i).2 = i) ∧
    (listIterItem l i).1 = (tupleIterItem l i).1 ∧ (listIterItem l i).2 = i + 1

theorem iterItemAgrees_proven : IterItemAgrees := by
  intro α l i h0 h1 h2
  have hv := validIndex_eq i l.length (by unfold ssizeMax at h1; omega) (by
    have : ssizeMax < 2 ^ 63 := by decide
    omega) (by omega) h2
  by_cases h : i < l.length
  · have h3 : ¬ (i ≥ l.length) := by omega
    have h4 : validIndex i l.length = true := by rw [hv]; simp [h0, h]
    refine ⟨?_, fun _ => ?_, fun h' => absurd h' h3, ?_, rfl⟩
    · simp [tupleIterItem, tupleIterNext, h, h3]
    · simp [tupleIterItem, h3]
    · simp [listIterItem, tupleIterItem, listGetItemRef, h4, h3]
  · have h3 : i ≥ l.length := by omega
    have h4 : validIndex i l.length = false := by rw [hv]; simp; omega
    refine ⟨?_, fun h' => absurd h' h, fun _ => ?_, ?_, rfl⟩
    · simp [tupleIterItem, tupleIterNext, h, h3]
    · simp [tupleIterItem, h3]
    · simp [listIterItem, tupleIterItem, listGetItemRef, h4, h3]

end PyLean.BytesObj.Seq
