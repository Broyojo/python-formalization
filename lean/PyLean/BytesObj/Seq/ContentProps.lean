import PyLean.ListSort.Model
import PyLean.BytesObj.Seq.AllocProps
import PyLean.BytesObj.Seq.SortAux

/-!
What the list methods do to the contents, over any element type; `extend` with an
honest length hint; the helpers of `list.sort` that `ListSort` leaves.
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α ρ : Type}

/-- The two-cursor reversal of `reverse_slice` is `List.reverse`. -/
theorem reverseLoop_eq (f : Nat) (front mid back : List α) (hf : mid.length ≤ f + 1) :
    reverseLoop f front mid back = front.reverse ++ mid.reverse ++ back := by
  induction f generalizing front mid back with
  | zero =>
    have : mid = [] ∨ ∃ a, mid = [a] := by
      match mid, hf with
      | [], _ => exact Or.inl rfl
      | [a], _ => exact Or.inr ⟨a, rfl⟩
    rcases this with rfl | ⟨a, rfl⟩ <;> simp [reverseLoop]
  | succ f ih =>
    unfold reverseLoop
    split
    · rename_i a b rest
      have hsplit : a :: b :: rest =
          a :: ((a :: b :: rest).dropLast.drop 1 ++ [(a :: b :: rest).getLast (by simp)]) := by
        have h := List.dropLast_concat_getLast (l := a :: b :: rest) (by simp)
        have hd : (a :: b :: rest).dropLast = a :: (a :: b :: rest).dropLast.drop 1 := by
          simp
        rw [hd] at h
        simpa using h.symm
      generalize (a :: b :: rest).dropLast.drop 1 = inner at hsplit ⊢
      generalize (a :: b :: rest).getLast (by simp) = hi at hsplit ⊢
      have hlen : inner.length + 2 = (a :: b :: rest).length := by
        rw [hsplit]; simp
      rw [ih (hi :: front) inner (a :: back) (by simp only [List.length_cons] at hlen hf; omega)]
      rw [hsplit]
      simp
    · simp
      rename_i h
      cases mid with
      | nil => simp
      | cons x xs =>
        cases xs with
        | nil => simp
        | cons y ys => exact absurd rfl (h x y ys)

/-- What the list methods do to the contents, for every element type and every
argument: `append`, `insert` at the clipped position, `clear`, `reverse`, `extend`
from a sequence or a sized container, `l.extend(l)`, `l += x` from a sequence and from something
not iterable, which leaves `l` alone, `l *= n`, `a + b`, `l.copy()`, `len(l)`,
`__init__` without an argument, and `__init__` with something not iterable, which
drops the old contents and then raises, because the clear comes first
(listobject.c:3491-3499). A method that fails with `MemoryError` is the `.ok`
hypothesis not holding. -/
def ListContents : Prop :=
  ∀ (α : Type) (o o' : LObj α) (a b s : List α) (v : α) (w : Int) (name : String), o.WF →
    (listAppend o v = .ok o' → o'.items = o.items ++ [v]) ∧
    (ins1 o w (some v) = .ok o' →
      o'.items = o.items.take (ins1Where o.items.length w).toNat ++
        v :: o.items.drop (ins1Where o.items.length w).toNat) ∧
    (0 ≤ ins1Where o.items.length w ∧ ins1Where o.items.length w ≤ o.items.length) ∧
    (listClear o).items = [] ∧
    (listReverse o).items = o.items.reverse ∧
    (listExtendFast o s = .ok o' → o'.items = o.items ++ s) ∧
    (listExtendSized o s = .ok o' → o'.items = o.items ++ s) ∧
    (listExtend o .self = (o', none) → o'.items = o.items ++ o.items) ∧
    (listIConcat o (.fast s) = (o', none) → o'.items = o.items ++ s) ∧
    (listIConcat o (.notIterable name)).1 = o ∧
    (listIConcat o (.notIterable name)).2 = some (.typeError s!"'{name}' object is not iterable") ∧
    (1 ≤ w → listInplaceRepeat o w = .ok o' → o'.items = (List.replicate w.toNat o.items).flatten) ∧
    (w < 1 → listInplaceRepeat o w = .ok o' → o'.items = []) ∧
    (listConcat a b).items = a ++ b ∧
    (listSliceLH a 0 a.length).items = a ∧
    (listInit o none).1.items = [] ∧
    (listInit o (some (.notIterable name))).1.items = [] ∧
    (listInit o (some (.notIterable name))).2 = some (.typeError s!"'{name}' object is not iterable")

theorem listClear_items (o : LObj α) (hw : o.WF) : (listClear o).items = [] := by
  unfold listClear
  by_cases h : o.hasItems = true
  · simp [h]
  · have hal : ¬ 0 < o.allocated := fun hp => h (hw.array hp)
    have hc := hw.covers
    have : o.items = [] := List.length_eq_zero_iff.mp (by omega)
    simp [h, this]

theorem listInit_clears (o : LObj α) (hw : o.WF) :
    (if o.hasItems then listClear o else o).items = [] := by
  by_cases h : o.hasItems = true
  · simp only [h, if_true]
    exact listClear_items o hw
  · have hal : ¬ 0 < o.allocated := fun hp => h (hw.array hp)
    have hc := hw.covers
    have : o.items = [] := List.length_eq_zero_iff.mp (by omega)
    simp [h, this]

theorem listInplaceRepeat_two (o o2 : LObj α) (h : listInplaceRepeat o 2 = .ok o2) :
    o2.items = o.items ++ o.items := by
  unfold listInplaceRepeat at h
  simp only at h
  by_cases h0 : (o.items.length : Int) = 0 ∨ (2 : Int) = 1
  · rw [if_pos h0] at h
    simp only [Except.ok.injEq] at h
    have h1 : o.items = [] := List.length_eq_zero_iff.mp (by omega)
    rw [← h, h1]
    simp
  · rw [if_neg h0, if_neg (by omega : ¬ (2 : Int) < 1)] at h
    by_cases h2 : (o.items.length : Int) > ssizeMax / 2
    · rw [if_pos h2] at h
      simp at h
    · rw [if_neg h2] at h
      cases hl : listResize o.allocated o.hasItems o.items.length ((o.items.length : Int) * 2) with
      | error e => rw [hl] at h; simp at h
      | ok p =>
        rw [hl] at h
        simp only [Except.ok.injEq] at h
        rw [← h]
        simp [List.replicate_succ]

theorem listExtendFast_items (o o' : LObj α) (s : List α) (hw : o.WF) (h : listExtendFast o s = .ok o') :
    o'.items = o.items ++ s := by
  unfold listExtendFast at h
  split at h
  · rename_i h0
    simp only [Except.ok.injEq] at h
    rw [← h, List.length_eq_zero_iff.mp h0]
    simp
  · split at h
    · cases hp : listPreallocateExact (s.length : Int) with
      | error e => rw [hp] at h; simp at h
      | ok c =>
        rw [hp] at h
        simp only [Except.ok.injEq] at h
        rw [← h]
    · exact (resizeTo_wf hw h).2

theorem replicate_flatten_nil (n : Nat) : (List.replicate n ([] : List α)).flatten = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem listContents_proven : ListContents := by
  intro α o o' a b s v w name hw
  refine ⟨?_, ?_, ?_, listClear_items o hw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp [listConcat], ?_, ?_, ?_, ?_⟩
  · intro h
    unfold listAppend at h
    split at h
    · simp only [Except.ok.injEq] at h
      rw [← h]
    · exact (resizeTo_wf hw h).2
  · intro h
    exact (resizeTo_wf hw h).2
  · unfold ins1Where
    simp only
    split
    · split <;> split <;> omega
    · split <;> omega
  · unfold listReverse
    split
    · exact reverseLoop_eq _ [] _ [] (by omega) |>.trans (by simp)
    · rename_i h
      cases hi : o.items with
      | nil => simp [hi]
      | cons x xs =>
        cases xs with
        | nil => simp [hi]
        | cons y ys =>
          rw [hi] at h
          simp at h
  · exact listExtendFast_items o o' s hw
  · intro h
    unfold listExtendSized at h
    split at h
    · rename_i h0
      simp only [Except.ok.injEq] at h
      have h1 : s = [] := List.length_eq_zero_iff.mp (by omega)
      rw [← h, h1]
      simp
    · exact (resizeTo_wf hw h).2
  · intro h
    cases hr : listInplaceRepeat o 2 with
    | error e => simp [listExtend, liftRes, hr] at h
    | ok o2 =>
      simp only [listExtend, liftRes, hr, Prod.mk.injEq] at h
      rw [← h.1]
      exact listInplaceRepeat_two o o2 hr
  · intro h
    cases hr : listExtendFast o s with
    | error e => simp [listIConcat, listExtend, liftRes, hr] at h
    | ok o2 =>
      simp only [listIConcat, listExtend, liftRes, hr, Prod.mk.injEq] at h
      rw [← h.1]
      exact listExtendFast_items o o2 s hw hr
  · simp [listIConcat, listExtend]
  · simp [listIConcat, listExtend]
  · intro h1 h
    unfold listInplaceRepeat at h
    simp only at h
    by_cases h0 : (o.items.length : Int) = 0 ∨ w = 1
    · rw [if_pos h0] at h
      simp only [Except.ok.injEq] at h
      rw [← h]
      rcases h0 with h0 | h0
      · have he : o.items = [] := List.length_eq_zero_iff.mp (by omega)
        rw [he, replicate_flatten_nil]
      · rw [h0]
        simp
    · rw [if_neg h0, if_neg (by omega)] at h
      by_cases h2 : (o.items.length : Int) > ssizeMax / w
      · rw [if_pos h2] at h
        simp at h
      · rw [if_neg h2] at h
        cases hl : listResize o.allocated o.hasItems o.items.length ((o.items.length : Int) * w) with
        | error e => rw [hl] at h; simp at h
        | ok p =>
          rw [hl] at h
          simp only [Except.ok.injEq] at h
          rw [← h]
  · intro h1 h
    unfold listInplaceRepeat at h
    simp only at h
    by_cases h0 : (o.items.length : Int) = 0 ∨ w = 1
    · rw [if_pos h0] at h
      simp only [Except.ok.injEq] at h
      rw [← h]
      rcases h0 with h0 | h0
      · exact List.length_eq_zero_iff.mp (by omega)
      · omega
    · rw [if_neg h0, if_pos h1] at h
      simp only [Except.ok.injEq] at h
      rw [← h]
      exact listClear_items o hw
  · exact listSliceLH_all a
  · simp only [listInit]
    exact listInit_clears o hw
  · simp only [listInit, listExtend]
    exact listInit_clears o hw
  · simp [listInit, listExtend]

/-! ## extend with an honest hint -/

/-- A size below `sys.maxsize / 16` never trips the overflow test of `list_resize`. -/
theorem listResize_small (allocated : Int) (h : Bool) (size n : Int) (h0 : 0 ≤ n)
    (hn : n ≤ ssizeMax / 16) : ∃ r, listResize allocated h size n = .ok r := by
  unfold listResize
  split
  · exact ⟨_, rfl⟩
  · simp only
    have h16 : ssizeMax / 16 = 576460752303423487 := by decide
    have h8 : ssizeMax / 8 = 1152921504606846975 := by decide
    rw [h16] at hn
    have hle : newAllocated size n ≤ ssizeMax / 8 := by
      rw [h8]
      have h1 : overalloc n ≤ 1152921504606846975 := by
        unfold overalloc
        omega
      have h2 : ((n + 3) / 4) * 4 ≤ 1152921504606846975 := by omega
      unfold newAllocated
      simp only
      by_cases hz : n = 0
      · simp [hz]
      · rw [if_neg hz]
        split
        · exact h2
        · exact h1
    rw [if_pos hle]
    exact ⟨_, rfl⟩

theorem extendDrain_ok (o : LObj α) (xs : List α) (hw : o.WF)
    (hb : ((o.items.length + xs.length : Nat) : Int) ≤ ssizeMax / 16) :
    ∃ o', extendDrain o xs = .ok o' ∧ o'.items = o.items ++ xs ∧ o'.WF := by
  induction xs generalizing o with
  | nil => exact ⟨o, rfl, by simp, hw⟩
  | cons x xs ih =>
    simp only [List.length_cons] at hb
    have hcase : ∃ o2, extendDrain o (x :: xs) = extendDrain o2 xs ∧
        o2.items = o.items ++ [x] ∧ o2.WF := by
      by_cases hr : (o.items.length : Int) < o.allocated
      · refine ⟨{ o with items := o.items ++ [x] }, by rw [extendDrain, if_pos hr], rfl, ?_⟩
        refine ⟨hw.nonneg, ?_, hw.array, hw.bytes⟩
        show ((o.items ++ [x]).length : Int) ≤ o.allocated
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · have hnew : (((o.items ++ [x]).length : Nat) : Int) ≤ ssizeMax / 16 := by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        obtain ⟨p, hp⟩ := listResize_small o.allocated o.hasItems o.items.length
          (((o.items ++ [x]).length : Nat) : Int) (by omega) hnew
        obtain ⟨a, b⟩ := p
        have hres : resizeTo o (o.items ++ [x]) = .ok { items := o.items ++ [x], allocated := a, hasItems := b } := by
          unfold resizeTo
          rw [hp]
        have happ : listAppend o x = .ok { items := o.items ++ [x], allocated := a, hasItems := b } := by
          unfold listAppend
          rw [if_neg hr]
          exact hres
        obtain ⟨hw2, hi⟩ := resizeTo_wf hw hres
        exact ⟨_, by rw [extendDrain, if_neg hr, happ], hi, hw2⟩
    obtain ⟨o2, heq, hi, hw2⟩ := hcase
    have hb2 : ((o2.items.length + xs.length : Nat) : Int) ≤ ssizeMax / 16 := by
      rw [hi]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    obtain ⟨o3, h3, h4, h5⟩ := ih o2 hw2 hb2
    refine ⟨o3, ?_, ?_, h5⟩
    · rw [heq, h3]
    · rw [h4, hi]
      simp

theorem extendRoom_ok (o : LObj α) (n : Int) (hw : o.WF) (h0 : 0 ≤ n)
    (hb : (o.items.length : Int) + n ≤ ssizeMax / 16) :
    ∃ o', extendRoom o n = .ok o' ∧ o'.items = o.items ∧ o'.WF := by
  have hmax : ¬ ((o.items.length : Int) > ssizeMax - n) := by
    have : ssizeMax / 16 ≤ ssizeMax := by decide
    have : (0 : Int) ≤ ssizeMax / 16 := by decide
    omega
  unfold extendRoom
  simp only
  rw [if_neg hmax]
  by_cases hh : o.hasItems = true
  · simp only [hh, Bool.not_true, Bool.false_eq_true, if_false]
    obtain ⟨p, hp⟩ := listResize_small o.allocated o.hasItems o.items.length ((o.items.length : Int) + n)
      (by omega) hb
    obtain ⟨a, b⟩ := p
    rw [hh] at hp
    rw [hp]
    obtain ⟨g1, g2, g3, g4⟩ := listResize_spec _ _ _ _ a b (by omega) hw.nonneg hw.bytes
      (fun _ => rfl) hp
    refine ⟨_, rfl, rfl, ⟨g2, ?_, g4, g3⟩⟩
    show (o.items.length : Int) ≤ a
    omega
  · have hal : ¬ 0 < o.allocated := fun hp => hh (hw.array hp)
    have hc := hw.covers
    have hnil : o.items = [] := List.length_eq_zero_iff.mp (by omega)
    simp only [hh, Bool.not_false, if_true]
    by_cases hn : n = 0
    · rw [if_neg (by simpa using hn)]
      exact ⟨o, rfl, rfl, hw⟩
    · rw [if_pos hn]
      have hrounded : ((n + 1) / 2) * 2 ≤ ssizeMax / 8 := by
        unfold ssizeMax at *
        have h3 : (2 : Int) ^ 63 = 9223372036854775808 := by decide
        rw [h3] at *
        omega
      have hpre : listPreallocateExact n = .ok (((n + 1) / 2) * 2) := by
        unfold listPreallocateExact
        simp only
        rw [if_pos hrounded]
      rw [hpre]
      refine ⟨_, rfl, rfl, ⟨?_, ?_, fun _ => rfl, hrounded⟩⟩
      · show (0 : Int) ≤ ((n + 1) / 2) * 2
        omega
      · show (o.items.length : Int) ≤ ((n + 1) / 2) * 2
        rw [hnil]
        simp
        omega

/-- `list.extend` from a generic iterable, for every list and every hint that is not
absurd: the result is the old items followed by what the iterator yields, the hint
has no effect on the contents, and the invariant holds. "Not absurd" is `len(l) + hint
+ len(items) <= sys.maxsize / 16`: the broad version, for every hint `__length_hint__`
may legally return, is `ListHintInert`, which is refuted. -/
def ListExtendIterContents : Prop :=
  ∀ (α : Type) (o : LObj α) (src : IterSrc α) (n : Int), o.WF → src.hint = .ok n → 0 ≤ n →
    src.err = none →
    ((o.items.length + src.items.length : Nat) : Int) + n ≤ ssizeMax / 16 →
    (listExtendIter o src).2 = none ∧ (listExtendIter o src).1.items = o.items ++ src.items ∧
      (listExtendIter o src).1.WF

theorem listExtendIterContents_proven : ListExtendIterContents := by
  intro α o src n hw hh h0 he hb
  obtain ⟨o1, h1, h2, h3⟩ := extendRoom_ok o n hw h0 (by push_cast at hb; omega)
  have hb2 : ((o1.items.length + src.items.length : Nat) : Int) ≤ ssizeMax / 16 := by
    rw [h2]; omega
  obtain ⟨o2, h4, h5, h6⟩ := extendDrain_ok o1 src.items h3 hb2
  unfold listExtendIter
  simp only [hh, h1, h4, he]
  by_cases hroom : (o2.items.length : Int) < o2.allocated
  · simp only [hroom, if_true]
    have hsmall : (o2.items.length : Int) ≤ ssizeMax / 16 := by
      rw [h5, h2]
      simp only [List.length_append]
      push_cast at hb ⊢
      omega
    obtain ⟨p, hp⟩ := listResize_small o2.allocated o2.hasItems o2.items.length o2.items.length (by omega) hsmall
    obtain ⟨a, b⟩ := p
    rw [hp]
    obtain ⟨g1, g2, g3, g4⟩ := listResize_spec _ _ _ _ a b (by omega) h6.nonneg h6.bytes h6.array hp
    refine ⟨by first | trivial | rfl, ?_, ⟨g2, g1, g4, g3⟩⟩
    show o2.items = _
    rw [h5, h2]
  · simp only [hroom, if_false]
    exact ⟨by first | trivial | rfl, by rw [h5, h2], h6⟩

/-! ## The helpers of list.sort -/

/-- `sortslice` moves keep `keys[i]` the key of `values[i]`, the invariant that makes
`list.sort(key=...)` return the values in key order: reversing a run, advancing,
`memcpy`/`memmove` (`sortslice_memcpy`, `sortslice_memmove`), and single-item copies
(`sortslice_copy`, `sortslice_copy_incr`, `sortslice_copy_decr`), for any key function. -/
def SortsliceParallel : Prop :=
  ∀ (κ α : Type) (f : α → κ) (s s1 s2 : SortSlice κ α) (i j n : Nat),
    Parallel f s → (Parallel f (sortsliceReverse s n) ∧ Parallel f (sortsliceAdvance s n)) ∧
    ∀ v1 v2, s1.values = some v1 → s2.values = some v2 → Parallel f s1 → Parallel f s2 →
      Parallel f (sortsliceMemcpy s1 i s2 j n) ∧ Parallel f (sortsliceCopy s1 i s2 j)

theorem sortsliceParallel_proven : SortsliceParallel := by
  intro κ α f s s1 s2 i j n hs
  constructor
  · unfold Parallel at hs
    cases hv : s.values with
    | none => simp [Parallel, sortsliceReverse, sortsliceAdvance, hv]
    | some vs =>
      rw [hv] at hs
      simp only at hs
      simp only [Parallel, sortsliceReverse, sortsliceAdvance, hv, Option.map_some, hs]
      simp [List.map_take, List.map_drop, List.map_reverse]
  · intro v1 v2 h1 h2 hp1 hp2
    simp only [Parallel, h1, h2] at hp1 hp2
    constructor
    · simp only [Parallel, sortsliceMemcpy, h1, h2, blit, hp1, hp2]
      simp [List.map_take, List.map_drop, List.map_append]
    · simp only [Parallel, sortsliceCopy, h1, h2, hp1, hp2]
      cases hget : v2[j]? with
      | none => simp [hget]
      | some x => simp [hget, List.map_set]

/-- `merge_init` and `merge_getmem`: with a key function half the stack space goes to
the values; the temporary area is then at least `need` and the overflow check of
line 2247 cannot fire for a `need` no larger than the limit. `listsort.txt` bounds
`need` by half the list, so `merge_getmem`'s `MemoryError` by overflow is unreachable. -/
def MergeMemSpec : Prop :=
  ∀ (n need : Int) (kf : Bool) (ms : MergeMem), 0 ≤ n →
    (mergeInit n false).alloced = 256 ∧
    ((mergeInit n true).alloced = min ((n + 1) / 2) 128) ∧
    (mergeInit n kf).hasValues = kf ∧
    (need ≤ ms.alloced → mergeGetmem ms need = .ok ms) ∧
    (ms.alloced < need → need ≤ ssizeMax / 8 / (if ms.hasValues then 2 else 1) →
      mergeGetmem ms need = .ok { ms with alloced := need, onHeap := true })

theorem mergeMemSpec_proven : MergeMemSpec := by
  intro n need kf ms h0
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · show (if (256 : Int) / 2 < (n + 1) / 2 then (256 : Int) / 2 else (n + 1) / 2) = min ((n + 1) / 2) 128
    split <;> omega
  · cases kf <;> rfl
  · intro h
    unfold mergeGetmem
    rw [if_pos h]
  · intro h1 h2
    unfold mergeGetmem
    rw [if_neg (by omega)]
    simp only
    rw [if_neg (by omega)]

theorem memcmp_strLt (v w : List Nat) :
    (let res := memcmpL (min v.length w.length) v w
     if res ≠ 0 then decide (res < 0) else decide (v.length < w.length)) = strLt v w := by
  induction v generalizing w with
  | nil => cases w <;> simp [memcmpL, strLt]
  | cons x xs ih =>
    cases w with
    | nil => simp [memcmpL, strLt]
    | cons y ys =>
      have hmin : min (xs.length + 1) (ys.length + 1) = min xs.length ys.length + 1 := by omega
      simp only [List.length_cons, hmin, memcmpL, strLt]
      by_cases h1 : x < y
      · simp [h1]
      · by_cases h2 : y < x
        · simp [h1, h2]
        · simp only [h1, h2, if_false]
          have := ih ys
          simpa using this

theorem cmpSizes_succ (op : CmpOp) (a b : Int) : cmpSizes op (a + 1) (b + 1) = cmpSizes op a b := by
  cases op <;> (unfold cmpSizes; simp only [decide_eq_decide]; omega)

theorem tupleRichcompare_step (E : ElemOps α ρ) (op : CmpOp) (x y : α) (xs ys : List α)
    (h : richBool E .eq x y = .ok true) :
    tupleRichcompare E op (x :: xs) (y :: ys) = tupleRichcompare E op xs ys := by
  unfold tupleRichcompare
  simp only [tupleFirstDiff, h]
  cases hd : tupleFirstDiff E xs ys with
  | error e => rfl
  | ok r =>
    cases r with
    | some p => rfl
    | none =>
      simp only [List.length_cons]
      have e1 : ((xs.length + 1 : Nat) : Int) = (xs.length : Int) + 1 := by omega
      have e2 : ((ys.length + 1 : Nat) : Int) = (ys.length : Int) + 1 := by omega
      rw [e1, e2, cmpSizes_succ]

/-- `unsafe_tuple_compare` with the generic first comparison is `tuple < tuple`,
for every element type and comparison (which may raise), given that `Py_True` and
`Py_False` have their own truth values. -/
theorem unsafeTuple_go (E : ElemOps α ρ) (ht : ∀ b, E.truth (E.ofBool b) = .ok b) (v w : List α) (i : Nat) :
    unsafeTupleCompare.go E (fun x y => richBool E .lt x y) i v w =
      match tupleRichcompare E .lt v w with
      | .ok r => E.truth r
      | .error e => .error e := by
  induction v generalizing w i with
  | nil =>
    cases w <;> simp [unsafeTupleCompare.go, tupleRichcompare, tupleFirstDiff, cmpSizes, ht]
  | cons x xs ih =>
    cases w with
    | nil =>
      have hc : cmpSizes .lt (((x :: xs).length : Nat) : Int) ((([] : List α).length : Nat) : Int) = false := by
        unfold cmpSizes
        simp only [decide_eq_false_iff_not, List.length_cons, List.length_nil]
        omega
      simp only [unsafeTupleCompare.go, tupleRichcompare, tupleFirstDiff, ht, hc]
      simp
    | cons y ys =>
      cases hc : richBool E .eq x y with
      | error e =>
        have hr : tupleRichcompare E .lt (x :: xs) (y :: ys) = .error e := by
          simp [tupleRichcompare, tupleFirstDiff, hc]
        simp only [unsafeTupleCompare.go, hc, hr]
      | ok b =>
        cases b with
        | true =>
          rw [tupleRichcompare_step E .lt x y xs ys hc, ← ih ys (i + 1)]
          simp only [unsafeTupleCompare.go, hc]
        | false =>
          have hr : tupleRichcompare E .lt (x :: xs) (y :: ys) = E.rich .lt x y := by
            simp [tupleRichcompare, tupleFirstDiff, hc]
          have hb : richBool E .lt x y = (match E.rich .lt x y with
              | .ok r => E.truth r
              | .error e => .error e) := by
            have h1 : (CmpOp.lt == CmpOp.eq) = false := by decide
            have h2 : (CmpOp.lt == CmpOp.ne) = false := by decide
            unfold richBool
            simp only [h1, h2, Bool.and_false, Bool.false_eq_true, if_false]
            cases E.rich .lt x y <;> rfl
          rw [hr, ← hb]
          simp only [unsafeTupleCompare.go, hc]
          split <;> rfl

/-- `PyList_Sort(v)`, listobject.c:3166-3180. -/
def pyListSort (lt : α → α → Bool) (op : Option (List α)) : Py (List α) :=
  match op with
  | none => .error systemError
  | some l => .ok (PyLean.ListSort.listSort lt l)

/-- The compares `list.sort` selects agree with the generic path they replace:
`safe_object_compare` is `PyObject_RichCompareBool(v, w, Py_LT)`;
`unsafe_latin_compare` is `str.__lt__` on all byte strings, whichever is the shorter;
`unsafe_tuple_compare` is `tuple.__lt__` for every comparison, including raising ones.
`PyList_Sort` rejects a non-list and is otherwise `list.sort`. -/
def SortCompareAgree : Prop :=
  ∀ (α ρ : Type) (E : ElemOps α ρ) (lt : α → α → Bool) (x y : α)
    (v w : List Nat) (t u : List α) (l : List α),
    (∀ b, E.truth (E.ofBool b) = .ok b) →
    safeObjectCompare E x y = richBool E .lt x y ∧
    unsafeLatinCompare v w = strLt v w ∧
    unsafeTupleCompare E (fun a b => richBool E .lt a b) t u =
      (match tupleRichcompare E .lt t u with
       | .ok r => E.truth r
       | .error e => .error e) ∧
    pyListSort lt (none : Option (List α)) = .error systemError ∧
    pyListSort lt (some l) = .ok (PyLean.ListSort.listSort lt l)

theorem sortCompareAgree_proven : SortCompareAgree := by
  intro α ρ E lt x y v w t u l ht
  refine ⟨rfl, memcmp_strLt v w, unsafeTuple_go E ht t u 0, rfl, rfl⟩

end PyLean.BytesObj.Seq
