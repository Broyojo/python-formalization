import PyLean.BytesObj.Seq.ListRows4

/-!
The `sortslice` helpers of Objects/listobject.c:1660-1723 (CPython 3.15.2), slot by slot.
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {κ α : Type}

/-- A blit of `n` items from `src[j..]` to `dst[i..]`, for ranges inside both arrays, slot by slot. -/
theorem blit_get {β : Type} (dst src : List β) (i j n t : Nat) (h1 : i + n ≤ dst.length) (h2 : j + n ≤ src.length) :
    (blit dst i src j n)[t]? = if i ≤ t ∧ t < i + n then src[j + (t - i)]? else dst[t]? := by
  unfold blit
  have hA : (dst.take i).length = i := by simp; omega
  have hB : ((src.drop j).take n).length = n := by simp; omega
  by_cases ht1 : t < i
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_take, if_pos ht1, if_neg (by omega)]
  · by_cases ht2 : t < i + n
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega), hA,
        List.getElem?_take, if_pos (by omega), List.getElem?_drop, if_pos ⟨by omega, ht2⟩]
    · rw [List.getElem?_append_right (by simp; omega), List.getElem?_drop, if_neg (by omega)]
      congr 1
      simp only [List.length_append, List.length_take, List.length_drop]
      omega

/-- The `sortslice` helpers (listobject.c:1660-1723), which move keys and values together, slot by slot,
for every slice:

* `sortslice_copy(s1, i, s2, j)` (:1674-1680) puts `s2[j]` at `s1[i]`, keys and values, and changes no
  other slot;
* `sortslice_copy_incr` (:1682-1688) is that copy at the cursors, then both cursors one forward;
* `sortslice_copy_decr` (:1690-1696) is that copy at the cursors, then both cursors one back;
* `sortslice_memcpy(s1, i, s2, j, n)` (:1699-1706) and `sortslice_memmove` (:1708-1715) put
  `s2[j + k]` at `s1[i + k]` for `k < n` and leave the other slots; `memmove` reads the source as it was,
  so moving within one slice is the same statement with `s2 = s1`;
* `sortslice_advance(s, n)` (:1717-1723) moves the cursor `n` slots on;
* a slice without values (`values == NULL`) stays without. Ranges are inside the arrays. -/
def SortsliceMoves : Prop :=
  ∀ (κ α : Type) (s1 s2 : SortSlice κ α) (v1 v2 : List α) (i j n t : Nat),
    ((i < s1.keys.length → j < s2.keys.length →
      (sortsliceCopy s1 i s2 j).keys[i]? = s2.keys[j]? ∧
      (t ≠ i → (sortsliceCopy s1 i s2 j).keys[t]? = s1.keys[t]?)) ∧
     (s1.values = some v1 → s2.values = some v2 → i < v1.length → j < v2.length →
      ∃ w, (sortsliceCopy s1 i s2 j).values = some w ∧ w[i]? = v2[j]? ∧ (t ≠ i → w[t]? = v1[t]?)) ∧
     (s1.values = none → (sortsliceCopy s1 i s2 j).values = none)) ∧
    (sortsliceCopyIncr s1 s2 =
      (sortsliceCopy s1 0 s2 0, sortsliceAdvance (sortsliceCopy s1 0 s2 0) 1, sortsliceAdvance s2 1)) ∧
    (sortsliceCopyDecr s1 i s2 j = (sortsliceCopy s1 i s2 j, (i : Int) - 1, (j : Int) - 1)) ∧
    (i + n ≤ s1.keys.length → j + n ≤ s2.keys.length →
      (sortsliceMemcpy s1 i s2 j n).keys[t]? = (if i ≤ t ∧ t < i + n then s2.keys[j + (t - i)]? else s1.keys[t]?) ∧
      (sortsliceMemmove s1 i s2 j n).keys[t]? = (if i ≤ t ∧ t < i + n then s2.keys[j + (t - i)]? else s1.keys[t]?)) ∧
    (s1.values = some v1 → s2.values = some v2 → i + n ≤ v1.length → j + n ≤ v2.length →
      (∃ w, (sortsliceMemcpy s1 i s2 j n).values = some w ∧
        w[t]? = if i ≤ t ∧ t < i + n then v2[j + (t - i)]? else v1[t]?) ∧
      (∃ w, (sortsliceMemmove s1 i s2 j n).values = some w ∧
        w[t]? = if i ≤ t ∧ t < i + n then v2[j + (t - i)]? else v1[t]?)) ∧
    (s1.values = none → (sortsliceMemcpy s1 i s2 j n).values = none ∧ (sortsliceMemmove s1 i s2 j n).values = none) ∧
    ((sortsliceAdvance s1 n).keys[t]? = s1.keys[n + t]? ∧
      (s1.values = some v1 → ∃ w, (sortsliceAdvance s1 n).values = some w ∧ w[t]? = v1[n + t]?) ∧
      (s1.values = none → (sortsliceAdvance s1 n).values = none))

theorem sortsliceMoves_proven : SortsliceMoves := by
  intro κ α s1 s2 v1 v2 i j n t
  refine ⟨⟨fun h1 h2 => ?_, fun h1 h2 h3 h4 => ?_, fun h1 => ?_⟩, rfl, rfl, fun h1 h2 => ?_,
    fun h1 h2 h3 h4 => ?_, fun h1 => ?_, ?_, fun h1 => ?_, fun h1 => ?_⟩
  · have hj : s2.keys[j]? = some s2.keys[j] := List.getElem?_eq_getElem h2
    simp only [sortsliceCopy, hj]
    refine ⟨List.getElem?_set_self h1, fun ht => ?_⟩
    exact List.getElem?_set_ne (Ne.symm ht)
  · have hj : v2[j]? = some v2[j] := List.getElem?_eq_getElem h4
    refine ⟨v1.set i v2[j], ?_, ?_, fun ht => ?_⟩
    · simp only [sortsliceCopy, h1, h2, hj]
    · rw [List.getElem?_set_self h3, hj]
    · exact List.getElem?_set_ne (Ne.symm ht)
  · simp only [sortsliceCopy, h1]
  · exact ⟨blit_get _ _ i j n t h1 h2, blit_get _ _ i j n t h1 h2⟩
  · refine ⟨⟨blit v1 i v2 j n, by simp only [sortsliceMemcpy, h1, h2], blit_get _ _ i j n t h3 h4⟩,
      ⟨blit v1 i v2 j n, by simp only [sortsliceMemmove, h1, h2], blit_get _ _ i j n t h3 h4⟩⟩
  · exact ⟨by simp only [sortsliceMemcpy, h1], by simp only [sortsliceMemmove, h1]⟩
  · simp only [sortsliceAdvance]
    exact List.getElem?_drop
  · refine ⟨v1.drop n, by simp only [sortsliceAdvance, h1, Option.map_some], ?_⟩
    exact List.getElem?_drop
  · simp only [sortsliceAdvance, h1, Option.map_none]

end PyLean.BytesObj.Seq
