import PyLean.BytesObj.Bytes.FormatProps5

/-!
`bytes % args`: the integer field (`formatlong` and the sign block) and the float conversions
(`formatfloat` with `PyOS_double_to_string`).
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

set_option linter.unusedSimpArgs false

/-! ## The text of an int -/

/-- `str(v)` splits into the sign and the digits. -/
theorem intRepr_split (v : Int) (t : Seq) (ht : intRepr v = .ok t) :
    ∃ d ds, digitsBase 10 v.natAbs = d :: ds ∧ d ≠ 45 ∧ d ≠ 43 ∧
      t = (if v < 0 then [45] else []) ++ d :: ds := by
  obtain ⟨d, ds, hd, h45, h43⟩ := digits_head 10 v.natAbs (by decide) (by decide)
  exact ⟨d, ds, hd, h45, h43, by rw [intRepr_shape v t ht, hd]⟩

/-- The sign block (bytesobject.c:1041-1052) on the text of an int. -/
theorem signStep_int (fl : Fl) (v : Int) (d : Nat) (ds : Seq) (h45 : d ≠ 45) (h43 : d ≠ 43) :
    signStep true fl ((if v < 0 then [45] else []) ++ d :: ds)
        (((if v < 0 then [45] else []) ++ d :: ds).length : Int) =
      if v < 0 then (45, d :: ds, ((d :: ds).length : Int))
      else ((if fl.sign then 43 else if fl.blank then 32 else 0), d :: ds, ((d :: ds).length : Int)) := by
  by_cases hv : v < 0
  · simp only [hv, if_true, List.cons_append, List.nil_append]
    simp [signStep]
  · simp only [hv, if_false, List.nil_append]
    unfold signStep
    simp only [if_true]
    split
    · rename_i h; simp at h; omega
    · rename_i h; simp at h; omega
    · split <;> (try split) <;> simp_all

/-- `formatlong` on an exact int with no precision and no `#`: the text of `str(v)`. -/
theorem formatLong_dec (st : FS) (v : Int) (fl : Fl) (t : Seq) (ht : intRepr v = .ok t)
    (ha : fl.alt = false) :
    formatLong st (.int v) fl (-1) 100 = .ok t := by
  have hl := intRepr_len v t ht
  have h1 : ¬ ((-1 : Int) > intMax - 3) := by decide
  have h2 : ¬ ((t.length : Int) > intMax) := by unfold intMax; omega
  simp [formatLong, Obj.longValue?, unicodeFormatLong, numberToBase, longBase, ht, h1, h2, ha,
    bind, Except.bind, pure, Except.pure,
    formatLongText_dec t false 100 (by decide) (by decide) (by decide)]

/-! ## Closed forms of a numeric field -/

/-- The sign written by the sign block, as bytes. -/
def signBytes (s : Nat) : Seq := if s = 0 then [] else [s]

theorem numSpace (fl : Fl) (c : Int) (hc : hasPrefix fl c = false) (s : Nat) (p : Seq) (w : Int) :
    fieldWrites fl c 32 s (if w < p.length then p.length else w) p.length p =
      if fl.ljust then signBytes s ++ p ++ List.replicate (w.toNat - (signBytes s ++ p).length) 32
      else List.replicate (w.toNat - (signBytes s ++ p).length) 32 ++ signBytes s ++ p := by
  have h0 : (0 : Int) ≤ p.length := by omega
  rw [fieldWrites_space _ _ _ _ _ _ hc h0 (by split <;> omega)]
  simp only [signBytes]
  by_cases hs : s = 0 <;> by_cases hw : w < p.length <;> by_cases hl : fl.ljust = true <;>
    simp [hs, hw, hl, List.take_of_length_le] <;> (try split) <;> omega

theorem numZero (fl : Fl) (c : Int) (hc : hasPrefix fl c = false) (hl : fl.ljust = false) (s : Nat)
    (p : Seq) (w : Int) :
    fieldWrites fl c 48 s (if w < p.length then p.length else w) p.length p =
      signBytes s ++ List.replicate (w.toNat - (signBytes s ++ p).length) 48 ++ p := by
  have h0 : (0 : Int) ≤ p.length := by omega
  rw [fieldWrites_zero _ _ _ _ _ _ hc hl h0 (by split <;> omega)]
  simp only [signBytes]
  by_cases hs : s = 0 <;> by_cases hw : w < p.length <;>
    simp [hs, hw, List.take_of_length_le] <;> (try split) <;> omega

theorem numSpace' (fl : Fl) (c : Int) (hc : hasPrefix fl c = false) (s : Nat) (p : Seq) (w L : Int)
    (hL : L = p.length) :
    fieldWrites fl c 32 s (if w < L then L else w) L p =
      if fl.ljust then signBytes s ++ p ++ List.replicate (w.toNat - (signBytes s ++ p).length) 32
      else List.replicate (w.toNat - (signBytes s ++ p).length) 32 ++ signBytes s ++ p := by
  subst hL; exact numSpace fl c hc s p w

theorem numZero' (fl : Fl) (c : Int) (hc : hasPrefix fl c = false) (hl : fl.ljust = false) (s : Nat)
    (p : Seq) (w L : Int) (hL : L = p.length) :
    fieldWrites fl c 48 s (if w < L then L else w) L p =
      signBytes s ++ List.replicate (w.toNat - (signBytes s ++ p).length) 48 ++ p := by
  subst hL; exact numZero fl c hc hl s p w

theorem alloc_bound (s : Nat) (w L : Int) (h0 : 0 ≤ L) :
    0 ≤ fieldAlloc s (if w < L then L else w) L ∧ fieldAlloc s (if w < L then L else w) L ≤ max w L + 1 := by
  unfold fieldAlloc
  simp only
  split <;> split <;> (try split) <;> omega

/-- The end of a one-field format: the writer finishes with the field. -/
theorem finish_field (w : Writer) (fl : Fl) (c : Int) (fill sign : Nat) (W L : Int) (p rhs : Seq)
    (hb : w.useBytearray = false) (h2 : 2 ≤ w.size) (hfill : fill = 32 ∨ fill = 48) (hL0 : 0 ≤ L)
    (hLp : L ≤ p.length) (hLW : L ≤ W) (hpre : hasPrefix fl c = false)
    (hs : w.size + fieldAlloc sign W L < 2 ^ 46) (he : fieldWrites fl c fill sign W L p = rhs) :
    writerFinish (growIf w (fieldAlloc sign W L)) (fieldWrites fl c fill sign W L p) = .ok rhs := by
  have hA := fieldAllocExact_proven fl c fill sign W L p hfill hL0 hLp hLW (by simp [hpre])
  have hA0 : 0 ≤ fieldAlloc sign W L := by rw [← hA]; omega
  rw [writerFinish_growIf _ _ _ hb (by omega) hA0 hs (by rw [hA]; split <;> omega), he]

/-- The integer field: `%*d` pads with spaces on the left (the sign goes with the digits),
`%-*d` on the right, `%0*d` puts zeros between the sign and the digits, and `%+d` and `% d` add a
`+` or a space before a non-negative number, through `formatlong` and the sign block
(bytesobject.c:1041-1123). The text is `str(v)`, which is refused past 4300 digits.
Hypothesis: the width is below `2^44`, so the writer can allocate it. -/
def FormatIntField : Prop :=
  ∀ (v w : Int) (t : Seq), intRepr v = .ok t → 0 ≤ w → w < 2 ^ 44 →
    bytesMod (asc "%*d") (.tuple [.int w, .int v]) = .ok (List.replicate (w.toNat - t.length) 32 ++ t) ∧
    bytesMod (asc "%-*d") (.tuple [.int w, .int v]) = .ok (t ++ List.replicate (w.toNat - t.length) 32) ∧
    bytesMod (asc "%0*d") (.tuple [.int w, .int v]) =
      .ok ((if v < 0 then [45] else []) ++ List.replicate (w.toNat - t.length) 48 ++ digitsBase 10 v.natAbs) ∧
    bytesMod (asc "%+d") (.tuple [.int v]) = .ok ((if 0 ≤ v then [43] else []) ++ t) ∧
    bytesMod (asc "% d") (.tuple [.int v]) = .ok ((if 0 ≤ v then [32] else []) ++ t)

theorem asc_psd : asc "%*d" = [37, 42, 100] := by decide
theorem asc_pmsd : asc "%-*d" = [37, 45, 42, 100] := by decide
theorem asc_pzsd : asc "%0*d" = [37, 48, 42, 100] := by decide
theorem asc_ppd : asc "%+d" = [37, 43, 100] := by decide
theorem asc_pbd : asc "% d" = [37, 32, 100] := by decide

theorem formatIntField_proven : FormatIntField := by
  intro v w t ht hw1 hw2
  have hwr : ¬ (w ≤ ssizeMin ∨ w > ssizeMax) := by
    simp only [ssizeMin, ssizeMax_val]; omega
  have hw : ¬ w < 0 := by omega
  have hl := intRepr_len v t ht
  obtain ⟨d, ds, hd, h45, h43, htt⟩ := intRepr_split v t ht
  have fl0 := formatLong_dec
  have e0 : (0 : Int) ≤ (d :: ds).length := by omega
  have hlen : (t.length : Int) = (if v < 0 then 1 else 0) + (d :: ds).length := by
    rw [htt]; split <;> simp <;> omega
  have hwn : w ≠ -1 := by omega
  have hf : ∀ st fl, fl.alt = false → formatLong st (.int v) fl (-1) 100 = .ok t :=
    fun st fl ha => formatLong_dec st v fl t ht ha
  have hb := alloc_bound
  have hcase : (v < 0 ∧ t = 45 :: d :: ds) ∨ (0 ≤ v ∧ t = d :: ds) := by
    by_cases hv : v < 0
    · exact Or.inl ⟨hv, by simp [htt, hv]⟩
    · exact Or.inr ⟨by omega, by simp [htt, hv]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [asc_psd]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      starWidth, Obj.longValue?, hwr, hw, hwn, isIntConv, hf, bind, Except.bind, pure, Except.pure]
    rcases hcase with ⟨hv, rfl⟩ | ⟨hv, rfl⟩
    · simp only [List.length_cons] at hl
      have hb1 := hb 45 w ((ds.length : Int) + 1) (by omega)
      rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep]; omega)]
      simp [signStep]
      rw [formatLoop]
      simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
        Int.reduceSub, List.nil_append]
      refine finish_field _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by omega) (by simp)
        (by split <;> omega) (by simp [hasPrefix]) (by simp; omega) ?_
      rw [numSpace' _ _ (by simp [hasPrefix]) _ _ _ _ (by simp)]
      simp [signBytes]
    · simp only [List.length_cons] at hl
      have hb1 := hb 0 w ((ds.length : Int) + 1) (by omega)
      rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, h45, h43]; omega)]
      simp [signStep, h45, h43]
      rw [formatLoop]
      simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
        Int.reduceSub, List.nil_append]
      refine finish_field _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by omega) (by simp)
        (by split <;> omega) (by simp [hasPrefix]) (by simp; omega) ?_
      rw [numSpace' _ _ (by simp [hasPrefix]) _ _ _ _ (by simp)]
      simp [signBytes]
  · rw [asc_pmsd]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      starWidth, Obj.longValue?, hwr, hw, hwn, isIntConv, hf, bind, Except.bind, pure, Except.pure]
    rcases hcase with ⟨hv, rfl⟩ | ⟨hv, rfl⟩
    · simp only [List.length_cons] at hl
      have hb1 := hb 45 w ((ds.length : Int) + 1) (by omega)
      rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep]; omega)]
      simp [signStep]
      rw [formatLoop]
      simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
        Int.reduceSub, List.nil_append]
      refine finish_field _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by omega) (by simp)
        (by split <;> omega) (by simp [hasPrefix]) (by simp; omega) ?_
      rw [numSpace' _ _ (by simp [hasPrefix]) _ _ _ _ (by simp)]
      simp [signBytes]
    · simp only [List.length_cons] at hl
      have hb1 := hb 0 w ((ds.length : Int) + 1) (by omega)
      rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, h45, h43]; omega)]
      simp [signStep, h45, h43]
      rw [formatLoop]
      simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
        Int.reduceSub, List.nil_append]
      refine finish_field _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by omega) (by simp)
        (by split <;> omega) (by simp [hasPrefix]) (by simp; omega) ?_
      rw [numSpace' _ _ (by simp [hasPrefix]) _ _ _ _ (by simp)]
      simp [signBytes]
  · rw [asc_pzsd]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      starWidth, Obj.longValue?, hwr, hw, hwn, isIntConv, hf, bind, Except.bind, pure, Except.pure]
    rcases hcase with ⟨hv, rfl⟩ | ⟨hv, rfl⟩
    · simp only [List.length_cons] at hl
      have hb1 := hb 45 w ((ds.length : Int) + 1) (by omega)
      rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep]; omega)]
      simp [signStep]
      rw [formatLoop]
      simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
        Int.reduceSub, List.nil_append]
      refine finish_field _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by omega) (by simp)
        (by split <;> omega) (by simp [hasPrefix]) (by simp; omega) ?_
      rw [numZero' _ _ (by simp [hasPrefix]) rfl _ _ _ _ (by simp)]
      simp [signBytes, hd, hv]
    · simp only [List.length_cons] at hl
      have hb1 := hb 0 w ((ds.length : Int) + 1) (by omega)
      rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, h45, h43]; omega)]
      simp [signStep, h45, h43]
      rw [formatLoop]
      simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
        Int.reduceSub, List.nil_append]
      refine finish_field _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by omega) (by simp)
        (by split <;> omega) (by simp [hasPrefix]) (by simp; omega) ?_
      rw [numZero' _ _ (by simp [hasPrefix]) rfl _ _ _ _ (by simp)]
      simp [signBytes, hd, hv]
  · rw [asc_ppd]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      isIntConv, hf, bind, Except.bind, pure, Except.pure]
    rcases hcase with ⟨hv, rfl⟩ | ⟨hv, rfl⟩
    · simp only [List.length_cons] at hl
      have hb1 := hb 45 (-1) ((ds.length : Int) + 1) (by omega)
      rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep]; omega)]
      simp [signStep]
      rw [formatLoop]
      simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
        Int.reduceSub, List.nil_append]
      refine finish_field _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by omega) (by simp)
        (by split <;> omega) (by simp [hasPrefix]) (by simp; omega) ?_
      rw [numSpace' _ _ (by simp [hasPrefix]) _ _ _ _ (by simp)]
      simp [signBytes, hv]
    · simp only [List.length_cons] at hl
      have hb1 := hb 43 (-1) ((ds.length : Int) + 1) (by omega)
      rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, h45, h43]; omega)]
      simp [signStep, h45, h43]
      rw [formatLoop]
      simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
        Int.reduceSub, List.nil_append]
      refine finish_field _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by omega) (by simp)
        (by split <;> omega) (by simp [hasPrefix]) (by simp; omega) ?_
      rw [numSpace' _ _ (by simp [hasPrefix]) _ _ _ _ (by simp)]
      simp [signBytes, hv]
  · rw [asc_pbd]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      isIntConv, hf, bind, Except.bind, pure, Except.pure]
    rcases hcase with ⟨hv, rfl⟩ | ⟨hv, rfl⟩
    · simp only [List.length_cons] at hl
      have hb1 := hb 45 (-1) ((ds.length : Int) + 1) (by omega)
      rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep]; omega)]
      simp [signStep]
      rw [formatLoop]
      simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
        Int.reduceSub, List.nil_append]
      refine finish_field _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by omega) (by simp)
        (by split <;> omega) (by simp [hasPrefix]) (by simp; omega) ?_
      rw [numSpace' _ _ (by simp [hasPrefix]) _ _ _ _ (by simp)]
      simp [signBytes, hv]
    · simp only [List.length_cons] at hl
      have hb1 := hb 32 (-1) ((ds.length : Int) + 1) (by omega)
      rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, h45, h43]; omega)]
      simp [signStep, h45, h43]
      rw [formatLoop]
      simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
        Int.reduceSub, List.nil_append]
      refine finish_field _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by omega) (by simp)
        (by split <;> omega) (by simp [hasPrefix]) (by simp; omega) ?_
      rw [numSpace' _ _ (by simp [hasPrefix]) _ _ _ _ (by simp)]
      simp [signBytes, hv]

end PyLean.BytesObj.Bytes
