import PyLean.BytesObj.Bytes.FormatProps3

/-!
`bytes % args` end to end: what each conversion writes, and the argument cursor.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

set_option linter.unusedSimpArgs false

/-! ## The field writes, in closed form -/

/-- A field padded with spaces: the sign (if any) goes right before the text. -/
theorem fieldWrites_space (fl : Fl) (c : Int) (sign : Nat) (W L : Int) (p : Seq)
    (hc : hasPrefix fl c = false) (h0 : 0 ≤ L) (hW : L ≤ W) :
    fieldWrites fl c 32 sign W L p =
      let W1 := if sign ≠ 0 ∧ W > L then W - 1 else W
      let sg : Seq := if sign ≠ 0 then [sign] else []
      if fl.ljust then sg ++ p.take L.toNat ++ List.replicate (W1 - L).toNat 32
      else List.replicate (W1 - L).toNat 32 ++ sg ++ p.take L.toNat := by
  unfold fieldWrites
  simp only [hc, Bool.false_eq_true, false_and, ite_false, and_false, ne_eq]
  by_cases hs : sign = 0 <;> by_cases hl : fl.ljust = true <;>
    simp only [hs, hl, not_true_eq_false, not_false_eq_true, true_and, false_and, and_true,
      Bool.not_true, Bool.not_false, ite_true, ite_false, decide_true, decide_false, Bool.false_eq_true,
      List.nil_append, List.append_nil, List.append_assoc] <;>
    (repeat' split) <;> simp_all <;> (try omega)

/-- A field padded with zeros, not left-justified: sign, zeros, text. -/
theorem fieldWrites_zero (fl : Fl) (c : Int) (sign : Nat) (W L : Int) (p : Seq)
    (hc : hasPrefix fl c = false) (hl : fl.ljust = false) (h0 : 0 ≤ L) (hW : L ≤ W) :
    fieldWrites fl c 48 sign W L p =
      let W1 := if sign ≠ 0 ∧ W > L then W - 1 else W
      (if sign ≠ 0 then [sign] else []) ++ List.replicate (W1 - L).toNat 48 ++ p.take L.toNat := by
  unfold fieldWrites
  simp only [hc, hl, Bool.false_eq_true, false_and, ite_false, and_false, ne_eq, Bool.not_false]
  by_cases hs : sign = 0 <;>
    simp only [hs, not_true_eq_false, not_false_eq_true, true_and, false_and, and_true,
      ite_true, ite_false, decide_true, decide_false, Bool.false_eq_true, Nat.reduceEqDiff,
      List.nil_append, List.append_nil, List.append_assoc] <;>
    (repeat' split) <;> simp_all <;> (try omega)

/-! ## `%b`, `%s`, the argument cursor, `*` -/

/-- `%b` and `%s` write the bytes of their argument (`format_obj`, bytesobject.c:562-613), and
`getnextarg` hands out the tuple items in order (:412-416): `b'%b%s' % (x, y)` is the bytes of `x`
then those of `y`. A `*` precision (:827-850) cuts the bytes, a negative one cuts all; a `*` width
(:771-804) pads with spaces on the left, or on the right when negative. Hypothesis: the result
has fewer than `2^44` bytes, which the writer can allocate. -/
def FormatBytesArgs : Prop :=
  (∀ (x y : Obj) (sx sy : Seq), bytesLikeArg x = some sx → bytesLikeArg y = some sy →
    (sx.length : Int) + sy.length < 2 ^ 44 →
    bytesMod (asc "%b%s") (.tuple [x, y]) = .ok (sx ++ sy)) ∧
  (∀ (x : Obj) (sx : Seq) (p : Int), bytesLikeArg x = some sx → (sx.length : Int) < 2 ^ 44 →
    -2147483648 ≤ p → p ≤ 2147483647 →
    bytesMod (asc "%.*b") (.tuple [.int p, x]) = .ok (sx.take p.toNat)) ∧
  (∀ (x : Obj) (sx : Seq) (w : Int), bytesLikeArg x = some sx → (sx.length : Int) < 2 ^ 44 →
    -2 ^ 44 < w → w < 2 ^ 44 →
    bytesMod (asc "%*b") (.tuple [.int w, x]) =
      .ok (if 0 ≤ w then List.replicate (w.toNat - sx.length) 32 ++ sx
           else sx ++ List.replicate ((-w).toNat - sx.length) 32))

theorem asc_pbps : asc "%b%s" = [37, 98, 37, 115] := by decide
theorem asc_pdsb : asc "%.*b" = [37, 46, 42, 98] := by decide
theorem asc_psb : asc "%*b" = [37, 42, 98] := by decide

theorem formatBytesArgs_proven : FormatBytesArgs := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y sx sy hx hy hl
    have fx := formatObj_of_bytesLike x sx hx
    have fy := formatObj_of_bytesLike y sy hy
    have e1 : (-1 : Int) < sx.length := by omega
    have e2 : (-1 : Int) < sy.length := by omega
    rw [asc_pbps]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg, fx,
      bind, Except.bind, pure, Except.pure]
    rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, fieldAlloc]; omega)]
    simp [signStep, fieldAlloc, e1, fieldWrites_self, hasPrefix]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg, fy,
      bind, Except.bind, pure, Except.pure]
    have g1 := growIf_size { size := 4, overallocate := true } sx.length (by simp) (by simp; omega)
    rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp [g1]; omega)
      (by simp [signStep, fieldAlloc, g1]; omega)]
    simp [signStep, fieldAlloc, e2, fieldWrites_self, hasPrefix]
    rw [formatLoop]
    simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE]
    apply writerFinish_growIf
    · simp
    · simp [g1]; split <;> omega
    · omega
    · simp [g1]; split <;> omega
    · simp [g1]; split <;> split <;> omega
  · intro x sx p hx hl hp1 hp2
    have fx := formatObj_of_bytesLike x sx hx
    have hpr : ¬ (p < -2147483648 ∨ p > 2147483647) := by omega
    rw [asc_pdsb]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg, fx,
      starPrec, Obj.longValue?, hpr, bind, Except.bind, pure, Except.pure]
    rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, fieldAlloc]; split <;> split <;> omega)]
    simp only [signStep, Bool.false_eq_true, ite_false]
    rw [formatLoop]
    simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
      Int.reduceSub, List.nil_append]
    generalize hL : (if (0 ≤ if p < 0 then 0 else p) ∧ (if p < 0 then 0 else p) < ↑(List.length sx) then
      if p < 0 then 0 else p else ↑(List.length sx)) = L
    have hL0 : 0 ≤ L := by rw [← hL]; split <;> split <;> omega
    have hLs : L ≤ sx.length := by rw [← hL]; split <;> split <;> omega
    have htk : sx.take L.toNat = sx.take p.toNat := by
      rw [← hL]
      split <;> split
      all_goals first
        | rfl
        | (congr 1; omega)
        | (rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)])
    have e1 : (-1 : Int) < L := by omega
    have hA := fieldAllocExact_proven {} 98 32 0 L L sx (Or.inl rfl) hL0 hLs (Int.le_refl _) (by simp [hasPrefix])
    simp only [e1, ite_true]
    rw [writerFinish_growIf _ _ _ (by simp) (by simp) (by simp [fieldAlloc]; omega)
      (by simp [fieldAlloc]; omega) (by rw [hA]; simp [fieldAlloc]; split <;> omega)]
    rw [fieldWrites_space _ _ _ _ _ _ (by simp [hasPrefix]) hL0 (Int.le_refl _)]
    simp [htk]
  · intro x sx w hx hl hw1 hw2
    have fx := formatObj_of_bytesLike x sx hx
    have hwr : ¬ (w ≤ ssizeMin ∨ w > ssizeMax) := by
      simp only [ssizeMin, ssizeMax_val]; omega
    rw [asc_psb]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg, fx,
      starWidth, Obj.longValue?, hwr, bind, Except.bind, pure, Except.pure]
    have e0 : (0 : Int) ≤ sx.length := by omega
    by_cases hw : w < 0
    · have hW : (sx.length : Int) ≤ max (-w) sx.length := by omega
      have hA := fieldAllocExact_proven { ljust := true } 98 32 0 (max (-w) sx.length) sx.length sx
        (Or.inl rfl) e0 (Int.le_refl _) hW (by simp [hasPrefix])
      simp only [hw, ite_true]
      rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, fieldAlloc]; split <;> omega)]
      simp only [signStep, Bool.false_eq_true, ite_false]
      rw [formatLoop]
      simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
        Int.reduceSub, List.nil_append]
      have hm : (if -w < (sx.length : Int) then (sx.length : Int) else -w) = max (-w) sx.length := by
        split <;> omega
      rw [hm]
      rw [writerFinish_growIf _ _ _ (by simp) (by simp) (by simp [fieldAlloc]; omega)
        (by simp [fieldAlloc]; omega) (by rw [hA]; simp [fieldAlloc]; split <;> omega)]
      rw [fieldWrites_space _ _ _ _ _ _ (by simp [hasPrefix]) e0 hW]
      have hn : (max (-w) (sx.length : Int) - sx.length).toNat = (-w).toNat - sx.length := by omega
      have hnw : ¬ (0 ≤ w) := by omega
      simp [hnw, hn, List.take_of_length_le]
    · have hW : (sx.length : Int) ≤ max w sx.length := by omega
      have hA := fieldAllocExact_proven {} 98 32 0 (max w sx.length) sx.length sx
        (Or.inl rfl) e0 (Int.le_refl _) hW (by simp [hasPrefix])
      simp only [hw, ite_false]
      rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, fieldAlloc]; split <;> omega)]
      simp only [signStep, Bool.false_eq_true, ite_false]
      rw [formatLoop]
      simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
        Int.reduceSub, List.nil_append]
      have hm : (if w < (sx.length : Int) then (sx.length : Int) else w) = max w sx.length := by
        split <;> omega
      rw [hm]
      rw [writerFinish_growIf _ _ _ (by simp) (by simp) (by simp [fieldAlloc]; omega)
        (by simp [fieldAlloc]; omega) (by rw [hA]; simp [fieldAlloc]; split <;> omega)]
      rw [fieldWrites_space _ _ _ _ _ _ (by simp [hasPrefix]) e0 hW]
      have hn : (max w (sx.length : Int) - sx.length).toNat = w.toNat - sx.length := by omega
      have hw' : 0 ≤ w := by omega
      simp [hw', hn, List.take_of_length_le]

end PyLean.BytesObj.Bytes
