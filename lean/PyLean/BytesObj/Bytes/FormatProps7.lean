import PyLean.BytesObj.Bytes.FormatProps6

/-!
`bytes % args`: the float conversions, `formatfloat` (bytesobject.c:430-479) on
`PyOS_double_to_string` (`Binary64.PyOS_double_to_string_checked`).
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

set_option linter.unusedSimpArgs false

/-- The float conversion characters, bytesobject.c:970-975. -/
def floatConvs : List Nat := asc "eEfFgG"

theorem floatConvs_val : floatConvs = [101, 69, 102, 70, 103, 71] := by decide

/-- The sign block takes a leading `-` or `+` off any text and the field puts it back. -/
theorem signStep_cases (fl : Fl) (hs : fl.sign = false) (hb : fl.blank = false) (t : Seq) :
    ∃ s p, signStep true fl t t.length = (s, p, (p.length : Int)) ∧ signBytes s ++ p = t := by
  cases t with
  | nil => exact ⟨0, [], by simp [signStep, hs, hb], rfl⟩
  | cons a rest =>
    by_cases h45 : a = 45
    · subst h45; exact ⟨45, rest, by simp [signStep], by simp [signBytes]⟩
    · by_cases h43 : a = 43
      · subst h43; exact ⟨43, rest, by simp [signStep], by simp [signBytes]⟩
      · refine ⟨0, a :: rest, ?_, by simp [signBytes]⟩
        unfold signStep
        simp only [if_true]
        split
        · rename_i h; simp at h; omega
        · rename_i h; simp at h; omega
        · simp [hs, hb]

/-- `%e %E %f %F %g %G` write the text `PyOS_double_to_string` gives for the double, with 6
digits when no precision is given (bytesobject.c:451-452) and `Py_DTSF_ALT` for `#` (:454-456), by
the fast path (:977-984); a `*` precision is used as it is, a negative one as 0 (:849-850), and an
error of `PyOS_double_to_string` (the `precision too big` of 3.15, pystrtod.c:1246-1251) is kept;
an int is converted by `PyLong_AsDouble` first (`PyFloat_AsDouble`, :441); and a `*` width pads with
spaces on the left, the sign staying with the digits. Hypothesis: the text has fewer than `2^44`
bytes, which the writer can allocate. -/
def FormatFloatText : Prop :=
  (∀ (x : Binary64.F64) (c : Nat) (t : Seq), c ∈ floatConvs → doubleToString x c 6 false = .ok t →
    (t.length : Int) < 2 ^ 44 → bytesMod [37, c] (.tuple [.float x]) = .ok t) ∧
  (∀ (x : Binary64.F64) (c : Nat) (t : Seq), c ∈ floatConvs → doubleToString x c 6 true = .ok t →
    (t.length : Int) < 2 ^ 44 → bytesMod [37, 35, c] (.tuple [.float x]) = .ok t) ∧
  (∀ (x : Binary64.F64) (c : Nat) (p : Int) (t : Seq), c ∈ floatConvs → -2147483648 ≤ p →
    p ≤ 2147483647 → doubleToString x c (max p 0) false = .ok t → (t.length : Int) < 2 ^ 44 →
    bytesMod [37, 46, 42, c] (.tuple [.int p, .float x]) = .ok t) ∧
  (∀ (x : Binary64.F64) (c : Nat) (p : Int) (e : PyExc), c ∈ floatConvs → -2147483648 ≤ p →
    p ≤ 2147483647 → doubleToString x c (max p 0) false = .error e →
    bytesMod [37, 46, 42, c] (.tuple [.int p, .float x]) = .error e) ∧
  (∀ (n : Int) (y : Binary64.F64) (c : Nat) (t : Seq), c ∈ floatConvs →
    Binary64.PyLong_AsDouble n = .ok y → doubleToString y c 6 false = .ok t →
    (t.length : Int) < 2 ^ 44 → bytesMod [37, c] (.tuple [.int n]) = .ok t) ∧
  (∀ (x : Binary64.F64) (c : Nat) (w : Int) (t : Seq), c ∈ floatConvs → 0 ≤ w → w < 2 ^ 44 →
    doubleToString x c 6 false = .ok t → (t.length : Int) < 2 ^ 44 →
    bytesMod [37, 42, c] (.tuple [.int w, .float x]) = .ok (List.replicate (w.toNat - t.length) 32 ++ t))

theorem formatFloatText_proven : FormatFloatText := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x c t hc ht hl
    rw [floatConvs_val] at hc
    have hg := writerGrow_eq { size := 2 } t.length (by simp) (by omega) (by simp; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
        writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
      rw [formatLoop]
      simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
        isIntConv, isFloatConv, formatFloatText, asDouble, ht, hg.1, bind, Except.bind, pure, Except.pure]
      rw [formatLoop]
      simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
        Int.reduceSub, List.nil_append]
      exact writerFinish_ok _ _ (by simp [hg.2.2]) (by rw [hg.2.1]; simp only; omega) (by rw [hg.2.1]; simp only; omega)
  · intro x c t hc ht hl
    rw [floatConvs_val] at hc
    have hg := writerGrow_eq { size := 3 } t.length (by simp) (by omega) (by simp; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
        writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
      rw [formatLoop]
      simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
        isIntConv, isFloatConv, formatFloatText, asDouble, ht, hg.1, bind, Except.bind, pure, Except.pure]
      rw [formatLoop]
      simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
        Int.reduceSub, List.nil_append]
      exact writerFinish_ok _ _ (by simp [hg.2.2]) (by rw [hg.2.1]; simp only; omega) (by rw [hg.2.1]; simp only; omega)
  · intro x c p t hc hp1 hp2 ht hl
    rw [floatConvs_val] at hc
    have hpr : ¬ (p < -2147483648 ∨ p > 2147483647) := by omega
    have hmax : (if p < 0 then 0 else p) = max p 0 := by split <;> omega
    have hp0 : ¬ ((if p < 0 then 0 else p) < 0) := by split <;> omega
    have hpn : (if p < 0 then 0 else p) ≠ -1 := by split <;> omega
    have hpn' : max p 0 ≠ -1 := by omega
    have hp0' : ¬ (max p 0 < 0) := by omega
    obtain ⟨s, q, hss, hsq⟩ := signStep_cases {} rfl rfl t
    have hb1 := alloc_bound s (-1) q.length (by omega)
    have hql : q.length ≤ t.length := by rw [← hsq]; simp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
        writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
      rw [formatLoop]
      simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
        starPrec, Obj.longValue?, hpr, hpn, hp0, hmax, hpn', hp0', isIntConv, isFloatConv, formatFloatText, asDouble,
        ht, bind, Except.bind, pure, Except.pure]
      rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by rw [hss]; simp; omega)]
      rw [hss]
      simp only
      rw [formatLoop]
      simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
        Int.reduceSub, List.nil_append]
      refine finish_field _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by omega) (by simp)
        (by split <;> omega) (by simp [hasPrefix]) (by simp; omega) ?_
      rw [numSpace' _ _ (by simp [hasPrefix]) _ _ _ _ rfl]
      simp [hsq]
  · intro x c p e hc hp1 hp2 he
    rw [floatConvs_val] at hc
    have hpr : ¬ (p < -2147483648 ∨ p > 2147483647) := by omega
    have hmax : (if p < 0 then 0 else p) = max p 0 := by split <;> omega
    have hp0 : ¬ ((if p < 0 then 0 else p) < 0) := by split <;> omega
    have hpn : (if p < 0 then 0 else p) ≠ -1 := by split <;> omega
    have hpn' : max p 0 ≠ -1 := by omega
    have hp0' : ¬ (max p 0 < 0) := by omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
        writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
      rw [formatLoop]
      simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
        starPrec, Obj.longValue?, hpr, hpn, hp0, hmax, hpn', hp0', isIntConv, isFloatConv, formatFloatText, asDouble,
        he, bind, Except.bind, pure, Except.pure]
  · intro n y c t hc hy ht hl
    rw [floatConvs_val] at hc
    have hg := writerGrow_eq { size := 2 } t.length (by simp) (by omega) (by simp; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
        writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
      rw [formatLoop]
      simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
        isIntConv, isFloatConv, formatFloatText, asDouble, Obj.index?, hy, ht, hg.1, bind, Except.bind,
        pure, Except.pure]
      rw [formatLoop]
      simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
        Int.reduceSub, List.nil_append]
      exact writerFinish_ok _ _ (by simp [hg.2.2]) (by rw [hg.2.1]; simp only; omega) (by rw [hg.2.1]; simp only; omega)
  · intro x c w t hc hw1 hw2 ht hl
    rw [floatConvs_val] at hc
    have hwr : ¬ (w ≤ ssizeMin ∨ w > ssizeMax) := by
      simp only [ssizeMin, ssizeMax_val]; omega
    have hw : ¬ w < 0 := by omega
    have hwn : w ≠ -1 := by omega
    obtain ⟨s, q, hss, hsq⟩ := signStep_cases {} rfl rfl t
    have hb1 := alloc_bound s w q.length (by omega)
    have hql : q.length ≤ t.length := by rw [← hsq]; simp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
        writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
      rw [formatLoop]
      simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
        starWidth, Obj.longValue?, hwr, hw, hwn, isIntConv, isFloatConv, formatFloatText, asDouble,
        ht, bind, Except.bind, pure, Except.pure]
      rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by rw [hss]; simp; omega)]
      rw [hss]
      simp only
      rw [formatLoop]
      simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
        Int.reduceSub, List.nil_append]
      refine finish_field _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by omega) (by simp)
        (by split <;> omega) (by simp [hasPrefix]) (by simp; omega) ?_
      rw [numSpace' _ _ (by simp [hasPrefix]) _ _ _ _ rfl]
      simp [hsq]

end PyLean.BytesObj.Bytes
