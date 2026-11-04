import PyLean.BytesObj.Bytes.FormatProps4

/-!
`bytes % args`: the refusals on the argument path, `%c`, and `%a`.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

set_option linter.unusedSimpArgs false

/-! ## The refusals on the argument path -/

/-- `getnextarg` past the end of the tuple, and with a single argument that is not a tuple, is
"not enough arguments" with the count it had (bytesobject.c:421-424); an argument left over is
"not all arguments converted" with both counts (:1145-1151); a `*` takes an int (:781-784) of
`Py_ssize_t` range as a width (:785-797) and of `int` range as a precision (:840-848), and each
refusal names the argument by its 1-based position through `FORMAT_ERROR`. Hypothesis of the first,
third and fourth: an argument of fewer than `2^44` bytes. -/
def FormatArgErrors : Prop :=
  (∀ (x : Obj) (sx : Seq), bytesLikeArg x = some sx → (sx.length : Int) < 2 ^ 44 →
    bytesMod (asc "%b%b") (.tuple [x]) =
      .error (.typeError "not enough arguments for format string (got 1)")) ∧
  (bytesMod (asc "%b") (.tuple []) = .error (.typeError "not enough arguments for format string (got 0)")) ∧
  (∀ (s : Seq), (s.length : Int) < 2 ^ 44 →
    bytesMod (asc "%b%b") (.bytes s) =
      .error (.typeError "not enough arguments for format string (got 1)")) ∧
  (∀ (x y : Obj) (sx : Seq), bytesLikeArg x = some sx → (sx.length : Int) < 2 ^ 44 →
    bytesMod (asc "%b") (.tuple [x, y]) =
      .error (.typeError "not all arguments converted during bytes formatting (required 1, got 2)")) ∧
  (∀ (w : Int) (x : Obj), (w ≤ ssizeMin ∨ w > ssizeMax) →
    bytesMod (asc "%*b") (.tuple [.int w, x]) =
      .error (.overflowError "format argument 1: too big for width")) ∧
  (∀ (p : Int) (x : Obj), (p < -2147483648 ∨ p > 2147483647) →
    bytesMod (asc "%.*b") (.tuple [.int p, x]) =
      .error (.overflowError "format argument 1: too big for precision")) ∧
  (∀ (v x : Obj), v.longValue? = none →
    bytesMod (asc "%*b") (.tuple [v, x]) =
      .error (.typeError s!"format argument 1: * requires int, not {v.typeName}"))

theorem asc_pb : asc "%b" = [37, 98] := by decide
theorem asc_pbpb : asc "%b%b" = [37, 98, 37, 98] := by decide

theorem formatArgErrors_proven : FormatArgErrors := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x sx hx hl
    have fx := formatObj_of_bytesLike x sx hx
    have e1 : (-1 : Int) < sx.length := by omega
    rw [asc_pbpb]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg, fx,
      bind, Except.bind, pure, Except.pure]
    rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, fieldAlloc]; omega)]
    simp [signStep, fieldAlloc, e1, fieldWrites_self, hasPrefix]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw]
    rfl
  · rw [asc_pb]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw]
    rfl
  · intro s hl
    have e1 : (-1 : Int) < s.length := by omega
    rw [asc_pbpb]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      formatObj, bind, Except.bind, pure, Except.pure]
    rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, fieldAlloc]; omega)]
    simp [signStep, fieldAlloc, e1, fieldWrites_self, hasPrefix]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw]
    rfl
  · intro x y sx hx hl
    have fx := formatObj_of_bytesLike x sx hx
    have e1 : (-1 : Int) < sx.length := by omega
    rw [asc_pb]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg, fx,
      bind, Except.bind, pure, Except.pure]
    rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, fieldAlloc]; omega)]
    simp [signStep, fieldAlloc, e1, fieldWrites_self, hasPrefix]
    rw [formatLoop]
    simp [throw, throwThe, MonadExcept.throw]
    rfl
  · intro w x hw
    rw [asc_psb]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      starWidth, Obj.longValue?, hw, formatError, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExcept.throw]
    rfl
  · intro p x hp
    rw [asc_pdsb]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      starPrec, Obj.longValue?, hp, formatError, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExcept.throw]
    rfl
  · intro v x hv
    rw [asc_psb]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      starWidth, hv, formatError, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExcept.throw]
    rfl

/-! ## `%c` and `%a` -/

/-- `%c` writes the byte of an int in `range(256)` and of a bytes or bytearray of length 1
(`byte_converter`, :513-557) through the fast path (:1000-1004), and pads it to a `*` width through
the field writer. An int outside the range is the `OverflowError`, naming the argument by position
in a tuple and by no position for a single argument. Hypothesis of the width: below `2^44`. -/
def FormatChar : Prop :=
  (∀ n : Int, 0 ≤ n → n ≤ 255 → bytesMod (asc "%c") (.tuple [.int n]) = .ok [n.toNat]) ∧
  (∀ b : Nat, bytesMod (asc "%c") (.tuple [.bytes [b]]) = .ok [b] ∧
    bytesMod (asc "%c") (.tuple [.bytearray [b]]) = .ok [b]) ∧
  (∀ n : Int, (n < 0 ∨ n > 255) → bytesMod (asc "%c") (.tuple [.int n]) =
    .error (.overflowError "format argument 1: %c argument not in range(256)")) ∧
  (∀ n : Int, (n < 0 ∨ n > 255) → bytesMod (asc "%c") (.int n) =
    .error (.overflowError "format argument: %c argument not in range(256)")) ∧
  (∀ (w n : Int), 0 ≤ w → w < 2 ^ 44 → 0 ≤ n → n ≤ 255 →
    bytesMod (asc "%*c") (.tuple [.int w, .int n]) = .ok (List.replicate (w.toNat - 1) 32 ++ [n.toNat]))

theorem asc_pc : asc "%c" = [37, 99] := by decide
theorem asc_psc : asc "%*c" = [37, 42, 99] := by decide

theorem formatChar_proven : FormatChar := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n h1 h2
    rw [asc_pc]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      byteConverter, Obj.index?, h1, h2, isIntConv, isFloatConv, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [writerFinish, writerFinishSize, bytesSizeCheck, mallocFails, bytesObjectSize, ssizeMax_val]
  · intro b
    constructor <;>
    · rw [asc_pc]
      simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
        writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
      rw [formatLoop]
      simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
        byteConverter, isIntConv, isFloatConv, bind, Except.bind, pure, Except.pure]
      rw [formatLoop]
      simp [writerFinish, writerFinishSize, bytesSizeCheck, mallocFails, bytesObjectSize, ssizeMax_val]
  · intro n h
    rw [asc_pc]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      byteConverter, Obj.index?, formatError, isIntConv, isFloatConv, h, bind, Except.bind, pure,
      Except.pure]
    rfl
  · intro n h
    rw [asc_pc]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      byteConverter, Obj.index?, formatError, isIntConv, isFloatConv, h, bind, Except.bind, pure,
      Except.pure]
  · intro w n hw1 hw2 h1 h2
    have hwr : ¬ (w ≤ ssizeMin ∨ w > ssizeMax) := by
      simp only [ssizeMin, ssizeMax_val]; omega
    have hw : ¬ w < 0 := by omega
    have hW : (1 : Int) ≤ max w 1 := by omega
    have hA := fieldAllocExact_proven {} 99 32 0 (max w 1) 1 [n.toNat] (Or.inl rfl) (by omega)
      (by simp) hW (by simp [hasPrefix])
    rw [asc_psc]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      starWidth, Obj.longValue?, hwr, hw, byteConverter, Obj.index?, h1, h2, isIntConv, isFloatConv, bind, Except.bind, pure,
      Except.pure]
    rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, fieldAlloc]; split <;> omega)]
    have hwn : w ≠ -1 := by omega
    simp only [signStep, Bool.false_eq_true, ite_false, hwn]
    rw [formatLoop]
    simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
      Int.reduceSub, List.nil_append]
    have hm : (if w < (1 : Int) then (1 : Int) else w) = max w 1 := by split <;> omega
    rw [hm]
    rw [writerFinish_growIf _ _ _ (by simp) (by simp) (by simp [fieldAlloc]; omega)
      (by simp [fieldAlloc]; omega) (by rw [hA]; simp [fieldAlloc]; split <;> omega)]
    rw [fieldWrites_space _ _ _ _ _ _ (by simp [hasPrefix]) (by omega) hW]
    have hn : (max w 1 - 1).toNat = w.toNat - 1 := by omega
    simp [hn]

/-- `%a` and `%r` write `ascii(x)` (`PyObject_ASCII`, :897-907), and keep its exception.
Hypothesis: the text has fewer than `2^44` bytes. -/
def FormatAscii : Prop :=
  (∀ (x : Obj) (t : Seq), asciiObj 8 x = .ok t → (t.length : Int) < 2 ^ 44 →
    bytesMod (asc "%a") (.tuple [x]) = .ok t ∧ bytesMod (asc "%r") (.tuple [x]) = .ok t) ∧
  (∀ (x : Obj) (e : PyExc), asciiObj 8 x = .error e →
    bytesMod (asc "%a") (.tuple [x]) = .error e ∧ bytesMod (asc "%r") (.tuple [x]) = .error e)

theorem asc_pa : asc "%a" = [37, 97] := by decide
theorem asc_pr : asc "%r" = [37, 114] := by decide

theorem formatAscii_proven : FormatAscii := by
  refine ⟨?_, ?_⟩
  · intro x t ht hl
    have e1 : (-1 : Int) < t.length := by omega
    constructor
    all_goals
      first | rw [asc_pa] | rw [asc_pr]
      simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
        writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
      rw [formatLoop]
      simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg, ht,
        bind, Except.bind, pure, Except.pure]
      rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, fieldAlloc]; omega)]
      simp [signStep, fieldAlloc, e1, fieldWrites_self, hasPrefix]
      rw [formatLoop]
      simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE]
      apply writerFinish_growIf
      · simp
      · simp
      · omega
      · simp; omega
      · simp; split <;> omega
  · intro x e he
    constructor
    all_goals
      first | rw [asc_pa] | rw [asc_pr]
      simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
        writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
      rw [formatLoop]
      simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg, he,
        bind, Except.bind, pure, Except.pure]

end PyLean.BytesObj.Bytes
