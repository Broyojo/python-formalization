import PyLean.BytesObj.Bytes.FormatProps7

/-!
`bytes % args`: the mapping key, the digit limits of the width and the precision, and
`bytes_mod`'s `NotImplemented`.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

set_option linter.unusedSimpArgs false

/-- The value a dict with bytes keys has for `key`, as `PyObject_GetItem` finds it. -/
def dictLookup (kv : List (Seq × Obj)) (key : Seq) : Option Obj := (kv.find? (fun p => p.1 == key)).map (·.2)

/-- `%(key)b` looks the key up in the mapping (bytesobject.c:702-745): the key is the bytes between
the balanced parentheses, `ab` in `%(ab)b`, empty in `%()b`, and `(x)` in `%((x))b`; a missing key
is the mapping's `KeyError`. A right operand that is no mapping is refused with its type (:707-711).
Once a key was used, a specifier without one is refused (:748-754), and a `*` with one is refused
(:772-778). Hypothesis: the value has fewer than `2^44` bytes. -/
def FormatMapping : Prop :=
  (∀ (kv : List (Seq × Obj)) (v : Obj) (sv : Seq), dictLookup kv (asc "ab") = some v →
    bytesLikeArg v = some sv → (sv.length : Int) < 2 ^ 44 →
    bytesMod (asc "%(ab)b") (.dict kv) = .ok sv) ∧
  (∀ (kv : List (Seq × Obj)) (v : Obj) (sv : Seq), dictLookup kv [] = some v →
    bytesLikeArg v = some sv → (sv.length : Int) < 2 ^ 44 →
    bytesMod (asc "%()b") (.dict kv) = .ok sv) ∧
  (∀ (kv : List (Seq × Obj)) (v : Obj) (sv : Seq), dictLookup kv (asc "(x)") = some v →
    bytesLikeArg v = some sv → (sv.length : Int) < 2 ^ 44 →
    bytesMod (asc "%((x))b") (.dict kv) = .ok sv) ∧
  (∀ (kv : List (Seq × Obj)), dictLookup kv (asc "ab") = none →
    ∃ m, bytesMod (asc "%(ab)b") (.dict kv) = .error (.keyError m)) ∧
  (∀ (args : Obj), asMapping args = none →
    bytesMod (asc "%(a)b") args = .error (.typeError s!"format requires a mapping, not {args.typeName}")) ∧
  (∀ (kv : List (Seq × Obj)) (v : Obj) (sv : Seq), dictLookup kv (asc "a") = some v →
    bytesLikeArg v = some sv → (sv.length : Int) < 2 ^ 44 →
    bytesMod (asc "%(a)b%b") (.dict kv) =
      .error (.valueError "format requires a parenthesised mapping key at position 5")) ∧
  (∀ (kv : List (Seq × Obj)) (v : Obj), dictLookup kv (asc "a") = some v →
    bytesMod (asc "%(a)*b") (.dict kv) =
      .error (.valueError "* cannot be used with a parenthesised mapping key at position 0"))

theorem mappingGet_dict (kv : List (Seq × Obj)) (key : Seq) (v : Obj) (h : dictLookup kv key = some v) :
    mappingGet (.dict kv) key = .ok v := by
  unfold dictLookup at h
  cases hf : kv.find? (fun p => p.1 == key) with
  | none => simp [hf] at h
  | some p =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    simp [mappingGet, hf, h]

theorem mappingGet_none (kv : List (Seq × Obj)) (key : Seq) (h : dictLookup kv key = none) :
    mappingGet (.dict kv) key = .error (.keyError ("~" ++ String.ofList (key.map Char.ofNat))) := by
  unfold dictLookup at h
  cases hf : kv.find? (fun p => p.1 == key) with
  | none => simp [mappingGet, hf]
  | some p => simp [hf] at h

theorem asc_kab : asc "%(ab)b" = [37, 40, 97, 98, 41, 98] := by decide
theorem asc_k0 : asc "%()b" = [37, 40, 41, 98] := by decide
theorem asc_kx : asc "%((x))b" = [37, 40, 40, 120, 41, 41, 98] := by decide
theorem asc_ka : asc "%(a)b" = [37, 40, 97, 41, 98] := by decide
theorem asc_kab2 : asc "%(a)b%b" = [37, 40, 97, 41, 98, 37, 98] := by decide
theorem asc_kas : asc "%(a)*b" = [37, 40, 97, 41, 42, 98] := by decide
theorem asc_ab : asc "ab" = [97, 98] := by decide
theorem asc_x : asc "(x)" = [40, 120, 41] := by decide
theorem asc_a : asc "a" = [97] := by decide

theorem formatMapping_proven : FormatMapping := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro kv v sv hk hv hl
    rw [asc_ab] at hk
    have fv := formatObj_of_bytesLike v sv hv
    have hg := mappingGet_dict kv _ v hk
    have e1 : (-1 : Int) < sv.length := by omega
    rw [asc_kab]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, keyLoop, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      fv, hg, bind, Except.bind, pure, Except.pure]
    rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, fieldAlloc]; omega)]
    simp [signStep, fieldAlloc, e1, fieldWrites_self, hasPrefix]
    rw [formatLoop]
    simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
      Int.reduceSub, List.nil_append]
    apply writerFinish_growIf
    · simp
    · simp
    · omega
    · simp; omega
    · simp; split <;> omega
  · intro kv v sv hk hv hl
    skip
    have fv := formatObj_of_bytesLike v sv hv
    have hg := mappingGet_dict kv _ v hk
    have e1 : (-1 : Int) < sv.length := by omega
    rw [asc_k0]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, keyLoop, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      fv, hg, bind, Except.bind, pure, Except.pure]
    rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, fieldAlloc]; omega)]
    simp [signStep, fieldAlloc, e1, fieldWrites_self, hasPrefix]
    rw [formatLoop]
    simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
      Int.reduceSub, List.nil_append]
    apply writerFinish_growIf
    · simp
    · simp
    · omega
    · simp; omega
    · simp; split <;> omega
  · intro kv v sv hk hv hl
    rw [asc_x] at hk
    have fv := formatObj_of_bytesLike v sv hv
    have hg := mappingGet_dict kv _ v hk
    have e1 : (-1 : Int) < sv.length := by omega
    rw [asc_kx]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, keyLoop, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      fv, hg, bind, Except.bind, pure, Except.pure]
    rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, fieldAlloc]; omega)]
    simp [signStep, fieldAlloc, e1, fieldWrites_self, hasPrefix]
    rw [formatLoop]
    simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
      Int.reduceSub, List.nil_append]
    apply writerFinish_growIf
    · simp
    · simp
    · omega
    · simp; omega
    · simp; split <;> omega
  · intro kv hk
    rw [asc_ab] at hk
    have hg := mappingGet_none kv _ hk
    refine ⟨"~" ++ String.ofList ([97, 98].map Char.ofNat), ?_⟩
    rw [asc_kab]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, keyLoop, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      hg, bind, Except.bind, pure, Except.pure]
  · intro args ha
    rw [asc_ka]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, ha, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, bind, Except.bind, pure, Except.pure]
    rfl
  · intro kv v sv hk hv hl
    rw [asc_a] at hk
    have fv := formatObj_of_bytesLike v sv hv
    have hg := mappingGet_dict kv _ v hk
    have e1 : (-1 : Int) < sv.length := by omega
    rw [asc_kab2]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, keyLoop, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      fv, hg, bind, Except.bind, pure, Except.pure]
    rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, fieldAlloc]; omega)]
    simp [signStep, fieldAlloc, e1, fieldWrites_self, hasPrefix]
    rw [formatLoop]
    simp [formatSpec, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw]
    rfl
  · intro kv v hk
    rw [asc_a] at hk
    have hg := mappingGet_dict kv _ v hk
    rw [asc_kas]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, keyLoop, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg,
      hg, starKey, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw]
    rfl

/-! ## The digit limits of the width and the precision -/

/-- A width is parsed in `Py_ssize_t` (bytesobject.c:805-818): `PY_SSIZE_T_MAX` itself is a width
(which the writer then cannot allocate: `MemoryError`), one more is `width too big`; a precision is parsed in
`int` (:855-868): `INT_MAX` is a precision, one more is `precision too big`. Both are refused before
any argument is looked at. Hypothesis of the second: an argument of fewer than `2^44` bytes; of the
fourth: one of at most `INT_MAX` bytes, so that the precision does not cut it. -/
def FormatDigitLimits : Prop :=
  (∀ x : Obj, bytesMod (asc "%9223372036854775808b") (.tuple [x]) =
    .error (.valueError "width too big at position 0")) ∧
  (∀ (x : Obj) (sx : Seq), bytesLikeArg x = some sx → (sx.length : Int) < 2 ^ 44 →
    bytesMod (asc "%9223372036854775807b") (.tuple [x]) = .error memoryError) ∧
  (∀ x : Obj, bytesMod (asc "%.2147483648b") (.tuple [x]) =
    .error (.valueError "precision too big at position 0")) ∧
  (∀ (x : Obj) (sx : Seq), bytesLikeArg x = some sx → (sx.length : Int) ≤ 2147483647 →
    bytesMod (asc "%.2147483647b") (.tuple [x]) = .ok sx)

theorem asc_w1 : asc "%9223372036854775808b" = [37, 57, 50, 50, 51, 51, 55, 50, 48, 51, 54, 56, 53, 52, 55, 55, 53, 56, 48, 56, 98] := by decide
theorem asc_w0 : asc "%9223372036854775807b" = [37, 57, 50, 50, 51, 51, 55, 50, 48, 51, 54, 56, 53, 52, 55, 55, 53, 56, 48, 55, 98] := by decide
theorem asc_p1 : asc "%.2147483648b" = [37, 46, 50, 49, 52, 55, 52, 56, 51, 54, 52, 56, 98] := by decide
theorem asc_p0 : asc "%.2147483647b" = [37, 46, 50, 49, 52, 55, 52, 56, 51, 54, 52, 55, 98] := by decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
theorem formatDigitLimits_proven : FormatDigitLimits := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [asc_w1]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, digitsLoop, ssizeMax_val,
      bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw]
    rfl
  · intro x sx hx hl
    have fx := formatObj_of_bytesLike x sx hx
    rw [asc_w0]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, digitsLoop,
      ssizeMax_val, getNextArg, fx, bind, Except.bind, pure, Except.pure]
    have h1 : ¬ ((9223372036854775807 : Int) < sx.length) := by omega
    simp [writeField, signStep, fieldAlloc, h1, writerGrow, ssizeMax_val, bind, Except.bind, pure,
      Except.pure]
  · intro x
    rw [asc_p1]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, digitsLoop, intMax,
      bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw]
    rfl
  · intro x sx hx hl
    have fx := formatObj_of_bytesLike x sx hx
    have e1 : (-1 : Int) < sx.length := by omega
    have h2 : ¬ ((2147483647 : Int) < sx.length) := by omega
    rw [asc_p0]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw,
      writerAllocated, smallBufferSize, asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, digitsLoop, intMax,
      getNextArg, fx, h2, bind, Except.bind, pure, Except.pure]
    rw [writeField_eq' _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp [signStep, fieldAlloc]; omega)]
    simp [signStep, fieldAlloc, e1, fieldWrites_self, hasPrefix]
    rw [formatLoop]
    simp only [ge_iff_le, Int.reduceNeg, Int.le_refl, not_true_eq_false, ite_false, Int.reduceLE,
      Int.reduceSub, List.nil_append]
    apply writerFinish_growIf
    · simp
    · simp
    · omega
    · simp; omega
    · simp; split <;> omega

/-! ## `bytes_mod` -/

/-- `bytes_mod(self, arg)` (bytesobject.c:2842-2850) answers `NotImplemented` for every `self` that
is not a bytes object, a bytearray and a buffer included, which is what `x % b` reaches with the
bytes on the right; for a bytes `self` it formats `self` with `arg`. -/
def BytesModNotImpl : Prop :=
  (∀ (self arg : Obj), (∀ s, self ≠ .bytes s) → bytesModObj self arg = .ok none) ∧
  (∀ (s : Seq) (arg : Obj), bytesModObj (.bytes s) arg = (bytesFormatEx s arg false).map some)

theorem bytesModNotImpl_proven : BytesModNotImpl := by
  refine ⟨?_, ?_⟩
  · intro self arg h
    cases self <;> simp [bytesModObj]
    exact absurd rfl (h _)
  · intro s arg
    simp only [bytesModObj]
    cases bytesFormatEx s arg false <;> rfl

/-! ## The fast path has no `INT_MAX` guard -/

/-- `FastSlowLong` without its hypothesis: for every int, the fast path of `%d %i %u %o %x`
(`_PyLong_FormatBytesWriter`, bytesobject.c:924-957) and the general path through `formatlong` give
the same text. -/
def FastSlowLongAll : Prop :=
  ∀ (v : Int) (c : Int) (alt : Bool), (c = 100 ∨ c = 105 ∨ c = 117 ∨ c = 111 ∨ c = 120) →
    fastLong v c alt = slowLong v c alt

theorem toDigits_len_ge (b : Nat) (hb : 1 < b) : ∀ (k n : Nat), b ^ k ≤ n → k + 1 ≤ (Nat.toDigits b n).length := by
  intro k
  induction k with
  | zero => intro n _; have := Nat.toDigits_ne_nil (b := b) (n := n); cases h : Nat.toDigits b n <;> simp_all
  | succ k ih =>
    intro n hn
    have hbn : b ≤ n := by
      have : b ^ 1 ≤ b ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      simp at this; omega
    rw [Nat.toDigits_eq_if hb]
    rw [if_neg (by omega)]
    simp only [List.length_append, List.length_cons, List.length_nil]
    have : b ^ k ≤ n / b := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      rw [Nat.pow_succ] at hn
      exact hn
    have := ih (n / b) this
    omega

/-- The counterexample: `16 ** 2**31` has `2**31 + 1` hex digits, so `b'%x' % v` is written by the
fast path while `formatlong` refuses the text of `PyNumber_ToBase` (`0x` and the digits, more than
`INT_MAX` bytes) with `string too large in _PyUnicode_FormatLong` (unicode_format.c:247-251). -/
theorem fastSlowLongAll_refuted : ¬ FastSlowLongAll := by
  intro h
  obtain ⟨N, hN2⟩ : ∃ N : Nat, 2147483647 ≤ N := ⟨2147483647, Nat.le_refl _⟩
  have hv := h ((16 : Int) ^ N) 120 false (by simp)
  have hlen : N + 1 ≤ (Nat.toDigits 16 (16 ^ N)).length := toDigits_len_ge 16 (by decide) N _ (Nat.le_refl _)
  have hpos : ¬ ((16 : Int) ^ N < 0) := by
    have h16 : (0 : Int) ≤ 16 := by decide
    exact Int.not_lt.mpr (Int.pow_nonneg h16)
  have hna : ((16 : Int) ^ N).natAbs = 16 ^ N := by simp [Int.natAbs_pow]
  have h1 : ¬ ((-1 : Int) > intMax - 3) := by decide
  have h2 : intMax < ((asc "0x").length : Int) + ((digitsBase 16 (16 ^ N)).length : Int) := by
    simp only [digitsBase, List.length_map]
    have : (asc "0x").length = 2 := by decide
    rw [this]; unfold intMax; omega
  simp only [fastLong, slowLong, formatLong, Obj.longValue?, unicodeFormatLong, numberToBase, longBase,
    hpos, hna, ite_false, bind, Except.bind, pure, Except.pure] at hv
  simp [h1, h2, hpos, throw, throwThe, MonadExcept.throw] at hv

end PyLean.BytesObj.Bytes
