import PyLean.Sequences.HalfTrip
import PyLean.Sequences.ArrayFloat
import PyLean.Sequences.ArrayText

/-!
Properties of the `e`, `f`, `d`, `Zf` and `Zd` items of `array.array`
(`Modules/arraymodule.c:618-739`, CPython 3.15.2).
-/

namespace PyLean.Sequences

open PyLean

/-! ### Every stored pattern reads and stores back -/

/-- For every bit pattern an `e`, `f`, `d`, `Zf` or `Zd` item can hold (`frombytes` stores any),
`a[i]` reads it as a float (a complex for `Zf`, `Zd`) by the C conversion of the getitem, and
`a[i] = a[i]` stores the same pattern back, except that a signalling NaN of `e` or `f` (or of a
part of `Zf`) comes back with its quiet bit set: `e_setitem` and `f_setitem` narrow through a C
`float` (`(float)PyFloat_AsDouble(v)`, Python/getargs.c:922-930), and the hardware conversion
quiets a signalling NaN and keeps its payload. A `d` or `Zd` item comes back unchanged,
signalling NaNs included. Covers `e_getitem` (:618-624, `PyFloat_Unpack2`), `e_setitem`
(:627-641, `PyFloat_Pack2` of the promoted `float`), `f_getitem`/`f_setitem` (:644-661),
`d_getitem`/`d_setitem` (:664-681), `cf_getitem`/`cf_setitem` (:684-710) and
`cd_getitem`/`cd_setitem` (:713-739). -/
def ArrayFloatRoundTrip : Prop :=
  (∀ h : Nat, h < 65536 → tcGetitem .e h = .ok (.float (halfToDouble h)) ∧
    tcSetitem .e true (.float (halfToDouble h)) = .ok (quiet16 h : Nat)) ∧
  (∀ b : Nat, b < 4294967296 → tcGetitem .f b = .ok (.float (floatToDouble b)) ∧
    tcSetitem .f true (.float (floatToDouble b)) = .ok (quiet32 b : Nat)) ∧
  (∀ b : Nat, b < 18446744073709551616 → tcGetitem .d b = .ok (.float b) ∧
    tcSetitem .d true (.float b) = .ok (b : Nat)) ∧
  (∀ x : Nat, x < 18446744073709551616 →
    tcGetitem .Zf x = .ok (.complex (floatToDouble (x % 4294967296)) (floatToDouble (x / 4294967296))) ∧
    tcSetitem .Zf true (.complex (floatToDouble (x % 4294967296)) (floatToDouble (x / 4294967296))) =
      .ok (quiet32 (x % 4294967296) + 4294967296 * quiet32 (x / 4294967296) : Nat)) ∧
  (∀ x : Nat, x < 340282366920938463463374607431768211456 →
    tcGetitem .Zd x = .ok (.complex (x % 18446744073709551616) (x / 18446744073709551616)) ∧
    tcSetitem .Zd true (.complex (x % 18446744073709551616) (x / 18446744073709551616)) = .ok (x : Nat))

theorem arrayFloatRoundTrip_proven : ArrayFloatRoundTrip := by
  refine ⟨fun h hh => ⟨?_, ?_⟩, fun b hb => ⟨?_, ?_⟩, fun b hb => ⟨?_, ?_⟩, fun x hx => ⟨?_, ?_⟩,
    fun x hx => ⟨?_, ?_⟩⟩
  · simp [tcGetitem]
  · have := eTrip_all h hh
    unfold eTrip at this
    simp only [tcSetitem, asDouble, bind, Except.bind, Bool.not_true, Bool.false_eq_true, if_false,
      pure, Except.pure, this]
  · simp [tcGetitem]
  · simp only [tcSetitem, asDouble, bind, Except.bind, Bool.not_true, Bool.false_eq_true, if_false,
      pure, Except.pure, fTrip b hb]
  · simp [tcGetitem]
  · simp only [tcSetitem, asDouble, bind, Except.bind, Bool.not_true, Bool.false_eq_true, if_false,
      pure, Except.pure]
  · simp [tcGetitem]
  · simp only [tcSetitem, asComplex, bind, Except.bind, Bool.not_true, Bool.false_eq_true, if_false,
      pure, Except.pure, fTrip _ (Nat.mod_lt _ (by decide)), fTrip (x / 4294967296) (by omega)]
  · simp [tcGetitem]
  · simp only [tcSetitem, asComplex, bind, Except.bind, Bool.not_true, Bool.false_eq_true, if_false,
      pure, Except.pure, Except.ok.injEq]
    omega

/-- `ArrayFloatItems` (ArrayText.lean) said that every `f` pattern reads and stores back
unchanged. Refuted by the signalling NaN `0x7f800001`, which comes back as `0x7fc00001`. The
exact statement is `ArrayFloatRoundTrip`. -/
theorem arrayFloatItems_refuted : ¬ ArrayFloatItems := by
  intro h
  obtain ⟨v, h1, h2⟩ := h.1 2139095041 (by decide)
  have e1 : tcGetitem .f (2139095041 : Nat) = .ok (.float (floatToDouble 2139095041)) := by simp [tcGetitem]
  rw [e1] at h1
  cases h1
  have e2 := (arrayFloatRoundTrip_proven.2.1 2139095041 (by decide)).2
  rw [e2] at h2
  have : quiet32 2139095041 = 2143289345 := by decide
  rw [this] at h2
  simp at h2

/-! ### The `struct` twins -/

/-- `array('e', [x]).tobytes() == struct.pack('<e', x)` for every float `x`, including the
`OverflowError`: both store a binary16, and `struct` calls `PyFloat_Pack2(x)` on the double
(Modules/_struct.c `pack_halffloat`; `Binary64.PyFloat_Pack2` is the mirror of
Objects/floatobject.c:1895-2000). Doc/library/array.rst:74-79 gives the item type as
`_Float16`, to which C converts a double with one correct rounding.

Refuted: `e_setitem` parses the value with `PyArg_Parse(v, "f")` (arraymodule.c:629-630), so the
double is first rounded to a C `float`, then `PyFloat_Pack2` rounds that again. For
`x = 1 + 2**-11 + 2**-40` the first rounding lands on the binary16 tie `1 + 2**-11`, which
rounds to even, `1.0`; `struct` gives the nearest binary16, `1 + 2**-10`. -/
def ArrayHalfStruct : Prop :=
  ∀ x : Nat, x < 18446744073709551616 →
    (tcSetitem .e true (.float x)).map (fun h => itemBytes .e h) =
      Binary64.PyFloat_Pack2 (Binary64.F64.ofBits x) true

set_option maxRecDepth 20000 in
theorem arrayHalfStruct_refuted : ¬ ArrayHalfStruct := by
  intro h
  have := h 0x3ff0020000001000 (by decide)
  have e1 : (tcSetitem .e true (.float 0x3ff0020000001000)).map (fun h => itemBytes .e h) = .ok [0, 60] := by
    decide +kernel
  have e2 : Binary64.PyFloat_Pack2 (Binary64.F64.ofBits 0x3ff0020000001000) true = .ok [1, 60] := by
    decide +kernel
  rw [e1, e2] at this
  simp at this

/-- `array('f', [x]).tobytes() == struct.pack('<f', x)` for every float `x`: both store a
binary32, and `struct` calls `PyFloat_Pack4(x)` (`Binary64.PyFloat_Pack4`, the mirror of
Objects/floatobject.c:2003-2066), which raises `OverflowError` for a finite `x` that rounds to
infinity and keeps a signalling NaN signalling.

Refuted: `f_setitem` stores `(float)PyFloat_AsDouble(v)` (arraymodule.c:650-661), so
`x = 1e300` becomes `inf` where `struct` raises. -/
def ArraySingleStruct : Prop :=
  ∀ x : Nat, x < 18446744073709551616 →
    (tcSetitem .f true (.float x)).map (fun b => itemBytes .f b) =
      Binary64.PyFloat_Pack4 (Binary64.F64.ofBits x) true

set_option maxRecDepth 20000 in
theorem arraySingleStruct_refuted : ¬ ArraySingleStruct := by
  intro h
  have := h 0x7e37e43c8800759c (by decide)
  have e1 : (tcSetitem .f true (.float 0x7e37e43c8800759c)).map (fun b => itemBytes .f b) =
      .ok [0, 0, 128, 127] := by
    decide +kernel
  have e2 : Binary64.PyFloat_Pack4 (Binary64.F64.ofBits 0x7e37e43c8800759c) true =
      .error (.overflowError "float too large to pack with f format") := by
    decide +kernel
  rw [e1, e2] at this
  simp at this

/-! ### The argument conversions -/

/-- The setitems of the float and complex typecodes on every object `v` (ints, floats, complex
numbers, strs, and instances of user classes with any `__float__`, `__index__` and `__complex__`,
which may raise or return objects of any class):
* `d_setitem` stores `PyFloat_AsDouble(v)`, `f_setitem` its rounding to binary32, `e_setitem`
  `PyFloat_Pack2` of that binary32 (the two roundings of `ArrayHalfStruct`); `cd_setitem` stores
  the two parts of `PyComplex_AsCComplex(v)`, `cf_setitem` each rounded to binary32. A failed
  conversion raises its exception, the same one for every typecode, before the index is checked
  (`CHECK_ARRAY_BOUNDS` comes after `PyArg_Parse`).
* `PyFloat_AsDouble` (Doc/c-api/float.rst:45-55): a float, or an instance of a float subclass,
  is its value without a call of `__float__`; otherwise `__float__` is called and must return a
  float (a float subclass after a `DeprecationWarning`, which raises when warnings are errors;
  anything else is `TypeError`; its exception propagates); an int converts with
  `OverflowError` past the binary64 range; without `__float__` the class's `__index__` is used;
  without either, `TypeError("must be real number, not T")`.
* `PyComplex_AsCComplex` (Doc/c-api/complex.rst:105-120): a complex or complex-subclass
  instance is its value; otherwise `__complex__` comes first, and an object without it is the
  real number `PyFloat_AsDouble(v)` with imaginary part `+0.0`, with the same exception. -/
def ArrayFloatConv : Prop :=
  -- the five setitems, one conversion each, then the narrowing
  (∀ v, tcSetitem .d true v = (asDouble v).map (fun x => (x : Int))) ∧
  (∀ v, tcSetitem .f true v = (asDouble v).map (fun x => (doubleToFloat x : Int))) ∧
  (∀ v, tcSetitem .f true v = (tcSetitem .d true v).map (fun x => (doubleToFloat x.toNat : Int))) ∧
  (∀ v, tcSetitem .e true v =
    (tcSetitem .f true v >>= fun y => (packHalf (floatToDouble y.toNat)).map (fun h => (h : Int)))) ∧
  (∀ v, tcSetitem .Zd true v = (asComplex v).map (fun p => ((p.1 + 18446744073709551616 * p.2 : Nat) : Int))) ∧
  (∀ v, tcSetitem .Zf true v =
    (asComplex v).map (fun p => ((doubleToFloat p.1 + 4294967296 * doubleToFloat p.2 : Nat) : Int))) ∧
  (∀ tc v e, (tc = .e ∨ tc = .f ∨ tc = .d) → asDouble v = .error e →
    tcSetitem tc true v = .error e ∧ tcSetitem tc false v = .error e) ∧
  (∀ tc v e, (tc = .Zf ∨ tc = .Zd) → asComplex v = .error e →
    tcSetitem tc true v = .error e ∧ tcSetitem tc false v = .error e) ∧
  (∀ tc v x, (tc = .e ∨ tc = .f ∨ tc = .d) → asDouble v = .ok x →
    tcSetitem tc false v = .error (.indexError "array assignment index out of range")) ∧
  -- `PyFloat_AsDouble`, object by object
  (∀ b, asDouble (.float b) = .ok b) ∧
  (∀ n, asDouble (.int n) = longAsDouble n) ∧
  (∀ t b flt idx cpx, asDouble (.user t (.float b) flt idx cpx) = .ok b) ∧
  (∀ t base r idx cpx, (∀ b, base ≠ .float b) → asDouble (.user t base (some r) idx cpx) = retFloat t r) ∧
  (∀ t n idx cpx, asDouble (.user t (.int n) none idx cpx) = longAsDouble n) ∧
  (∀ t base r cpx, (base = .plain ∨ ∃ re im, base = .complex re im) →
    asDouble (.user t base none (some r) cpx) = (retIndex t r >>= longAsDouble)) ∧
  (∀ t base cpx, (base = .plain ∨ ∃ re im, base = .complex re im) →
    asDouble (.user t base none none cpx) = .error (.typeError s!"must be real number, not {t}")) ∧
  (∀ re im, asDouble (.complex re im) = .error (.typeError "must be real number, not complex")) ∧
  (∀ cs, asDouble (.str cs) = .error (.typeError "must be real number, not str")) ∧
  -- what `__float__` returned
  (∀ t b, retFloat t (.float b) = .ok b) ∧
  (∀ t u b, retFloat t (.floatSub u b none) = .ok b) ∧
  (∀ t u b e, retFloat t (.floatSub u b (some e)) = .error e) ∧
  (∀ t e, retFloat t (.raises e) = .error e) ∧
  (∀ t n, retFloat t (.int n) = .error (.typeError s!"{t}.__float__() must return a float, not {(Ret.int n).tname}")) ∧
  (∀ t u, retFloat t (.other u) = .error (.typeError s!"{t}.__float__() must return a float, not {u}")) ∧
  -- `int` to `double`: exact below 2**53, `OverflowError` exactly when it rounds past the range
  (∀ n : Int, n.natAbs < 9007199254740992 → ∃ b, longAsDouble n = .ok b) ∧
  (longAsDouble (2 ^ 1024) = .error (.overflowError "int too large to convert to float")) ∧
  -- `PyComplex_AsCComplex`, object by object
  (∀ re im, asComplex (.complex re im) = .ok (re, im)) ∧
  (∀ t re im flt idx cpx, asComplex (.user t (.complex re im) flt idx cpx) = .ok (re, im)) ∧
  (∀ t base flt idx r, (∀ re im, base ≠ .complex re im) →
    asComplex (.user t base flt idx (some r)) = retComplex t r) ∧
  (∀ v, (∀ re im, v ≠ .complex re im) → (∀ t base flt idx r, v ≠ .user t base flt idx (some r)) →
    (∀ t re im flt idx, v ≠ .user t (.complex re im) flt idx none) →
    asComplex v = (asDouble v).map (fun x => (x, 0))) ∧
  (∀ t r, (r = .float 0 ∨ r = .int 0 ∨ ∃ u, r = .other u) →
    retComplex t r = .error (.typeError s!"{t}.__complex__() must return a complex, not {r.tname}")) ∧
  (∀ t e, retComplex t (.raises e) = .error e) ∧
  (∀ t u re im e, retComplex t (.complexSub u re im (some e)) = .error e)

theorem arrayFloatConv_proven : ArrayFloatConv := by
  refine ⟨fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_,
    fun tc v e htc he => ?_, fun tc v e htc he => ?_, fun tc v x htc hx => ?_,
    fun _ => rfl, fun _ => rfl, fun _ _ _ _ _ => rfl, fun t base r idx cpx hb => ?_,
    fun _ _ _ _ => rfl, fun t base r cpx hb => ?_, fun t base cpx hb => ?_, fun _ _ => rfl,
    fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun n hn => ?_, ?_, fun _ _ => rfl, fun _ _ _ _ _ _ => rfl,
    fun t base flt idx r hb => ?_, fun v h1 h2 h3 => ?_, fun t r hr => ?_, fun _ _ => rfl,
    fun _ _ _ _ _ => rfl⟩
  · simp only [tcSetitem, bind, Except.bind, pure, Except.pure, Bool.not_true, Bool.false_eq_true, if_false]
    cases asDouble v <;> rfl
  · simp only [tcSetitem, bind, Except.bind, pure, Except.pure, Bool.not_true, Bool.false_eq_true, if_false]
    cases asDouble v <;> rfl
  · simp only [tcSetitem, bind, Except.bind, pure, Except.pure, Bool.not_true, Bool.false_eq_true, if_false]
    cases asDouble v <;> simp [Except.map]
  · simp only [tcSetitem, bind, Except.bind, pure, Except.pure, Bool.not_true, Bool.false_eq_true, if_false]
    cases asDouble v with
    | error e => rfl
    | ok x =>
      simp only [Int.toNat_natCast]
      cases packHalf (floatToDouble (doubleToFloat x)) <;> rfl
  · simp only [tcSetitem, bind, Except.bind, pure, Except.pure, Bool.not_true, Bool.false_eq_true, if_false]
    cases asComplex v <;> rfl
  · simp only [tcSetitem, bind, Except.bind, pure, Except.pure, Bool.not_true, Bool.false_eq_true, if_false]
    cases asComplex v <;> rfl
  · rcases htc with rfl | rfl | rfl <;>
      simp only [tcSetitem, bind, Except.bind, pure, Except.pure, he] <;> trivial
  · rcases htc with rfl | rfl <;>
      simp only [tcSetitem, bind, Except.bind, pure, Except.pure, he] <;> trivial
  · rcases htc with rfl | rfl | rfl <;>
      simp only [tcSetitem, bind, Except.bind, pure, Except.pure, hx, Bool.not_false, if_true, throwE]
  · cases base with
    | float b => exact absurd rfl (hb b)
    | _ => rfl
  · rcases hb with rfl | ⟨re, im, rfl⟩ <;> (simp only [asDouble]; cases retIndex t r <;> rfl)
  · rcases hb with rfl | ⟨re, im, rfl⟩ <;> rfl
  · have hn0 : n = 0 ∨ n ≠ 0 := by omega
    rcases hn0 with rfl | hn0
    · exact ⟨0, rfl⟩
    · have hm : n.natAbs ≠ 0 := by omega
      have hL := bitLength_le n.natAbs 53 hm (by simp only [Nat.reducePow]; omega)
      unfold longAsDouble intToDouble
      rw [if_neg hn0]
      simp only []
      rw [if_pos hL]
      simp only []
      rw [if_neg (by omega)]
      exact ⟨_, rfl⟩
  · decide +kernel
  · cases base with
    | complex re im => exact absurd rfl (hb re im)
    | _ => rfl
  · cases v with
    | complex re im => exact absurd rfl (h1 re im)
    | user t base flt idx cpx =>
      cases cpx with
      | some r => exact absurd rfl (h2 t base flt idx r)
      | none =>
        cases base with
        | complex re im => exact absurd rfl (h3 t re im flt idx)
        | _ => simp only [asComplex]; cases asDouble _ <;> rfl
    | _ => simp only [asComplex]; cases asDouble _ <;> rfl
  · rcases hr with rfl | rfl | ⟨u, rfl⟩ <;> rfl

end PyLean.Sequences
