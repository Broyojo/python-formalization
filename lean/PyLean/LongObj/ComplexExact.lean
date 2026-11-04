import PyLean.LongObj.ComplexNewProps

/-!
Exact statements about `Objects/complexobject.c` (CPython 3.15.2) at the object layer:
the documented hash rule, the cases of the constructors and of `complex.from_number`, and
the branches of `_Py_c_abs`. They hold for every `CDouble` instance, so they are about which
code runs and in what order; the values are those of the operations of the instance.
-/

namespace PyLean.LongObj.Cplx

open CDouble

/-! ## `complex_hash` -/

/-- The numeric hash rule, Doc/builtins/stdtypes.rst:800-805: for a complex `z`, `hash(z.real)
+ sys.hash_info.imag * hash(z.imag)` reduced modulo `2**64` into `range(-2**63, 2**63)`, with
`-1` replaced by `-2`. `hd` is `_Py_HashDouble`, which returns a `Py_hash_t` that is never
`-1` (Python/pyhash.c:127-128, and `Py_HashPointer` for a NaN): the hypothesis. The C code
(complexobject.c:631-651) works in `Py_uhash_t` instead. -/
def HashNumericRule : Prop :=
  ∀ (R : Type) [CDouble R] (hd : R → Int),
    (∀ x, -(2 ^ 63) ≤ hd x ∧ hd x < 2 ^ 63 ∧ hd x ≠ -1) → ∀ v : Cx R,
      complex_hash hd v =
        let h := (hd v.real + 1000003 * hd v.imag + 2 ^ 63) % 2 ^ 64 - 2 ^ 63
        if h = -1 then -2 else h

theorem toUhash_int (h : Int) : (toUhash h : Int) = h % 2 ^ 64 := by
  unfold toUhash
  have : 0 ≤ h % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  omega

theorem hashNumericRule_proven : HashNumericRule := by
  intro R _ hd hh v
  obtain ⟨r1, r2, r3⟩ := hh v.real
  obtain ⟨i1, i2, i3⟩ := hh v.imag
  have hr := hash_range r1 r2 r3
  have hi := hash_range i1 i2 i3
  have hrb : (toUhash (hd v.real) == 2 ^ 64 - 1) = false := by simpa using hr.1
  have hib : (toUhash (hd v.imag) == 2 ^ 64 - 1) = false := by simpa using hi.1
  simp only [complex_hash, hrb, hib, Bool.false_eq_true, ite_false]
  have er := toUhash_int (hd v.real)
  have ei := toUhash_int (hd v.imag)
  generalize toUhash (hd v.real) = ur at er hr
  generalize toUhash (hd v.imag) = ui at ei hi
  generalize hd v.real = A at er r1 r2 r3
  generalize hd v.imag = B at ei i1 i2 i3
  have e64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  have e63 : (2 : Nat) ^ 63 = 9223372036854775808 := by decide
  have f64 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  have f63 : (2 : Int) ^ 63 = 9223372036854775808 := by decide
  rw [f64] at er ei
  rw [e64] at hr hi ⊢
  simp only [hashImag, toHash, e63, f64, f63]
  by_cases hc : (ur + 1000003 * ui) % 18446744073709551616 = 18446744073709551616 - 1
  · simp only [hc, beq_self_eq_true, ite_true]
    have : (A + 1000003 * B + 9223372036854775808) % 18446744073709551616 - 9223372036854775808 = -1 := by
      omega
    simp only [this, ite_true]
    decide
  · have hc' : ((ur + 1000003 * ui) % 18446744073709551616 == 18446744073709551616 - 1) = false := by
      simpa using hc
    simp only [hc', Bool.false_eq_true, ite_false]
    split <;> split <;> omega

/-! ## `actual_complex_new` -/

/-- `actual_complex_new`, complexobject.c:1114-1172, on one positional argument.

* An exact complex with `type` complex is the argument itself (:1128-1135).
* A complex or complex subclass instance with the inherited `__complex__` gives a new object
  of `type` with its value (:1139-1143), so `complex(z)` for a subclass instance `z` and
  `S(z)` for a subclass `S` copy the value.
* An overriding `__complex__` that returns an exact complex is called, and its value is the
  result, in a new object of `type`.
* Without `__complex__`, a complex instance (the branch of :1147-1153) gives its value.
* An object that is not a string, has no `__complex__`, and whose type has no `nb_float` or
  `nb_index` raises `TypeError` (:1166-1169), with nothing run. -/
def ActualNewCases : Prop :=
  ∀ (R : Type) [CDouble R] (E : Env R) (t : TyArg) (arg : Obj R) (s : List Ev),
    (∀ c, arg.val = .cplx c → arg.dcomplex = .builtin →
      actual_complex_new E t [arg] [] s =
        .ok (if arg.exact && t == .complex then ⟨.complex, c, true⟩ else ⟨t, c, false⟩) s) ∧
    (∀ res d, arg.dcomplex = .returns res → res.val = .cplx d → res.exact = true →
      (∀ a b, arg.val ≠ .str a b) → (arg.isComplexExact && t == .complex) = false →
      actual_complex_new E t [arg] [] s = .ok ⟨t, d, false⟩ (Ev.call "__complex__" :: s)) ∧
    (∀ c, arg.val = .cplx c → arg.dcomplex = .absent →
      (arg.isComplexExact && t == .complex) = false →
      actual_complex_new E t [arg] [] s = .ok ⟨t, c, false⟩ s) ∧
    ((∀ a b, arg.val ≠ .str a b) → arg.isComplex = false → arg.dcomplex = .absent →
      (arg.ti.hasNumber && (!arg.nbFloat.isAbsent || !arg.nbIndex.isAbsent)) = false →
      actual_complex_new E t [arg] [] s =
        .error (.typeError
          s!"complex() argument must be a string or a number, not {arg.ti.fqName}") s)

theorem actualNewCases_proven : ActualNewCases := by
  intro R _ E t arg s
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hv hd
    have htry := (trySpecialOutcomes_proven R E arg s).2.2.2.2.2.1 c hd hv
    by_cases he : (arg.exact && t == .complex) = true
    · have hx : arg.isComplexExact = true := by
        simp only [Obj.isComplexExact, Obj.isComplex, hv]
        simp only [Bool.and_eq_true] at he
        simp [he.1]
      have he2 : arg.exact = true ∧ (t == TyArg.complex) = true := by simpa using he
      have ht : t = .complex := by simpa using he2.2
      subst ht
      simp only [actual_complex_new, List.length_cons, List.length_nil, List.isEmpty_nil]
      simp [hx, he2.1, pure, EStateM.pure, cvalOf, hv]
    · have he' : (arg.exact && t == .complex) = false := by simpa using he
      have hx : (arg.isComplexExact && t == .complex) = false := by
        simp only [Obj.isComplexExact, Obj.isComplex, hv]
        simpa using he'
      simp only [actual_complex_new, List.length_cons, List.length_nil, List.isEmpty_nil]
      simp only [Nat.lt_irrefl, decide_false, Bool.false_or, Bool.not_true, Bool.false_eq_true,
        ite_false, hx, hv, bind, EStateM.bind, htry]
      simp [he', complex_subtype_from_doubles, complex_subtype_from_c_complex, pure,
        EStateM.pure]
  · intro res d h1 h2 h3 hs hx
    have htry := (trySpecialOutcomes_proven R E arg s).2.2.1 res d h1 h2 h3
    simp only [actual_complex_new, List.length_cons, List.length_nil, List.isEmpty_nil]
    simp only [Nat.lt_irrefl, decide_false, Bool.false_or, Bool.not_true, Bool.false_eq_true,
      ite_false, hx]
    cases hv : arg.val with
    | str a b => exact absurd hv (hs a b)
    | _ =>
      simp only [bind, EStateM.bind, htry]
      rfl
  · intro c hv hd hx
    have htry := (trySpecialOutcomes_proven R E arg s).1 hd
    simp only [actual_complex_new, List.length_cons, List.length_nil, List.isEmpty_nil]
    simp only [Nat.lt_irrefl, decide_false, Bool.false_or, Bool.not_true, Bool.false_eq_true,
      ite_false, hx, hv, bind, EStateM.bind, htry]
    simp [Obj.isComplex, hv, cvalOf, complex_subtype_from_doubles, complex_subtype_from_c_complex,
      pure, EStateM.pure]
  · intro hs hc hd hn
    have htry := (trySpecialOutcomes_proven R E arg s).1 hd
    have hx : (arg.isComplexExact && t == .complex) = false := by
      simp [Obj.isComplexExact, hc]
    rw [actual_one_arg_body E t arg hc hs]
    simp only [bind, EStateM.bind, htry, hc, Bool.false_eq_true, ite_false, hn]
    rfl

/-! ## `complex_new_impl` -/

def realMsg (o : Obj R) : String :=
  s!"complex() argument 'real' must be a real number, not {o.ti.fqName}"

def imagMsg (o : Obj R) : String :=
  s!"complex() argument 'imag' must be a real number, not {o.ti.fqName}"

/-- `complex_new_impl`, complexobject.c:1189-1317, when `real` or `imag` is a complex: the
deprecated path. With exact complex `cr` and `ci`, `complex(cr, ci)` is `cr + ci*1j` computed
as the correction of :1310-1315, `cr.real - ci.imag` and `ci.real + cr.imag`, and warns
twice, `real` first (:1264-1268, :1288-1292). `complex(x, ci)` for a float `x` is
`(x - ci.imag) + ci.real*1j` with one warning; `complex(cr, y)` for a float `y` is
`cr.real + (y + cr.imag)*1j`; `complex(real=cr)` keeps `cr` (:1283-1284). If a warning filter
turns `DeprecationWarning` into an error, the first warning is the result. An object whose
`__complex__` (:1206) returns an exact complex `c`, and whose type has `nb_float`, is used as
`c` without a warning. -/
def NewImplCorrection : Prop :=
  ∀ (R : Type) [CDouble R] (E : Env R) (t : TyArg) (cr ci : Cx R) (x y : R) (s : List Ev),
    (E.warnErr = false →
      complex_new_impl E t (some (mkComplex cr)) (some (mkComplex ci)) s =
        .ok ⟨t, ⟨cr.real -. ci.imag, ci.real +. cr.imag⟩, false⟩
          (Ev.warn (imagMsg (mkComplex ci)) :: Ev.warn (realMsg (mkComplex cr)) :: s)) ∧
    (E.warnErr = true →
      complex_new_impl E t (some (mkComplex cr)) (some (mkComplex ci)) s =
        .error (.named "DeprecationWarning" (realMsg (mkComplex cr))) s) ∧
    (E.warnErr = false →
      complex_new_impl E t (some (mkFloat x)) (some (mkComplex ci)) s =
        .ok ⟨t, ⟨x -. ci.imag, ci.real⟩, false⟩ (Ev.warn (imagMsg (mkComplex ci)) :: s)) ∧
    (E.warnErr = true →
      complex_new_impl E t (some (mkFloat x)) (some (mkComplex ci)) s =
        .error (.named "DeprecationWarning" (imagMsg (mkComplex ci))) s) ∧
    (E.warnErr = false →
      complex_new_impl E t (some (mkComplex cr)) (some (mkFloat y)) s =
        .ok ⟨t, ⟨cr.real, y +. cr.imag⟩, false⟩ (Ev.warn (realMsg (mkComplex cr)) :: s)) ∧
    (E.warnErr = false →
      complex_new_impl E t (some (mkComplex cr)) none s =
        .ok ⟨t, ⟨cr.real, cr.imag⟩, false⟩ (Ev.warn (realMsg (mkComplex cr)) :: s)) ∧
    (∀ (ti : TypeInfo) (ex : Bool) (val : Val R) (nf ni : Slot R),
      ti.hasNumber = true → nf.isAbsent = false →
      complex_new_impl E t (some (.mk ti ex val (.returns (mkComplex cr)) nf ni))
          (some (mkFloat y)) s =
        .ok ⟨t, ⟨cr.real, y +. cr.imag⟩, false⟩ (Ev.call "__complex__" :: s))

theorem newImplCorrection_proven : NewImplCorrection := by
  intro R _ E t cr ci x y s
  obtain ⟨w, db, sd⟩ := E
  refine ⟨fun hw => ?_, fun hw => ?_, fun hw => ?_, fun hw => ?_, fun hw => ?_, fun hw => ?_,
    fun ti ex val nf ni h1 h2 => ?_⟩
  all_goals try (simp only at hw; subst hw; rfl)
  obtain ⟨tp, fq, hn⟩ := ti
  simp only at h1
  subst h1
  cases nf <;> simp [Slot.isAbsent] at h2 <;> rfl

/-! ## `complex_from_number_impl` -/

/-- `complex.from_number`, complexobject.c:1330-1346. An exact complex with `type` complex is
the argument itself (:1334-1337). Otherwise the value is `PyComplex_AsCComplex` (:1338), so
a complex subclass instance gives its stored value even when it overrides `__complex__`, with
nothing run, and a string is not parsed: it fails in `PyFloat_AsDouble` with the `TypeError`
of floatobject.c, nothing run. A subclass `type` is then called on the exact result
(:1342-1344), which gives an instance of it with the same value. Errors of the conversion
propagate. -/
def FromNumberCases : Prop :=
  ∀ (R : Type) [CDouble R] (E : Env R) (t : TyArg) (x : Obj R) (s : List Ev),
    (x.isComplexExact = true → complex_from_number_impl E .complex x s = .ok ⟨.complex, cvalOf x, true⟩ s) ∧
    (∀ c, x.val = .cplx c → x.exact = false →
      complex_from_number_impl E t x s = .ok ⟨t, c, false⟩ s) ∧
    (∀ a b, x.val = .str a b → x.dcomplex = .absent → x.ti.hasNumber = true →
      x.nbFloat.isAbsent = true → x.nbIndex.isAbsent = true →
      complex_from_number_impl E t x s =
        .error (.typeError s!"must be real number, not {pct 50 x.ti.tpName}") s) ∧
    (∀ cv s', (x.isComplexExact && t == .complex) = false → PyComplex_AsCComplex E x s = .ok cv s' →
      complex_from_number_impl E t x s = .ok ⟨t, cv, false⟩ s') ∧
    (∀ e s', (x.isComplexExact && t == .complex) = false → PyComplex_AsCComplex E x s = .error e s' →
      complex_from_number_impl E t x s = .error e s')

theorem from_number_body {R : Type} [CDouble R] (E : Env R) (t : TyArg) (x : Obj R) (s : List Ev)
    (hx : (x.isComplexExact && t == .complex) = false) :
    complex_from_number_impl E t x s =
      match PyComplex_AsCComplex E x s with
      | .ok cv s' => .ok ⟨t, cv, false⟩ s'
      | .error e s' => .error e s' := by
  unfold complex_from_number_impl
  simp only [hx, Bool.false_eq_true, ite_false, bind, EStateM.bind]
  cases h : PyComplex_AsCComplex E x s with
  | error e s' => rfl
  | ok cv s' =>
    cases t with
    | complex => rfl
    | sub n => rfl

theorem fromNumberCases_proven : FromNumberCases := by
  intro R _ E t x s
  refine ⟨fun h => ?_, fun c hv he => ?_, fun a b hv hd h1 h2 h3 => ?_, fun cv s' hx h => ?_,
    fun e s' hx h => ?_⟩
  · simp [complex_from_number_impl, h, pure, EStateM.pure]
  · have hx : (x.isComplexExact && t == .complex) = false := by
      simp [Obj.isComplexExact, he]
    rw [from_number_body E t x s hx]
    simp [PyComplex_AsCComplex, hv, pure, EStateM.pure]
  · have hx : (x.isComplexExact && t == .complex) = false := by
      simp [Obj.isComplexExact, Obj.isComplex, hv]
    rw [from_number_body E t x s hx]
    have htry := (trySpecialOutcomes_proven R E x s).1 hd
    simp only [PyComplex_AsCComplex, hv, bind, EStateM.bind, htry, PyFloat_AsDouble, h1, h2, h3,
      Bool.not_true, Bool.false_or, ite_true, Bool.true_and, Bool.not_false, Bool.false_eq_true,
      ite_false]
    rfl
  · rw [from_number_body E t x s hx, h]
  · rw [from_number_body E t x s hx, h]

/-! ## `_Py_c_abs` -/

/-- `_Py_c_abs`, complexobject.c:368-397, on every value and every incoming `errno`: an
infinite part gives its absolute value, the real part first, even beside a NaN, and clears
`errno` (C99 Annex G); a NaN part with no infinite part gives a NaN and leaves `errno` as it
was, against the comment on :370; finite parts give `hypot`, with `ERANGE` exactly when it is
not finite. -/
def CAbsBranches : Prop :=
  ∀ (R : Type) [CDouble R] (L : Libm R) (z : Cx R) (e : Errno),
    (isinf z.real = true → c_abs L z e = (fabs z.real, Errno.ok)) ∧
    (isinf z.real = false → isinf z.imag = true → c_abs L z e = (fabs z.imag, Errno.ok)) ∧
    ((isnan z.real || isnan z.imag) = true → isinf z.real = false → isinf z.imag = false →
      c_abs L z e = (nan, e)) ∧
    (isfinite z.real = true → isfinite z.imag = true →
      c_abs L z e = ((L.hypot z.real z.imag).1,
        if isfinite (L.hypot z.real z.imag).1 then Errno.ok else Errno.erange))

theorem cAbsBranches_proven : CAbsBranches := by
  intro R _ L z e
  refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h1 h2 h3 => ?_, fun h1 h2 => ?_⟩
  · simp [c_abs, isfinite, h]
  · simp [c_abs, isfinite, h1, h2]
  · have : (!isfinite z.real || !isfinite z.imag) = true := by
      simp only [isfinite] at *
      cases hr : isnan z.real <;> cases hi : isnan z.imag <;> simp_all
    simp [c_abs, this, h2, h3]
  · simp only [c_abs, h1, h2, Bool.not_true, Bool.or_false, Bool.false_eq_true, ite_false]
    cases hf : isfinite (L.hypot z.real z.imag).1 <;> simp

end PyLean.LongObj.Cplx
