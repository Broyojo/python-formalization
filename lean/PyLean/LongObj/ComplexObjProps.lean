import PyLean.LongObj.ComplexFindings

/-!
Properties of the object layer of `Objects/complexobject.c`.

Most hold for every `CDouble` instance, so they are facts about dispatch and check
order that no rounding can affect. An `Obj` is arbitrary, so a theorem quantifying
over one covers every behaviour of a user's `__complex__`, `__float__` and
`__index__`. The state `s` is the log of earlier events.
-/

namespace PyLean.LongObj.Cplx

open CDouble

section lemmas

variable {R : Type} [CDouble R]

theorem try_special_absent (E : Env R) (op : Obj R) (h : op.dcomplex = .absent) :
    try_complex_special_method E op = pure none := by
  simp [try_complex_special_method, h]

@[simp] theorem liftPy_ok {α : Type} (a : α) (s : List Ev) :
    liftPy (.ok a) s = .ok a s := rfl

@[simp] theorem liftPy_error {α : Type} (e : PyExc) (s : List Ev) :
    (liftPy (.error e) : M α) s = .error e s := rfl

end lemmas

/-! ## Allocation -/

/-- The four constructors store exactly the doubles they are given, signed zeros
and NaNs included, in an object of the requested type. -/
def ConstructorsStore : Prop :=
  ∀ (R : Type) [CDouble R] (t : TyArg) (r i : R) (c : Cx R),
    (complex_subtype_from_c_complex t c).cval = c ∧
    (complex_subtype_from_c_complex t c).type = t ∧
    (complex_subtype_from_doubles t r i).cval = ⟨r, i⟩ ∧
    (complex_subtype_from_doubles t r i).type = t ∧
    (PyComplex_FromCComplex c).cval = c ∧
    (PyComplex_FromCComplex c).type = TyArg.complex ∧
    (PyComplex_FromDoubles r i).cval = ⟨r, i⟩ ∧
    (PyComplex_FromDoubles r i).type = TyArg.complex

theorem constructorsStore_proven : ConstructorsStore := by
  intro R _ t r i c
  simp [complex_subtype_from_c_complex, complex_subtype_from_doubles, PyComplex_FromCComplex,
    PyComplex_FromDoubles]

/-! ## Unary slots and small methods -/

/-- `complex_neg` and `_Py_c_neg` compute the same value, and a double negation
and a double conjugation are the identity in every instance where C unary minus
is an involution, as IEEE-754 sign-bit negation is. Conjugation leaves the real
part alone. -/
def NegConjInvolutions : Prop :=
  ∀ (R : Type) [CDouble R], (∀ x : R, CDouble.neg (CDouble.neg x) = x) → ∀ z : Cx R,
    complex_neg z = c_neg z ∧
    complex_neg (complex_neg z) = z ∧
    complex_conjugate_impl (complex_conjugate_impl z) = z ∧
    (complex_conjugate_impl z).real = z.real

theorem negConjInvolutions_proven : NegConjInvolutions := by
  intro R _ h z
  cases z with
  | mk re im =>
    simp [complex_neg, c_neg, complex_conjugate_impl, h]

/-- `+z` and `z.__complex__()` return the argument itself when it is an exact
complex, and an exact copy of the value when it is a subclass instance. -/
def PosAndComplexIdentity : Prop :=
  ∀ (R : Type) [CDouble R] (o : Obj R) (c : Cx R),
    (complex_pos o c).cval = c ∧
    (complex_pos o c).type = TyArg.complex ∧
    (complex_pos o c).isArg = o.isComplexExact ∧
    (complex___complex___impl o c).cval = c ∧
    (complex___complex___impl o c).type = TyArg.complex ∧
    (complex___complex___impl o c).isArg = o.isComplexExact

theorem posAndComplexIdentity_proven : PosAndComplexIdentity := by
  intro R _ o c
  by_cases h : o.isComplexExact <;>
    simp [complex_pos, complex___complex___impl, PyComplex_FromCComplex, h]

/-- `bool(z)` is false exactly when both parts compare equal to zero, so a NaN in
either part is truthy. -/
def BoolIffNonzero : Prop :=
  ∀ (R : Type) [CDouble R] (v : Cx R),
    complex_bool v = false ↔ (v.real ==. CDouble.zero) = true ∧ (v.imag ==. CDouble.zero) = true

theorem boolIffNonzero_proven : BoolIffNonzero := by
  intro R _ v
  simp [complex_bool, CDouble.ne]

/-- `__getnewargs__` round-trips through the constructor bit for bit, signed zeros
and NaNs included, which is what `copy` and `pickle` rely on, and it runs no
Python code and warns about nothing. -/
def GetnewargsRoundTrip : Prop :=
  ∀ (R : Type) [CDouble R] (E : Env R) (z : Cx R) (s : List Ev),
    let a := complex___getnewargs___impl z
    actual_complex_new E .complex [mkFloat a.1, mkFloat a.2] [] s =
      .ok ⟨.complex, z, false⟩ s

theorem getnewargsRoundTrip_proven : GetnewargsRoundTrip := by
  intro R _ E z s
  rfl

/-! ## `complex_hash` -/

theorem toUhash_of_nonneg {h : Int} (h0 : 0 ≤ h) (h1 : h < 2 ^ 63) : (toUhash h : Int) = h := by
  have e : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  have e' : (2 : Int) ^ 63 = 9223372036854775808 := by decide
  unfold toUhash
  rw [e]
  omega

theorem toUhash_of_neg {h : Int} (h0 : h < 0) (h1 : -(2 ^ 63) ≤ h) :
    (toUhash h : Int) = h + 18446744073709551616 := by
  have e : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  have e' : (2 : Int) ^ 63 = 9223372036854775808 := by decide
  unfold toUhash
  rw [e]
  omega

/-- `complex_hash` over any real hash `hd`. `_Py_HashDouble` returns a `Py_hash_t`
that is never `-1` (`Python/pyhash.c:129-131`, and `Py_HashPointer` for a NaN),
which is the hypothesis. Then the result is never `-1`, and if the imaginary part
hashes to `0` the result is the hash of the real part: the note on lines 625-630,
which is what makes `hash(x + 0j) == hash(x)`. -/
def HashComposition : Prop :=
  ∀ (R : Type) [CDouble R] (hd : R → Int),
    (∀ x, -(2 ^ 63) ≤ hd x ∧ hd x < 2 ^ 63 ∧ hd x ≠ -1) → ∀ v : Cx R,
      complex_hash hd v ≠ -1 ∧ (hd v.imag = 0 → complex_hash hd v = hd v.real)

theorem hash_range {h : Int} (h1 : -(2 ^ 63) ≤ h) (h2 : h < 2 ^ 63) (h3 : h ≠ -1) :
    toUhash h ≠ 2 ^ 64 - 1 ∧ toUhash h < 2 ^ 64 := by
  have e' : (2 : Int) ^ 63 = 9223372036854775808 := by decide
  have en : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  rw [en]
  by_cases h0 : 0 ≤ h
  · have := toUhash_of_nonneg h0 h2
    omega
  · have := toUhash_of_neg (by omega) h1
    omega

theorem toHash_ne (c : Nat) (hc : c < 2 ^ 64) (hne : c ≠ 2 ^ 64 - 1) : toHash c ≠ -1 := by
  have en : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  have en' : (2 : Nat) ^ 63 = 9223372036854775808 := by decide
  have ei : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  rw [en] at hc hne
  unfold toHash
  rw [en']
  split <;> omega

theorem toHash_toUhash {h : Int} (h1 : -(2 ^ 63) ≤ h) (h2 : h < 2 ^ 63) :
    toHash (toUhash h) = h := by
  have en' : (2 : Nat) ^ 63 = 9223372036854775808 := by decide
  have ei : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  have e' : (2 : Int) ^ 63 = 9223372036854775808 := by decide
  unfold toHash
  rw [en', ei]
  by_cases h0 : 0 ≤ h
  · have := toUhash_of_nonneg h0 h2
    split <;> omega
  · have := toUhash_of_neg (by omega) h1
    split <;> omega

theorem hashComposition_proven : HashComposition := by
  intro R _ hd hh v
  obtain ⟨r1, r2, r3⟩ := hh v.real
  obtain ⟨i1, i2, i3⟩ := hh v.imag
  have hr := hash_range r1 r2 r3
  have hi := hash_range i1 i2 i3
  have hrb : (toUhash (hd v.real) == 2 ^ 64 - 1) = false := by simpa using hr.1
  have hib : (toUhash (hd v.imag) == 2 ^ 64 - 1) = false := by simpa using hi.1
  have en : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  constructor
  · simp only [complex_hash, hrb, hib, Bool.false_eq_true, ite_false]
    generalize hc : (toUhash (hd v.real) + hashImag * toUhash (hd v.imag)) % 2 ^ 64 = c
    have hclt : c < 2 ^ 64 := by rw [← hc]; exact Nat.mod_lt _ (by decide)
    by_cases hce : c = 2 ^ 64 - 1
    · have : (c == 2 ^ 64 - 1) = true := by simpa using hce
      simp only [this, ite_true]
      exact toHash_ne _ (by decide) (by decide)
    · have : (c == 2 ^ 64 - 1) = false := by simpa using hce
      simp only [this, Bool.false_eq_true, ite_false]
      exact toHash_ne _ hclt hce
  · intro h0
    have hu0 : toUhash (hd v.imag) = 0 := by rw [h0]; rfl
    simp only [complex_hash, hrb, hib, Bool.false_eq_true, ite_false, hu0, Nat.mul_zero,
      Nat.add_zero]
    have hm : toUhash (hd v.real) % 2 ^ 64 = toUhash (hd v.real) := Nat.mod_eq_of_lt hr.2
    rw [hm, hrb]
    simp only [Bool.false_eq_true, ite_false]
    exact toHash_toUhash r1 r2

/-! ## `complex_repr` and `complex___format___impl` -/

/-- A real part that is `+0` is left out, with no parentheses; every other real
part, including `-0`, prints in parentheses with a forced sign on the imaginary
part. `format(z, '')` is `repr(z)`, and any other spec goes to the format engine. -/
def ReprStructure : Prop :=
  ∀ (R : Type) [CDouble R] (ds : R → Bool → String)
    (adv : Cx R → List Nat → Py String) (v : Cx R) (spec : List Nat),
    (complex_repr ds v =
      if (v.real ==. CDouble.zero && CDouble.copysign CDouble.one v.real ==. CDouble.one) = true
      then ds v.imag false ++ "j"
      else "(" ++ ds v.real false ++ ds v.imag true ++ "j)") ∧
    complex___format___impl ds adv v [] = .ok (complex_repr ds v) ∧
    (spec ≠ [] → complex___format___impl ds adv v spec = adv v spec)

theorem reprStructure_proven : ReprStructure := by
  intro R _ ds adv v spec
  refine ⟨?_, rfl, ?_⟩
  · unfold complex_repr
    split
    · simp [String.append_assoc]
    · simp [String.append_assoc]
  · intro hs
    cases spec with
    | nil => exact absurd rfl hs
    | cons c t => rfl

/-! ## Conversion to double, and the binary slots -/

/-- `real_to_double`: a `float` instance gives its value, an `int` instance its
`PyLong_AsDouble` or the `OverflowError`, anything else `NotImplemented`.
`real_to_complex` and `TO_COMPLEX` add a zero imaginary part, except that a
complex is taken as it is. -/
def RealToDouble : Prop :=
  ∀ (R : Type) [CDouble R] (o : Obj R),
    (∀ x, o.val = .flt x → real_to_double o = .ok (some x)) ∧
    (∀ n x, o.val = .long n → ofInt n = some x → real_to_double o = .ok (some x)) ∧
    (∀ n, o.val = .long n → ofInt (R := R) n = none →
      real_to_double o = .error intTooLarge) ∧
    ((∀ x, o.val ≠ .flt x) → (∀ n, o.val ≠ .long n) → real_to_double o = .ok none) ∧
    (∀ x, real_to_double o = .ok (some x) → real_to_complex o = .ok (some ⟨x, CDouble.zero⟩)) ∧
    (∀ c, o.val = .cplx c → TO_COMPLEX o = .ok (some c))

instance {R : Type} : Inhabited (Val R) := ⟨.none⟩

theorem realToDouble_proven : RealToDouble := by
  intro R _ o
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x h; simp [real_to_double, h]
  · intro n x h hx; simp [real_to_double, h, longAsDouble, hx]
  · intro n h hx; simp [real_to_double, h, longAsDouble, hx]
  · intro h1 h2
    unfold real_to_double
    cases hv : o.val with
    | flt x => exact absurd hv (h1 x)
    | long n => exact absurd hv (h2 n)
    | cplx _ => rfl
    | str _ _ => rfl
    | none => rfl
    | other => rfl
  · intro x h
    simp [real_to_complex, h]
  · intro c h; simp [TO_COMPLEX, h]

/-- The comment on lines 665-678: mixed-mode arithmetic combines a real operand
with a complex directly, without coercing it first, so the part it does not
touch is exactly the complex operand's, whatever that value is (a `-0.0` or a NaN
in that part survives). The formula for the real part is the same on both orders
for `+` and `*`. -/
def MixedModeDirect : Prop :=
  ∀ (R : Type) [CDouble R] (x : R) (b : Cx R),
    complex_add (mkFloat x) (mkComplex b) = .ok (some ⟨CDouble.add b.real x, b.imag⟩) ∧
    complex_add (mkComplex b) (mkFloat x) = .ok (some ⟨CDouble.add b.real x, b.imag⟩) ∧
    complex_sub (mkComplex b) (mkFloat x) = .ok (some ⟨CDouble.sub b.real x, b.imag⟩) ∧
    complex_sub (mkFloat x) (mkComplex b) =
      .ok (some ⟨CDouble.sub x b.real, CDouble.neg b.imag⟩) ∧
    complex_mul (mkFloat x) (mkComplex b) =
      .ok (some ⟨CDouble.mul b.real x, CDouble.mul b.imag x⟩) ∧
    complex_mul (mkComplex b) (mkFloat x) =
      .ok (some ⟨CDouble.mul b.real x, CDouble.mul b.imag x⟩)

theorem mixedModeDirect_proven : MixedModeDirect := by
  intro R _ x b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- A binary slot on anything other than a `float`, `int` or `complex` instance is
`NotImplemented`, so the other operand gets its turn. -/
def BinopNotImplemented : Prop :=
  ∀ (R : Type) [CDouble R] (b : Cx R) (o : Obj R),
    (∀ x, o.val ≠ .flt x) → (∀ n, o.val ≠ .long n) → (∀ c, o.val ≠ .cplx c) →
      complex_add (mkComplex b) o = .ok none ∧
      complex_sub o (mkComplex b) = .ok none ∧
      complex_mul (mkComplex b) o = .ok none ∧
      complex_div o (mkComplex b) = .ok none

theorem binopNotImplemented_proven : BinopNotImplemented := by
  intro R _ b o h1 h2 h3
  cases o with
  | mk ti ex val dc nf ni =>
    cases val with
    | cplx c => exact absurd rfl (h3 c)
    | flt x => exact absurd rfl (h1 x)
    | long n => exact absurd rfl (h2 n)
    | str t r => exact ⟨rfl, rfl, rfl, rfl⟩
    | none => exact ⟨rfl, rfl, rfl, rfl⟩
    | other => exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## `complex_pow` -/

/-- `pow(v, w, z)` with `z` not `None` raises `ValueError: complex modulo`, but only
after both operands have converted: `NotImplemented` and the int-overflow error
come first. -/
def PowModuloOrder : Prop :=
  ∀ (R : Type) [CDouble R] (L : Libm R) (v w z : Obj R),
    (∀ a b, TO_COMPLEX v = .ok (some a) → TO_COMPLEX w = .ok (some b) →
      (match z.val with | .none => false | _ => true) = true →
      complex_pow L v w z = .error (.valueError "complex modulo")) ∧
    (TO_COMPLEX v = .ok none → complex_pow L v w z = .ok none) ∧
    (∀ e, TO_COMPLEX v = .error e → complex_pow L v w z = .error e) ∧
    (∀ a, TO_COMPLEX v = .ok (some a) → TO_COMPLEX w = .ok none →
      complex_pow L v w z = .ok none) ∧
    (∀ a e, TO_COMPLEX v = .ok (some a) → TO_COMPLEX w = .error e →
      complex_pow L v w z = .error e)

theorem powModuloOrder_proven : PowModuloOrder := by
  intro R _ L v w z
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b ha hb hz
    simp only [complex_pow, ha, hb]
    cases hv : z.val with
    | none => simp [hv] at hz
    | cplx _ => rfl
    | flt _ => rfl
    | long _ => rfl
    | str _ _ => rfl
    | other => rfl
  · intro h; simp [complex_pow, h]
  · intro e h; simp [complex_pow, h]
  · intro a h1 h2; simp [complex_pow, h1, h2]
  · intro a e h1 h2; simp [complex_pow, h1, h2]

/-- The exponent test on line 738 decides the path. An integral exponent with
`|b.real| <= 100` and a zero imaginary part makes no libm call at all, so the
result cannot depend on the libm; any other exponent is `_Py_c_pow`. -/
def PowFastPathBound : Prop :=
  ∀ (R : Type) [CDouble R] (L₁ L₂ : Libm R) (a b : Cx R),
    ((b.imag ==. CDouble.zero && b.real ==. CDouble.floor b.real &&
        le (fabs b.real) hundred) = true →
      complex_pow_core L₁ a b = complex_pow_core L₂ a b) ∧
    ((b.imag ==. CDouble.zero && b.real ==. CDouble.floor b.real &&
        le (fabs b.real) hundred) = false →
      complex_pow_core L₁ a b =
        let (p, e) := c_pow L₁ a b Errno.ok
        if e = Errno.edom then
          .error (.zeroDivisionError "zero to a negative or complex power")
        else if e = Errno.erange then .error (.overflowError "complex exponentiation")
        else .ok p)

theorem powFastPathBound_proven : PowFastPathBound := by
  intro R _ L₁ L₂ a b
  constructor
  · intro h
    simp only [complex_pow_core, h, ite_true]
  · intro h
    simp only [complex_pow_core, h, Bool.false_eq_true, ite_false]

theorem c_powu_zero {R : Type} [CDouble R] (x : Cx R) : c_powu x 0 = c_1 := rfl

/-- `z ** 0` is `1` for every `z`, NaN and infinity included, by either sign of
zero in either part of the exponent. -/
def PowZeroIsOne : Prop :=
  ∀ (L : Libm Dbl) (a b : Cx Dbl), b.real.bits % 2 ^ 63 = 0 → b.imag.bits % 2 ^ 63 = 0 →
    b.real.bits < 2 ^ 64 → b.imag.bits < 2 ^ 64 →
    complex_pow_core L a b = .ok ⟨Dbl.d1, ⟨0⟩⟩

theorem c_powi_zero_dbl (a : Cx Dbl) (n : Int) (hn : n = 0) (e : Errno) :
    c_powi a n e = (⟨Dbl.d1, ⟨0⟩⟩, e) := by
  subst hn
  have h : c_powi a 0 e = c_quot c_1 (c_powu a 0) e := by simp [c_powi]
  rw [h, c_powu_zero]
  cases e <;> decide +kernel

theorem powZeroIsOne_proven : PowZeroIsOne := by
  intro L a b hr hi hr' hi'
  have zeros : ∀ x : Dbl, x.bits % 2 ^ 63 = 0 → x.bits < 2 ^ 64 → x = ⟨0⟩ ∨ x = ⟨2 ^ 63⟩ := by
    intro x h1 h2
    cases x with
    | mk v =>
      simp only at h1 h2
      simp only [Dbl.mk.injEq]
      omega
  have checks : ∀ x y : Dbl, (x = ⟨0⟩ ∨ x = ⟨2 ^ 63⟩) → (y = ⟨0⟩ ∨ y = ⟨2 ^ 63⟩) →
      (y ==. CDouble.zero && x ==. CDouble.floor x && le (fabs x) hundred) = true ∧
        CDouble.toLong x = 0 := by
    intro x y hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide +kernel
  obtain ⟨hc, hl⟩ := checks b.real b.imag (zeros _ hr hr') (zeros _ hi hi')
  simp only [complex_pow_core, hc, ite_true]
  rw [c_powi_zero_dbl a _ hl]
  decide +kernel

/-- The first two branches of `_Py_c_pow`: a zero exponent gives `1`, before the
base is looked at, and `0 ** b` is `0`, with `EDOM` exactly when `b` has a nonzero
imaginary part or a negative real part. Neither calls libm. -/
def CPowBranches : Prop :=
  ∀ (R : Type) [CDouble R] (L : Libm R) (a b : Cx R) (e : Errno),
    ((b.real ==. CDouble.zero && b.imag ==. CDouble.zero) = true →
      c_pow L a b e = (⟨CDouble.one, CDouble.zero⟩, e)) ∧
    ((b.real ==. CDouble.zero && b.imag ==. CDouble.zero) = false →
      (a.real ==. CDouble.zero && a.imag ==. CDouble.zero) = true →
      c_pow L a b e =
        (⟨CDouble.zero, CDouble.zero⟩,
          if (CDouble.ne b.imag CDouble.zero || b.real <. CDouble.zero) = true
          then Errno.edom else e))

theorem cPowBranches_proven : CPowBranches := by
  intro R _ L a b e
  constructor
  · intro h; simp only [c_pow, h, ite_true]
  · intro h1 h2
    simp only [c_pow, h1, h2, ite_true, Bool.false_eq_true, ite_false]

/-! ## `complex_richcompare` -/

/-- Only `==` and `!=` are implemented, `!=` is the negation of `==` on every
right operand, an int is compared exactly through `eqInt` and only when the
imaginary part is zero, and the result for a `float` or `complex` is the
componentwise C `==`. -/
def RichCompareShape : Prop :=
  ∀ (R : Type) [CDouble R] (v : Cx R) (w : Obj R),
    (∀ op, op ≠ CmpOp.eq → op ≠ CmpOp.ne → complex_richcompare v w op = none) ∧
    complex_richcompare v w CmpOp.ne = (complex_richcompare v w CmpOp.eq).map (!·) ∧
    (∀ n, w.val = .long n →
      complex_richcompare v w CmpOp.eq =
        some (v.imag ==. CDouble.zero && eqInt v.real n)) ∧
    (∀ x, w.val = .flt x →
      complex_richcompare v w CmpOp.eq =
        some (v.real ==. x && v.imag ==. CDouble.zero)) ∧
    (∀ c, w.val = .cplx c →
      complex_richcompare v w CmpOp.eq =
        some (v.real ==. c.real && v.imag ==. c.imag))

theorem richCompareShape_proven : RichCompareShape := by
  intro R _ v w
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro op h1 h2
    cases op <;> first | exact absurd rfl h1 | exact absurd rfl h2 | rfl
  · have hne : (CmpOp.ne == CmpOp.eq) = false := by decide
    simp only [complex_richcompare]
    cases hv : w.val with
    | long n =>
      by_cases hi : (v.imag ==. CDouble.zero) = true <;> simp [hi]
    | flt x =>
      cases h1 : (v.real ==. x) <;> cases h2 : (v.imag ==. CDouble.zero) <;> simp [hne]
    | cplx c =>
      cases h1 : (v.real ==. c.real) <;> cases h2 : (v.imag ==. c.imag) <;> simp [hne]
    | str _ _ => simp
    | none => simp
    | other => simp
  · intro n h
    simp only [complex_richcompare, h]
    by_cases hi : (v.imag ==. CDouble.zero) = true <;> simp [hi]
  · intro x h
    simp [complex_richcompare, h]
  · intro c h
    simp [complex_richcompare, h]

/-- At exact binary64, `complex(x) == n` compares the int without rounding it:
it holds exactly when the integer value of `x`'s bits, in units of `2^-1074`, is
`n · 2^1074`, however large `n` is. -/
def RichCompareHugeInt : Prop :=
  ∀ (x : Dbl) (n : Int) (w : Obj Dbl), w.val = .long n →
    complex_richcompare ⟨x, ⟨0⟩⟩ w CmpOp.eq =
      some (!x.isNaN && !x.isInf && x.sval == n * 2 ^ 1074)

set_option exponentiation.threshold 1100 in
theorem richCompareHugeInt_proven : RichCompareHugeInt := by
  intro x n w h
  have hz : ((⟨0⟩ : Dbl) ==. (CDouble.zero : Dbl)) = true := by decide +kernel
  simp only [complex_richcompare, h]
  simp only [hz]
  have hop1 : (CmpOp.eq != CmpOp.eq) = false := by decide
  simp only [hop1, Bool.false_and, Bool.false_eq_true, ite_false]
  have hop2 : (CmpOp.eq == CmpOp.eq) = true := by decide
  simp only [ite_true, hop2, Bool.true_and]
  have : CDouble.eqInt x n = (!x.isNaN && !x.isInf && x.sval == n * 2 ^ 1074) := by
    show Dbl.eqInt x n = _
    simp only [Dbl.eqInt]
    cases hn : x.isNaN <;> cases hi : x.isInf <;> simp
  rw [this]

/-! ## C API accessors -/

/-- Reshape a result without touching the log. -/
def mapRes {α β : Type} (f : α → β) : EStateM.Result PyExc (List Ev) α →
    EStateM.Result PyExc (List Ev) β
  | .ok a s => .ok (f a) s
  | .error e s => .error e s

/-- `PyComplex_RealAsDouble` and `PyComplex_ImagAsDouble` agree with the two parts
of `PyComplex_AsCComplex`, on every object, in value, in exception and in the
calls and warnings they make. Each of the three has its own copy of the logic. -/
def AccessorsAgree : Prop :=
  ∀ (R : Type) [CDouble R] (E : Env R) (op : Obj R) (s : List Ev),
    PyComplex_RealAsDouble E op s = mapRes Cx.real (PyComplex_AsCComplex E op s) ∧
    PyComplex_ImagAsDouble E op s = mapRes Cx.imag (PyComplex_AsCComplex E op s)

theorem accessorsAgree_proven : AccessorsAgree := by
  intro R _ E op s
  unfold PyComplex_RealAsDouble PyComplex_ImagAsDouble PyComplex_AsCComplex
  cases hv : op.val
  case cplx c => constructor <;> rfl
  all_goals
    simp only [bind, EStateM.bind]
    cases h1 : try_complex_special_method E op s with
    | ok a s' =>
      cases a with
      | some c => constructor <;> simp [h1, mapRes, pure, EStateM.pure]
      | none =>
        cases h2 : PyFloat_AsDouble E op s' <;> constructor <;>
          simp [h1, h2, mapRes, pure, EStateM.pure, EStateM.bind]
    | error e s' => constructor <;> simp [h1, mapRes]

end PyLean.LongObj.Cplx
