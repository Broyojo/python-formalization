import PyLean.CoreLibs.Misc.Numbers.Model

/-!
Properties of the `numbers` mixins. The mixins are generic, so each statement quantifies over every
concrete subclass (`Prims`) and says how the primitives determine the mixin. The hypotheses say what
a subclass promises: its operators do not raise on the values in question and they implement the
arithmetic of an abstract group or of the integers, read through `v`.
-/

namespace PyLean.CoreLibs.Misc.Numbers

open PyLean

/-- An abelian group: what `__sub__` and `__rsub__` need from the numbers of a subclass. -/
structure AbGroup (G : Type) where
  add : G → G → G
  neg : G → G
  add_comm : ∀ a b, add a b = add b a

/-- The primitives `+` and unary `-` of a subclass implement the group `g` through `v`. -/
structure AddHom {α F C G : Type} (p : Prims α F C) (g : AbGroup G) (v : α → G) : Prop where
  add : ∀ a b, ∃ r, p.add a b = .ok r ∧ v r = g.add (v a) (v b)
  neg : ∀ a, ∃ r, p.neg a = .ok r ∧ v r = g.neg (v a)

/-- `Complex.__sub__` and `Complex.__rsub__`: for every subclass whose `+` and unary `-` implement
an abelian group, `x - y` is `x + (-y)` and `y - x`, through the right-hand method, is `y + (-x)`:
the mixins compute subtraction in that group, with the operands the right way round. A subclass
whose `-` raises keeps that exception, and `+` is never reached. -/
def ComplexSubRsub : Prop :=
  ∀ (α F C G : Type) (p : Prims α F C) (g : AbGroup G) (v : α → G), AddHom p g v →
    ∀ x y : α,
      (∃ r, Complex.__sub__ p x y = .ok r ∧ v r = g.add (v x) (g.neg (v y))) ∧
      (∃ r, Complex.__rsub__ p x y = .ok r ∧ v r = g.add (v y) (g.neg (v x)))

theorem complexSubRsub_proven : ComplexSubRsub := by
  intro α F C G p g v h x y
  constructor
  · obtain ⟨n, hn, vn⟩ := h.neg y
    obtain ⟨r, hr, vr⟩ := h.add x n
    refine ⟨r, ?_, by rw [vr, vn]⟩
    simp [Complex.__sub__, hn, hr, bind, Except.bind]
  · obtain ⟨n, hn, vn⟩ := h.neg x
    obtain ⟨r, hr, vr⟩ := h.add n y
    refine ⟨r, ?_, by rw [vr, vn, g.add_comm]⟩
    simp [Complex.__rsub__, hn, hr, bind, Except.bind]

/-- `Complex.__sub__` evaluates `-other` first: an exception from `__neg__` is the result, whatever
`__add__` does. `Complex.__rsub__` likewise on `self`. -/
def ComplexSubNegFirst : Prop :=
  ∀ (α F C : Type) (p : Prims α F C) (x y : α) (e : PyExc),
    (p.neg y = .error e → Complex.__sub__ p x y = .error e) ∧
    (p.neg x = .error e → Complex.__rsub__ p x y = .error e)

theorem complexSubNegFirst_proven : ComplexSubNegFirst := by
  intro α F C p x y e
  constructor
  · intro h; simp [Complex.__sub__, h, bind, Except.bind]
  · intro h; simp [Complex.__rsub__, h, bind, Except.bind]

/-- `Complex.__bool__` ("True if self != 0"): when `==` on the subclass is equality of the values
read through `v`, `bool(x)` is `v x ≠ v 0`. An exception from `__eq__` is the result. -/
def ComplexBool : Prop :=
  ∀ (α F C G : Type) [DecidableEq G] (p : Prims α F C) (v : α → G),
    (∀ a b, p.eq a b = .ok (decide (v a = v b))) →
    ∀ x, Complex.__bool__ p x = .ok (decide (v x ≠ v p.zero))

theorem complexBool_proven : ComplexBool := by
  intro α F C G _ p v h x
  simp [Complex.__bool__, h, bind, Except.bind, pure, Except.pure]

/-- `Real.__divmod__` and `Real.__rdivmod__`: `__rdivmod__(self, other)` is `__divmod__(other, self)`
on every subclass, value or exception; `//` is evaluated first, so its exception wins over `%`'s and
`%` is not reached. When `//` and `%` are int floor division and modulus, the pair satisfies
`q * b + r = a`. -/
def RealDivmod : Prop :=
  ∀ (α F C : Type) (p : Prims α F C) (a b : α),
    Real.__rdivmod__ p b a = Real.__divmod__ p a b ∧
    (∀ e, p.floordiv a b = .error e → Real.__divmod__ p a b = .error e) ∧
    (∀ q e, p.floordiv a b = .ok q → p.mod a b = .error e → Real.__divmod__ p a b = .error e) ∧
    (∀ q r, p.floordiv a b = .ok q → p.mod a b = .ok r → Real.__divmod__ p a b = .ok (q, r))

theorem realDivmod_proven : RealDivmod := by
  intro α F C p a b
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro e h; simp [Real.__divmod__, h, bind, Except.bind]
  · intro q e h1 h2; simp [Real.__divmod__, h1, h2, bind, Except.bind]
  · intro q r h1 h2; simp [Real.__divmod__, h1, h2, bind, Except.bind, pure, Except.pure]

/-- `divmod` for a subclass over the ints: `q * b + r = a` whenever `b ≠ 0`, from Python's floor
division and modulus. -/
def RealDivmodEuclid : Prop :=
  ∀ (F C : Type) (p : Prims Int F C),
    (∀ a b, b ≠ 0 → p.floordiv a b = .ok (a.fdiv b)) →
    (∀ a b, b ≠ 0 → p.mod a b = .ok (a.fmod b)) →
    ∀ a b : Int, b ≠ 0 → ∃ q r, Real.__divmod__ p a b = .ok (q, r) ∧ q * b + r = a

theorem realDivmodEuclid_proven : RealDivmodEuclid := by
  intro F C p h1 h2 a b hb
  refine ⟨a.fdiv b, a.fmod b, ?_, ?_⟩
  · simp [Real.__divmod__, h1 a b hb, h2 a b hb, bind, Except.bind, pure, Except.pure]
  · rw [Int.mul_comm, Int.mul_fdiv_add_fmod]

/-- The components of a `Real`: `x.real` and `x.conjugate()` are `+x`, so they agree with each other
and are the number itself when `+` is the identity; `x.imag` is `0` without any primitive being
called; and "complex(self) == complex(float(self), 0)": when `complex(f)` has imaginary part `0`,
`complex(x)` is `(float(x), 0)`. -/
def RealComponents : Prop :=
  ∀ (α F : Type) (p : Prims α F (F × F)) (f0 : F) (x : α),
    Real.real p x = Real.conjugate p x ∧
    ((∀ a, p.pos a = .ok a) → Real.real p x = .ok x) ∧
    Real.imag p x = .ok p.zero ∧
    ∀ f, (∀ g, p.complexOf g = .ok (g, f0)) → p.float x = .ok f → Real.__complex__ p x = .ok (f, f0)

theorem realComponents_proven : RealComponents := by
  intro α F p f0 x
  refine ⟨rfl, ?_, rfl, ?_⟩
  · intro h; exact h x
  · intro f h1 h2; simp [Real.__complex__, h1, h2, bind, Except.bind]

/-- An `Integral` is a `Rational` with denominator 1: `Integral.numerator` is `+self`,
`Integral.denominator` is `1`, and the two float conversions agree. `Rational.__float__` run on the
`Integral` properties gives `Integral.__float__` whenever `int(+x) = int(x)`, `int(1) = 1` and
`n / 1` equals `float(n)` for ints, which `long_true_divide` and `PyLong_AsDouble` satisfy, both
being correctly rounded. `__index__` is `int(self)`. -/
def IntegralRationalAgree : Prop :=
  ∀ (α F C : Type) (p : Prims α F C) (x : α),
    p.numerator = Integral.numerator p →
    p.denominator = Integral.denominator p →
    (∀ a, p.pos a = .ok a) →
    p.toInt p.one = .ok 1 →
    (∀ n, p.intDiv n 1 = p.intFloat n) →
    Rational.__float__ p x = Integral.__float__ p x ∧ Integral.__index__ p x = p.toInt x

theorem integralRationalAgree_proven : IntegralRationalAgree := by
  intro α F C p x h1 h2 h3 h4 h5
  refine ⟨?_, rfl⟩
  simp only [Rational.__float__, Integral.__float__, h1, h2, Integral.numerator,
    Integral.denominator, h3, bind, Except.bind]
  cases h : p.toInt x with
  | error e => rfl
  | ok n => simp [h4, h5]

/-- Every abstract method has the behaviour its body states: `NotImplementedError` for the stubs,
for every argument, and `None` for `Complex.__complex__`, whose body is only a docstring. The result
is observable through `super()` in a subclass. -/
def AbstractStubs : Prop :=
  ∀ (α F : Type) (a b : α),
    Complex.__complex__ a = .ok () ∧
    Complex.real a = notImpl ∧ Complex.imag a = notImpl ∧
    Complex.__add__ a b = notImpl ∧ Complex.__radd__ a b = notImpl ∧
    Complex.__neg__ a = notImpl ∧ Complex.__pos__ a = notImpl ∧
    Complex.__mul__ a b = notImpl ∧ Complex.__rmul__ a b = notImpl ∧
    Complex.__truediv__ a b = notImpl ∧ Complex.__rtruediv__ a b = notImpl ∧
    Complex.__pow__ a b = notImpl ∧ Complex.__rpow__ a b = notImpl ∧
    Complex.__abs__ a = notImpl ∧ Complex.conjugate a = notImpl ∧
    Complex.__eq__ a b = notImpl ∧
    Real.__float__ (F := F) a = notImpl ∧ Real.__trunc__ a = notImpl ∧
    Real.__floor__ a = notImpl ∧ Real.__ceil__ a = notImpl ∧ Real.__round__ a = notImpl ∧
    Real.__floordiv__ a b = notImpl ∧ Real.__rfloordiv__ a b = notImpl ∧
    Real.__mod__ a b = notImpl ∧ Real.__rmod__ a b = notImpl ∧
    Real.__lt__ a b = notImpl ∧ Real.__le__ a b = notImpl ∧
    Rational.numerator a = notImpl ∧ Rational.denominator a = notImpl ∧
    Integral.__int__ a = notImpl ∧ Integral.__pow__ a b = notImpl ∧
    Integral.__lshift__ a b = notImpl ∧ Integral.__rlshift__ a b = notImpl ∧
    Integral.__rshift__ a b = notImpl ∧ Integral.__rrshift__ a b = notImpl ∧
    Integral.__and__ a b = notImpl ∧ Integral.__rand__ a b = notImpl ∧
    Integral.__xor__ a b = notImpl ∧ Integral.__rxor__ a b = notImpl ∧
    Integral.__or__ a b = notImpl ∧ Integral.__ror__ a b = notImpl ∧
    Integral.__invert__ a = notImpl

theorem abstractStubs_proven : AbstractStubs := by
  intro α F a b
  simp only [Complex.__complex__, Complex.real, Complex.imag, Complex.__add__, Complex.__radd__,
    Complex.__neg__, Complex.__pos__, Complex.__mul__, Complex.__rmul__, Complex.__truediv__,
    Complex.__rtruediv__, Complex.__pow__, Complex.__rpow__, Complex.__abs__, Complex.conjugate,
    Complex.__eq__, Real.__float__, Real.__trunc__, Real.__floor__, Real.__ceil__, Real.__round__,
    Real.__floordiv__, Real.__rfloordiv__, Real.__mod__, Real.__rmod__, Real.__lt__, Real.__le__,
    Rational.numerator, Rational.denominator, Integral.__int__, Integral.__pow__,
    Integral.__lshift__, Integral.__rlshift__, Integral.__rshift__, Integral.__rrshift__,
    Integral.__and__, Integral.__rand__, Integral.__xor__, Integral.__rxor__, Integral.__or__,
    Integral.__ror__, Integral.__invert__, and_self]

/-- A mixin over a primitive that is still abstract fails with `NotImplementedError` and returns
no number: a subclass that forgets `__neg__` or calls up to the stub cannot get a wrong difference. -/
def MixinOverStub : Prop :=
  ∀ (α F C : Type) (p : Prims α F C) (x y : α),
    p.neg = Complex.__neg__ →
    Complex.__sub__ p x y = notImpl ∧ Complex.__rsub__ p x y = notImpl

theorem mixinOverStub_proven : MixinOverStub := by
  intro α F C p x y h
  simp [Complex.__sub__, Complex.__rsub__, h, Complex.__neg__, notImpl, bind, Except.bind]

end PyLean.CoreLibs.Misc.Numbers
