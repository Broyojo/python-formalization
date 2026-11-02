import PyLean.Fractions.Parse

/-!
`Fraction(x)` with one argument: the dispatch of `Fraction.__new__`,
fractions.py:239-287.

3.15 moved the `numbers.Rational` branch from directly after the exact-`int` test to
last, so `as_integer_ratio` and then `str` are now tried first. An object that is both
sees a different branch than it did on 3.14: a `Fraction` subclass that overrides
`as_integer_ratio`, or an `int` subclass that overrides `numerator`. The branches return
what the object says, without normalizing it.

`x` is described by what the source asks of it. `as_integer_ratio` is a callback: `ratio`
is its outcome after unpacking into two names (a wrong arity is the `ValueError` from the
unpacking), and floats and `Decimal`s are this case, so their exact conversion is not
modelled here. Ints that are not ints in the result (`Fraction` stores what `numerator`
returns) are out of scope.
-/

namespace PyLean.Fractions

open PyLean

/-- The answers of the object passed as `numerator` when `denominator is None`. -/
structure CtorArg where
  /-- `type(numerator) is int`, with its value. -/
  exactInt : Option Int
  /-- `isinstance(numerator, float)`. -/
  isFloat : Bool
  /-- `isinstance(numerator, type)`. -/
  isType : Bool
  /-- `hasattr(numerator, 'as_integer_ratio')`, with the outcome of calling it. -/
  ratio : Option (Py (Int × Int))
  /-- `isinstance(numerator, str)`, with its text. -/
  str : Option (List Char)
  /-- `isinstance(numerator, numbers.Rational)`, with `.numerator` and `.denominator`. -/
  rational : Option (Int × Int)

/-- The message of the last `else`, fractions.py:286-287. -/
def ctorTypeErrorMsg : String :=
  "argument should be a string or a Rational instance or have the as_integer_ratio() method"

/-- Takes the branch at fractions.py:245-247. -/
def takesRatio (x : CtorArg) : Bool := x.isFloat || (!x.isType && x.ratio.isSome)

/-- `Fraction(numerator)`, fractions.py:239-287, in the source's branch order. Only the
string branch goes on to the common tail, which `parse` includes. -/
def ofOne (x : CtorArg) : Py Frac :=
  match x.exactInt with
  | some n => .ok (ofInt n)
  | none =>
    if takesRatio x then
      match x.ratio with
      | some r => (fun (p : Int × Int) => (⟨p.1, p.2⟩ : Frac)) <$> r
      -- `float` defines the method, so `isFloat` implies `ratio.isSome`.
      | none => .error (.named "AttributeError" "~as_integer_ratio")
    else
      match x.str with
      | some s => parse s
      | none =>
        match x.rational with
        | some (n, d) => .ok ⟨n, d⟩
        | none => .error (.typeError ctorTypeErrorMsg)

/-- The branch order of 3.15, as a statement. `as_integer_ratio` wins over `str` and
`numbers.Rational` unless `x` is a type; `str` wins over `numbers.Rational`; and an object
that is `Rational` and agrees with itself gets the same result as under the old order, so
`Fraction(Fraction(a, b))` copies. The 3.14 order fails the second clause. -/
def CtorOneArgOrder : Prop :=
  (∀ (x : CtorArg) (n : Int), x.exactInt = some n → ofOne x = .ok ⟨n, 1⟩) ∧
  (∀ (x : CtorArg) (r : Py (Int × Int)), x.exactInt = none → x.ratio = some r →
    (x.isFloat = true ∨ x.isType = false) →
    ofOne x = (fun (p : Int × Int) => (⟨p.1, p.2⟩ : Frac)) <$> r) ∧
  (∀ (x : CtorArg) (s : List Char), x.exactInt = none → takesRatio x = false →
    x.str = some s → ofOne x = parse s) ∧
  (∀ (x : CtorArg) (n d : Int), x.exactInt = none → takesRatio x = false → x.str = none →
    x.rational = some (n, d) → ofOne x = .ok ⟨n, d⟩) ∧
  (∀ x : CtorArg, x.exactInt = none → takesRatio x = false → x.str = none → x.rational = none →
    ofOne x = .error (.typeError ctorTypeErrorMsg)) ∧
  (∀ (x : CtorArg) (n d : Int), x.exactInt = none → x.isType = false →
    x.ratio = some (.ok (n, d)) → x.rational = some (n, d) → ofOne x = .ok ⟨n, d⟩)

theorem ctorOneArgOrder_proven : CtorOneArgOrder := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x n h
    simp [ofOne, h, ofInt]
  · intro x r h1 h2 h3
    have : takesRatio x = true := by
      rcases h3 with h3 | h3 <;> simp [takesRatio, h2, h3]
    simp [ofOne, h1, h2, this]
  · intro x s h1 h2 h3
    simp [ofOne, h1, h2, h3]
  · intro x n d h1 h2 h3 h4
    simp [ofOne, h1, h2, h3, h4]
  · intro x h1 h2 h3 h4
    simp [ofOne, h1, h2, h3, h4]
  · intro x n d h1 h2 h3 _
    have : takesRatio x = true := by simp [takesRatio, h2, h3]
    simp [ofOne, h1, h3, this, Functor.map, Except.map]

end PyLean.Fractions
