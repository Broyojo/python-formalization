import PyLean.Decimal.Parse
import PyLean.Decimal.Tuple
import PyLean.Decimal.Format
import PyLean.Decimal.Arith

/-!
Twin-agreement properties refuted by a concrete input. Every witness is
evaluated by the kernel (`decide`), and every one is reproduced on CPython by
the matching `bugs/decimal-*.yaml`.
-/

namespace PyLean.Decimal

open PyLean

set_option exponentiation.threshold 5000

/-! ## Parsing: `_decimal` accepts every string `_pydecimal` accepts -/

/-- For every string `s`, if `_pydecimal.Decimal(s)` returns a value that
`_decimal` can represent (`InCLimits`, the documented C limits), then
`_decimal.Decimal(s)` returns the same value. -/
def ParseCAcceptsPy : Prop :=
  ∀ (s : List Char) (d : Dec), pyParse s = .ok d → InCLimits d → cParse s = .ok d

/-- `Decimal('ınf')` (U+0131 dotless i): `_pydecimal`'s `re.IGNORECASE`
matches `ı` against `i` by Unicode case folding; `_decimal` rejects it. -/
theorem parseCAcceptsPy_refuted : ¬ParseCAcceptsPy := by
  intro h
  have hpy : pyParse ['ı', 'n', 'f'] = .ok (.inf false) := by decide
  have hc : cParse ['ı', 'n', 'f'] = .error invalidOp := by decide
  have := h _ _ hpy trivial
  rw [hc] at this
  cases this

/-! ## Parsing: `_pydecimal` accepts every string `_decimal` accepts -/

/-- For every string `s`, if `_decimal.Decimal(s)` returns a value, then
`_pydecimal.Decimal(s)` returns the same value. -/
def ParsePyAcceptsC : Prop :=
  ∀ (s : List Char) (d : Dec), cParse s = .ok d → pyParse s = .ok d

/-- `Decimal('1' * 4301)`: `_pydecimal` builds `str(int(intpart+fracpart))`
and `int()` refuses more than 4300 digits. -/
theorem parsePyAcceptsC_refuted : ¬ParsePyAcceptsC := by
  intro h
  have hc : cParse (List.replicate 4301 '1') = .ok (.fin false (digitsValue (List.replicate 4301 '1')) 0) := by
    set_option maxRecDepth 100000 in decide
  have hpy : pyParse (List.replicate 4301 '1') = .error (.valueError (limitToIntMsg 4301)) := by
    set_option maxRecDepth 100000 in decide
  have := h _ _ hc
  rw [hpy] at this
  cases this

/-! ## `str` round trip in `_pydecimal` -/

/-- For every value `d` within the C limits, `Decimal(str(d))` in
`_pydecimal` gives back `d`, exponent included. -/
def StrRoundTripPy : Prop :=
  ∀ d : Dec, InCLimits d → (pyStr d >>= pyParse) = .ok d

/-- `d = Decimal(10**4300)`: `str(d)` has 4301 digits, which `_pydecimal`
cannot parse back. -/
theorem strRoundTripPy_refuted : ¬StrRoundTripPy := by
  intro h
  have hl : InCLimits (.fin false (10 ^ 4300) 0) := by
    set_option maxRecDepth 100000 in decide
  have hv : (pyStr (.fin false (10 ^ 4300) 0) >>= pyParse) = .error (.valueError (limitToIntMsg 4301)) := by
    set_option maxRecDepth 100000 in decide
  have := h _ hl
  rw [hv] at this
  cases this

/-! ## `hash` -/

/-- Whenever `_decimal` hashes a value, `_pydecimal` hashes it to the same
int. -/
def HashTwinsAgree : Prop :=
  ∀ (d : Dec) (h : Option Int), cHash d = .ok h → pyHash d = .ok h

/-- `hash(Decimal(10**4300))`: `_pydecimal.__hash__` calls `int(self._int)`. -/
theorem hashTwinsAgree_refuted : ¬HashTwinsAgree := by
  intro h
  have hv : pyHash (.fin false (10 ^ 4300) 0) = .error (.valueError (limitToIntMsg 4301)) := by
    set_option maxRecDepth 100000 in decide
  have := h (.fin false (10 ^ 4300) 0) _ rfl
  rw [hv] at this
  cases this

/-! ## Integer conversions -/

/-- For every finite value and each of `math.floor` (ROUND_FLOOR),
`math.ceil` (ROUND_CEILING) and `round` (ROUND_HALF_EVEN), `_pydecimal`
returns the correctly rounded int, the one `_decimal` returns. -/
def IntConversionsPy : Prop :=
  ∀ (m : Rounding) (neg : Bool) (c : Nat) (e : Int),
    m = .floor ∨ m = .ceiling ∨ m = .halfEven →
    pyToInt m (.fin neg c e) = .ok (roundToIntExact m neg c e)

/-- `math.floor(Decimal('1E+4300'))`: `_rescale(0, ROUND_FLOOR)` pads the
coefficient to 4301 digits, then `int()` of it fails. (`int(d)` itself
works: `__int__` multiplies by `10**exp` instead.) -/
theorem intConversionsPy_refuted : ¬IntConversionsPy := by
  intro h
  have hv : pyToInt .floor (.fin false 1 4300) = .error (.valueError (limitToIntMsg 4301)) := by
    set_option maxRecDepth 100000 in decide
  have := h .floor false 1 4300 (.inl rfl)
  rw [hv] at this
  cases this

/-! ## Arithmetic -/

/-- `*` under any context never raises `ValueError` (it returns a value, or
raises a trapped decimal signal). -/
def MulNoValueErrorPy : Prop :=
  ∀ (c : Ctx) (a b : Dec) (fl : List Signal) (msg : String),
    (mul c a b).run fl ≠ .error (.valueError msg)

/-- `Decimal('1'*2200) * Decimal('1'*2200)` under the default context: the
exact product has 4400 digits and `_pydecimal.__mul__` formats it with
`str()` before rounding it to 28 digits. -/
theorem mulNoValueErrorPy_refuted : ¬MulNoValueErrorPy := by
  intro h
  let x : Nat := digitsValue (List.replicate 2200 '1')
  have hv : (mul {} (.fin false x 0) (.fin false x 0)).run [] = .error (.valueError limitToStrMsg) := by
    set_option maxRecDepth 100000 in decide
  exact h {} _ _ [] _ hv

/-! ## The tuple constructor -/

/-- For every tuple `(sign, digits, exp)` with an exponent of at most 10^17
in magnitude and at most 10^17 digits (so the value is within the C
limits), if `_pydecimal.Decimal(t)` succeeds then `_decimal.Decimal(t)`
succeeds and both print the same. -/
def TupleTwinsAgree : Prop :=
  ∀ (s : PyVal) (ds : Option (List PyVal)) (e : PyVal) (o : PyObj),
    (∀ x, e.asInt? = some x → x.natAbs ≤ 10 ^ 17) →
    (∀ l, ds = some l → l.length ≤ 10 ^ 17) →
    pyFromTuple s ds e = .ok o →
    ∃ d, cFromTuple s ds e = .ok d ∧ pyStrObj o = .ok (toSci d)

/-- `Decimal((0, (True,), 0))`: `_pydecimal` accepts the bool (an int in
range) and stores `str(True)`, giving `Decimal('True')`; `_decimal` reads it
as 1. -/
theorem tupleTwinsAgree_refuted : ¬TupleTwinsAgree := by
  intro h
  have hpy : pyFromTuple (.int 0) (some [.bool true]) (.int 0) = .ok ⟨false, "True".toList, .num 0⟩ := by decide
  obtain ⟨d, hc, hs⟩ := h _ _ _ _ (by intro x hx; cases hx; decide) (by intro l hl; cases hl; decide) hpy
  have hc' : cFromTuple (.int 0) (some [.bool true]) (.int 0) = .ok (.fin false 1 0) := by decide
  rw [hc'] at hc
  cases hc
  revert hs
  decide

/-! ## Format specifications -/

/-- For both libmpdec versions and every format spec not ending in the C-only,
deprecated type `N`, if `format(_decimal.Decimal(x), spec)` accepts the spec
then so does `_pydecimal` (and so do `float` and `int`). -/
def FormatCAcceptsOnlyPy : Prop :=
  ∀ (lib : LibMpdec) (s : List Nat), s.getLast? ≠ some (cp 'N') →
    cFormat lib s = .accepted → pyFormat s = .accepted

/-- `format(Decimal('1234.5'), '10\x00xyz')`: `_decimal` hands the spec to
libmpdec as a C string, which ends at the NUL, so it formats with width 10;
`_pydecimal` rejects the spec. -/
theorem formatCAcceptsOnlyPy_refuted : ¬FormatCAcceptsOnlyPy := by
  intro h
  have := h .bundled251 [0x31, 0x30, 0, 0x78, 0x79, 0x7A] (by decide) (by decide)
  revert this
  decide

/-- `format(_decimal.Decimal(x), spec)` never raises `UnicodeEncodeError`. -/
def FormatNoEncodeError : Prop :=
  ∀ (lib : LibMpdec) (s : List Nat), cFormat lib s ≠ .unicodeEncodeError

/-- `format(Decimal('1.5'), '\ud800<5')`: a lone surrogate as the fill
character (accepted by `_pydecimal`, `float`, `int` and `Fraction`) makes
`PyUnicode_AsUTF8AndSize` fail. -/
theorem formatNoEncodeError_refuted : ¬FormatNoEncodeError := by
  intro h
  exact h .bundled251 [0xD800, 0x3C, 0x35] (by decide)

end PyLean.Decimal
