import PyLean.Registry
import PyLean.LongObj.PylongInt
import PyLean.LongObj.PylongDiv
import PyLean.LongObj.StrLimit

/-! Registry entries for `int`/`str` conversion and `Lib/_pylong.py`. -/

namespace PyLean.LongObj

open PyLean PyLean.Registry PyLean.MathInt

/-- `hex`, `oct`, `bin` and their prefixes: sign, prefix, and the digits of the magnitude.
Hypotheses: `IsDigits`, `Normal`, no negative zero (type invariants of an object), and the
allocation bound. -/
def FormatBinaryExact : Prop :=
  ∀ (x : Long) (base : Nat) (alt : Bool), (base = 2 ∨ base = 8 ∨ base = 16) → IsDigits x.ds →
    Normal x.ds → (x.neg = true → x.ds ≠ []) → x.ds.length ≤ maxLongDigits →
    longFormatBinary x base alt = .ok ((if x.neg then ['-'] else []) ++
      (if alt then ['0', if base = 16 then 'x' else if base = 8 then 'o' else 'b'] else []) ++
      Nat.toDigits base (val x.ds))

theorem formatBinaryExact_proven : FormatBinaryExact :=
  fun x base alt h1 h2 h3 h4 h5 => longFormatBinary_spec x base alt h1 h2 h3 h4 h5

/-- `_pylong.int_to_decimal_string` gives the decimal expansion, for any leaf `str` that is
correct below its 1001-digit cut. -/
def PylongDecimalExact : Prop :=
  ∀ (strf : Int → Py (List Char)), (∀ n : Nat, n < 10 ^ 1001 → strf n = .ok (Nat.toDigits 10 n)) →
    ∀ n : Int, intToDecimalString strf n = .ok (decStr n)

theorem pylongDecimalExact_proven : PylongDecimalExact := fun _ h n => intToDecimalString_spec h n

/-- `_pylong.compute_powers` holds exactly the powers it promises, and all its internal
assertions hold. -/
def ComputePowersExact : Prop :=
  ∀ (w base M : Nat) (needHi : Bool),
    ∃ d, computePowersNat w base M needHi = .ok d ∧
      (∀ k v, dGet k d = some v → v = base ^ k) ∧
      ∀ k, (dGet k d).isSome ↔ ∃ x, Reach M w x ∧ M < x ∧ k = whichOf needHi x

theorem computePowersExact_proven : ComputePowersExact := computePowersNat_spec

/-- `_pylong._divmod_pos` is exact division. This discharges the assumption of
`mathint-divmod-floor` about the `_pylong` branch of `l_divmod`. -/
def PylongDivmodExact : Prop :=
  ∀ a b : Nat, 0 < b → divmodPos a b = .ok (a / b, a % b)

theorem pylongDivmodExact_proven : PylongDivmodExact := divmodPos_spec

def entriesStr : List Entry := [
  { id := "longobj-int-bytes-grammar", pyFile := "Objects/longobject.c"
    pyFns := ["_PyLong_FromBytes", "PyLong_FromString", "long_from_string_base", "long_from_binary_base",
      "long_from_non_binary_base", "pylong_int_from_string"]
    statement := "Below two million characters, int(bytes, base) accepts exactly the literals of the documented grammar, with their value, and raises the 4300-digit-limit ValueError exactly where it applies."
    source := "int() docs; sys.set_int_max_str_digits docs", status := .proven
    prop := ``IntBytesGrammar, thm := some ``intBytesGrammar_proven
    notes := "The two-million bound is on input length, stated in the property; the digit loops are proven at every size below it." },
  { id := "longobj-int-str-grammar", pyFile := "Objects/longobject.c", pyFns := ["PyLong_FromUnicodeObject"]
    statement := "int(str, base) is the same after _PyUnicode_TransformDecimalAndSpaceToASCII."
    source := "int() docs", status := .proven
    prop := ``IntStrGrammar, thm := some ``intStrGrammar_proven },
  { id := "longobj-str-round-trip", pyFile := "Objects/longobject.c"
    pyFns := ["long_to_decimal_string_internal", "long_to_decimal_string", "pylong_int_to_decimal_string"]
    statement := "int(str(n)) == n for every n within the digit limit, below two million digits."
    source := "invariant: round trip", status := .proven
    prop := ``RoundTripDecimal, thm := some ``roundTripDecimal_proven },
  { id := "longobj-str-exact", pyFile := "Objects/longobject.c"
    pyFns := ["long_to_decimal_string_internal", "long_to_decimal_string", "pylong_int_to_decimal_string"]
    statement := "For every int and every accepted limit, str(int) either raises the limit ValueError with its exact message (below 1001 digits of 2**30 exactly when the digit count exceeds a non-zero limit, above that exactly when the pre-check fires) or returns the canonical decimal string: an optional '-', then digits with no leading zero, no '+' and no '_'."
    source := "str() docs; sys.set_int_max_str_digits docs; invariant: canonical output", status := .proven
    prop := ``StrIntExact, thm := some ``strIntExact_proven
    notes := "This is longToDecimalString_eq with decStr_canonical. It shows the limit bypass of longobj-str-digit-limit on the _pylong path." },
  { id := "longobj-pylong-to-decimal-paths", pyFile := "Objects/longobject.c"
    pyFns := ["pylong_int_to_decimal_string"]
    statement := "pylong_int_to_decimal_string passes an import failure and an exception from _pylong.int_to_decimal_string through, raises 'TypeError: _pylong.int_to_decimal_string did not return a str' for a non-str result, and otherwise returns that str's characters, for an arbitrary (replaced) _pylong."
    source := "longobject.c:2033-2045", status := .proven
    prop := ``PylongToDecimalPaths, thm := some ``pylongToDecimalPaths_proven
    notes := "Smoke-tested on 3.15.2 by replacing _pylong.int_to_decimal_string and by sys.modules['_pylong'] = None. A str subclass result is returned as that object (PyUnicode_Check accepts it); the model keeps its characters. Writer MemoryError is out of scope." },
  { id := "longobj-str-digit-limit", pyFile := "Objects/longobject.c"
    pyFns := ["long_to_decimal_string_internal", "long_to_decimal_string", "pylong_int_to_decimal_string"]
    statement := "For every limit >= 640, str(int) raises ValueError exactly when the decimal digit count (without the sign) exceeds the limit, and otherwise returns the digits."
    source := "Doc/builtins/stdtypes.rst:6820-6824 (\"When an operation would exceed the limit, a ValueError is raised\")", status := .refuted
    prop := ``StrDigitLimitExact, thm := some ``strDigitLimitExact_refuted
    bug := some "longobj-str-digits-limit-pylong-path"
    notes := "Counterexample: limit 10000, str(10**10050) returns 10051 digits. Above 1000 digits of 2**30 the code switches to _pylong right after the rough pre-check, and the exact check at :2207-2217 is never reached. Holds for every limit below 9000: longobj-str-digit-limit-below-9000." },
  { id := "longobj-str-digit-limit-below-9000", pyFile := "Objects/longobject.c"
    pyFns := ["long_to_decimal_string_internal", "long_to_decimal_string", "pylong_int_to_decimal_string"]
    statement := "For every limit from 640 to 8999, str(int) raises the limit ValueError exactly when the decimal digit count exceeds the limit, and otherwise returns the digits."
    source := "Doc/builtins/stdtypes.rst:6820-6824, narrowed to where it holds", status := .proven
    prop := ``StrDigitLimitBelow9000, thm := some ``strDigitLimitBelow9000_proven
    notes := "The default limit 4300 is in this range. Below 9000, limit // 90 <= 99, so the pre-check fires on every value of more than 1000 digits of 2**30." },
  { id := "longobj-radix-round-trip", pyFile := "Objects/longobject.c"
    pyFns := []
    statement := "int(format(n, 'b'/'o'/'x'), base) == n, and the same through bin, oct and hex with base the radix or 0; power-of-two bases are free of the limit."
    source := "invariant: round trip", status := .proven
    prop := ``RoundTripRadix, thm := some ``roundTripRadix_proven },
  { id := "longobj-format-binary", pyFile := "Objects/longobject.c", pyFns := ["long_format_binary"]
    statement := "hex, oct and bin return the sign, the prefix and the digits of the magnitude."
    source := "bin(), oct(), hex() docs", status := .proven
    prop := ``FormatBinaryExact, thm := some ``formatBinaryExact_proven },
  { id := "longobj-pylong-decimal", pyFile := "Lib/_pylong.py"
    pyFns := ["int_to_decimal_string"]
    statement := "_pylong.int_to_decimal_string gives the decimal expansion, for any leaf str correct below its cut."
    source := "_pylong.py docstring; twin of long_to_decimal_string", status := .proven
    prop := ``PylongDecimalExact, thm := some ``pylongDecimalExact_proven
    notes := "Above 450000 bits int_to_decimal uses the decimal module; that path is modelled as its result, since Modules/_decimal is out of scope." },
  { id := "longobj-pylong-powers", pyFile := "Lib/_pylong.py", pyFns := ["compute_powers"]
    statement := "compute_powers returns a dict of exactly the promised keys, each mapped to the right power."
    source := "compute_powers docstring", status := .proven
    prop := ``ComputePowersExact, thm := some ``computePowersExact_proven },
  { id := "longobj-pylong-from-string", pyFile := "Lib/_pylong.py"
    pyFns := ["_str_to_int_inner"]
    statement := "The path of int(str) through _pylong gives the same value as the grammar, up to the two-million bound."
    source := "twin of long_from_non_binary_base", status := .proven
    prop := ``IntStrGrammar, thm := some ``intStrGrammar_proven },
  { id := "longobj-pylong-divmod", pyFile := "Lib/_pylong.py"
    pyFns := ["_divmod_pos", "_div2n1n", "_div3n2n", "_int2digits", "_digits2int"]
    statement := "_pylong._divmod_pos, with Burnikel-Ziegler's _div2n1n and _div3n2n, is exact division for all a and b > 0."
    source := "twin of long_divrem", status := .proven
    prop := ``PylongDivmodExact, thm := some ``pylongDivmodExact_proven }
]

end PyLean.LongObj
