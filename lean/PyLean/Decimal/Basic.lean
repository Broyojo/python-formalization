import PyLean.Core

/-!
Shared vocabulary for the `decimal` model: the value type, character
classes, the `int_max_str_digits` limit, libmpdec's 64-bit limits and the
scientific string conversion.

Two implementations are modelled side by side:

* `_pydecimal` (`Lib/_pydecimal.py`, the pure-Python twin), whose `Decimal`
  object has the attributes `_sign` (0/1), `_int` (the coefficient as a
  string of ASCII digits), `_exp` (an int, or `'F'`, `'n'`, `'N'` for
  Infinity, quiet NaN, signaling NaN) and `_is_special`;
* `_decimal` (`Modules/_decimal/_decimal.c` over libmpdec, the C twin),
  whose `mpd_t` holds a sign, a coefficient, an exponent and special flags.

For every value either twin can build from a well-formed input, both carry
the same information, captured by `Dec`. `_pydecimal`'s `_int` is the decimal
spelling of `Dec.fin`'s `coeff` (`str(int(...))` everywhere it is built,
_pydecimal.py:596, :622, :637), except when a constructor is fed digits
that are not plain ints; that case is modelled separately in `Tuple.lean`.
-/

namespace PyLean.Decimal

open PyLean

/-- A decimal value: a finite number `(-1)^neg * coeff * 10^exp`, an
infinity, or a (signaling) NaN with a diagnostic payload (`0` = none). -/
inductive Dec where
  | fin (neg : Bool) (coeff : Nat) (exp : Int)
  | inf (neg : Bool)
  | nan (neg : Bool) (signaling : Bool) (payload : Nat)
  deriving Repr, DecidableEq, Inhabited

/-! ## Decimal digits -/

/-- `len(str(n))`. -/
def numDigits (n : Nat) : Nat := (Nat.toDigits 10 n).length

/-- `sys.flags.int_max_str_digits` default, Include/internal/pycore_long.h:29. -/
def maxStrDigits : Nat := 4300

/-- `_MAX_STR_DIGITS_ERROR_FMT_TO_INT`, Objects/longobject.c:32. -/
def limitToIntMsg (digits : Nat) : String :=
  s!"Exceeds the limit (4300 digits) for integer string conversion: value has {digits} digits; use sys.set_int_max_str_digits() to increase the limit"

/-- `_MAX_STR_DIGITS_ERROR_FMT_TO_STR`, Objects/longobject.c:33. -/
def limitToStrMsg : String :=
  "Exceeds the limit (4300 digits) for integer string conversion; use sys.set_int_max_str_digits() to increase the limit"

/-- `int(s)` for a string of `n` decimal digits (Objects/longobject.c:3022-3032:
the digit count, leading zeros included, is compared with the limit). -/
def intLimit (n : Nat) : Py Unit :=
  if n > maxStrDigits then .error (.valueError (limitToIntMsg n)) else .ok ()

/-- `str(i)` for an int with `|i| = n` (Objects/longobject.c:2207-2216). -/
def strLimit (n : Nat) : Py Unit :=
  if numDigits n > maxStrDigits then .error (.valueError limitToStrMsg) else .ok ()

/-! ## Character classes (Unicode 16.0, as in CPython 3.14) -/

/-- First code point of every run of ten `Nd` characters (`str.isdecimal()`,
`\d` in a `str` pattern, `Py_UNICODE_TODECIMAL >= 0`). Every `Nd` character
is `zero + k` for one of these zeros and `0 <= k <= 9`, with value `k`. -/
def ndZeros : List Nat := [
  0x30, 0x660, 0x6f0, 0x7c0, 0x966, 0x9e6, 0xa66, 0xae6, 0xb66, 0xbe6, 0xc66,
  0xce6, 0xd66, 0xde6, 0xe50, 0xed0, 0xf20, 0x1040, 0x1090, 0x17e0, 0x1810,
  0x1946, 0x19d0, 0x1a80, 0x1a90, 0x1b50, 0x1bb0, 0x1c40, 0x1c50, 0xa620,
  0xa8d0, 0xa900, 0xa9d0, 0xa9f0, 0xaa50, 0xabf0, 0xff10, 0x104a0, 0x10d30,
  0x10d40, 0x11066, 0x110f0, 0x11136, 0x111d0, 0x112f0, 0x11450, 0x114d0,
  0x11650, 0x116c0, 0x116d0, 0x116da, 0x11730, 0x118e0, 0x11950, 0x11bf0,
  0x11c50, 0x11d50, 0x11da0, 0x11f50, 0x16130, 0x16a60, 0x16ac0, 0x16b50,
  0x16d70, 0x1ccf0, 0x1d7ce, 0x1d7d8, 0x1d7e2, 0x1d7ec, 0x1d7f6, 0x1e140,
  0x1e2f0, 0x1e4f0, 0x1e5f1, 0x1e950, 0x1fbf0]

/-- The decimal value of an `Nd` character, `none` otherwise. -/
def digitVal (c : Char) : Option Nat :=
  let n := c.toNat
  match ndZeros.find? (fun z => z ≤ n ∧ n ≤ z + 9) with
  | some z => some (n - z)
  | none => none

def isDigit (c : Char) : Bool := (digitVal c).isSome

/-- `str.isspace()` / `Py_UNICODE_ISSPACE` (Objects/unicodetype_db.h
`_PyUnicode_IsWhitespace`). -/
def isSpace (c : Char) : Bool :=
  let n := c.toNat
  (0x09 ≤ n && n ≤ 0x0D) || (0x1C ≤ n && n ≤ 0x20) || n == 0x85 || n == 0xA0 ||
  n == 0x1680 || (0x2000 ≤ n && n ≤ 0x200A) || n == 0x2028 || n == 0x2029 ||
  n == 0x202F || n == 0x205F || n == 0x3000

/-- `str.strip()` with no argument (Objects/unicodeobject.c `do_strip`,
`Py_UNICODE_ISSPACE` at both ends); also `numeric_as_ascii`'s `strip_ws`
loops, Modules/_decimal/_decimal.c:2291-2298. -/
def strip (s : List Char) : List Char :=
  ((s.dropWhile isSpace).reverse.dropWhile isSpace).reverse

/-- Value of a list of `Nd` characters read as a decimal numeral. -/
def digitsValue (cs : List Char) : Nat :=
  cs.foldl (fun acc c => acc * 10 + (digitVal c).getD 0) 0

/-! ## libmpdec limits on 64-bit builds (libmpdec/mpdecimal.h:135-154) -/

def mpdSsizeMax : Int := 2 ^ 63 - 1
def mpdSsizeMin : Int := -(2 ^ 63)
def mpdMaxPrec : Int := 999999999999999999
def mpdMaxEmax : Int := 999999999999999999
def mpdMinEmin : Int := -999999999999999999
def mpdMinEtiny : Int := mpdMinEmin - (mpdMaxPrec - 1)
def mpdExpInf : Int := 2000000000000000001

/-- A finite value `coeff * 10^exp` (or a NaN payload) that libmpdec's
`mpd_maxcontext` represents without rounding or clamping: `_mpd_check_exp`
and `_mpd_check_round` (libmpdec/mpdecimal.c:1823-1966) under
`prec = MPD_MAX_PREC`, `emax = MPD_MAX_EMAX`, `emin = MPD_MIN_EMIN`,
`clamp = 0` raise none of Clamped, Rounded, Inexact exactly when the
coefficient has at most `MPD_MAX_PREC` digits, the adjusted exponent is at
most `MPD_MAX_EMAX` and the exponent is at least `MPD_MIN_ETINY`. These are
the documented limits of the C module (Doc/library/decimal.rst, "Constants"). -/
def InCLimits : Dec → Prop
  | .fin _ c e => (numDigits c : Int) ≤ mpdMaxPrec ∧ e + numDigits c - 1 ≤ mpdMaxEmax ∧ mpdMinEtiny ≤ e
  | .inf _ => True
  | .nan _ _ p => (numDigits p : Int) ≤ mpdMaxPrec

instance (d : Dec) : Decidable (InCLimits d) := by
  cases d <;> simp only [InCLimits] <;> infer_instance

/-! ## Exceptions -/

/-- `decimal.InvalidOperation` raised by a trapped signal. The message of the
C twin is the list of signals, the Python twin's is an explanation; neither
is modelled (`~`). -/
def invalidOp : PyExc := .named "InvalidOperation" "~"

/-! ## `__str__` (to-scientific-string) -/

/-- `"%+d" % n`. -/
def fmtSigned (n : Int) : List Char :=
  (if n < 0 then '-' else '+') :: Nat.toDigits 10 n.natAbs

/-- The finite branch of `Decimal.__str__(eng=False)`, _pydecimal.py:1091-1126,
for `_int = ds` (a non-empty digit string), `_exp = e` and the context's
`capitals`. The C twin's `mpd_to_sci` (libmpdec/io.c `_mpd_to_string` with
`MPD_DEFAULT_DOTPLACE`) produces the same spelling. -/
def sciFinite (neg : Bool) (ds : List Char) (e : Int) (caps : Bool) : List Char :=
  let sign := if neg then ['-'] else []
  let leftdigits : Int := e + ds.length
  let dotplace : Int := if e ≤ 0 ∧ leftdigits > -6 then leftdigits else 1
  let (intpart, fracpart) :=
    if dotplace ≤ 0 then (['0'], '.' :: (List.replicate (-dotplace).toNat '0' ++ ds))
    else if dotplace ≥ ds.length then (ds ++ List.replicate (dotplace - ds.length).toNat '0', [])
    else (ds.take dotplace.toNat, '.' :: ds.drop dotplace.toNat)
  let exp := if leftdigits = dotplace then [] else
    (if caps then 'E' else 'e') :: fmtSigned (leftdigits - dotplace)
  sign ++ intpart ++ fracpart ++ exp

/-- `str(d)` (`capitals = 1`, the default). Specials: _pydecimal.py:1082-1089. -/
def toSci (d : Dec) (caps : Bool := true) : List Char :=
  match d with
  | .inf neg => (if neg then ['-'] else []) ++ "Infinity".toList
  | .nan neg sig p =>
    (if neg then ['-'] else []) ++ (if sig then "sNaN" else "NaN").toList ++
      (if p = 0 then [] else Nat.toDigits 10 p)
  | .fin neg c e => sciFinite neg (Nat.toDigits 10 c) e caps

/-- The adjusted exponent `exp + len(_int) - 1` (`Decimal.adjusted`). -/
def adjusted (c : Nat) (e : Int) : Int := e + numDigits c - 1

end PyLean.Decimal
