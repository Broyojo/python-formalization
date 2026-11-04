import PyLean.Binary64.Model

/-!
`Objects/floatobject.c`, CPython 3.15.2, on top of the exact binary64 model:
arithmetic, comparison with exact ints, `hash`, `is_integer`, the integer
conversions, `hex`, `fromhex`, `as_integer_ratio`, `pow`, `divmod`, `//`, `%`,
`__getformat__` and the pack/unpack routines.

3.15 dropped the `unknown_format` branches of `PyFloat_Pack4/8` and
`PyFloat_Unpack4/8`, so the pack and unpack routines below are the whole bodies. The
models assume a little-endian platform (`_PY_FLOAT_LITTLE_ENDIAN`), like the machines
they are tested on.

The decimal paths (`repr`, `float(str)`, `round(x, n)`) live in `Dtoa.lean` and
`Strtod.lean`, on top of the mirror of `Python/dtoa.c`.
-/

namespace PyLean.Binary64

open PyLean

/-- The small part of the object model that float code looks at. -/
inductive Obj where
  | float (x : F64)
  /-- A strict subclass of `float`, by type name. -/
  | floatSub (ty : String) (x : F64)
  | int (n : Int)
  /-- Anything else: its `tp_name`, what its `__float__` and `__index__` return, when it
  defines them, and its fully qualified name (what `%T` prints), which differs from
  `tp_name` only for a class outside `builtins`. -/
  | other (ty : String) (dunderFloat : Option Obj) (dunderIndex : Option Int)
      (fq : String := ty)
  deriving Repr, Inhabited

/-! ## Constants -/

def d0 : F64 := F64.zero false
def d1 : F64 := F64.one
def dm1 : F64 := F64.one.neg
def d2 : F64 := F64.ofBits 0x4000000000000000
def d16 : F64 := F64.ofBits 0x4030000000000000
def dHalf : F64 := F64.ofBits 0x3fe0000000000000

/-- `PyFloat_GetMax`, floatobject.c:32-36. -/
def PyFloat_GetMax : F64 := F64.maxFinite

/-- `PyFloat_GetMin`, floatobject.c:38-42. -/
def PyFloat_GetMin : F64 := F64.ofBits 0x0010000000000000

/-- `sys.float_info`, `PyFloat_GetInfo`, floatobject.c:82-122. -/
structure FloatInfo where
  max : F64
  max_exp : Int
  max_10_exp : Int
  min : F64
  min_exp : Int
  min_10_exp : Int
  dig : Int
  mant_dig : Int
  epsilon : F64
  radix : Int
  rounds : Int

def PyFloat_GetInfo : FloatInfo :=
  { max := PyFloat_GetMax, max_exp := 1024, max_10_exp := 308
    min := PyFloat_GetMin, min_exp := -1021, min_10_exp := -307
    dig := 15, mant_dig := 53, epsilon := F64.ofBits 0x3cb0000000000000
    radix := 2, rounds := 1 }

/-! ## Conversions shared with `Objects/longobject.c` -/

/-- `PyLong_AsDouble`, longobject.c:3567-3596. `_PyLong_Frexp` rounds half to even,
so this is the exact value rounded, with an error for what rounds past `DBL_MAX`. -/
def PyLong_AsDouble (n : Int) : Py F64 :=
  let r := F64.ofInt n
  if r.isInf then .error (.overflowError "int too large to convert to float") else .ok r

/-- `PyLong_FromDouble`, longobject.c:469-514: truncation toward zero, with the
checks in source order. -/
def PyLong_FromDouble (x : F64) : Py Int :=
  if x.isInf then .error (.overflowError "cannot convert float infinity to integer")
  else if x.isNaN then .error (.valueError "cannot convert float NaN to integer")
  else .ok x.truncInt

/-- `_Py_convert_int_to_double`, floatobject.c:319-336, joined with the
`CONVERT_TO_DOUBLE` macro at :311-315. `none` is `NotImplemented`. -/
def convertToDouble (v : Obj) : Py (Option F64) :=
  match v with
  | .float x | .floatSub _ x => .ok (some x)
  | .int n => do return some (← PyLong_AsDouble n)
  | .other .. => .ok none

/-- `PyFloat_AsDouble`, floatobject.c:247-303, for one level of `__float__`. The
`DeprecationWarning` for a strict subclass result does not change the value. -/
def PyFloat_AsDouble (op : Obj) : Py F64 :=
  match op with
  | .float x | .floatSub _ x => .ok x
  | .int n => PyLong_AsDouble n
  | .other _ none (some i) _ => PyLong_AsDouble i
  | .other ty none none _ => .error (.typeError s!"must be real number, not {ty}")
  | .other _ (some r) _ fq =>
    match r with
    | .float x | .floatSub _ x => .ok x
    | .int .. => .error (.typeError s!"{fq}.__float__() must return a float, not int")
    | .other _ _ _ rfq => .error (.typeError s!"{fq}.__float__() must return a float, not {rfq}")

/-! ## Comparison -/

inductive CmpOp where
  | lt | le | eq | ne | gt | ge
  deriving DecidableEq, Repr

/-- The `Compare:` block, floatobject.c:507-528. -/
def compareDoubles (op : CmpOp) (i j : F64) : Bool :=
  match op with
  | .eq => F64.eq i j
  | .ne => F64.ne i j
  | .le => F64.le i j
  | .ge => F64.ge i j
  | .lt => F64.lt i j
  | .gt => F64.gt i j

/-- `PyObject_RichCompareBool` on two ints. -/
def compareInts (op : CmpOp) (a b : Int) : Bool :=
  match op with
  | .eq => a == b
  | .ne => a != b
  | .le => decide (a ≤ b)
  | .ge => decide (b ≤ a)
  | .lt => decide (a < b)
  | .gt => decide (b < a)

/-- `_PyLong_NumBits`: bits in the magnitude. -/
def numBits (n : Int) : Nat := bitLength n.natAbs

/-- The `PyLong_Check(w)` branch of `float_richcompare`, floatobject.c:397-502,
for a finite `i`. -/
def compareFiniteInt (op : CmpOp) (i : F64) (w : Int) : Bool :=
  let vsign : Int := if F64.eq i d0 then 0 else if F64.lt i d0 then -1 else 1
  let wsign : Int := w.sign
  if vsign != wsign then
    compareDoubles op (F64.ofInt vsign) (F64.ofInt wsign)
  else
    let nbits := numBits w
    if 1024 < nbits then
      -- `j = wsign * 2.0`, floatobject.c:423-426
      compareDoubles op (F64.ofInt vsign) (F64.ofInt (wsign * 2))
    else if nbits ≤ 48 then
      compareDoubles op i (F64.ofInt w)
    else
      let exponent := (F64.frexp i).2
      if exponent < nbits then compareDoubles op d0 i
      else if (nbits : Int) < exponent then compareDoubles op i d0
      else
        let intpart := F64.trunc i
        let fracpart := F64.sub i intpart
        let op' : Option CmpOp :=
          if !fracpart.isZero then
            match op with
            | .eq => none
            | .ne => none
            | .lt | .le => some (if 0 < vsign then .lt else .le)
            | .gt | .ge => some (if 0 < vsign then .ge else .gt)
          else some op
        match op' with
        | none => op == .ne
        | some o => compareInts o intpart.truncInt w

/-- `float_richcompare`, floatobject.c:371-532. `none` is `NotImplemented`. -/
def float_richcompare (v : F64) (w : Obj) (op : CmpOp) : Option Bool :=
  match w with
  | .float j | .floatSub _ j => some (compareDoubles op v j)
  | .int n =>
    if !v.isFinite then some (compareDoubles op v d0)
    else some (compareFiniteInt op v n)
  | .other .. => none

/-! ## Hash -/

def hashBits : Nat := 61
def hashModulus : Nat := 2 ^ 61 - 1
def hashInf : Int := 314159

/-- Reinterpret a `Py_uhash_t` as `Py_hash_t`. -/
def toSigned64 (x : Nat) : Int := if x < 2 ^ 63 then x else (x : Int) - 2 ^ 64

/-- Rotate within 61 bits, `((x << n) & MOD) | x >> (BITS - n)`. -/
def hashRotate (x n : Nat) : Nat :=
  (((x * 2 ^ n) % 2 ^ 64) &&& hashModulus) ||| (x / 2 ^ (hashBits - n))

/-- The loop of `_Py_HashDouble`, pyhash.c:112-120: 28 bits at a time. -/
def hashLoop : Nat → F64 → Int → Nat → Int × Nat
  | 0, _, e, x => (e, x)
  | fuel + 1, m, e, x =>
    if m.isZero then (e, x)
    else
      let x1 := hashRotate x 28
      let m1 := F64.mul m (F64.ofBits 0x41b0000000000000)
      let e1 := e - 28
      let y := m1.truncInt.toNat
      let m2 := F64.sub m1 (F64.ofInt y)
      let x2 := x1 + y
      let x3 := if hashModulus ≤ x2 then x2 - hashModulus else x2
      hashLoop fuel m2 e1 x3

/-- `_Py_HashDouble`, pyhash.c:87-132, for a non-NaN `v`. A NaN hashes by object
identity (`PyObject_GenericHash`), which is not a function of its value, so the
result is `none`. -/
def _Py_HashDouble (v : F64) : Option Int :=
  if !v.isFinite then
    if v.isInf then some (if F64.lt d0 v then hashInf else -hashInf) else none
  else
    let (m0, e0) := F64.frexp v
    let (sign, m1) : Int × F64 := if F64.lt m0 d0 then (-1, m0.neg) else (1, m0)
    -- `m` holds at most 53 bits, so the loop runs at most 2 + 53 / 28 times.
    let (e, x) := hashLoop 4 m1 e0 0
    let e' : Nat := if 0 ≤ e then (e % hashBits).toNat
      else (hashBits : Int).toNat - 1 - ((-1 - e) % hashBits).toNat
    let x1 := hashRotate x e'
    let x2 := if sign == -1 then (2 ^ 64 - x1) % 2 ^ 64 else x1
    let x3 := if x2 = 2 ^ 64 - 1 then 2 ^ 64 - 2 else x2
    some (toSigned64 x3)

/-- `float_hash`, floatobject.c:534-539. -/
def float_hash (v : F64) : Option Int := _Py_HashDouble v

/-! ## Binary arithmetic -/

/-- The two `CONVERT_TO_DOUBLE` lines every binary method opens with. -/
def withDoubles {α} (v w : Obj) (k : F64 → F64 → Py α) : Py (Option α) := do
  let some a ← convertToDouble v | return none
  let some b ← convertToDouble w | return none
  return some (← k a b)

/-- `float_add`, floatobject.c:541-549. -/
def float_add (v w : Obj) : Py (Option F64) := withDoubles v w fun a b => .ok (F64.add a b)

/-- `float_sub`, floatobject.c:551-559. -/
def float_sub (v w : Obj) : Py (Option F64) := withDoubles v w fun a b => .ok (F64.sub a b)

/-- `float_mul`, floatobject.c:561-569. -/
def float_mul (v w : Obj) : Py (Option F64) := withDoubles v w fun a b => .ok (F64.mul a b)

def zeroDiv {α} : Py α := .error (.zeroDivisionError "division by zero")

/-- `float_div`, floatobject.c:571-584. -/
def float_div (v w : Obj) : Py (Option F64) :=
  withDoubles v w fun a b => if F64.eq b d0 then zeroDiv else .ok (F64.div a b)

/-- The core of `float_rem`, floatobject.c:593-611. -/
def floatRemCore (vx wx : F64) : Py F64 :=
  if F64.eq wx d0 then zeroDiv
  else
    let m := F64.fmod vx wx
    if !m.isZero then
      -- ensure the remainder has the same sign as the denominator
      if F64.lt wx d0 != F64.lt m d0 then .ok (F64.add m wx) else .ok m
    else .ok (F64.copysign d0 wx)

/-- `float_rem`, floatobject.c:586-612. -/
def float_rem (v w : Obj) : Py (Option F64) := withDoubles v w floatRemCore

/-- `_float_div_mod`, floatobject.c:614-650: `(floordiv, mod)`. -/
def float_div_mod (vx wx : F64) : F64 × F64 :=
  let m0 := F64.fmod vx wx
  let div0 := F64.div (F64.sub vx m0) wx
  let (m1, div1) : F64 × F64 :=
    if !m0.isZero then
      if F64.lt wx d0 != F64.lt m0 d0 then (F64.add m0 wx, F64.sub div0 d1) else (m0, div0)
    else (F64.copysign d0 wx, div0)
  let floordiv :=
    if !div1.isZero then
      let fd := F64.floor div1
      if F64.gt (F64.sub div1 fd) dHalf then F64.add fd d1 else fd
    else F64.copysign d0 (F64.div vx wx)
  (floordiv, m1)

/-- `float_divmod`, floatobject.c:652-665. -/
def float_divmod (v w : Obj) : Py (Option (F64 × F64)) :=
  withDoubles v w fun vx wx => if F64.eq wx d0 then zeroDiv else .ok (float_div_mod vx wx)

/-- `float_floor_div`, floatobject.c:667-680. -/
def float_floor_div (v w : Obj) : Py (Option F64) :=
  withDoubles v w fun vx wx => if F64.eq wx d0 then zeroDiv else .ok (float_div_mod vx wx).1

/-! ## Power -/

/-- What `float_pow` can produce: a float, or a hand-off to `complex_pow`. -/
inductive PowResult where
  | float (x : F64)
  | complexPow (iv iw : F64)
  deriving DecidableEq, Repr

/-- `DOUBLE_IS_ODD_INTEGER`, floatobject.c:684. -/
def isOddInteger (x : F64) : Bool := F64.eq (F64.fmod x.abs d2) d1

/-- `float_pow`, floatobject.c:686-803, after the `CONVERT_TO_DOUBLE` lines, for
any C library `pow`. The body never asks `cpow` about a NaN, an infinity, a zero
base, or a negative base. `_Py_ADJUST_ERANGE1` turns an infinite result into
`ERANGE`, and a C library that sets `ERANGE` on underflow to zero is cleared, so
the only error left is overflow (`glibc` raises no other). -/
def floatPowCore (cpow : F64 → F64 → F64) (iv0 iw : F64) : Py PowResult :=
  if F64.eq iw d0 then .ok (.float d1)
  else if iv0.isNaN then .ok (.float iv0)
  else if iw.isNaN then .ok (.float (if F64.eq iv0 d1 then d1 else iw))
  else if iw.isInf then
    let iv := iv0.abs
    if F64.eq iv d1 then .ok (.float d1)
    else if F64.gt iw d0 == F64.gt iv d1 then .ok (.float iw.abs)
    else .ok (.float d0)
  else if iv0.isInf then
    let iw_is_odd := isOddInteger iw
    if F64.gt iw d0 then .ok (.float (if iw_is_odd then iv0 else iv0.abs))
    else .ok (.float (if iw_is_odd then F64.copysign d0 iv0 else d0))
  else if F64.eq iv0 d0 then
    let iw_is_odd := isOddInteger iw
    if F64.lt iw d0 then .error (.zeroDivisionError "zero to a negative power")
    else .ok (.float (if iw_is_odd then iv0 else d0))
  else
    let step : Option (F64 × Bool) :=
      if F64.lt iv0 d0 then
        if F64.ne iw (F64.floor iw) then none
        else some (iv0.neg, isOddInteger iw)
      else some (iv0, false)
    match step with
    | none => .ok (.complexPow iv0 iw)
    | some (iv, negate_result) =>
      if F64.eq iv d1 then .ok (.float (if negate_result then dm1 else d1))
      else
        let ix0 := cpow iv iw
        let erange := ix0.isInf
        let ix := if negate_result then ix0.neg else ix0
        if erange then .error (.overflowError "~[Errno 34] Numerical result out of range")
        else .ok (.float ix)

/-- `float_pow`, floatobject.c:686-803. -/
def float_pow (cpow : F64 → F64 → F64) (v w : Obj) (z : Option Obj) : Py (Option PowResult) :=
  match z with
  | some _ =>
    .error (.typeError "pow() 3rd argument not allowed unless all arguments are integers")
  | none => withDoubles v w (floatPowCore cpow)

/-! ## Unary methods -/

/-- `float_neg`, floatobject.c:807-812. -/
def float_neg (v : F64) : F64 := v.neg

/-- `float_abs`, floatobject.c:814-819. -/
def float_abs (v : F64) : F64 := v.abs

/-- `float_bool`, floatobject.c:821-826. -/
def float_bool (v : F64) : Bool := F64.ne v d0

/-- `float_is_integer_impl`, floatobject.c:834-853. -/
def float_is_integer (x : F64) : Bool :=
  if !x.isFinite then false else F64.eq (F64.floor x) x

/-- `float___trunc___impl`, floatobject.c:861-866. -/
def float_trunc (x : F64) : Py Int := PyLong_FromDouble x

/-- `float___floor___impl`, floatobject.c:874-880. -/
def float_floor (x : F64) : Py Int := PyLong_FromDouble (F64.floor x)

/-- `float___ceil___impl`, floatobject.c:888-894. -/
def float_ceil (x : F64) : Py Int := PyLong_FromDouble (F64.ceil x)

/-- `round(x)` with no `ndigits`, floatobject.c:1031-1039. -/
def float_round_int (x : F64) : Py Int :=
  let rounded := F64.roundAway x
  let r := if F64.eq (F64.sub x rounded).abs dHalf
    then F64.mul d2 (F64.roundAway (F64.div x d2)) else rounded
  PyLong_FromDouble r

/-- `float_float`, floatobject.c:1068-1077: an exact float itself, or the value of
a subclass instance. -/
def float_float (x : F64) : F64 := x

/-- `float_conjugate_impl`, floatobject.c:1085-1090. -/
def float_conjugate (x : F64) : F64 := float_float x

/-- `float_getreal`, floatobject.c:1703-1707. -/
def float_getreal (x : F64) : F64 := float_float x

/-- `float_getimag`, floatobject.c:1709-1713. -/
def float_getimag (_ : F64) : F64 := d0

/-- `float___getnewargs___impl`, floatobject.c:1664-1669. -/
def float_getnewargs (x : F64) : F64 := x

/-- `float___getformat___impl`, floatobject.c:1689-1701, on a little-endian IEEE
platform. -/
def float_getformat (typestr : String) : Py String :=
  if typestr == "double" || typestr == "float" then .ok "IEEE, little-endian"
  else .error (.valueError "__getformat__() argument 1 must be 'double' or 'float'")

/-! ## `float.hex` -/

/-- `char_from_hex`, floatobject.c:1094-1099. -/
def char_from_hex (x : Nat) : Char :=
  "0123456789abcdef".toList.getD x '?'

/-- The digit loop of `float_hex_impl`, floatobject.c:1186-1191. -/
def hexDigits : Nat → F64 → List Char
  | 0, _ => []
  | n + 1, m =>
    let m1 := F64.mul m d16
    let k := m1.truncInt
    char_from_hex k.toNat :: hexDigits n (F64.sub m1 (F64.ofInt k))

def intToDecimal (n : Nat) : String := toString n

/-- `float_hex_impl`, floatobject.c:1153-1205. `TOHEX_NBITS` is 53, so 13 digits
follow the point. -/
def float_hex (x : F64) : String :=
  if x.isNaN then "nan"
  else if x.isInf then (if x.sign then "-inf" else "inf")
  else if F64.eq x d0 then
    if x.sign then "-0x0.0p+0" else "0x0.0p+0"
  else
    let (m0, e0) := F64.frexp x.abs
    let shift : Int := 1 - max (-1021 - e0) 0
    let m1 := F64.ldexp m0 shift
    let e1 := e0 - shift
    let k := m1.truncInt
    let head := char_from_hex k.toNat
    let digits := hexDigits 13 (F64.sub m1 (F64.ofInt k))
    let s := String.ofList (head :: '.' :: digits)
    let (esign, e) : Char × Nat := if e1 < 0 then ('-', (-e1).toNat) else ('+', e1.toNat)
    let body := "0x" ++ s ++ "p" ++ String.singleton esign ++ intToDecimal e
    if F64.lt x d0 then "-" ++ body else body

/-! ## C strings -/

/-- A NUL-terminated string as a list of bytes: reading past the end gives `0`. -/
def at_ (s : List Nat) (i : Nat) : Nat := s.getD i 0

/-- `Py_ISSPACE`. -/
def isSpace (c : Nat) : Bool := c == 32 || (9 ≤ c && c ≤ 13)

/-- `Py_ISDIGIT`. -/
def isDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57

/-- `Py_TOLOWER`. -/
def toLower (c : Nat) : Nat := if 65 ≤ c && c ≤ 90 then c + 32 else c

/-- `while (p(*s)) s++`. The NUL at the end stops any `p` that rejects `0`, so
`fuel = length + 1` is always enough. -/
def scan (s : List Nat) (p : Nat → Bool) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i => if p (at_ s i) then scan s p fuel (i + 1) else i

def scanFrom (s : List Nat) (p : Nat → Bool) (i : Nat) : Nat := scan s p (s.length + 1) i

/-- `case_insensitive_match`, pystrtod.c:12-20. -/
def case_insensitive_match (s : List Nat) (i : Nat) : List Nat → Bool
  | [] => true
  | t :: ts => toLower (at_ s i) == t && case_insensitive_match s (i + 1) ts

/-- `_Py_parse_inf_or_nan`, pystrtod.c:27-58: the value and the end position. On
failure the value is `-1.0` and the end is `p`. -/
def _Py_parse_inf_or_nan (s : List Nat) (p : Nat) : F64 × Nat :=
  let c := at_ s p
  let (negate, i) : Bool × Nat :=
    if c == 45 then (true, p + 1) else if c == 43 then (false, p + 1) else (false, p)
  if case_insensitive_match s i [105, 110, 102] then
    let j := i + 3
    let j' := if case_insensitive_match s j [105, 110, 105, 116, 121] then j + 5 else j
    (F64.inf negate, j')
  else if case_insensitive_match s i [110, 97, 110] then
    (if negate then F64.qnan.neg else F64.qnan, i + 3)
  else (dm1, p)

/-! ## `float.fromhex` -/

/-- `hex_from_char`, floatobject.c:1131-1134: `-1` becomes `none`. -/
def hex_from_char (c : Nat) : Option Nat :=
  if 48 ≤ c && c ≤ 57 then some (c - 48)
  else if 97 ≤ c && c ≤ 102 then some (c - 87)
  else if 65 ≤ c && c ≤ 70 then some (c - 55)
  else none

def isHex (c : Nat) : Bool := (hex_from_char c).isSome

def longMax : Int := 2 ^ 63 - 1
def longMin : Int := -(2 ^ 63)

/-- C truncating `/` by 2 of `LONG_MIN`. -/
def longMinDiv2 : Int := -(2 ^ 62)
def longMaxDiv2 : Int := 2 ^ 62 - 1

/-- `strtol(s + start, NULL, 10)` for `[sign] digits`, saturating. -/
def strtolClip (s : List Nat) (start stop : Nat) : Int :=
  let c := at_ s start
  let neg := c == 45
  let i := if c == 45 || c == 43 then start + 1 else start
  let v := ((List.range (stop - i)).foldl (fun acc k => 10 * acc + (at_ s (i + k) - 48)) 0 : Nat)
  if neg then max (-(v : Int)) longMin else min (v : Int) longMax

def hexOverflow {α} : Py α :=
  .error (.overflowError "hexadecimal value too large to represent as a float")

def hexParseError {α} : Py α :=
  .error (.valueError "invalid hexadecimal floating-point string")

/-- `HEX_DIGIT(j)`, floatobject.c:1358-1360. -/
def hexDigit (s : List Nat) (coeff_end fdigits j : Nat) : Nat :=
  (hex_from_char (at_ s (if j < fdigits then coeff_end - j else coeff_end - 1 - j))).getD 0

/-- `for (i = hi; i > stop; i--) x = 16.0*x + HEX_DIGIT(i-1)`. -/
def hexAccum (dig : Nat → Nat) : Nat → Nat → F64 → F64
  | 0, _, x => x
  | n + 1, i, x =>
    hexAccum dig n (i - 1) (F64.add (F64.mul d16 x) (F64.ofInt (dig i)))

/-- Discard leading zeros, floatobject.c:1367-1368. -/
def dropLeadingZeros (dig : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if dig n == 0 then dropLeadingZeros dig n else n + 1

/-- `for (digit = d; digit != 0; digit /= 2) top_exp++`, floatobject.c:1381-1382. -/
def bitsOfDigit (d : Nat) : Nat := bitLength d

/-- The body of `float_fromhex_impl` from the digit scan on, floatobject.c:1366-1435.
It returns the unsigned value. An overflow returns straight away, without reaching
the trailing-whitespace check at `finished:`. -/
def hexValue (dig : Nat → Nat) (ndigits0 fdigits : Nat) (exp0 : Int) : Py F64 :=
  let ndigits := dropLeadingZeros dig ndigits0
  if ndigits == 0 || decide (exp0 < longMinDiv2) then .ok d0
  else if longMaxDiv2 < exp0 then hexOverflow
  else
    let exp : Int := exp0 - 4 * (fdigits : Int)
    let top_exp : Int := exp + 4 * ((ndigits : Int) - 1) + bitsOfDigit (dig (ndigits - 1))
    if top_exp < -1074 then .ok d0
    else if 1024 < top_exp then hexOverflow
    else
      let lsb : Int := max top_exp (-1021) - 53
      if lsb ≤ exp then
        let x := hexAccum dig ndigits (ndigits - 1) d0
        .ok (F64.ldexp x exp)
      else
        let half_eps : Nat := 2 ^ ((lsb - exp - 1) % 4).toNat
        let key_digit : Nat := ((lsb - exp - 1) / 4).toNat
        let x0 := hexAccum dig (ndigits - 1 - key_digit) (ndigits - 1) d0
        let digit := dig key_digit
        let x1 := F64.add (F64.mul d16 x0) (F64.ofInt (digit &&& (16 - 2 * half_eps) : Nat))
        let round_up : Bool :=
          (digit &&& half_eps) != 0 &&
            ((digit &&& (3 * half_eps - 1)) != 0 ||
              (half_eps == 8 && decide (key_digit + 1 < ndigits) && (dig (key_digit + 1) &&& 1) != 0) ||
              (List.range key_digit).any (fun i => dig i != 0))
        if round_up then
          let x2 := F64.add x1 (F64.ofInt (2 * half_eps : Nat))
          if top_exp == 1024 && F64.eq x2 (F64.ldexp (F64.ofInt (2 * half_eps : Nat)) 53) then
            hexOverflow
          else .ok (F64.ldexp x2 (exp + 4 * (key_digit : Int)))
        else .ok (F64.ldexp x1 (exp + 4 * (key_digit : Int)))

/-- `finished:`, floatobject.c:1437-1443. -/
def hexFinish (s : List Nat) (i : Nat) (x : F64) (negate : Bool) : Py F64 :=
  let i' := scanFrom s isSpace i
  if i' != s.length then hexParseError
  else .ok (if negate then x.neg else x)

/-- `float_fromhex_impl`, floatobject.c:1224-1463, over the UTF-8 bytes of the
argument. -/
def float_fromhex (s : List Nat) : Py F64 :=
  let s0 := scanFrom s isSpace 0
  let (x, coeff_end0) := _Py_parse_inf_or_nan s s0
  if coeff_end0 != s0 then hexFinish s coeff_end0 x false
  else
    let c := at_ s s0
    let (negate, s1) : Bool × Nat :=
      if c == 45 then (true, s0 + 1) else if c == 43 then (false, s0 + 1) else (false, s0)
    let s2 :=
      if at_ s s1 == 48 && (at_ s (s1 + 1) == 120 || at_ s (s1 + 1) == 88) then s1 + 2 else s1
    let coeff_start := s2
    let s3 := scanFrom s isHex s2
    let s_store := s3
    let (s4, coeff_end) : Nat × Nat :=
      if at_ s s3 == 46 then
        let t := scanFrom s isHex (s3 + 1)
        (t, t - 1)
      else (s3, s3)
    let ndigits := coeff_end - coeff_start
    let fdigits := coeff_end - s_store
    if ndigits == 0 then hexParseError
    else if (2 ^ 62 - 1074) / 4 < ndigits then
      .error (.valueError "hexadecimal string too long to convert")
    else
      let parsed : Py (Nat × Int) :=
        if at_ s s4 == 112 || at_ s s4 == 80 then
          let exp_start := s4 + 1
          let c1 := at_ s exp_start
          let t := if c1 == 45 || c1 == 43 then exp_start + 1 else exp_start
          if !isDigit (at_ s t) then hexParseError
          else
            let t' := scanFrom s isDigit (t + 1)
            .ok (t', strtolClip s exp_start t')
        else .ok (s4, 0)
      match parsed with
      | .error e => .error e
      | .ok (s5, exp) =>
        match hexValue (hexDigit s coeff_end fdigits) ndigits fdigits exp with
        | .error e => .error e
        | .ok v => hexFinish s s5 v negate

/-! ## `as_integer_ratio` -/

/-- The loop of `float_as_integer_ratio_impl`, floatobject.c:1512-1515. -/
def ratioLoop : Nat → F64 → Int → F64 × Int
  | 0, f, e => (f, e)
  | n + 1, f, e =>
    if F64.ne f (F64.floor f) then ratioLoop n (F64.mul f d2) (e - 1) else (f, e)

/-- `float_as_integer_ratio_impl`, floatobject.c:1482-1552. -/
def float_as_integer_ratio (x : F64) : Py (Int × Int) :=
  if x.isInf then .error (.overflowError "cannot convert Infinity to integer ratio")
  else if x.isNaN then .error (.valueError "cannot convert NaN to integer ratio")
  else
    let (f0, e0) := F64.frexp x
    let (f, exponent) := ratioLoop 300 f0 e0
    match PyLong_FromDouble f with
    | .error e => .error e
    | .ok numerator =>
      if 0 < exponent then .ok (numerator * 2 ^ exponent.toNat, 1)
      else .ok (numerator, 2 ^ (-exponent).toNat)

/-! ## Pack and unpack -/

/-- Lay `n` big-endian bytes of `v` out in the requested byte order. -/
def layout (n v : Nat) (le : Bool) : List Nat :=
  let be := (List.range n).map fun i => (v / 2 ^ (8 * (n - 1 - i))) % 256
  if le then be.reverse else be

def unlayout (b : List Nat) (le : Bool) : Nat :=
  (if le then b.reverse else b).foldl (fun acc c => acc * 256 + c) 0

def pack2Overflow {α} : Py α :=
  .error (.overflowError "float too large to pack with e format")

/-- The finite nonzero branch of `PyFloat_Pack2`, floatobject.c:1927-1977, after
the sign has been taken off. -/
def pack2Finite (x : F64) : Py (Nat × Nat) :=
  let (f0, e0) := F64.frexp x
  let f1 := F64.mul f0 d2
  let e1 := e0 - 1
  if 16 ≤ e1 then pack2Overflow
  else
    let (f2, e2) : F64 × Int :=
      if e1 < -25 then (d0, 0)
      else if e1 < -14 then (F64.ldexp f1 (14 + e1), 0)
      else (F64.sub f1 d1, e1 + 15)
    let f3 := F64.mul f2 (F64.ofBits 0x4090000000000000)
    let bits := f3.truncInt.toNat
    let d := F64.sub f3 (F64.ofInt bits)
    if F64.gt d dHalf || (F64.eq d dHalf && bits % 2 == 1) then
      let b1 := bits + 1
      if b1 == 1024 then
        let e3 := e2 + 1
        if e3 == 31 then pack2Overflow else .ok (e3.toNat, 0)
      else .ok (e2.toNat, b1)
    else .ok (e2.toNat, bits)

/-- `PyFloat_Pack2`, floatobject.c:1894-2000. -/
def PyFloat_Pack2 (x : F64) (le : Bool) : Py (List Nat) :=
  let finish (sign : Bool) (e bits : Nat) : Py (List Nat) :=
    .ok (layout 2 (bits ||| (e * 1024) ||| ((if sign then 1 else 0) * 2 ^ 15)) le)
  if x.isZero then finish x.sign 0 0
  else if x.isInf then finish (F64.lt x d0) 0x1f 0
  else if x.isNaN then
    let v := x.bits &&& 0xffc0000000000
    let bits := v / 2 ^ 42
    finish x.sign 0x1f (if bits == 0 then bits ||| 512 else bits)
  else
    let sign := F64.lt x d0
    match pack2Finite (if sign then x.neg else x) with
    | .error e => .error e
    | .ok (e, bits) => finish sign e bits

/-- `(float)x` on x86-64 and AArch64: correctly rounded, and a NaN keeps its sign
and the top 22 payload bits and comes out quiet. -/
def toFloat32Bits (x : F64) : Nat :=
  if x.isNaN then
    (if x.sign then 2 ^ 31 else 0) + 0x7fc00000 + (x.frac / 2 ^ 29) % 2 ^ 22
  else if x.isInf then (if x.sign then 0xff800000 else 0x7f800000)
  else if x.isZero then (if x.sign then 2 ^ 31 else 0)
  else
    let q := x.toRat
    binary32.encode x.sign (roundPos binary32 q.num.natAbs q.den)

/-- `PyFloat_Pack4`, floatobject.c:2003-2066. -/
def PyFloat_Pack4 (x : F64) (le : Bool) : Py (List Nat) :=
  let y := toFloat32Bits x
  let yIsInf := y % 2 ^ 31 == 0x7f800000
  if yIsInf && !x.isInf then
    .error (.overflowError "float too large to pack with f format")
  else
    let y' :=
      if x.isNaN && (x.bits / 2 ^ 51) % 2 == 0 && y % 2 ^ 22 != 0 then y - 2 ^ 22 else y
    .ok (layout 4 y' le)

/-- `PyFloat_Pack8`, floatobject.c:2069-2087. -/
def PyFloat_Pack8 (x : F64) (le : Bool) : Py (List Nat) := .ok (layout 8 x.bits le)

/-- `PyFloat_Unpack2`, floatobject.c:2089-2143. -/
def PyFloat_Unpack2 (data : List Nat) (le : Bool) : F64 :=
  let b := unlayout data le
  let first := b / 256
  let second := b % 256
  let sign := (first / 128) % 2 == 1
  let e0 := (first &&& 0x7C) / 4
  let f := ((first &&& 0x03) * 256) ||| second
  if e0 == 0x1f then
    if f == 0 then F64.inf sign
    else
      F64.ofBits ((if sign then 0xfff0000000000000 else 0x7ff0000000000000) + f * 2 ^ 42)
  else
    let x0 := F64.div (F64.ofInt f) (F64.ofBits 0x4090000000000000)
    let (x1, e1) : F64 × Int :=
      if e0 == 0 then (x0, -14) else (F64.add x0 d1, (e0 : Int) - 15)
    let x2 := F64.ldexp x1 e1
    if sign then x2.neg else x2

/-- The conversion `(double)x` from a binary32 pattern. -/
def ofFloat32Bits (v : Nat) : F64 :=
  match binary32.view v with
  | .nan neg payload =>
    -- (double)x quiets a signaling NaN
    F64.ofBits ((if neg then 2 ^ 63 else 0) + 0x7ff8000000000000 + (payload % 2 ^ 22) * 2 ^ 29)
  | .inf neg => F64.inf neg
  | .finite neg m e =>
    let q := dyadic m e
    if m == 0 then F64.zero neg else F64.ofRat (if neg then -q else q)

/-- `PyFloat_Unpack4`, floatobject.c:2146-2201. -/
def PyFloat_Unpack4 (data : List Nat) (le : Bool) : F64 :=
  let v := unlayout data le
  let y := ofFloat32Bits v
  match binary32.view v with
  | .nan .. =>
    if (v / 2 ^ 22) % 2 == 0 then F64.ofBits (y.bits - 2 ^ 51) else y
  | _ => y

/-- `PyFloat_Unpack8`, floatobject.c:2204-2224. -/
def PyFloat_Unpack8 (data : List Nat) (le : Bool) : F64 :=
  F64.ofBits (unlayout data le)

/-- `nu_float`, Modules/_struct.c:483-488: `(double)x`, with none of the signaling-NaN
care of `PyFloat_Unpack4`. 3.15 removed the "Skip float and double" exception from
`init_endian_tables` (_struct.c:1519-1558), so on a little-endian host `<f` and `=f`
come here as well as native `f`, and only `>f` still calls `PyFloat_Unpack4`. -/
def nu_float (data : List Nat) : F64 := ofFloat32Bits (unlayout data true)

end PyLean.Binary64
