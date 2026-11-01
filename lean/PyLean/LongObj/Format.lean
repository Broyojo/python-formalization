import PyLean.LongObj.Digits

/-!
`int` to string, `Objects/longobject.c` (CPython 3.14.7): the base-`10^9` loop of
`long_to_decimal_string_internal` with its pre-check and exact digit count, and
the shift-and-mask loop of `long_format_binary`.

`interp->long_state.max_str_digits` is the explicit parameter `lim`
(`sys.set_int_max_str_digits` allows `0`, meaning no limit, or at least `640`,
sysmodule.c:4533).

Output buffers are filled right to left in C (`*--p = ...`): the model conses
onto `acc`, and the final length check stands for `assert(p == start)`. A theorem
of the form `f x = .ok s` therefore also says that the computed `strlen`/`sz` is
exactly the number of characters written, so the writes stay inside the buffer.
`pout` writes are capacity-checked in the same way.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-! ## Constants -/

/-- `_PY_LONG_MAX_STR_DIGITS_THRESHOLD`, pycore_long.h:42. -/
def strDigitsThreshold : Nat := 640
/-- `_PY_LONG_DEFAULT_MAX_STR_DIGITS`, pycore_long.h:29. -/
def defaultMaxStrDigits : Nat := 4300
/-- `_PyLong_DECIMAL_SHIFT`, longintrepr.h:48. -/
def decShift : Nat := 9
/-- `_PyLong_DECIMAL_BASE`, longintrepr.h:49. -/
def decBase : Nat := 10 ^ 9

/-- `sys.set_int_max_str_digits` admits `0` or anything from the threshold up,
sysmodule.c:4533. -/
def ValidLimit (lim : Nat) : Prop := lim = 0 ∨ strDigitsThreshold ≤ lim

/-- `_MAX_STR_DIGITS_ERROR_FMT_TO_STR`, longobject.c:31. -/
def limitToStrMsg (lim : Nat) : String :=
  s!"Exceeds the limit ({lim} digits) for integer string conversion; use sys.set_int_max_str_digits() to increase the limit"

/-! ## Decimal conversion, base `10^9` limbs -/

/-- The inner `for (j = 0; j < size; j++)` loop, longobject.c:2102-2107. -/
def decStep : List Nat → Nat → Py (List Nat × Nat)
  | [], hi => .ok ([], hi)
  | p :: ps, hi => do
    let z ← chk64 ((p <<< 30) ||| hi)
    let hi' ← chk32 (z / decBase)
    let p' ← chk32 (z - hi' * decBase)
    let (r, h) ← decStep ps hi'
    return (p' :: r, h)

/-- `while (hi) { pout[size++] = hi % DECIMAL_BASE; hi /= DECIMAL_BASE; }`,
longobject.c:2108-2111. `cap` is the allocated size of `scratch`. -/
def pushHi (cap : Nat) : Nat → List Nat → Nat → Py (List Nat)
  | 0, _, _ => .error .modelFuel
  | f + 1, pout, hi =>
    if hi ≠ 0 then
      if pout.length < cap then pushHi cap f (pout ++ [hi % decBase]) (hi / decBase)
      else .error cOverflow
    else .ok pout

/-- The outer loop `for (i = size_a; --i >= 0; )`, longobject.c:2100-2117, reading
`pin` from the top digit; `SIGCHECK` has no effect on a value. -/
def decLoop (cap : Nat) : List Nat → List Nat → Py (List Nat)
  | [], pout => .ok pout
  | d :: ds, pout => do
    let (p, hi) ← decStep pout d
    let p' ← pushHi cap 3 p hi
    decLoop cap ds p'

/-- `while (rem >= tenpow) { tenpow *= 10; strlen++; }`, longobject.c:2127-2130;
`tenpow` is a `digit`. Returns the number of `strlen++`. -/
def lenLoop : Nat → Nat → Nat → Nat → Py Nat
  | 0, _, _, _ => .error .modelFuel
  | f + 1, rem, tenpow, n =>
    if rem ≥ tenpow then do
      let t ← chk32 (tenpow * 10)
      lenLoop f rem t (n + 1)
    else .ok n

/-- `*--p = '0' + rem % 10; rem /= 10;` repeated `j` times, longobject.c:2169-2172. -/
def writeFixed : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | j + 1, rem, acc => writeFixed j (rem / 10) (Char.ofNat (48 + rem % 10) :: acc)

/-- `do { *--p = '0' + rem % 10; rem /= 10; } while (rem != 0);`,
longobject.c:2176-2179. -/
def writeTop : Nat → Nat → List Char → Py (List Char)
  | 0, _, _ => .error .modelFuel
  | f + 1, rem, acc =>
    let acc' := Char.ofNat (48 + rem % 10) :: acc
    if rem / 10 ≠ 0 then writeTop f (rem / 10) acc' else .ok acc'

/-- The `for` loop over `pout[0..size-2]` and the top limb, longobject.c:2167-2179. -/
def writeLimbs : List Nat → List Char → Py (List Char)
  | [], _ => .error cOverflow
  | [t], acc => writeTop 10 t acc
  | p :: q :: ps, acc => writeLimbs (q :: ps) (writeFixed decShift p acc)

/-- Lines 2086-2240 of `long_to_decimal_string_internal`: everything after the
switch to `_pylong`. All three output targets (`PyUnicode_New`, `writer`,
`bytes_writer`) receive the same characters. -/
def decCore (lim : Nat) (x : Long) : Py (List Char) := do
  let size_a := x.ds.length
  let d := (33 * decShift) / (10 * 30 - 33 * decShift)
  let size := 1 + size_a + size_a / d
  longAlloc size
  let pout ← decLoop size x.ds.reverse []
  let pout := if pout.length = 0 then [0] else pout
  let negative := if x.neg then 1 else 0
  let n ← lenLoop 11 (pout.getLastD 0) 10 0
  let strlen := negative + 1 + (pout.length - 1) * decShift + n
  if strlen > strDigitsThreshold then
    let strlen_nosign := strlen - negative
    if lim > 0 ∧ strlen_nosign > lim then
      throw (.valueError (limitToStrMsg lim))
  let acc ← writeLimbs pout []
  let acc := if x.neg then '-' :: acc else acc
  if acc.length = strlen then return acc else throw cOverflow

/-- The pre-check at longobject.c:2049-2059, based on `10/3 >= log2(10)`. -/
def decPreCheck (lim size_a : Nat) : Py Unit :=
  if size_a ≥ 10 * strDigitsThreshold / (3 * 30) + 2 then
    if lim > 0 ∧ lim / (3 * 30) ≤ (size_a - 11) / 10 then
      .error (.valueError (limitToStrMsg lim))
    else .ok ()
  else .ok ()

/-- `long_to_decimal_string_internal(aa, ...)`, longobject.c:2020-2240; `pyl` is
`pylong_int_to_decimal_string` (the switch at :2061-2070). -/
def longToDecimalWith (pyl : Long → Py (List Char)) (lim : Nat) (x : Long) : Py (List Char) := do
  let size_a := x.ds.length
  decPreCheck lim size_a
  if size_a > 1000 then pyl x else decCore lim x

/-! ## Power-of-two bases -/

/-- `bit_length_digit(x)`, longobject.c:889, through `_Py_bit_length`. -/
def bitLengthDigit (x : Nat) : Nat := bitLength x

/-- `PY_SSIZE_T_MAX`. -/
def ssizeMax : Nat := 2 ^ 63 - 1

/-- The `do { ... } while` loop of `WRITE_DIGITS`, longobject.c:2344-2351. `last`
is `i == size_a-1`. `accumbits` is a C `int`; on the last digit it may go below
zero, where it is no longer read. -/
def fmtWhile (base bits : Nat) (last : Bool) :
    Nat → Nat → Int → List Char → Py (Nat × Int × List Char)
  | 0, _, _, _ => .error .modelFuel
  | f + 1, accum, ab, acc =>
    let cdigit := accum &&& (base - 1)
    let c := cdigit + (if cdigit < 10 then 48 else 97 - 10)
    let acc' := Char.ofNat c :: acc
    let ab' := ab - (bits : Int)
    let accum' := accum >>> bits
    if (if last then decide (accum' > 0) else decide (ab' ≥ (bits : Int))) then
      fmtWhile base bits last f accum' ab' acc'
    else .ok (accum', ab', acc')

/-- The `for (i = 0; i < size_a; ++i)` loop, longobject.c:2340-2352. -/
def fmtLoop (base bits : Nat) : List Nat → Nat → Int → List Char → Py (List Char)
  | [], _, _, acc => .ok acc
  | d :: ds, accum, ab, acc => do
    let a ← chk64 (accum ||| (d <<< ab.toNat))
    let (a', ab', acc') ← fmtWhile base bits ds.isEmpty 64 a (ab + 30) acc
    fmtLoop base bits ds a' ab' acc'

/-- `long_format_binary(aa, base, alternate, ...)`, longobject.c:2257-2419, for
`base` one of 2, 8, 16. All output targets receive the same characters. -/
def longFormatBinary (x : Long) (base : Nat) (alternate : Bool) : Py (List Char) := do
  let size_a := x.ds.length
  let negative := if x.neg then 1 else 0
  let bits := if base = 16 then 4 else if base = 8 then 3 else 1
  let sz ←
    if size_a = 0 then pure 1
    else if size_a > (ssizeMax - 3) / 30 then
      throw (.overflowError "int too large to format")
    else
      let size_a_in_bits := (size_a - 1) * 30 + bitLengthDigit (x.ds.getLastD 0)
      pure (negative + (size_a_in_bits + (bits - 1)) / bits)
  let sz := if alternate then sz + 2 else sz
  let acc ← if size_a = 0 then pure ['0'] else fmtLoop base bits x.ds 0 0 []
  let acc :=
    if alternate then
      '0' :: (if base = 16 then 'x' else if base = 8 then 'o' else 'b') :: acc
    else acc
  let acc := if x.neg then '-' :: acc else acc
  if acc.length = sz then return acc else throw cOverflow

/-- `_PyLong_Format(obj, base)`, longobject.c:2422-2433. -/
def pyLongFormatWith (pyl : Long → Py (List Char)) (lim : Nat) (x : Long) (base : Nat) :
    Py (List Char) :=
  if base = 10 then longToDecimalWith pyl lim x else longFormatBinary x base true

/-- `_PyLong_FormatWriter(writer, obj, base, alternate)`, longobject.c:2436-2446,
and `_PyLong_FormatBytesWriter(...)`, longobject.c:2449-2466: the same dispatch
into a writer. -/
def pyLongFormatWriterWith (pyl : Long → Py (List Char)) (lim : Nat) (x : Long) (base : Nat)
    (alternate : Bool) : Py (List Char) :=
  if base = 10 then longToDecimalWith pyl lim x else longFormatBinary x base alternate

end PyLean.LongObj
